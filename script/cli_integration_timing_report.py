#!/usr/bin/env python3
"""Render Scala CLI integration-test timings for a GitHub Actions summary."""

from __future__ import annotations

import argparse
import csv
import json
import math
import statistics
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Sequence


SCHEMA_VERSION = 1


@dataclass(frozen=True)
class TestTiming:
    configuration: str
    suite_id: str
    suite_name: str
    test_name: str
    status: str
    started_at_ms: int | None
    duration_ms: int | None

    @property
    def display_name(self) -> str:
        return f"{self.suite_name} — {self.test_name}"


@dataclass(frozen=True)
class Distribution:
    count: int
    total_ms: int
    q1_ms: float
    median_ms: float
    q3_ms: float
    max_ms: int
    upper_fence_ms: float


def read_timings(paths: Iterable[Path]) -> tuple[list[TestTiming], list[str]]:
    """Read JSONL event streams and pair starts with completions."""
    starts: dict[tuple[str, str, str], dict[str, object]] = {}
    timings: list[TestTiming] = []
    warnings: list[str] = []

    for path in sorted(paths):
        try:
            lines = path.read_text(encoding="utf-8").splitlines()
        except OSError as error:
            warnings.append(f"Could not read {path}: {error}")
            continue

        for line_number, line in enumerate(lines, start=1):
            if not line.strip():
                continue
            try:
                record = json.loads(line)
                if record.get("schemaVersion") != SCHEMA_VERSION:
                    raise ValueError(
                        f"unsupported schema version {record.get('schemaVersion')!r}"
                    )
                configuration = str(record["configuration"])
                suite_id = str(record["suiteId"])
                test_name = str(record["testName"])
                key = (configuration, suite_id, test_name)
                event = record["event"]
                if event == "started":
                    starts[key] = record
                elif event == "finished":
                    started = starts.pop(key, None)
                    duration_ms = int(record["durationMillis"])
                    timings.append(
                        TestTiming(
                            configuration=configuration,
                            suite_id=suite_id,
                            suite_name=str(record["suiteName"]),
                            test_name=test_name,
                            status=str(record["status"]),
                            started_at_ms=(
                                int(started["timestampEpochMillis"])
                                if started is not None
                                else int(record["timestampEpochMillis"]) - duration_ms
                            ),
                            duration_ms=duration_ms,
                        )
                    )
                else:
                    raise ValueError(f"unknown event {event!r}")
            except (KeyError, TypeError, ValueError, json.JSONDecodeError) as error:
                warnings.append(f"Ignored {path}:{line_number}: {error}")

    for (configuration, suite_id, test_name), record in starts.items():
        timings.append(
            TestTiming(
                configuration=configuration,
                suite_id=suite_id,
                suite_name=str(record["suiteName"]),
                test_name=test_name,
                status="incomplete",
                started_at_ms=int(record["timestampEpochMillis"]),
                duration_ms=None,
            )
        )

    return timings, warnings


def distribution(timings: Sequence[TestTiming]) -> Distribution | None:
    durations = sorted(
        timing.duration_ms for timing in timings if timing.duration_ms is not None
    )
    if not durations:
        return None
    if len(durations) == 1:
        q1_ms = q3_ms = float(durations[0])
    else:
        q1_ms, _, q3_ms = statistics.quantiles(
            durations, n=4, method="inclusive"
        )
    median_ms = float(statistics.median(durations))
    return Distribution(
        count=len(durations),
        total_ms=sum(durations),
        q1_ms=q1_ms,
        median_ms=median_ms,
        q3_ms=q3_ms,
        max_ms=max(durations),
        upper_fence_ms=q3_ms + 1.5 * (q3_ms - q1_ms),
    )


def is_outlier(timing: TestTiming, stats: Distribution) -> bool:
    return timing.duration_ms is not None and timing.duration_ms > stats.upper_fence_ms


def markdown_escape(value: str) -> str:
    return value.replace("\n", " ").replace("|", "\\|")


def format_duration(milliseconds: float) -> str:
    return f"{milliseconds / 1000.0:.3f} s"


def fallback_bar(duration_ms: int, maximum_ms: int, width: int = 20) -> str:
    filled = max(1, round(width * duration_ms / maximum_ms)) if maximum_ms else 0
    return "█" * filled + "░" * (width - filled)


def render_markdown(
    timings: Sequence[TestTiming], label: str, warnings: Sequence[str]
) -> str:
    by_configuration: dict[str, list[TestTiming]] = {}
    for timing in timings:
        by_configuration.setdefault(timing.configuration, []).append(timing)

    lines = [f"## CLI integration-test timings — {markdown_escape(label)}", ""]
    if warnings:
        lines.extend(["> [!WARNING]", "> Some timing records could not be read:"])
        lines.extend(f"> - {markdown_escape(warning)}" for warning in warnings)
        lines.append("")

    completed = [timing for timing in timings if timing.duration_ms is not None]
    if not completed:
        lines.extend(
            [
                "> [!WARNING]",
                "> No completed timing records were produced. The test worker may "
                "have failed before ScalaTest started.",
                "",
            ]
        )

    lines.extend(
        [
            "Times are grouped by test configuration. Outliers use Tukey's upper fence (Q3 + 1.5 × IQR).",
            "",
            "| Configuration | Tests | Total | Q1 | Median | Q3 | Max | Outliers |",
            "| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |",
        ]
    )
    for configuration in sorted(by_configuration):
        config_timings = by_configuration[configuration]
        stats = distribution(config_timings)
        if stats is None:
            lines.append(
                f"| {markdown_escape(configuration)} | 0 | — | — | — | — | — | 0 |"
            )
        else:
            outlier_count = sum(is_outlier(timing, stats) for timing in config_timings)
            lines.append(
                f"| {markdown_escape(configuration)} | {stats.count} | {format_duration(stats.total_ms)} "
                f"| {format_duration(stats.q1_ms)} | {format_duration(stats.median_ms)} "
                f"| {format_duration(stats.q3_ms)} | {format_duration(stats.max_ms)} | {outlier_count} |"
            )
    lines.append("")

    for configuration in sorted(by_configuration):
        config_timings = by_configuration[configuration]
        complete = sorted(
            (timing for timing in config_timings if timing.duration_ms is not None),
            key=lambda timing: timing.duration_ms or 0,
            reverse=True,
        )
        incomplete = sorted(
            (timing for timing in config_timings if timing.duration_ms is None),
            key=lambda timing: timing.display_name,
        )
        stats = distribution(config_timings)

        lines.extend([f"### {markdown_escape(configuration)}", ""])
        if incomplete:
            lines.extend(
                [
                    "> [!WARNING]",
                    f"> {len(incomplete)} test(s) started but did not finish:",
                ]
            )
            lines.extend(
                f"> - {markdown_escape(timing.display_name)}"
                for timing in incomplete
            )
            lines.append("")

        if stats is None:
            lines.extend(["No completed tests for this configuration.", ""])
            continue

        slowest = complete[:10]
        labels = ", ".join(f'"T{index}"' for index in range(1, len(slowest) + 1))
        bars = ", ".join(str(timing.duration_ms) for timing in slowest)
        medians = ", ".join(f"{stats.median_ms:g}" for _ in slowest)
        y_max = max(1, math.ceil(stats.max_ms * 1.05))
        lines.extend(
            [
                "```mermaid",
                "xychart-beta",
                f'    title "Slowest tests — {configuration}"',
                f"    x-axis [{labels}]",
                f'    y-axis "milliseconds" 0 --> {y_max}',
                f"    bar [{bars}]",
                f"    line [{medians}]",
                "```",
                "",
                f"The line is the configuration median ({format_duration(stats.median_ms)}). "
                "The distribution column is a text fallback for clients that do not render Mermaid.",
                "",
                "| ID | Test | Duration | × median | Distribution | Outlier |",
                "| --- | --- | ---: | ---: | --- | :---: |",
            ]
        )
        for index, timing in enumerate(slowest, start=1):
            assert timing.duration_ms is not None
            multiple = (
                f"{timing.duration_ms / stats.median_ms:.1f}×"
                if stats.median_ms > 0
                else "—"
            )
            marker = "⚠️" if is_outlier(timing, stats) else ""
            lines.append(
                f"| T{index} | {markdown_escape(timing.display_name)} | "
                f"{format_duration(timing.duration_ms)} | {multiple} | "
                f"`{fallback_bar(timing.duration_ms, stats.max_ms)}` | {marker} |"
            )
        lines.append("")

    return "\n".join(lines)


def write_csv(path: Path, timings: Sequence[TestTiming]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="") as output:
        writer = csv.writer(output)
        writer.writerow(
            [
                "configuration",
                "suite_id",
                "suite_name",
                "test_name",
                "status",
                "started_at_epoch_ms",
                "duration_ms",
            ]
        )
        for timing in sorted(
            timings, key=lambda item: (item.configuration, item.suite_name, item.test_name)
        ):
            writer.writerow(
                [
                    timing.configuration,
                    timing.suite_id,
                    timing.suite_name,
                    timing.test_name,
                    timing.status,
                    timing.started_at_ms if timing.started_at_ms is not None else "",
                    timing.duration_ms if timing.duration_ms is not None else "",
                ]
            )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--input",
        type=Path,
        required=True,
        help="Directory containing JSONL event files",
    )
    parser.add_argument(
        "--markdown", type=Path, required=True, help="Markdown summary output"
    )
    parser.add_argument(
        "--csv", type=Path, required=True, help="Flat CSV diagnostics output"
    )
    parser.add_argument(
        "--label", required=True, help="Runner/configuration label shown in the summary"
    )
    args = parser.parse_args()

    paths = args.input.glob("*.jsonl") if args.input.is_dir() else []
    timings, warnings = read_timings(paths)
    markdown = render_markdown(timings, args.label, warnings)
    args.markdown.parent.mkdir(parents=True, exist_ok=True)
    args.markdown.write_text(markdown, encoding="utf-8")
    write_csv(args.csv, timings)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
