import json
import sys
import tempfile
import unittest
from pathlib import Path


REPOSITORY_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPOSITORY_ROOT / "script"))

from cli_integration_timing_report import (  # noqa: E402
    TestTiming,
    distribution,
    is_outlier,
    read_timings,
    render_markdown,
)


class TimingReportTest(unittest.TestCase):
    def test_inclusive_quartiles_and_tukey_outliers(self):
        timings = [self.timing(duration) for duration in [100, 100, 100, 100, 1000]]

        stats = distribution(timings)

        self.assertIsNotNone(stats)
        assert stats is not None
        self.assertEqual(100, stats.q1_ms)
        self.assertEqual(100, stats.median_ms)
        self.assertEqual(100, stats.q3_ms)
        self.assertTrue(is_outlier(timings[-1], stats))

    def test_odd_and_even_medians(self):
        odd = distribution([self.timing(value) for value in [1, 2, 9]])
        even = distribution([self.timing(value) for value in [1, 2, 3, 4]])

        assert odd is not None and even is not None
        self.assertEqual(2, odd.median_ms)
        self.assertEqual(2.5, even.median_ms)
        self.assertEqual(1.75, even.q1_ms)
        self.assertEqual(3.25, even.q3_ms)

    def test_reads_multiple_configurations_and_reports_incomplete_test(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.write_events(
                root / "general.jsonl",
                [
                    self.started("general", "suite-a", "Suite A", "fast", 10),
                    self.finished("general", "suite-a", "Suite A", "fast", 20, 10),
                    self.started("general", "suite-a", "Suite A", "stuck", 30),
                ],
            )
            self.write_events(
                root / "arrays-z3.jsonl",
                [
                    self.started("arrays-z3", "suite-b", "Suite B", "check", 40),
                    self.finished("arrays-z3", "suite-b", "Suite B", "check", 65, 25),
                ],
            )

            timings, warnings = read_timings(root.glob("*.jsonl"))

        self.assertEqual([], warnings)
        self.assertEqual(
            {"general", "arrays-z3"}, {item.configuration for item in timings}
        )
        incomplete = [item for item in timings if item.status == "incomplete"]
        self.assertEqual(["stuck"], [item.test_name for item in incomplete])

    def test_markdown_contains_native_chart_legend_fallback_and_escaping(self):
        timings = [
            self.timing(100, name="uses | pipe"),
            self.timing(100, name="median"),
            self.timing(100, name="also median"),
            self.timing(100, name="still median"),
            self.timing(1000, name="factorization"),
        ]

        markdown = render_markdown(timings, "ubuntu / general", [])

        self.assertIn("```mermaid", markdown)
        self.assertIn("xychart-beta", markdown)
        self.assertIn("line [100, 100, 100, 100, 100]", markdown)
        self.assertIn("Suite — uses \\| pipe", markdown)
        self.assertIn("`████", markdown)
        self.assertIn("⚠️", markdown)

    def test_malformed_record_becomes_warning_instead_of_hiding_results(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "general.jsonl"
            path.write_text("not-json\n", encoding="utf-8")

            timings, warnings = read_timings([path])

        self.assertEqual([], timings)
        self.assertEqual(1, len(warnings))

    @staticmethod
    def timing(duration, configuration="general", name="test"):
        return TestTiming(configuration, "suite", "Suite", name, "succeeded", 1, duration)

    @staticmethod
    def started(configuration, suite_id, suite_name, test_name, timestamp):
        return {
            "schemaVersion": 1,
            "event": "started",
            "configuration": configuration,
            "suiteId": suite_id,
            "suiteName": suite_name,
            "testName": test_name,
            "timestampEpochMillis": timestamp,
        }

    @staticmethod
    def finished(configuration, suite_id, suite_name, test_name, timestamp, duration):
        return {
            "schemaVersion": 1,
            "event": "finished",
            "configuration": configuration,
            "suiteId": suite_id,
            "suiteName": suite_name,
            "testName": test_name,
            "status": "succeeded",
            "timestampEpochMillis": timestamp,
            "durationMillis": duration,
        }

    @staticmethod
    def write_events(path, events):
        path.write_text(
            "".join(json.dumps(event) + "\n" for event in events), encoding="utf-8"
        )


if __name__ == "__main__":
    unittest.main()
