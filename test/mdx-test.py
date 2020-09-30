#!/usr/bin/env python3
#
# Run an integration test suite using mdx
# See the tla/cli-integration-tests.md for details.
#
# Shon Feder, 2020

import argparse
import logging
import os
import sys

from pathlib import Path
from subprocess import run, PIPE


# NOTE: The script assumes the /.envrc file in this repo's root has been loaded

DEFAULT_TEST_FILE = "cli-integration-tests.md"
LOG_FILE = "mdx-test.log"


def get_target_dir() -> Path:
    target_dir_str = os.getenv("TARGET_DIR")
    if target_dir_str is None:
        raise RuntimeError(
            "Environment variable TARGET_DIR is not set. Ensure /.envrc is sourced."
        )
    return Path(target_dir_str) / "test"


def configure_logger() -> None:
    console_handler = logging.StreamHandler()
    console_handler.setLevel(logging.WARNING)
    logging.basicConfig(
        format="[%(asctime)s] %(levelname)s:%(message)s",
        filename=log_file,
        level=logging.DEBUG,
        handlers=[console_handler],
    )


def cli_parser(working_dir) -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Run an mdx integration test")
    parser.add_argument(
        "--test_file",
        metavar="TEST_FILE",
        type=Path,
        default=Path(working_dir / DEFAULT_TEST_FILE),
        help="Markdown file containing integration tests in code blocks",
    )
    parser.add_argument(
        "test",
        metavar="TEST",
        default=None,
        nargs="?",
        help="Test to run. Determined by markdown section headers",
    )
    return parser


# Workaround for desired behavior while following issue is pending
# https://github.com/realworldocaml/mdx/issues/289
def test_is_in_file(test: str, f: Path) -> bool:
    with f.open("r") as f:
        return test in f.read()


if __name__ == "__main__":
    # Directories in our working context
    this_dir = Path(os.path.dirname(os.path.realpath(__file__)))
    working_dir = this_dir / "tla"
    target_dir = get_target_dir()

    log_file = target_dir / LOG_FILE

    args = cli_parser(working_dir).parse_args()

    # The file holding the integration tests
    test_file = args.test_file.resolve()

    # The directory we'll write test artifacts to
    test_target_dir = target_dir / test_file.parent.relative_to(this_dir)
    # Ensure the directory exists
    test_target_dir.mkdir(parents=True, exist_ok=True)

    # The file where the corrected results are written
    corrected_file = test_target_dir / (test_file.name + ".corrected")

    working_dir_str = str(working_dir)
    test_file_str = str(corrected_file)
    corrected_file_str = str(test_file)

    # Run the mdx tests to generate the corrected file
    cmd = [
        "ocaml-mdx",
        "test",
        "--root",
        working_dir_str,
        "--output",
        test_file_str,
        corrected_file_str,
    ]
    if args.test is not None:
        if test_is_in_file(args.test, test_file):
            cmd.extend(["--section", args.test])
        else:
            print(
                f"Test cannot be run: there is no section {args.test} in file {str(test_file)} ",
                file=sys.stderr,
            )
            sys.exit(1)

    result = run(cmd, stdout=PIPE, stderr=PIPE)
    logging.debug(f"command args: {result.args}")

    if result.returncode != 0:
        logging.error(f"Failed to run test. Check {log_file}. Result: {result}")
        sys.exit(1)

    # Run diff to check the corrected results against the expected results
    cmd = ["diff", "--unified=4"]
    cmd.extend([test_file_str, corrected_file_str])
    result = run(cmd)
    sys.exit(result.returncode)
