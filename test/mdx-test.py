#!/usr/bin/env python3
#
# Run an integration test suite using mdx
#
# This script is responsible for:
#
# - Sequencing two command invoations (ocaml-mdx and diff)
# - Ensures pretty feedback on test failure
# - Provides some defensive automation to protect against misuse or common
#   errors
# - Managing paths in a general way, to prevent polluting our working directory
#   with test artifacts
#
# See tla/cli-integration-tests.md for on usage details.
#
# Shon Feder, 2020

import argparse
import logging
import os
import sys

from pathlib import Path
from subprocess import run, Popen, PIPE, STDOUT

logger = logging.getLogger("integration test logger")
logger.setLevel(logging.DEBUG)

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


def configure_logger(debug: bool) -> None:
    formatter = logging.Formatter("[%(asctime)s] %(levelname)s:%(message)s")

    console_handler_level = logging.DEBUG if debug else logging.WARNING
    console_handler = logging.StreamHandler()
    console_handler.setLevel(console_handler_level)

    file_handler = logging.FileHandler(log_file)
    file_handler.setLevel(logging.DEBUG)

    for h in (console_handler, file_handler):
        h.setFormatter(formatter)
        logger.addHandler(h)

    logger.debug(f"Output level: {logging.getLevelName(console_handler_level)}")


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
    parser.add_argument(
        "--debug",
        "-d",
        action="store_true",
        default=False,
        help="Enable debugging output",
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

    # Must come after the `test_target_dir` is created
    configure_logger(args.debug)

    # Run the mdx tests to generate the corrected file
    cmd = [
        "ocaml-mdx",
        "test",
        "--verbosity",
        "info",
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

    process = Popen(cmd, stdout=PIPE, stderr=PIPE)
    logger.debug(f"running command: {' '.join(list(process.args))}")
    while process.poll() is None:
        line = process.stderr.readline().rstrip()
        logger.info(line)

    if process.returncode != 0:
        logger.error(f"Failed to run test. Check {log_file}. Error: {process.stderr}")
        sys.exit(1)

    # Run diff to check the corrected results against the expected results
    result = run(["diff", "--unified=4", test_file_str, corrected_file_str])
    sys.exit(result.returncode)
