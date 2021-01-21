#!/usr/bin/env bash
set -euo pipefail

# Shared variables used in other scripts

exports () {
    # The directory of this file
    local DIR
    DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

    export PROJ_ROOT=$DIR"/.."
    export UNRELEASED=$PROJ_ROOT"/UNRELEASED.md"
    export CHANGES=$PROJ_ROOT"/CHANGES.md"
    export RELEASE_NOTES=$PROJ_ROOT"/RELEASE-NOTES.md"
}
exports
