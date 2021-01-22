#!/usr/bin/env bash
set -euo pipefail

# Fetch the version of the project from mvn
#
# NOTE: While this script can be run locally, is mainly desgined for use in our
# `prepare-release` and `release` CI workflows.

# The directory of this file
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
# shellcheck source=./shared.sh
source "$DIR"/shared.sh

# We need to be in the root dir to get the project version from mvn
cd "$PROJ_ROOT"

# See https://stackoverflow.com/a/26514030/1187277
mvn -q \
    -Dexec.executable=echo \
    -Dexec.args='${project.version}' \
    --non-recursive \
    exec:exec
