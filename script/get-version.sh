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

cat "$PROJ_ROOT/VERSION"
