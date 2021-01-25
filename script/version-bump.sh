#!/usr/bin/env bash
set -euo pipefail

set -o xtrace

# Increment the version to a SNAPSHOT and update the changelog
#
# NOTE: While this script can be run locally, is mainly desgined for use in our
# `prepare-release` CI workflow.

# The directory of this file
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
# shellcheck source=./shared.sh
. "$DIR"/shared.sh

cd "$PROJ_ROOT"

VERSION=$("$DIR"/get-version.sh)

msg=$(git show -s --format=%s HEAD)
if [[ "$msg" != "[release] ${VERSION}" ]]
then
    echo "error: HEAD commit must be a [release] commit"
    echo "found: ${msg}"
    exit 4
fi

# Bump version to next SNAPSHOT
mvn --batch-mode release:update-versions -DautoVersionSubmodules=true

"$DIR"/update-changes.sh

DEV_VERSION=$("$DIR"/get-version.sh)
git add --update
git commit -m "Bump version to ${DEV_VERSION}"
