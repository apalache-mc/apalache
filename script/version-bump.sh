#!/usr/bin/env bash
set -euo pipefail

set -o xtrace

# Increment the version to a SNAPSHOT and update the changelog

# The directory of this file
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
# shellcheck source=./shared.sh
. "$DIR"/shared.sh

VERSION=$("$DIR"/get-version.sh)
"$DIR"/update-changes.sh
git add --update
git commit -m "Update changelog for version ${VERSION}"

mvn --batch-mode release:update-versions -DautoVersionSubmodules=true

DEV_VERSION=$("$DIR"/get-version.sh)
git add --update
git commit -m "Bump version to ${DEV_VERSION}"
