#!/usr/bin/env bash
set -euo pipefail

set -o xtrace

# Prepare a release on the current branch.
#
# NOTE: You must have a release commit checked out to run this script
# successfully.
#
# NOTE: While this script can be run locally, is mainly desgined for use in our
# `prepare-release` CI workflow.

# Set to false to prevent posting release notes in pull request
POST_BODY=${POST_BODY:-'true'}

# The directory of this file
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
# shellcheck source=./shared.sh
. "$DIR"/shared.sh

cd "$PROJ_ROOT"

# make sure that we do not release uncommited files
if ! (git diff --exit-code && git diff --cached --exit-code) >/dev/null
then
    echo "error: Git directory is not clean. Remove changes to tracked files."
    exit 255
fi

RELEASE_VERSION=${RELEASE_VERSION:-''}

# Set the new version in the source code
if [ -n "$RELEASE_VERSION" ]
then
    # Explicitly set the release version
    sbt "setVersion ${RELEASE_VERSION}"
else
    # Derive the relesae version by removing the -SNAPSHOT suffix
    sbt removeVersionSnapshot
    "$DIR"/get-version.sh
fi

sbt prepareRelease
