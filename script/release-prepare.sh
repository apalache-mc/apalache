#!/usr/bin/env bash
set -euo pipefail

set -o xtrace

# Perpare a release on the current branch

# The directory of this file
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
# shellcheck source=./shared.sh
. "$DIR"/shared.sh

# make sure that we do not release uncommited files
if ! (git diff --exit-code && git diff --cached --exit-code) >/dev/null
then
    echo "error: Git directory is not clean. Remove changes to tracked files."
    exit 255
fi

RELEASE_VERSION=${RELEASE_VERSION:-''}

if [ -n "$RELEASE_VERSION" ]
then
    # Explicitly set the release version
    mvn versions:set -DnewVersion="${RELEASE_VERSION}"
else
    # Derive the relesae version by removing the -SNAPSHOT suffix
    mvn versions:set -DremoveSnapshot
    RELEASE_VERSION=$("$DIR"/get-version.sh)
fi

git checkout -b "release/${RELEASE_VERSION}"
RELEASE_VERSION=$RELEASE_VERSION "$DIR"/release-notes.sh

git add --update
git add "$RELEASE_NOTES"
git commit -m "[release] ${RELEASE_VERSION}"
