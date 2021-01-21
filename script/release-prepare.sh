#!/usr/bin/env bash
set -euo pipefail

set -o xtrace

# Perpare a release on the current branch

# Set to false to prevent posting release notes in pull request
POST_BODY=${POST_BODY:-'true'}

# Whether we are running this in CI. Set to true automatically by GitHub
CI=${CI:-'fase'}

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
    mvn versions:set -DnewVersion="${RELEASE_VERSION}"
else
    # Derive the relesae version by removing the -SNAPSHOT suffix
    mvn versions:set -DremoveSnapshot
    RELEASE_VERSION=$("$DIR"/get-version.sh)
fi

# Prepare the release on a new branch
git checkout -b "release/${RELEASE_VERSION}"

# Generatre the release notes
RELEASE_VERSION=$RELEASE_VERSION "$DIR"/release-notes.sh

# Make the release commit
commit_msg="[release] ${RELEASE_VERSION}"
git add --update
git add "$RELEASE_NOTES"
git commit -m "$commit_msg"

if [[ "$CI" == true ]]
then
    # We use these artifacts when publishing the release
    make apalache
    git rev-parse HEAD > release-commit-sha
fi

if [[ "$POST_BODY" == true ]]
then
    body=$(cat "$RELEASE_NOTES")
else
    body=''
fi

body=$(cat "$RELEASE_NOTES")

# Bump the version
"$DIR"/version-bump.sh

# Open a pull request for the release
# See https://hub.github.com/hub-pull-request.1.html
hub pull-request \
    --push \
    --message="$commit_msg" --message="$body" \
    --base="unstable"
