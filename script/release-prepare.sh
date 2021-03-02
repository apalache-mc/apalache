#!/usr/bin/env bash
set -euo pipefail

set -o xtrace

# Prepare a release on the current branch.
#
# NOTE: You must have a release commit checked out to run thie script
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
    mvn versions:set -DnewVersion="${RELEASE_VERSION}"
else
    # Derive the relesae version by removing the -SNAPSHOT suffix
    mvn versions:set -DremoveSnapshot
    RELEASE_VERSION=$("$DIR"/get-version.sh)
fi

# Prepare the release on a new branch
git checkout -b "release/${RELEASE_VERSION}"

# Generate the release notes
RELEASE_VERSION=$RELEASE_VERSION "$DIR"/release-notes.sh

# Make the release commit
commit_msg="[release] ${RELEASE_VERSION}"
git add --update
git add "$RELEASE_NOTES"
git commit -m "$commit_msg"

if [[ "$POST_BODY" == true ]]
then
    body=$(cat "$RELEASE_NOTES")
else
    body=''
fi

body=$(cat "$RELEASE_NOTES")

# Bump the version
"$DIR"/version-bump.sh

instructions="
# Reviewer instructions

- Check the changelog to ensure the version increment is consistent with https://semver.org/.
  - If a different version should be released, follow [the instructions](https://github.com/informalsystems/apalache/blob/unstable/CONTRIBUTING.md#via-github).
- Review the changeset as a sanity check.
- Approve the PR, if it pases muster.
- **Merge** this branch (do not squash or rebase), but **DO NOT DELETE THE BRANCH**.
- After the release has been published to github, delete this branch.

---

# Release notes

"

# Open a pull request for the release
# See https://hub.github.com/hub-pull-request.1.html
hub pull-request \
    --push \
    --message="$instructions" \
    --message="$commit_msg" --message="$body" \
    --base="unstable"
