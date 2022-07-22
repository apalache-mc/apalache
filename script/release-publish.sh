#!/usr/bin/env bash
set -euo pipefail

set -o xtrace

# Package a release and tag the commit
#
# NOTE: While this script can be run locally, is mainly designed for use in our
# `release` CI workflow.

# The directory of this file
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
# shellcheck source=./shared.sh
. "$DIR"/shared.sh

# make sure that we do not release uncommited files
if ! (git diff --exit-code && git diff --cached --exit-code) >/dev/null
then
    echo "error: Git directory is not clean. Remove changes to tracked files."
    exit 3
fi

VERSION=$("$DIR"/get-version.sh)
msg=$(git show -s --format=%s HEAD)

if [[ "$msg" != "[release] ${VERSION}" ]]
then
    echo "error: HEAD commit must be a [release] commit"
    echo "found: ${msg}"
    exit 4
fi

if ! [ -f "$RELEASE_NOTES" ]
then
    echo "error: No RELEASE.md found"
    exit 5
fi

make dist

# Package the artifacts
# The archives without version suffix support stable links to the latest version.
# See https://github.com/informalsystems/apalache/issues/716
ZIPF="target/universal/apalache-${VERSION}.zip"
ZIPF_NO_VER="target/universal/apalache.zip"

TGZF="target/universal/apalache-${VERSION}.tgz"
TGZF_NO_VER="target/universal/apalache.tgz"

SHA256F="target/universal/sha256sum.txt"
(cd target/universal && sha256sum {apalache*.tgz,apalache*.zip} > sha256sum.txt)
# We put a `v` in front of our versions for tags
TAG_NAME="v${VERSION}"

# Tag the commit and push the tag
git tag -a "$TAG_NAME" -m "$msg"
git push --tags

# Publish the release
body=$(cat "$RELEASE_NOTES")
hub release create \
    --attach="$ZIPF" --attach="$ZIPF_NO_VER" \
    --attach="$TGZF" --attach="$TGZF_NO_VER" --attach="$SHA256F" \
    --message="$TAG_NAME" --message="$body" \
    "$TAG_NAME"
