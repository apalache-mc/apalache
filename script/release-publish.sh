#!/usr/bin/env bash
set -euo pipefail

set -o xtrace

# Package a release and tag the commit

# The directory of this file
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
# shellcheck source=./shared.sh
. "$DIR"/shared.sh

VERSION=$("$DIR"/get-version.sh)
msg=$(git show -s --format=%s HEAD)

# make sure that we do not release uncommited files
if ! (git diff --exit-code && git diff --cached --exit-code) >/dev/null
then
    echo "error: Git directory is not clean. Remove changes to tracked files."
    exit 3
fi

if [[ "$msg" != "[release] ${VERSION}" ]]
then
    echo "error: HEAD commit must be a [release] commit"
    echo "found: ${msg}"
    exit 4
fi

if ! [ -f "$RELEASE_NOTES" ]
then
    echo "error: No RELEASE-NOTES.md found"
    exit 5
fi

cd "$PROJ_ROOT"

# Build the package
make clean
make apalache

release="mod-distribution/target/apalache-pkg-${VERSION}-full.jar"

# Confirm the jar was produced
if [ ! -f "$release" ]; then
    echo "error: release file not found: $release"
    exit 6
fi

# Package the artifacts
TAG_NAME="v${VERSION}"

ZIPF="target/apalache-${TAG_NAME}.zip"
TGZF="target/apalache-${TAG_NAME}.tgz"
zip -r "$ZIPF" bin/apalache-mc "$release"
tar zpcf "$TGZF" bin/apalache-mc "$release"

# Tag the commit and push the tag
git tag -a $TAG_NAME -m "$msg"
git push --tags

# Publish the release
body=$(cat "$RELEASE_NOTES")
hub release create \
    --attach="$ZIPF" --attach="$TGZF" \
    --message="$TAG_NAME" --message="$body"
