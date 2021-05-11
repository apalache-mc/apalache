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
    echo "error: No RELEASE-NOTES.md found"
    exit 5
fi

cd "$PROJ_ROOT"

# Build the package
make clean
make apalache

# Relative location of the jar that gets published in releases
# This must be a relative path. Aboslute paths break the zip archive.
RELEASE_JAR="mod-distribution/target/apalache-pkg-${VERSION}-full.jar"

# Confirm the jar was produced
if [ ! -f "$RELEASE_JAR" ]; then
    echo "error: release file not found: $RELEASE_JAR"
    exit 6
fi

TAG_NAME="v${VERSION}"

# Ensure target directory exists
mkdir -p target

# Package the artifacts
# The archives without version suffix support stable links to the latest version.
# See https://github.com/informalsystems/apalache/issues/716
ZIPF="target/apalache-${TAG_NAME}.zip"
ZIPF_NO_VER="target/apalache.zip"
zip -r "$ZIPF" bin/apalache-mc "$RELEASE_JAR"
zip -r "$ZIPF_NO_VER" bin/apalache-mc "$RELEASE_JAR"

TGZF="target/apalache-${TAG_NAME}.tgz"
TGZF_NO_VER="target/apalache.tgz"
tar zpcf "$TGZF" bin/apalache-mc "$RELEASE_JAR"
tar zpcf "$TGZF_NO_VER" bin/apalache-mc "$RELEASE_JAR"

# Tag the commit and push the tag
git tag -a "$TAG_NAME" -m "$msg"
git push --tags

# Publish the release
body=$(cat "$RELEASE_NOTES")
hub release create \
    --attach="$ZIPF" --attach="$ZIPF_NO_VER" \
    --attach="$TGZF" --attach="$TGZF_NO_VER" \
    --message="$TAG_NAME" --message="$body" \
    "$TAG_NAME"
