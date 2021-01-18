#!/usr/bin/env bash
set -euo pipefail

set -o xtrace

# Package a release and tag the commit

# The directory of this file
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
# shellcheck source=./shared.sh
. "$DIR"/shared.sh

msg=$(git show -s --format=%s HEAD)

if ! [[ "$msg" != "[release] ${VERSION}" ]]
then
    echo "error: HEAD commit must be a [release] commit"
    echo "found: ${msg}"
    exit 4
fi

release="mod-distribution/target/apalache-pkg-${VERSION}-full.jar"

if [ ! -f "$release" ]; then
    echo "Release file not found: $release"
    exit 3
fi

# TODO remove echos
echo git tag -a "v${VERSION}" -m "$msg"
echo git push -tags

# overwrite the build number
BUILD=$(git describe --tags)

ZIPF="apalache-${BUILD}.zip"
TGZF="apalache-${BUILD}.tgz"

zip -r "$ZIPF" bin/apalache-mc "$release"
tar zpcf "$TGZF" bin/apalache-mc "$release"
