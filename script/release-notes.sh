#!/usr/bin/env bash

# Run this script to create release notes based on the changes recorded in the
# UNRELEASED.md file. The version for the release notes is determined by the
# version of the software specified in the pom.xml.

set -euo pipefail

# The directory of this file
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
# shellcheck source=./shared.sh
source "$DIR"/shared.sh

RELEASE_VERSION=${RELEASE_VERSION:-''}

PREAMBLE="<!-- NOTE:
     Release notes for unreleased changes go here, following this format:

        ### Feature Category 1

         * Change description, see #123

        ### Feature Category 2

         * Another change description, see #124

     DO NOT LEAVE A BLANK LINE BELOW THIS PREAMBLE -->"

PREAMBLE_LINES=$(( $(echo "$PREAMBLE" | wc -l | cut -d' ' -f 1) + 1))

if [ -z "$RELEASE_VERSION" ]
then
    # See https://stackoverflow.com/a/26514030/1187277
    RELEASE_VERSION=$(mvn -q \
        -Dexec.executable=echo \
        -Dexec.args='${project.version}' \
        --non-recursive \
        exec:exec)
fi

echo "## $RELEASE_VERSION" > "$RELEASE_NOTES"
echo "" >> "$RELEASE_NOTES"
tail -n +"$PREAMBLE_LINES" "$UNRELEASED" >> "$RELEASE_NOTES"

# Reinit the UNRELEASED file
echo "$PREAMBLE" > "$UNRELEASED"
