#!/usr/bin/env bash

# Run this script to update the CHANGES.md with the RELEASE-NOTES.md used in
# the last release.

set -euo pipefail

# The directory of this file
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
# shellcheck source=./shared.sh
source "$DIR"/shared.sh

PREAMBLE="<!-- NOTE:
     This file is generated. Do not write release notes here.
     Notes for unreleased changes go in ./UNRELEASED.md -->
"

PREAMBLE_LINES=$(( $(echo "$PREAMBLE" | wc -l | cut -d' ' -f 1) + 1))

# See https://unix.stackexchange.com/a/181938/95793
tmpfile=$(mktemp /tmp/release-notes-script.XXXXXX)
# Descriptor for writing
exec 3>"$tmpfile"
# Descriptor for reading (see https://stackoverflow.com/a/55435723/1187277)
exec 4<"$tmpfile"
# Ensures the tmp file is deleted when the script ends
rm "$tmpfile"

# Save the existing changelog (minus the preamble) into the temp file
tail -n +"$PREAMBLE_LINES" "$CHANGES" >&3

# Overwrite the changes with a new preabmle
echo "$PREAMBLE" > "$CHANGES"
# Update the change log with the new release notes
(cat "$RELEASE_NOTES"; echo "") >> "$CHANGES"
# Append the previous changes
cat <&4 >> "$CHANGES"

rm "$RELEASE_NOTES"
