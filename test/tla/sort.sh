#!/usr/bin/env bash
#
# This script aims for a stable sorting accross *nix systems
# see `man sort` for information on the options.

set -euf -o pipefail

export LC_ALL=C

sort --ignore-case --stable --dictionary-order
