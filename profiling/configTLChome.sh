#!/bin/bash

set -e 

TLC_HOME=$1

die () {
    echo >&2 "$@"
    exit 1
}

[ "$#" -eq 1 ] || die "1 argument required, $# provided"

echo $TLC_HOME > tlchome.conf