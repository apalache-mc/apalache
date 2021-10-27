#!/usr/bin/env bash
#
# This script wraps invocation of apalache-mc docker imgages. It is uses
# to invoke a dockerized apalache-mc, and takes care of supplying
# boilerplate arguments to the docker executable.

set -euo pipefail

default_tag=latest

APALACHE_TAG=${APALACHE_TAG:-}

if [ -z "$APALACHE_TAG" ]
then
    >&2 echo "# No docker image supplied. Defaulting to '$default_tag'"
    >&2 echo "# To run a specific docker tag set APALACHE_TAG."
    img="ghcr.io/informalsystems/apalache:${default_tag}"
else
    img="ghcr.io/informalsystems/apalache:${APALACHE_TAG}"
fi

# TODO Programmatically generate envars to expose
cmd="docker run -e OUT_DIR -e WRITE_INTERMEDIATE -e SMT_ENCODING -e TLA_PATH -e JVM_ARGS --user $(id -u) --rm -v $(pwd):/var/apalache ${img} ${*}"
>&2 echo "# running command: ${cmd}"
$cmd
