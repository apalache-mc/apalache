#!/usr/bin/env bash
set -euo pipefail

default_tag=latest

APALACHE_TAG=${APALACHE_TAG:-}

if [ -z "$APALACHE_TAG" ]
then
    >&2 echo "# No docker image supplied. Defaulting to '$default_tag'"
    >&2 echo "# To run a specific docker tag set APALACHE_TAG."
    img="apalache/mc:${default_tag}"
else
    img="apalache/mc:${APALACHE_TAG}"
fi

cmd="docker run -e TLA_PATH --rm -v $(pwd):/var/apalache ${img} ${@}"
>&2 echo "# running command: ${cmd}"
$cmd
