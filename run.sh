#!/usr/bin/env bash

# Run the given command in the development shell
# Launch the apalache development shell
#
# Several workarounds are applied to produce a pure, but
# unbroken environment. These were adapted from
# https://github.com/NixOS/nix/issues/4359#issuecomment-907768110

# Allows for benign exceptions within an otherwiase pure environment
keep_env=$( (printenv | grep _DONE |cut -f1 -d= ; printf "%s\n" HOME USER LOGNAME DISPLAY TERM IN_NIX_SHELL NIX_SHELL_PRESERVE_PROMPT TZ PAGER NIX_BUILD_SHELL SHLVL ;)|sed 's/^/--keep /')

nix develop \
    --ignore-environment \
    $keep_env \
    --keep USE_DOCKER \
    --keep APALACHE_TAG \
    --keep SSH_AUTH_SOCK \
    --command $@
