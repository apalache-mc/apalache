#!/usr/bin/env bash
set -euo pipefail

# Publish the tla-ir, tla-ir-java, and tla-io libraries to the Sonatype Central Portal.
# Credentials and signing keys are deliberately read from the environment and
# the user's GnuPG keyring, never from repository files.

DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"
DEFAULT_PROJ_ROOT="$(cd "$DIR/.." >/dev/null 2>&1 && pwd)"
PROJ_ROOT="${PUBLISH_MAVEN_PROJECT_ROOT:-$DEFAULT_PROJ_ROOT}"

usage() {
    cat <<'EOF'
Usage: ./script/publish-maven.sh snapshot|release

  snapshot  Publish a VERSION ending in -SNAPSHOT to Central snapshots.
  release   Upload a release VERSION and publish it automatically after validation.

Required environment variables:
  SONATYPE_USERNAME  Username from a Central Portal user token.
  SONATYPE_PASSWORD  Password from a Central Portal user token.

Artifacts are signed with the default secret key in the local GnuPG keyring.
GnuPG may use pinentry interactively; PGP_PASSPHRASE is supported for CI.
EOF
}

if [[ $# -ne 1 ]]
then
    usage >&2
    exit 2
fi

MODE=$1
case "$MODE" in
    snapshot|release) ;;
    *)
        usage >&2
        exit 2
        ;;
esac

cd "$PROJ_ROOT"
VERSION=$(<"$PROJ_ROOT/VERSION")

if [[ "$MODE" == "snapshot" ]]
then
    if [[ "$VERSION" != *-SNAPSHOT ]]
    then
        echo "error: snapshot mode requires VERSION to end in -SNAPSHOT (found: $VERSION)" >&2
        exit 3
    fi
else
    if [[ "$VERSION" == *-SNAPSHOT ]]
    then
        echo "error: $MODE mode requires a release VERSION (found: $VERSION)" >&2
        exit 3
    fi

    if ! (git diff --exit-code && git diff --cached --exit-code) >/dev/null
    then
        echo "error: $MODE mode requires a clean tracked worktree" >&2
        exit 4
    fi
fi

for variable in SONATYPE_USERNAME SONATYPE_PASSWORD
do
    if [[ -z "${!variable:-}" ]]
    then
        echo "error: required environment variable $variable is not set" >&2
        exit 5
    fi
done

if ! command -v gpg >/dev/null 2>&1
then
    echo "error: gpg is required to sign Maven Central artifacts" >&2
    exit 6
fi

if ! gpg --batch --list-secret-keys --with-colons 2>/dev/null | grep -m1 -q '^sec:'
then
    echo "error: no secret GPG key is available for signing" >&2
    exit 6
fi

case "$MODE" in
    snapshot)
        sbt -batch \
            "tlair / test" \
            "tla_ir_java / test" \
            "tla_io / test" \
            "tlair / publishSigned" \
            "tla_ir_java / publishSigned" \
            "tla_io / publishSigned"
        ;;
    release)
        echo "Publishing org.apalache-mc:tla-ir_2.13, org.apalache-mc:tla-ir-java, and org.apalache-mc:tla-io_2.13 version $VERSION"
        sbt -batch \
            "tlair / test" \
            "tla_ir_java / test" \
            "tla_io / test" \
            cleanMavenCentralStaging \
            "tlair / publishSigned" \
            "tla_ir_java / publishSigned" \
            "tla_io / publishSigned" \
            sonaRelease
        ;;
esac
