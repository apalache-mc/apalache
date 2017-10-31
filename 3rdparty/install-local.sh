#!/bin/sh
#
# Install the third-party jars that are not centrally available.
#
# If you upgrade the jars, change the versions accordingly.

REPO=$HOME/.apalache/apalache-local

echo "Installing the third-party libraries in your local cache..."
mkdir -p ${REPO}

mvn -f z3-pom.xml install install:install-file \
    "-Dfile=com.microsoft.z3.jar" "-DpomFile=z3-pom.xml"

mvn -f tla2tools-pom.xml install install:install-file \
    "-Dfile=tla2tools.jar" "-DpomFile=tla2tools-pom.xml"

