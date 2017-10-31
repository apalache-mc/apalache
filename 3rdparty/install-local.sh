#!/bin/sh
#
# Install the third-party jars that are not centrally available.
#
# If you upgrade the jars, change the versions accordingly.

mvn -f z3-pom.xml install install:install-file "-Dfile=${PWD}/com.microsoft.z3.jar" "-DpomFile=z3-pom.xml"

mvn -f tla2tools-pom.xml install install:install-file "-Dfile=${PWD}/tla2tools.jar" "-DpomFile=tla2tools-pom.xml"

