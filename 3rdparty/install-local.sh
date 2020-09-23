#!/bin/bash
#
# Install the third-party jars that are not centrally available.
#
# If you upgrade the jars, change the versions accordingly.

set -e

D=`dirname $0` && D=`cd $D; pwd`
CACHE=$1 # either empty, or --nocache

if [[ "$OSTYPE" == "darwin"* ]]; then
    echo "Assuming that you are using MacOS..."
    OST="macos"
else
    echo "Assuming that you are using Linux..."
    OST="linux"
fi

BOXHASH=77feaf4fc873990b72b31273985e2c88b8f2f502

if [ ! -d "$D/Box" ]; then
    echo "Checking out box..."
    git clone https://github.com/Kukovec/Box.git $D/Box
fi
pushd $D/Box
git reset --hard $BOXHASH
popd

echo "Installing Box..."
pushd $D/Box/Box
mvn install
cp target/box-1.0-SNAPSHOT.jar $D/lib/box.jar
popd
echo "Done with Box"

#mvn -f $D/tla2tools-pom.xml install install:install-file \
#    "-Dfile=$D/tla2tools.jar" "-DpomFile=$D/tla2tools-pom.xml"

mvn -f $D/box-pom.xml install install:install-file \
    "-Dfile=$D/lib/box.jar" "-DpomFile=$D/box-pom.xml"

cat <<EOF
1. To build Apalache, just use make.
2. To develop Apalache without using direnv, set the library paths as follows.

Add the following line in your ~/.bashrc or ~/.zshrc:
EOF

if [ "$OST" == "linux" ]; then
  echo 'export LD_LIBRARY_PATH="$LD_LIBRARY_PATH":'"$D/lib"
else
  echo 'export JAVA_LIBRARY_PATH="$JAVA_LIBRARY_PATH":'"$D/lib"
fi
