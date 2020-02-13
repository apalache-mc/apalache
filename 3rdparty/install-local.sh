#!/bin/bash
#
# Install the third-party jars that are not centrally available.
#
# If you upgrade the jars, change the versions accordingly.

set -e

D=`dirname $0` && D=`cd $D; pwd`
Z3_DIR="$D/z3-4.8.7"
CACHE=$1 # either empty, or --nocache

if [[ "$OSTYPE" == "darwin"* ]]; then
    echo "Assuming that you are using MacOS..."
    OST="macos"
else
    echo "Assuming that you are using Linux..."
    OST="linux"
fi

if [ "$CACHE" == "--nocache" ]; then
    echo "Cleaning the build cache"
    rm -rf "${Z3_DIR}" Box
fi

if [ -f "${Z3_DIR}/configure" ]; then
    echo "Using a cached Z3 build..."
else
    echo "Checking out z3..."
    git clone https://github.com/Z3Prover/z3.git ${Z3_DIR}
    pushd ${Z3_DIR}
    git checkout z3-4.8.7
    echo "Configuring z3 locally (Linux)..."
    python scripts/mk_make.py --java -p $D/
    echo "Compiling z3..."
    cd build
    make
    popd
fi

BOXHASH=77feaf4fc873990b72b31273985e2c88b8f2f502

if [ ! -d "$D/Box" ]; then
    echo "Checking out box..."
    git clone https://github.com/Kukovec/Box.git $D/Box
fi
pushd $D/Box
git reset --hard $BOXHASH
popd

# install Z3 libraries
echo "Compiling and installing z3..."
pushd ${Z3_DIR}
cd build
make install # install *.so and *.jar in 3rdparty
popd
echo "Done with z3"

echo "Installing Box..."
pushd $D/Box/Box
mvn install
cp target/box-1.0-SNAPSHOT.jar $D/lib/box.jar
popd
echo "Done with Box"

echo "Installing Z3 in your local maven cache..."

mvn -f $D/z3-pom.xml install install:install-file \
    "-Dfile=$D/lib/com.microsoft.z3.jar" "-DpomFile=$D/z3-pom.xml"

#mvn -f $D/tla2tools-pom.xml install install:install-file \
#    "-Dfile=$D/tla2tools.jar" "-DpomFile=$D/tla2tools-pom.xml"

mvn -f $D/box-pom.xml install install:install-file \
    "-Dfile=$D/lib/box.jar" "-DpomFile=$D/box-pom.xml"

if [ "$CACHE" == "--nocache" ]; then
    echo "Cleaning the build cache"
    rm -rf "${Z3_DIR}" Box
fi

cat <<EOF
1. To build Apalache, just use make.
2. To develop Apalache, set the library paths as follows.

Add the following line in your ~/.bashrc or ~/.zshrc:
EOF

if [ "$OST" == "linux" ]; then
  echo 'export LD_LIBRARY_PATH="$LD_LIBRARY_PATH":'"$D/lib"
else
  echo 'export JAVA_LIBRARY_PATH="$JAVA_LIBRARY_PATH":'"$D/lib"
fi
