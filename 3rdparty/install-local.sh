#!/bin/bash
#
# Install the third-party jars that are not centrally available.
#
# If you upgrade the jars, change the versions accordingly.

set -e

D=`dirname $0` && D=`cd $D; pwd`

if [[ "$OSTYPE" == "darwin"* ]]; then
    echo "Assuming that you are using MacOS..."
    OST="macos"
else
    echo "Assuming that you are using Linux..."
    OST="linux"
fi

if [ -f "$D/z3/configure" ]; then
    echo "Using a cached Z3 build..."
else
    echo "Checking out z3..."
    git clone https://github.com/Z3Prover/z3 $D/z3
    pushd $D/z3
    echo "Configuring z3 locally (Linux)..."
    python scripts/mk_make.py --java -p $D/
    echo "Compiling z3..."
    cd build
    make
    popd
fi

# install Z3 libraries
echo "Compiling and installing z3..."
pushd $D/z3
cd build
make install # install *.so and *.jar in 3rdparty
popd
echo "Done with z3"

echo "Downloading TLA2Tools..."
wget https://github.com/tlaplus/tlaplus/releases/download/v1.5.6/tla2tools.jar
#wget https://tla.msr-inria.inria.fr/tlatoolbox/ci/dist/tla2tools.jar
echo "Done with TLA2Tools"

echo "Installing Z3 and TLA2Tools in your local cache..."

mvn -f z3-pom.xml install install:install-file \
    "-Dfile=lib/com.microsoft.z3.jar" "-DpomFile=z3-pom.xml"

mvn -f tla2tools-pom.xml install install:install-file \
    "-Dfile=tla2tools.jar" "-DpomFile=tla2tools-pom.xml"

echo ""
echo "Add the following line in your ~/.bashrc or ~/.zshrc"
if [ "$OST" == "linux" ]; then
  echo 'export LD_LIBRARY_PATH="$LD_LIBRARY_PATH":'"$D/lib"
else
  echo 'export JAVA_LIBRARY_PATH="$JAVA_LIBRARY_PATH":'"$D/lib"
fi
