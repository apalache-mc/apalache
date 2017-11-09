#!/bin/bash
#
# Install the third-party jars that are not centrally available.
#
# If you upgrade the jars, change the versions accordingly.

set -e

D=`dirname $0` && D=`cd $D; pwd`

if [ -d "$D/z3" -a -f "$D/3rdparty/lib/com.microsoft.z3.jar" ]; then
    echo "Using a cached Z3 build..."
else
    echo "Downloading and compiling z3..."
    git clone https://github.com/Z3Prover/z3 $D/z3
    pushd $D/z3
    python scripts/mk_make.py --java -p $D/
    cd build
    make && make install # install *.so and *.jar in 3rdparty
    popd
    echo "Done with z3"
fi

echo "Downloading TLA2Tools..."
wget https://tla.msr-inria.inria.fr/tlatoolbox/dist/tla2tools.jar
echo "Done with TLA2Tools"

echo "Installing Z3 and TLA2Tools in your local cache..."

mvn -f z3-pom.xml install install:install-file \
    "-Dfile=lib/com.microsoft.z3.jar" "-DpomFile=z3-pom.xml"

mvn -f tla2tools-pom.xml install install:install-file \
    "-Dfile=tla2tools.jar" "-DpomFile=tla2tools-pom.xml"

echo ""
echo "Add the following line in your ~/.bashrc or ~/.zshrc"
echo 'export LD_LIBRARY_PATH="$LD_LIBRARY_PATH":'"$D/lib"
