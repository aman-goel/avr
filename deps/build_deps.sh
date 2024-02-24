#!/bin/bash -x
set -e

MATHSATVERSION="5.6.10"

echo "Installing dependencies..."

# Build and install yices2
pushd .
echo "  Installing Yices 2 from https://github.com/SRI-CSL/yices2 ..."
git clone https://github.com/SRI-CSL/yices2.git
cd yices2
autoconf
./configure
make
cd ..
echo "  Done!"
popd


### Build and install boolector
pushd .
echo "  Installing Boolector from https://github.com/Boolector/boolector ..."
git clone https://github.com/Boolector/boolector.git
cd boolector
./contrib/setup-btor2tools.sh
./contrib/setup-cadical.sh
./configure.sh --only-cadical
cd build
make
cd ..
echo "  Done!"
popd


### Build and install mathsat5
pushd .
echo "  Installing MathSAT v${MATHSATVERSION} from https://mathsat.fbk.eu/release/ ..."
wget https://mathsat.fbk.eu/release/mathsat-${MATHSATVERSION}-linux-x86_64.tar.gz
tar -xf mathsat-${MATHSATVERSION}-linux-x86_64.tar.gz
rm -f mathsat-${MATHSATVERSION}-linux-x86_64.tar.gz
mv mathsat-${MATHSATVERSION}-linux-x86_64 mathsat
echo "  Done!"
popd


### Build and install btor2tools
pushd .
echo "  Installing Btor2Tools from https://github.com/Boolector/btor2tools ..."
git clone https://github.com/Boolector/btor2tools.git
cd btor2tools
./configure.sh --static
cd build
make
cd ../..
echo "  Done!"
popd

echo "  Skipping installing Z3 (install manually if needed)"
### By default, z3 installation is disabled
# ### Build and install z3
# pushd .
# git clone https://github.com/Z3Prover/z3.git
# cd z3
# python scripts/mk_make.py --prefix . --staticlib
# cd build
# make -j4
# cd ../..
# popd

echo "  Skipping installing Yosys (install manually if needed, preferrably from https://github.com/aman-goel/yosys)"
### By default, yosys installation is disabled
# ### Build and install yosys
# pushd .
# git clone https://github.com/aman-goel/yosys.git
# cd yosys
# make -j8 PREFIX="$PWD"
# popd


RETURN="$?"
if [ "${RETURN}" != "0" ]; then
    echo "Installing dependencies failed."
    exit 1
fi
