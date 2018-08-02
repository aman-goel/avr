#!/bin/bash -x
# Make sure we exit if there is a failure
set -e

# Build and install yosys
pushd .
git clone https://github.com/aman-goel/yosys.git
cd yosys
make PREFIX="$PWD"
# sudo make install
popd

# Build and install yices2
	# statically linked

# Build and install z3
	# statically linked

RETURN="$?"
if [ "${RETURN}" != "0" ]; then
    echo "Installing dependencies failed."
    exit 1
fi
