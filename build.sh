#!/bin/bash
set -e

# Prerequisites: git autoconf gperf libgmp3-dev curl cmake
# Prerequisites (yosys): build-essential clang bison flex libreadline-dev gawk tcl-dev libffi-dev git graphviz xdot pkg-config python3 libboost-system-dev libboost-python-dev libboost-filesystem-dev zlib1g-dev

sudo apt update
sudo apt install git autoconf gperf libgmp3-dev curl cmake
sudo apt install build-essential clang bison flex libreadline-dev gawk tcl-dev libffi-dev git graphviz xdot pkg-config python3 libboost-system-dev libboost-python-dev libboost-filesystem-dev zlib1g-dev


# Build and install dependencies
pushd .
cd deps
./build_deps.sh
cd ..
popd


# Build AVR source
pushd .
cd src
make all
cd ..
popd


# Test AVR

python avr.py -n test_vmt      examples/vmt/counter.smt2
python avr.py -n test_vmt2     examples/vmt/simple.c.vmt
python avr.py -n test_btor2    examples/btor2/counter.btor2

# requires yosys
#python avr.py -n test_verilog  examples/verilog/counter.v


RETURN="$?"
if [ "${RETURN}" != "0" ]; then
    echo "Installing dependencies failed."
    exit 1
fi
