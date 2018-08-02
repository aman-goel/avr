#!/usr/bin/env python

import os, sys
import subprocess
import argparse
import tempfile
import shutil
import ntpath
from distutils import spawn
import re

version=2.0

DEFAULT_BIN="bin"
DEFAULT_OUT="output"
DEFAULT_YOSYS="yosys"
DEFAULT_CLK="clk"
DEFAULT_TIMEOUT=3600
DEFAULT_MEMOUT=4096
DEFAULT_SPLIT=True
DEFAULT_ALLOWINP=False
DEFAULT_RANDOM=False
DEFAULT_VERBOSITY=0
	
def getopts(header):
	p = argparse.ArgumentParser(description=str(header), formatter_class=argparse.RawDescriptionHelpFormatter)
	p.add_argument('-f', '--file', required=True, help='top file name', type=str)
	p.add_argument('-t', '--top',       help='top module name (default: autodetect)', type=str)
	p.add_argument('-o', '--out',       help='output path (default: %s)' % DEFAULT_OUT, type=str, default=DEFAULT_OUT)
	p.add_argument('-b', '--bin',       help='binary path (default: %s)' % DEFAULT_BIN, type=str, default=DEFAULT_BIN)
	p.add_argument('--yosys',           help='path to yosys installation (default: %s)' % DEFAULT_YOSYS, type=str, default=DEFAULT_YOSYS)
	p.add_argument('--clock',           help='clock signal name (default: %s)' % DEFAULT_CLK, type=str, default=DEFAULT_CLK)
	p.add_argument('--timeout',         help='timeout (CPU time) in seconds (default: %s)' % DEFAULT_TIMEOUT, type=int, default=DEFAULT_TIMEOUT)
	p.add_argument('--memout',          help='memory limit in mega bytes (default: %s)' % DEFAULT_RANDOM, type=int, default=DEFAULT_MEMOUT)
	p.add_argument('--split',           help='transform system by splitting variables at extract points (default: %r)' % DEFAULT_SPLIT, action="store_false", default=DEFAULT_SPLIT)
	p.add_argument('--allowinp',        help='allow clauses to use input variables (default: %r)' % DEFAULT_ALLOWINP, action="store_true", default=DEFAULT_ALLOWINP)
	p.add_argument('--random',          help='use random ordering and random seed (default: %r)' % DEFAULT_RANDOM, action="store_true", default=DEFAULT_RANDOM)
	p.add_argument('-v', '--verbosity', help='verbosity level (default: %r)' % DEFAULT_VERBOSITY, type=int, default=DEFAULT_VERBOSITY)
	args, leftovers = p.parse_known_args()
	return args, p.parse_args()

header="""
	Averroes (avr) -- Abstract VERification of Reachability Of Electronic Systems
	Versions """ + str(version) + """
	Reads a Verilog-2005 file and performs property checking.
		supports SystemVerilog concurrent assertions/assumptions

	Copyright (C) 2018  Aman Goel <amangoel@umich.edu> and Karem A. Sakallah <karem@umich.edu>, University of Michigan
	
	------------
	Dependencies
	------------
	1. Yosys   (Copyright (C) 2018 Clifford Wolf <clifford@clifford.at>)
	2. Yices 2 (Copyright (C) 2017 SRI International)
	3. Z3      (Copyright (c) 2015 Microsoft Corporation)
	
	---------------------------------
	Limitiations (as of Aug 01, 2018)
	---------------------------------
	1. Can only handle safety properties that can be expressed without temporal operators.
	2. Assumes single clock domain.
	3. Cannot handle asynchronous flops.
	4. Handles memory by simply expanding it using yosys.
		(customize the bin/avr for special preprocessing using Yosys)
		
	Please report bugs via email (amangoel@umich.edu) or on github (https://github.com/aman-goel/avr)
	
"""

short_header="""Averroes v""" + str(version) + """\tCopyright (c) 2018  Aman Goel and Karem A. Sakallah, University of Michigan"""

def split_path(name):
	head, tail = ntpath.split(name)
	if not tail:
		tail = ntpath.basename(head)
	return head, tail

def main():
	known, opts = getopts(header)
	if not os.path.isfile(opts.yosys + "/yosys"):
		raise Exception("Please install Yosys using build.sh (or https://github.com/aman-goel/yosys)")
	if not os.path.isfile(opts.bin + "/vwn"):
		raise Exception("avr: vwn binary not found")
	if not os.path.isfile(opts.bin + "/dpa"):
		raise Exception("avr: dpa binary not found")
	if not os.path.isfile(opts.bin + "/reach"):
		raise Exception("avr: reach binary not found")
	if not os.path.isfile(opts.bin + "/avr"):
		raise Exception("avr: main shell script not found")
	
	print(short_header)
	path, f = split_path(opts.file)
	command = ""
	command = command + "./" + opts.bin + "/avr"
	command = command + " " + f
	command = command + " " + path
	command = command + " " + opts.out
	command = command + " " + opts.bin
	command = command + " " + opts.yosys
	command = command + " " + opts.clock
	command = command + " " + str(opts.timeout)
	command = command + " " + str(opts.memout)
	command = command + " " + str(opts.split)
	command = command + " " + str(opts.allowinp)
	command = command + " " + str(opts.random)
	command = command + " " + str(opts.verbosity)
	if known.top is not None:
		command = command + " " + str(opts.top)
		
	s = subprocess.call( command, shell=True)
	if (s != 0):
		raise Exception("avr ERROR: return code %d" % s)

if __name__ == '__main__':
	main()
