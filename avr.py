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

DEFAULT_TOP="-"
DEFAULT_BIN="bin"
DEFAULT_NAME="test"
DEFAULT_PROP_SELECT="-"
DEFAULT_INIT_FILE="-"
DEFAULT_OUT="output"
DEFAULT_YOSYS="yosys"
DEFAULT_CLK="clk"
DEFAULT_TIMEOUT=1000
DEFAULT_MEMOUT=15000
DEFAULT_MEMORY=False
DEFAULT_SPLIT=False
DEFAULT_GRANULARITY=2
DEFAULT_RANDOM=False
DEFAULT_EFFORT_MININV=0
DEFAULT_VERBOSITY=0
DEFAULT_EN_VMT=False
DEFAULT_EN_JG=True
DEFAULT_ABTYPE="sa+uf"
DEFAULT_INTERPOLATION=0
DEFAULT_FORWARD_CHECK=0
DEFAULT_AB_LEVEL=2
DEFAULT_LAZY_ASSUME=0
DEFAULT_JG_PREPROCESS="-"
DEFAULT_PRINT_SMT2=False
DEFAULT_DOT="0000000"

def getopts(header):
	p = argparse.ArgumentParser(description=str(header), formatter_class=argparse.RawDescriptionHelpFormatter)
	p.add_argument('file', help='top file name', type=str)
	p.add_argument('-t', '--top',       help='top module name (default: autodetect)', type=str, default=DEFAULT_TOP)
	p.add_argument('-p', '--property',  help='select single property based on name (default: all asserts)', type=str, default=DEFAULT_PROP_SELECT)
	p.add_argument('-i', '--init',  help='init file for initial state (default: initial block)', type=str, default=DEFAULT_INIT_FILE)
	p.add_argument('-n', '--name',      help='<test-name> (default: %s)' % DEFAULT_NAME, type=str, default=DEFAULT_NAME)
	p.add_argument('-o', '--out',       help='<output-path> (default: %s)' % DEFAULT_OUT, type=str, default=DEFAULT_OUT)
	p.add_argument('-b', '--bin',       help='binary path (default: %s)' % DEFAULT_BIN, type=str, default=DEFAULT_BIN)
	p.add_argument('-y', '--yosys',     help='path to yosys installation (default: %s)' % DEFAULT_YOSYS, type=str, default=DEFAULT_YOSYS)
	p.add_argument('--vmt',             help='toggles using vmt frontend (default: %s)' % DEFAULT_EN_VMT, action="count", default=0)
	p.add_argument('-j', '--jg',        help='toggles using jg frontend (default: %s)' % DEFAULT_EN_JG, action="count", default=0)
	p.add_argument('--clock',           help='clock signal name (default: %s)' % DEFAULT_CLK, type=str, default=DEFAULT_CLK)
	p.add_argument('--timeout',         help='timeout (CPU time) in seconds (default: %s)' % DEFAULT_TIMEOUT, type=int, default=DEFAULT_TIMEOUT)
	p.add_argument('--memout',          help='memory limit in mega bytes (default: %s)' % DEFAULT_MEMOUT, type=int, default=DEFAULT_MEMOUT)
	p.add_argument('-a', '--abstract',  help='abstraction type (options: sa, sa+uf) (default: %s)' % DEFAULT_ABTYPE, type=str, default=DEFAULT_ABTYPE)
	p.add_argument('-m', '--memory',     help='toggles using memory abstraction instead of simple expansion (default: %r)' % DEFAULT_MEMORY, action="count", default=0)
	p.add_argument('-s', '--split',     help='toggles transforming system by splitting variables at extract points (default: %r)' % DEFAULT_SPLIT, action="count", default=0)
	p.add_argument('-g', '--granularity',help='abstract granularity level (between 0-2) (default: %r)' % DEFAULT_GRANULARITY, type=int, default=DEFAULT_GRANULARITY)
	p.add_argument('-r', '--random',    help='toggles using random ordering and random seed (default: %r)' % DEFAULT_RANDOM, action="count", default=0)
	p.add_argument('-e', '--effort_mininv',help='inductive invariant minimization effort when property is proved true (between 0-4) (default: %r)' % DEFAULT_EFFORT_MININV, type=int, default=DEFAULT_EFFORT_MININV)
	p.add_argument('--interpol',		help='interpolation level (between 0-1) (default: %r)' % DEFAULT_INTERPOLATION, type=int, default=DEFAULT_INTERPOLATION)
	p.add_argument('-f', '--forward',	help='forward check level (between 0-2) (default: %r)' % DEFAULT_FORWARD_CHECK, type=int, default=DEFAULT_FORWARD_CHECK)
	p.add_argument('-l', '--level',		help='abstraction level (between 0-5) (default: %r)' % DEFAULT_AB_LEVEL, type=int, default=DEFAULT_AB_LEVEL)
	p.add_argument('-la', '--lazy_assume',	help='lazy assumptions level (between 0-2) (default: %r)' % DEFAULT_LAZY_ASSUME, type=int, default=DEFAULT_LAZY_ASSUME)
	p.add_argument('--jgpre',  			help='preprocessing options for jg (default: %s)' % DEFAULT_JG_PREPROCESS, type=str, default=DEFAULT_JG_PREPROCESS)
	p.add_argument('--smt2',     		help='toggles printing system in smt2 format (default: %r)' % DEFAULT_PRINT_SMT2, action="count", default=0)
	p.add_argument('--dot', 			help='option to configure dot files generation (default: %s)' % DEFAULT_DOT, type=str, default=DEFAULT_DOT)
	p.add_argument('-v', '--verbosity', help='verbosity level (default: %r)' % DEFAULT_VERBOSITY, type=int, default=DEFAULT_VERBOSITY)
	args, leftovers = p.parse_known_args()
	return args, p.parse_args()

header="""
	Averroes (avr) -- Abstract VERification of Reachability Of Electronic Systems
	Versions """ + str(version) + """
	Reads a Verilog file and performs property checking using syntactic data abstraction.
		supports SystemVerilog concurrent assertions

	Copyright (c) 2019  Aman Goel <amangoel@umich.edu> and Karem A. Sakallah <karem@umich.edu>, University of Michigan
	
	------------
	Dependencies
	------------
	1. Yosys     (Copyright (c) 2019 Clifford Wolf <clifford@clifford.at>)
	2. Yices 2   (Copyright (c) 2019 SRI International)
	3. Z3        (Copyright (c) 2019 Microsoft Corporation)
	4. MathSAT5  (Copyright (c) 2019 Fondazione Bruno Kessler, Italy)
	5. Boolector (Copyright (c) 2007-2018 Armin Biere, 2007-2009 Robert Brummayer, 2012-2018 Aina Niemetz, 2012-2018 Mathias Preiner)
	6. JG	     (Copyright (c) 2007-Present Cadence Design Systems, Inc.)
	
	--------------
	Terms of usage
	--------------
	* Any usage of JG frontend requires prior written permission from Cadence Design Systems, Inc.

	---------------------------------
	NEW (Aug 20, 2019)
	---------------------------------
	1. New frontend for direct interface with JasperGold (Copyright (c) 2007-Present Cadence Design Systems, Inc.).

	---------------------------------
	Limitiations (as of Aug 20, 2019)
	---------------------------------
	1. Can only handle safety properties that can be expressed without temporal operators.
	2. Handles asynchronous flops as synchronous.
	3. Handles memory using memory abstraction (experimental).
	4. avr uses yosys as its frontend and can handle most designs/formats that are supported by yosys.
		(customize the bin/avr for special preprocessing using Yosys)
	5. Support for .vmt frontend is limited.

	Please report bugs and share your usage experience via email (amangoel@umich.edu) or on github (https://github.com/aman-goel/avr)
	
"""

short_header="""Averroes v""" + str(version) + """\tCopyright (c) 2019  Aman Goel and Karem A. Sakallah, University of Michigan"""

def split_path(name):
	head, tail = ntpath.split(name)
	if not tail:
		tail = ntpath.basename(head)
	return head, tail

def main():
	print(short_header)
	known, opts = getopts(header)
	if not os.path.isfile(opts.bin + "/avr"):
		raise Exception("avr: main shell script not found")
	if not os.path.isfile(opts.bin + "/vwn"):
		raise Exception("avr: vwn binary not found")
	if not os.path.isfile(opts.bin + "/dpa"):
		raise Exception("avr: dpa binary not found")
	if not os.path.isfile(opts.bin + "/reach"):
		raise Exception("avr: reach binary not found")

	path, f = split_path(opts.file)
	if not os.path.isfile(opts.file):
		raise Exception("Unable to find top file: %s" % opts.file)

	en_vmt = DEFAULT_EN_VMT
	if (opts.vmt % 2 == 1):
		en_vmt = not DEFAULT_EN_VMT
	en_jg  = DEFAULT_EN_JG
	if (opts.jg % 2 == 1):
		en_jg = not DEFAULT_EN_JG

	if (en_jg):
		print("\t(frontend: jg)")
		en_vmt = False
	elif en_vmt:
		print("\t(frontend: vmt)")
	else:
		print("\t(frontend: yosys)")
		if not os.path.isfile(opts.yosys + "/yosys"):
			if not os.path.isfile("/usr/local/bin/yosys"):
				raise Exception("Please install yosys using build.sh")
			else:
				opts.yosys = "/usr/local/bin"
				print("\t(found yosys in /usr/local/bin)")
	
	command = ""
	command = command + "./" + opts.bin + "/avr"
	command = command + " " + f
	command = command + " " + str(opts.top)
	command = command + " " + path
	command = command + " " + opts.name
	command = command + " " + opts.out
	command = command + " " + opts.bin
	command = command + " " + opts.yosys
	command = command + " " + opts.clock
	command = command + " " + str(opts.timeout)
	command = command + " " + str(opts.memout)

	memory = DEFAULT_MEMORY
	if (opts.memory % 2 == 1):
		memory = not DEFAULT_MEMORY
	command = command + " " + str(memory)
	
	split = DEFAULT_SPLIT
	if (opts.split % 2 == 1):
		split = not DEFAULT_SPLIT
	command = command + " " + str(split)
	command = command + " " + str(opts.granularity)
	
	random = DEFAULT_RANDOM
	if (opts.random % 2 == 1):
		random = not DEFAULT_RANDOM
	command = command + " " + str(random)
	
	command = command + " " + str(opts.verbosity)
	
	p = opts.property.replace(" ", "%")
	p = p.replace("\\", "\\\\")
	command = command + " " + "\"" + str(p) + "\"";
#	print(str(p))
	
	command = command + " " + str(opts.effort_mininv)
	command = command + " " + opts.init
	
	command = command + " " + str(en_vmt)
	command = command + " " + str(opts.abstract)
	command = command + " " + str(en_jg)
	command = command + " " + str(opts.interpol)
	command = command + " " + str(opts.forward)
	command = command + " " + str(opts.level)
	command = command + " " + str(opts.lazy_assume)
	command = command + " " + str(opts.jgpre)

	print_smt2 = DEFAULT_PRINT_SMT2
	if (opts.smt2 % 2 == 1):
		print_smt2 = not DEFAULT_PRINT_SMT2
	command = command + " " + str(print_smt2)
	command = command + " " + str(opts.dot)
	
	s = subprocess.call( command, shell=True)
	if (s != 0):
		raise Exception("avr ERROR: return code %d" % s)

if __name__ == '__main__':
	main()
