#!/usr/bin/env python

######################################################################################
# AVR: Abstractly Verifying Reachability
#
# Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
# All rights reserved.
#
# Author: Aman Goel (amangoel@umich.edu), University of Michigan
######################################################################################

import os, sys
import subprocess
import argparse
import tempfile
import shutil
import ntpath
from distutils import spawn
import re
from distutils.spawn import find_executable

version=2.1

DEFAULT_TOP="-"
DEFAULT_BIN="build/bin"
DEFAULT_NAME="test"
DEFAULT_PROP_SELECT="-"
DEFAULT_INIT_FILE="-"
DEFAULT_OUT="output"
DEFAULT_YOSYS="yosys"
DEFAULT_CLK="clk"
DEFAULT_TIMEOUT=3600
DEFAULT_MEMOUT=64000
DEFAULT_MEMORY=False
DEFAULT_SPLIT=True
DEFAULT_GRANULARITY=2
DEFAULT_RANDOM=False
DEFAULT_EFFORT_MININV=0
DEFAULT_VERBOSITY=0
DEFAULT_EN_VMT=False
DEFAULT_EN_JG=False
DEFAULT_EN_BTOR2=True
DEFAULT_ABTYPE="sa+uf"
DEFAULT_INTERPOLATION=0
DEFAULT_FORWARD_CHECK=0
DEFAULT_AB_LEVEL=2
DEFAULT_LAZY_ASSUME=0
DEFAULT_JG_PREPROCESS="-"
DEFAULT_PRINT_SMT2=False
DEFAULT_PRINT_WITNESS=False
DEFAULT_DOT="0000000"
DEFAULT_BMC_EN=False
DEFAULT_KIND_EN=False
DEFAULT_BMC_MAX_BOUND=1000
DEFAULT_PRINT_AIG=False

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
	p.add_argument('--bt',              help='toggles using btor2 frontend (default: %s)' % DEFAULT_EN_BTOR2, action="count", default=0)
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
	p.add_argument('--witness',         help='toggles printing witness (default: %r)' % DEFAULT_PRINT_WITNESS, action="count", default=0)
	p.add_argument('--dot', 			help='option to configure dot files generation (default: %s)' % DEFAULT_DOT, type=str, default=DEFAULT_DOT)
	p.add_argument('--bmc',             help='toggles using bmc engine (default: %r)' % DEFAULT_BMC_EN, action="count", default=0)
	p.add_argument('--kind',            help='toggles using k-ind engine (default: %r)' % DEFAULT_KIND_EN, action="count", default=0)
	p.add_argument('--aig',             help='toggles printing aig (default: %r)' % DEFAULT_PRINT_AIG, action="count", default=0)
	p.add_argument('-k', '--kmax',      help='max bound for bmc (default: %r)' % DEFAULT_BMC_MAX_BOUND, type=int, default=DEFAULT_BMC_MAX_BOUND)
	p.add_argument('-v', '--verbosity', help='verbosity level (default: %r)' % DEFAULT_VERBOSITY, type=int, default=DEFAULT_VERBOSITY)
	args, leftovers = p.parse_known_args()
	return args, p.parse_args()

header="""
---
AVR
---
  Abstractly Verifying Reachability
  
  Reads a state transition system and performs property checking 
  using equality abstraction
  
  Copyright (c) 2016 - Present  Aman Goel <amangoel@umich.edu> and 
  Karem Sakallah <karem@umich.edu>, University of Michigan
  
  Please report bugs and share your usage experience via email 
  (amangoel@umich.edu) or on github (https://github.com/aman-goel/avr)	
-------------------
"""

short_header="""AVR 
Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan"""

def split_path(name):
	head, tail = ntpath.split(name)
	if not tail:
		tail = ntpath.basename(head)
	return head, tail

def main():
	known, opts = getopts(header)
	print(short_header)
	if not os.path.isfile("build/avr"):
		raise Exception("avr: main shell script not found")
	if not os.path.isfile(opts.bin + "/vwn"):
		raise Exception("avr: vwn binary not found")
	if not os.path.isfile(opts.bin + "/dpa"):
		raise Exception("avr: dpa binary not found")
	if not os.path.isfile(opts.bin + "/reach"):
		raise Exception("avr: reach binary not found")
	if not os.path.exists(opts.out):
		os.makedirs(opts.out)

	path, f = split_path(opts.file)
	if path == "":
		path = "."
	if not os.path.isfile(opts.file):
		raise Exception("Unable to find top file: %s" % opts.file)

	en_vmt = False
	en_jg = False
	en_bt = False
	if opts.file.endswith('.btor2') or opts.file.endswith('.btor'):
		en_bt = True
	elif opts.file.endswith('.vmt') or opts.file.endswith('.smt2'):
		en_vmt = True
	elif opts.file.endswith('.wif'):
		en_jg = True
	elif not (opts.file.endswith('.v') or opts.file.endswith('.sv')):
		en_vmt = DEFAULT_EN_VMT
		if (opts.vmt % 2 == 1):
			en_vmt = not DEFAULT_EN_VMT
		en_jg  = DEFAULT_EN_JG
		if (opts.jg % 2 == 1):
			en_jg = not DEFAULT_EN_JG
		en_bt = DEFAULT_EN_BTOR2
		if (opts.bt % 2 == 1):
			en_bt = not DEFAULT_EN_BTOR2
		
	print("\t(output dir: %s/work_%s)" % (opts.out, opts.name))
	if (en_jg):
		print("\t(frontend: jg)")
		en_vmt = False
		en_bt = False
	elif en_vmt:
		print("\t(frontend: vmt)")
		en_bt = False
	elif en_bt:
		print("\t(frontend: btor2)")
	else:
		print("\t(frontend: yosys)")
		if not os.path.isfile(opts.yosys + "/yosys"):
			ys_path = find_executable('yosys')
			if not ys_path:
				if not os.path.isfile("/usr/local/bin/yosys"):
					raise Exception("Please install yosys using build.sh")
				else:
					opts.yosys = "/usr/local/bin"
			else:
				if ys_path.endswith('/yosys'):
					ys_path = ys_path[:-6]
				opts.yosys = ys_path
			print("\t(found yosys in %s)" % opts.yosys)
	
	command = "./build/avr"
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
	
	print_wit = DEFAULT_PRINT_WITNESS
	if (opts.witness % 2 == 1):
		print_wit = not DEFAULT_PRINT_WITNESS
	command = command + " " + str(print_wit)
	
	command = command + " " + str(opts.dot)
	command = command + " " + str(en_bt)
	
	bmc_en = DEFAULT_BMC_EN
	if (opts.bmc % 2 == 1):
		bmc_en = not DEFAULT_BMC_EN
	command = command + " " + str(bmc_en)
	
	kind_en = DEFAULT_KIND_EN
	if (opts.kind % 2 == 1):
		kind_en = not DEFAULT_KIND_EN
	command = command + " " + str(kind_en)
	
	command = command + " " + str(opts.kmax)
		
	print_aig = DEFAULT_PRINT_AIG
	if (opts.aig % 2 == 1):
		print_aig = not DEFAULT_PRINT_AIG
	command = command + " " + str(print_aig)
	
	s = subprocess.call("exec " + command, shell=True)
	if (s != 0):
		raise Exception("avr ERROR: return code %d" % s)
		
if __name__ == '__main__':
	main()
