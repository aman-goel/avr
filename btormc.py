#!/usr/bin/env python

import os, sys
import subprocess
import argparse
import tempfile
import shutil
import ntpath
from distutils import spawn
import re

DEFAULT_BIN="deps"
DEFAULT_NAME="test"
DEFAULT_OUT="output"
DEFAULT_KMAX=100
DEFAULT_TIMEOUT=3590
DEFAULT_MEMOUT=118000
DEFAULT_VERBOSITY=0
DEFAULT_PRINT_SMT2=False

def getopts(header):
	p = argparse.ArgumentParser(description=str(header), formatter_class=argparse.RawDescriptionHelpFormatter)
	p.add_argument('file', help='top file name', type=str)
	p.add_argument('-b', '--bin',       help='binary path (default: %s)' % DEFAULT_BIN, type=str, default=DEFAULT_BIN)
	p.add_argument('-n', '--name',      help='<test-name> (default: %s)' % DEFAULT_NAME, type=str, default=DEFAULT_NAME)
	p.add_argument('-o', '--out',       help='<output-path> (default: %s)' % DEFAULT_OUT, type=str, default=DEFAULT_OUT)
	p.add_argument('-k',                help='max bound for bmc (inclusive) (default: %s)' % DEFAULT_KMAX, type=int, default=DEFAULT_KMAX)
	p.add_argument('--timeout',         help='timeout (CPU time) in seconds (default: %s)' % DEFAULT_TIMEOUT, type=int, default=DEFAULT_TIMEOUT)
	p.add_argument('--memout',          help='memory limit in mega bytes (default: %s)' % DEFAULT_MEMOUT, type=int, default=DEFAULT_MEMOUT)
	p.add_argument('-v', '--verbosity', help='verbosity level (default: %r)' % DEFAULT_VERBOSITY, type=int, default=DEFAULT_VERBOSITY)
	p.add_argument('--smt2',     		help='toggles printing system in smt2 format (unsupported)', action="count", default=0)
	args, leftovers = p.parse_known_args()
	return args, p.parse_args()

header="""
------
BTORMC
------
  Reads a BTOR2 file and performs bounded model checking using btormc from Boolector
  
  Copyright (c) 2007-2019 Armin Biere.
  Copyright (c) 2007-2009 Robert Brummayer.
  Copyright (c) 2012-2019 Aina Niemetz.
  Copyright (c) 2012-2019 Mathias Preiner.
-------------------
"""

short_header="""BTORMC (copyright (c) 2019  Armin Biere, Robert Brummayer, Aina Niemetz, Mathias Preiner)"""

def split_path(name):
	head, tail = ntpath.split(name)
	if not tail:
		tail = ntpath.basename(head)
	return head, tail

def main():
	known, opts = getopts(header)
	#print(short_header)
	if not os.path.isfile(opts.bin + "/btormc"):
		raise Exception("btormc: binary not found")
	if not os.path.exists(opts.out):
		os.makedirs(opts.out)
	
	work_dir = opts.out + "/work_" + opts.name
	if os.path.exists(work_dir):
		shutil.rmtree(work_dir) 
	os.makedirs(work_dir)

	path, f = split_path(opts.file)
	if not os.path.isfile(opts.file):
		raise Exception("Unable to find top file: %s" % opts.file)

	print("\t(output dir: %s/work_%s)" % (opts.out, opts.name))
	print("\t(frontend: btor2)")
	
	bin_path = opts.bin + "/btormc"
	if not opts.bin.startswith("/"):
		bin_path = "./" + bin_path
		
	command = ""
	command = command + "ulimit -t " + str(opts.timeout) + "; ulimit -v " + str(1000*opts.memout) + ";"
	#command = command + " ulimit -v " + str(1000*opts.memout)
	#command = command + " timeout " + str(opts.timeout)
	command = command + " " + bin_path
	command = command + " -kmax " + str(opts.k)
	command = command + " -v " + str(opts.verbosity)
	command = command + " " + str(opts.file)
	
	outF = work_dir + "/btormc.out" 
	errF = work_dir + "/btormc.err"
	command = command + " > " + str(outF)
	command = command + " 2> " + str(errF)
	
	#print (command)
	s = subprocess.call( command, shell=True)
	if (s != 0):
		raise Exception("btormc ERROR: return code %d" % s)
	else:
		print("\t(btormc: done)")

if __name__ == '__main__':
	main()
