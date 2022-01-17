######################################################################################
# AVR: Abstractly Verifying Reachability
#
# Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
# All rights reserved.
#
# Author: Aman Goel (amangoel@umich.edu), University of Michigan
######################################################################################


import os, sys, datetime, time, resource, argparse, shutil, signal
from subprocess import Popen, PIPE, DEVNULL, STDOUT
from enum import Enum

version=2.1
start_time = time.time()

cmdSuffix = ""
maxWorkers = 8

optSuffix = " "
commands = []
commandsRun = []
disableNew = False
numW = 0
processes = {}

DEFAULT_TOP="-"
DEFAULT_OUT="output"
DEFAULT_NAME="test"
DEFAULT_WORKERS="workers.txt"
#DEFAULT_BIN="bin"
DEFAULT_TIMEOUT=3600
DEFAULT_MEMOUT=16000
DEFAULT_PRINT_SMT2=False
DEFAULT_PRINT_WITNESS=True

maxTimeSec = DEFAULT_TIMEOUT
maxMemMB = DEFAULT_MEMOUT
maxInitW = 2
resultW = 0
out_path = DEFAULT_OUT + "/" + DEFAULT_NAME

header="""
-----------------
AVR -- Proof Race
-----------------
  Abstractly Verifying Reachability
  
  Reads a state transition system and performs property checking 
  using equality abstraction
  
  Copyright (c) 2016 - Present  Aman Goel <amangoel@umich.edu> and 
  Karem Sakallah <karem@umich.edu>, University of Michigan
  
  Please report bugs and share your usage experience via email 
  (amangoel@umich.edu) or on github (https://github.com/aman-goel/avr)	
---------------------------------
"""

short_header="""AVR -- Proof Race 
Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan"""

def getopts(header):
	p = argparse.ArgumentParser(description=str(header), formatter_class=argparse.RawDescriptionHelpFormatter)
	p.add_argument('file', help='top file name', type=str)
	p.add_argument('-o', '--out',       help='<output-path> (default: %s)' % DEFAULT_OUT, type=str, default=DEFAULT_OUT)
	p.add_argument('-n', '--name',      help='<test-name> (default: %s)' % DEFAULT_NAME, type=str, default=DEFAULT_NAME)
	p.add_argument('-w', '--worker',    help='workers config file (default: %s)' % DEFAULT_WORKERS, type=str, default=DEFAULT_WORKERS)
	#p.add_argument('-b', '--bin',       help='binary path (default: %s)' % DEFAULT_BIN, type=str, default=DEFAULT_BIN)
	p.add_argument('--timeout',         help='timeout (CPU time) in seconds (default: %s)' % DEFAULT_TIMEOUT, type=int, default=DEFAULT_TIMEOUT)
	p.add_argument('--memout',          help='memory limit in mega bytes (default: %s)' % DEFAULT_MEMOUT, type=int, default=DEFAULT_MEMOUT)
	p.add_argument('--smt2',     		help='toggles printing system in smt2 format (default: %r)' % DEFAULT_PRINT_SMT2, action="count", default=0)
	p.add_argument('--witness',         help='toggles printing witness (default: %r)' % DEFAULT_PRINT_WITNESS, action="count", default=0)
	args, leftovers = p.parse_known_args()
	return args, p.parse_args()

def setup():
	global opts
	global optSuffix
	global maxTimeSec
	global maxMemMB
	global out_path
	known, opts = getopts(header)
	print(short_header)
	#if not os.path.isfile(opts.bin + "/avr"):
		#raise Exception("avr: main shell script not found")
	#if not os.path.isfile(opts.bin + "/vwn"):
		#raise Exception("avr: vwn binary not found")
	#if not os.path.isfile(opts.bin + "/dpa"):
		#raise Exception("avr: dpa binary not found")
	#if not os.path.isfile(opts.bin + "/reach"):
		#raise Exception("avr: reach binary not found")
	if not os.path.exists(opts.out):
		os.makedirs(opts.out)
	out_path = opts.out + "/pr_" + opts.name
	if os.path.exists(out_path):
		shutil.rmtree(out_path)
	os.makedirs(out_path)

	if not os.path.isfile(opts.file):
		raise Exception("Unable to find top file: %s" % opts.file)

	print(time_str(), "(starting avr proof race)")
	print(time_str(), "(output dir: %s)" % out_path)
	
	optSuffix = ""
	optSuffix = optSuffix + " " + opts.file
	optSuffix = optSuffix + " -o " + out_path
	#optSuffix = optSuffix + " -b " + opts.bin
	
	print_smt2 = DEFAULT_PRINT_SMT2
	if (opts.smt2 % 2 == 1):
		print_smt2 = not DEFAULT_PRINT_SMT2
	if print_smt2:
		optSuffix = optSuffix + " " + "--smt2"

	print_witness = DEFAULT_PRINT_WITNESS
	if (opts.witness % 2 == 1):
		print_witness = not DEFAULT_PRINT_WITNESS
	if print_witness:
		optSuffix = optSuffix + " " + "--witness"

	maxTimeSec = opts.timeout
	maxMemMB = opts.memout

	#optSuffix = optSuffix + " --timeout " + str(int(0.99*opts.timeout))
	#optSuffix = optSuffix + " --memout " + str(int(0.9*opts.memout))

COLOR1 = '\033[0;30;47m'
ENDC = '\033[m'

class WorkerStatus(Enum):
	avr_run = 0
	avr_h = 1
	avr_v = 2
	avr_to = -3
	avr_mo = -4
	avr_err = -5
	avr_u = -6

def WorkerStatus_str(status):
	return status.name

def get_result(status):
	if status == WorkerStatus.avr_h:
		return "safe"
	if status == WorkerStatus.avr_v:
		return "unsafe"
	return "unknown"

def time_str():
	#return "@ " + datetime.datetime.now().strftime("%H:%M:%S") + " "
	elapsed_time = time.time() - start_time
	return "@ %5.0fs " % elapsed_time
	
def run_command_all():
	with open(opts.worker) as f:
		for x in f:
			if (maxWorkers < 0 or len(commands) < maxWorkers):
				cmd = x.strip()
				if not cmd.startswith('#'):
					commands.append(x.strip())
	print (time_str(), "(max %d workers)" % len(commands))

def run_command(idx):
	elapsed_time = time.time() - start_time
	timeLimit = opts.timeout - elapsed_time
	timeSuffix = " --timeout " + str(int(0.99*timeLimit))

	mem_usage = mem_usage_all()
	memLimit = max(opts.memout - (1.5*mem_usage), 500)
	memSuffix = " --memout " + str(int(0.9*memLimit))
	global numW
	cmd = commands[idx] + optSuffix + timeSuffix + memSuffix + " -n w" + str(idx) + cmdSuffix
	#print ("starting cmd: %s" % cmd)
	#proc = Popen(cmd, shell=True, stdout=PIPE, stderr=PIPE, preexec_fn=os.setsid)
	proc = Popen("exec " + cmd, shell=True, stdout=PIPE, stderr=PIPE, close_fds=True)
	#proc = Popen("exec " + cmd, shell=True, stdout=None, stderr=None)
	print (time_str(), "(started worker %d with pid %d)" % (idx, proc.pid))
	processes[idx] = proc
	commandsRun.append(idx)
	numW += 1

def is_running(idx):
	if idx in processes:
		return True
	return False

def run_allowed(total_mem_usage):
	if total_mem_usage < (0.75*maxMemMB):
		return True
	return False

def run_commands_new(maxW):
	if disableNew:
		return;
	
	numRun = 0
	wi = numW
	total_mem_usage = 0
	while (wi < len(commands) and numRun < maxW):
		#print (time_str(), "(trying running %d)" % wi)
		if (not is_running(wi)):
			if (total_mem_usage == 0):
				total_mem_usage = mem_usage_all()
			retval = run_allowed(total_mem_usage)
			if retval:
				run_command(wi)
				numRun += 1
		wi += 1
	if numRun:
		print (time_str(), "(spawned %d workers)" % numRun)
		print (time_str(), "(total %d workers using %.0f MB)" % (numW, mem_usage_all()))
	
def kill_allowed(mem_usage):
	if mem_usage >= (0.9*maxMemMB):
		return True
	#print("kill not allowed since %f < %f" % (mem_usage, 0.98*maxMemMB))
	return False

def kill_command(idx):
	print (time_str(), "(killing worker %d)" % idx)
	terminate(idx)

def choose_kill_id():
	killIdx = numW - 1
	return killIdx

def kill_commands(maxW):
	global disableNew
	elapsed_time = time.time() - start_time
	if (elapsed_time > (0.995*opts.timeout)):
		disableNew = True
		terminate_all()
		return
	mem_usage = mem_usage_all()
	if (mem_usage > (opts.memout - 100)):
		disableNew = True
		if (numW > 1):
			terminate(commandsRun[-1])
		else:
			terminate_all()
		if (numW > 2):
			terminate(commandsRun[-2])
		return
	
	if (numW <= 1):
		return;
	
	numKill = 0
	while (numKill < maxW):
		i = (numW - 1)
		retval = kill_allowed(mem_usage)
		if retval:
			killIdx = choose_kill_id()
			kill_command(killIdx)
			numKill += 1
		else:
			break
	if numKill:
		disableNew = True
		print (time_str(), "(killed %d workers)" % numKill)
		print (time_str(), "(total %d workers using %.0f MB)" % (numW, mem_usage_all()))
	
def post_process(idx):
	proc = processes[idx]
	out, err = proc.communicate()
	print (time_str(), "(worker %d output)" % idx)
	sys.stdout.buffer.write(out)
	sys.stdout.buffer.write(err)


def check_process(idx):
	proc = processes[idx]
	retval = WorkerStatus.avr_run
	retcode = proc.poll()
	retval = WorkerStatus.avr_err
	#print("worker %d status: %s" % (idx, str(retcode)))
	if retcode != None:
		prFile = out_path + "/work_w" + str(idx) + "/result.pr"
		#print ("checking %s" % prFile)
		if os.path.isfile(prFile):
			with open(prFile) as f:
				prVal = f.read()
				if 'avr-h' in prVal:
					retval = WorkerStatus.avr_h
					return retval
				if 'avr-v' in prVal:
					retval = WorkerStatus.avr_v
					return retval
				if 'avr-f_to' in prVal:
					retval = WorkerStatus.avr_to
					return retval
				if 'avr-f_mo' in prVal:
					retval = WorkerStatus.avr_mo
					return retval
				if 'avr-f_' in prVal:
					retval = WorkerStatus.avr_err
					return retval
		else:
			prFile = out_path + "/work_w" + str(idx) + "/btormc.out"
			if os.path.isfile(prFile):
				with open(prFile) as f:
					prVal = f.read()
					if 'sat' in prVal:
						retval = WorkerStatus.avr_v
						return retval
					else:
						retval = WorkerStatus.avr_err
						return retval
	else:
		retval = WorkerStatus.avr_run
	return retval

def terminate_all():
	print (time_str(), "(stopping all workers)")
	for i in processes.keys():
		terminate(i)

def terminate(idx):
	proc = processes[idx]
	if proc.poll() is None:
		pidFile = out_path + "/work_w" + str(idx) + "/pid.txt"
		if (os.path.exists(pidFile)):
			with open(pidFile) as f:
				for x in f:
					terminate_ps(x)
		proc.terminate()
		proc.kill()

def check_process_all():
	global numW, resultW
	run_commands_new(maxInitW)
	it = 0
	while len(commandsRun):
		it += 1
		for i in commandsRun:
			retval = check_process(i)
			if retval != WorkerStatus.avr_run:
				commandsRun.remove(i)
				numW -= 1
				print (time_str(), "(worker %d finished with result %s) %s" % (i, get_result(retval), worker_desc(i)))
				if retval.value > 0:
					resultW = i
					post_process(i)
					terminate_all()
					return retval
		time.sleep(0.1)
		den_run = 20
		den_kill = 20
		if (it > 600):
			den_run = 40
			den_kill = 40
		elif (it > 300):
			den_run = 30
			den_kill = 30
		elif (it < 100):
			den_run = 5

		if (it % den_run == 0):
			run_commands_new(1)
		if (it % den_kill == 0):
			kill_commands(1)
		if (it % 100 == 0):
			print (time_str(), "(total %d workers using %.0f MB)" % (numW, mem_usage_all()))
	return WorkerStatus.avr_err

def colored(s):
	return COLOR1 + s + ENDC
	
def post_compile(retval):
	elapsed_time = time.time() - start_time
	s = colored("(proof race finished with answer %s in %.2f seconds)" % (get_result(retval), elapsed_time))
	res_path = out_path + "/work_w" + str(resultW) + "/"
	for filename in os.listdir(res_path):
		if filename.endswith('.results'):
			shutil.copy(res_path + filename, out_path + "/" + opts.name + ".results")
		#elif filename.endswith('.btor2'):
			#shutil.copy(res_path + filename, out_path + "/" + opts.name + ".btor2")
		#elif filename.endswith('result.pr') or filename.endswith('design.smt2') or filename.startswith('inv.') or filename.startswith('cex.witness'):
		elif filename.endswith('proof.smt2') or filename.endswith('design.smt2') or filename.startswith('inv.') or filename.startswith('cex.witness'):
			shutil.copy(res_path + filename, out_path)
		elif filename.endswith('btormc.out'):
			shutil.copy(res_path + filename, out_path+ "/cex.witness")
	print(time_str(), "(copied results from worker %d in %s)" % (resultW, out_path))
	print (time_str(), "(best config: %s)" % (worker_desc(resultW)))
	print(time_str(), s)

def worker_desc(idx):
	return commands[idx]

def mem_usage_all():
	total_mem_usage = 0.0
	for i in commandsRun:
		total_mem_usage += mem_usage_new(i)
	#print (time_str(), "(total memory usage %f)" % (total_mem_usage))
	return total_mem_usage

def mem_usage_new(idx):
	proc = processes[idx]
	mem_usage = 0
	if proc.poll() == None:
		pidFile = out_path + "/work_w" + str(idx) + "/pid.txt"
		if (os.path.exists(pidFile)):
			with open(pidFile) as f:
				for x in f:
					mem_usage += memory_usage_ps(x)
		#print (time_str(), "(worker %d memory usage %f)" % (idx, mem_usage))
		mem_usage *= 1e-3
	return mem_usage

def memory_usage_ps(pid_s):
	mem = 0
	valid, pid = is_valid_pid(pid_s)
	if (valid):
		if (check_pid(pid)):
			out = Popen("ps -v -p " + str(pid), shell=True, stdout=PIPE).communicate()[0].split(b'\n')
			#print("ps: ", out)
			if (len(out) >= 2):
				vsz_index = out[0].split().index(b'RSS')
				out1 = out[1].split()
				if (len(out1) > vsz_index):
					mem = float(out1[vsz_index])
					#print("mem: ", mem)
	#else:
		#assert(0)
	return mem

def terminate_ps(pid_s):
	valid, pid = is_valid_pid(pid_s)
	if (valid):
		if (check_pid(pid)):
			os.kill(pid, signal.SIGTERM)
			os.kill(pid, signal.SIGKILL)
	#else:
		#assert(0)

def check_pid(pid):
	""" Check For the existence of a unix pid. """
	try:
		os.kill(pid, 0)
	except OSError:
		return False
	else:
		return True

def is_valid_pid(pid_s):
	if pid_s and pid_s[0].isdigit():
		try:
			pid = int(pid_s)
			return True, pid
		except ValueError:
			return False, 0
	return False, 0

def main():
	setup()
	run_command_all()
	retval = check_process_all()
	post_compile(retval)

if __name__ == '__main__':
	main()
