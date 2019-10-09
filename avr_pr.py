import os, sys, datetime, time, psutil, resource, argparse, shutil, signal
from subprocess import Popen, PIPE, DEVNULL, STDOUT
from enum import Enum

version=2.0
start_time = time.time()

cmdSuffix = ""
maxWorkers = 10

optSuffix = " "
commands = []
commandsRun = []
memHigh = False
numW = 0
processes = {}

DEFAULT_TOP="-"
DEFAULT_OUT="output"
DEFAULT_NAME="test"
DEFAULT_WORKERS="workers.txt"
#DEFAULT_BIN="bin"
DEFAULT_TIMEOUT=3590
DEFAULT_MEMOUT=118000
DEFAULT_PRINT_SMT2=False

maxTimeSec = DEFAULT_TIMEOUT
maxMemMB = DEFAULT_MEMOUT
maxInitW = 3
resultW = 0
out_path = DEFAULT_OUT + "/" + DEFAULT_NAME

header="""
-----------------
AVR -- Proof Race
-----------------
  Abstractly Verifying Reachability
  
  Reads a state transition system and performs property checking 
  using syntax-guided data abstraction
  
  Copyright (c) 2019  Aman Goel <amangoel@umich.edu> and 
  Karem Sakallah <karem@umich.edu>, University of Michigan
  
  Please report bugs and share your usage experience via email 
  (amangoel@umich.edu) or on github (https://github.com/aman-goel/avr)	
---------------------------------
"""

short_header="""AVR -- Proof Race 
copyright (c) 2019  Aman Goel and Karem Sakallah, University of Michigan"""

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
	proc = Popen(cmd, shell=True, stdout=PIPE, stderr=PIPE, preexec_fn=os.setsid)
	print (time_str(), "(started worker %d with pid %d)" % (idx, proc.pid))
	processes[idx] = proc
	commandsRun.append(idx)
	numW += 1

def run_allowed(idx):
	if idx in processes:
		return False
	total_mem_usage = mem_usage_all()
	if total_mem_usage < (0.75*maxMemMB):
		return True
	return False

def run_commands_new(maxW):
	if memHigh:
		return;
	
	numRun = 0
	wi = numW
	while (wi < len(commands) and numRun < maxW):
		retval = run_allowed(wi)
		if retval:
			run_command(wi)
			numRun += 1
		wi += 1
	if numRun:
		print (time_str(), "(spawned %d workers)" % numRun)
		print (time_str(), "(total %d workers using %.0f MB)" % (numW, mem_usage_all()))
	
def kill_allowed(idx):
	total_mem_usage = mem_usage_all()
	if total_mem_usage >= (0.9*maxMemMB):
		return True
	#print("kill not allowed since %f < %f" % (total_mem_usage, 0.98*maxMemMB))
	return False

def kill_command(idx):
	print (time_str(), "(killing worker %d)" % idx)
	terminate(idx)

def choose_kill_id():
	killIdx = numW - 1
	return killIdx

def kill_commands(maxW):
	global memHigh
	elapsed_time = time.time() - start_time
	if (elapsed_time > (0.995*opts.timeout)):
		memHigh = True
		terminate_all()
	mem_usage = mem_usage_all()
	if (mem_usage > (opts.memout - 30)):
		memHigh = True
		terminate_all()
	
	if (numW <= 1):
		return;
	
	numKill = 0
	while (numKill < maxW):
		i = (numW - 1)
		retval = kill_allowed(i)
		if retval:
			killIdx = choose_kill_id()
			kill_command(killIdx)
			numKill += 1
		else:
			break
	if numKill:
		memHigh = True
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

def terminate(idx):
	proc = processes[idx]
	if proc.poll() is None:
		os.killpg(os.getpgid(proc.pid), signal.SIGTERM)
	if proc.poll() is None:
		os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
	#proc.terminate()
	#proc.kill()

def terminate_all():
	print (time_str(), "(stopping all workers)")
	for i in processes.keys():
		terminate(i)

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
		if (it % 10 == 0):
			run_commands_new(1)
		if (it % 10 == 0):
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
		elif filename.endswith('design.smt2') or filename.startswith('inv.') or filename.startswith('cex.witness'):
			shutil.copy(res_path + filename, out_path)
		elif filename.endswith('btormc.out'):
			shutil.copy(res_path + filename, out_path+ "/cex.witness")
	print(time_str(), "(copied results from worker %d in %s)" % (resultW, out_path))
	print(time_str(), s)

def worker_desc(idx):
	return commands[idx]

def mem_usage(idx):
	proc = processes[idx]
	mem_usage = 0
	if proc.poll() == None:
		psproc = psutil.Process(proc.pid)
		mem_usage = psproc.memory_info().rss
		for child in psproc.children(recursive=True):
			mem_usage += child.memory_info().rss
		mem_usage *= 1e-6
		
		#print (time_str(), "(worker %d memory usage %f)" % (idx, mem_usage / 1024 / 1024))
		#rusage_denom = 1024.
		#mem = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / rusage_denom
		#print (time_str(), "(worker %d memory usage2 %f)" % (idx, memory_usage_resource()))
		#mem_usage *= 1e-6

		#status = None
		#try:
			#status = open('/proc/self/status')
			#for line in status:
				#parts = line.split()
				#key = parts[0][2:-1].lower()
				#if key == 'rss':
					#mem_usage = int(parts[1])
					#mem_usage *= 1e-3
		#finally:
			#if status is not None:
				#status.close()

	return mem_usage

def mem_usage_all():
	total_mem_usage = 0.0
	for i in processes.keys():
		total_mem_usage += mem_usage(i)
	return total_mem_usage

def main():
	setup()
	run_command_all()
	retval = check_process_all()
	post_compile(retval)

if __name__ == '__main__':
	main()
