/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


#include "reach_core.h"
#include <execinfo.h>	// to dump call stacks (backtrace, backtrace_symbols)

namespace reach
{

//	I think the best way of feasibility check would be
//	to check 1) last_cube -> !p, 2) one_seg_check i.e. I -> first_cube
//	because the DP lemmas learnt from "last_cube -> !p" often are very useful
//	#define ONE_SEG_FEASIBILITY_CHECK

// For EUF (over ints or bvs) or CLU (over INTs)

// int memReadStat(int field){
//     char  name[256];
//     pid_t pid = getpid();
//     int   value;
// 
//     sprintf(name, "/proc/%d/statm", pid);
//     FILE* in = fopen(name, "rb");
//     if (in == NULL) return 0;
// 
//     for (; field >= 0; field--)
//         if (fscanf(in, "%d", &value) != 1)
//             printf("ERROR! Failed to parse memory statistics from \"/proc\".\n"), exit(1);
//     fclose(in);
//     return value;
// }
// 
// 
// int memReadPeak(void)
// {
//     char  name[256];
//     pid_t pid = getpid();
// 
//     sprintf(name, "/proc/%d/status", pid);
//     FILE* in = fopen(name, "rb");
//     if (in == NULL) return 0;
// 
//     // Find the correct line, beginning with "VmPeak:":
//     int peak_kb = 0;
//     while (!feof(in) && fscanf(in, "VmPeak: %d kB", &peak_kb) != 1)
//         while (!feof(in) && fgetc(in) != '\n')
//             ;
//     fclose(in);
// 
// 	return peak_kb;
// }
// 
// double cpuTime(void) {
//     struct rusage ru;
//     getrusage(RUSAGE_SELF, &ru);
//     return (double)ru.ru_utime.tv_sec + (double)ru.ru_utime.tv_usec / 1000000; }
//     
// double memUsed() { return (double)memReadStat(0) * (double)getpagesize() / (1024*1024); }
// double memUsedPeak() { 
//     double peak = memReadPeak() / 1024;
//     return peak == 0 ? memUsed() : peak;
// }

void solver_interrupt_handler(int signum)
{
	#ifdef _Z3
		z3_API::z3_interrupt(signum);
	#endif

	#ifdef _Y2
		y2_API::y2_interrupt(signum);
	#endif
}

// TODO remove this ugly code - will cause a problem when we run Averroes in parallel
static Reach *sigxcpu_handler_inst = NULL;

static bool error_to = false;
static bool error_err = false;

void SIGXCPU_handler(int signum) {
//     reportf("\n");
//     reportf("*** TIMEOUT ***\n");
//
	
// 	cout << "SIGXCPU: " << SIGXCPU << endl;
// 	cout << "SIGABRT: " << SIGABRT << endl;
// 	cout << "SIGSEGV: " << SIGSEGV << endl;
 	cout << "signum: " << signum << endl;
	
	if(signum == SIGXCPU){
		AVR_LOG(8, 0, "TIMEOUT" << endl);
		Inst::g_result = f_to;
		cout << "error: " << error_to << endl;
	}else{
		AVR_LOG(8, 0, "ERROR" << endl);
//		Solver::memory_out = true;

		// Increase limit on virtual memory (to allow running dump_execution_time):
		int mem_lim = sigxcpu_handler_inst->get_memlimit() + 200; // give additional 200 MB
		if ((mem_lim != 0) && (mem_lim != INT32_MAX)){
			rlim_t new_mem_lim = (rlim_t)mem_lim * 1024*1024;
			rlimit rl;
			getrlimit(RLIMIT_AS, &rl);
			if(rl.rlim_max == RLIM_INFINITY || new_mem_lim < rl.rlim_max){
				rl.rlim_cur = new_mem_lim;
				if (setrlimit(RLIMIT_AS, &rl) == -1)
					printf("WARNING! Could not set resource limit: Virtual memory.\n");
			} }
	}
	
	if (!error_to) {
		error_to = true;
//		cout << "entering: dump_execution_time" << endl;
		sigxcpu_handler_inst->dump_execution_time(EXIT_TIMEOUT);
//		cout << "exiting: dump_execution_time" << endl;
	}
	
//	assert(0);	// I'm not sure if _exit(0); would be better

// 	double cpu_time = cpuTime();
// 	double mem_used = memUsedPeak();
// // 	FILE* res = fopen("out.txt", "wb");
// // 	fprintf(res, "INDET	%.2f	%g	0	0	", mem_used, cpu_time);
// // 	fclose(res);
// 
// 	if(_global_timeout != 0 && cpu_time >= (double)(_global_timeout - 10)){
// 		cout << "TIMEOUT, elapsed time: " << cpu_time << endl;
// 		dump_execution_time();
// 	//	assert(0);
// 	}else{
// 	//if(_global_memory_limit != 0 && mem_used > (double)_global_memory_limit){
// 		cout << "MEMORY, memory usage: " << mem_used << endl;
// 		dump_execution_time();
// 	//	assert(0);
// 	}
	
    //SatELite::deleteTmpFiles();

//	try {
//		delete sigxcpu_handler_inst;
//	}
//	catch (const std::exception&) {
//		cout << "Unable to free memory" << endl;
//	}

	exit(0);
//    _exit(0);	// (using 'exit()' rather than '_exit()' sometimes causes the solver to hang (why?))
}
    
void SIGSEGV_handler(int signum) {
  cout << "ERROR (code: " << signum << ")" << endl;

	AVR_LOG(8, 0, "SEGFAULT" << endl);
	Inst::g_result = f_err;

	if (!error_err) {
		error_err = true;
		{
			void *array[10];
			size_t size;

			// get void*'s for all entries on the stack
			size = backtrace(array, 10);

			// print out all the frames to stderr
			fprintf(stderr, "Error: signal %d:\n", signum);
			backtrace_symbols_fd(array, size, STDERR_FILENO);
		}
		{
			// Increase limit on virtual memory (to allow running dump_execution_time):
			int mem_lim = sigxcpu_handler_inst->get_memlimit() + 200; // give additional 200 MB
			if ((mem_lim != 0) && (mem_lim != INT32_MAX)){
				rlim_t new_mem_lim = (rlim_t)mem_lim * 1024*1024;
				rlimit rl;
				getrlimit(RLIMIT_AS, &rl);
				if(rl.rlim_max == RLIM_INFINITY || new_mem_lim < rl.rlim_max){
					rl.rlim_cur = new_mem_lim;
					if (setrlimit(RLIMIT_AS, &rl) == -1)
						printf("WARNING! Could not set resource limit: Virtual memory.\n");
				}
			}
		}
		sigxcpu_handler_inst->dump_execution_time(EXIT_ERROR);
	}
	exit(0);
}

static void callback_memout(void) {
	Inst::g_result = f_mo;
  cout << "\tERROR (out of memory)" << endl;
  sigxcpu_handler_inst->dump_execution_time(EXIT_MEMOUT);
  exit(0);
}

//bool compare_inst (Inst *first, Inst *second) {
//	if (first->get_id() < second->get_id()) {
//		return true;
//	} else {
//		return false;
//	}
//}

Reach::~Reach(){
  _tb_queue.PQ_clear();
  Inst::uncreate_all();
  exit_solv();
}

void Reach::delete_solvers() {
  if (_cti_solver){
    delete static_cast < SOLVER_CTI *>(_cti_solver);
    _cti_solver = NULL;
  }
#ifdef AVR_PPC_SOLVER_ENABLE
  if (_ppc_solver){
    delete _ppc_solver;
    _ppc_solver = NULL;
  }
#endif
#ifdef AVR_PME_SOLVER_ENABLE
  if (_pme_solver) {
    delete _pme_solver;
    _pme_solver = NULL;
  }
#endif
  {
    int rs_size = _reach_solvers.size();
    for (int i = 0; i < rs_size; i++) {
      if (_reach_solvers[i].solver_main) {
        delete static_cast<SOLVER_CORE*>(_reach_solvers[i].solver_main);
        _reach_solvers[i].solver_main = NULL;
      }
#ifdef FRAME_SOLVER_MULTI
    	if (_reach_solvers[i].solver1) {
        delete static_cast<SOLVER_REACH*>(_reach_solvers[i].solver1);
        _reach_solvers[i].solver1 = NULL;
      }
#endif
    }
  }
  if (_euf_solver){
    delete static_cast<SOLVER_AB*>(_euf_solver);
    _euf_solver = NULL;
  }
  del_conc_solver();
}


void Reach::init_solv()
{
	_resFile << "backend:\t";

	string s = "";

#ifdef BACKEND_HYBRID
	s += "y2+bt";
#endif

#ifdef BACKEND_Y2
	s += "+y2";
#endif

#ifdef BACKEND_Z3
	s += "+z3";
#endif

#ifdef BACKEND_M5
	s += "+y2";
#endif

#ifdef BACKEND_BT
	s += "+bt";
#endif

	_resFile << s << endl;

#ifdef _Z3
	z3_API::z3_init();
#endif

#ifdef _Y2
	y2_API::y2_out_of_memory_callback = callback_memout;
	y2_API::y2_init();
#endif

#ifdef _M5
	m5_API::m5_init();
#endif

#ifdef _BT
	bt_API::bt_init();
#endif

#ifdef _MS
	ms_API::ms_init();
#endif
}

void Reach::exit_solv()
{
#ifdef _Z3
	z3_API::z3_exit();
#endif

#ifdef _Y2
	y2_API::y2_exit();
#endif

#ifdef _M5
	m5_API::m5_exit();
#endif

#ifdef _BT
	bt_API::bt_exit();
#endif

#ifdef _MS
	ms_API::ms_exit();
#endif
}

void Reach::reset_solv()
{
//#ifdef _Z3
//	z3_API::z3_reset();
//#endif

#ifdef _Y2
	y2_API::y2_reset();
#endif
}

void Reach::init_flow() {
	struct rusage usage;
	TIME_S(_start_time);

	//	memset(global_debug_level, 1, sizeof(int) *20);
#ifdef ARM_RELEASE
	for(int i = 0; i < 20; i++){
		global_debug_level[i] = 0;
	}
#else
	for(int i = 0; i < 25; i++){
		global_debug_level[i] = 0;
	}
// string global_loc_tag[20] = {
// // global_loc_tag[10] = "CONF"
// 	"PRE", "CTI", "BP", "FP", "DPR", "TB-D", "TB-BP", "CC", "RES", "EVAL", "CONF", "SOLV", "WN"
//	string s_dbg = _config->get_arg(AVR_VERB_ARG);
//	string s_dbg = "666666666";

	/// Aman
#ifdef TEMP_DEBUG_LEVEL
	string s_dbg = TEMP_DEBUG_LEVEL;
#else
	string s_dbg = _config->get_arg("vlevel");
#endif
	/// END

	string verb = _config->get_arg("verbosity");
	s_dbg[15] = verb[0];

	int dbg_idx = 0;
	if (s_dbg != "") {
		if (s_dbg.find_first_of(" ,:;\t") == string::npos) {
			for(dbg_idx = 0; dbg_idx < (int)s_dbg.length(); dbg_idx++){
				char ch = s_dbg[dbg_idx];
				int level = (int)ch - (int)'0';
//				int level_orig = level;
				level = (1 << (level + 1)) - 1;
				global_debug_level[dbg_idx] = level;
//				cout << "global_debug_level[" << dbg_idx << "] = " << level_orig << " i.e. " << level
//				    << "\t" << (global_debug_level[dbg_idx] & (1 << level_orig)) << endl;
			}
		} else {
			int level = 0;
			int bit_idx = 0;
			for(int c = 0; c < (int)s_dbg.length(); c++){
				char ch = s_dbg[c];
				if(ch == ' '){
					global_debug_level[dbg_idx] = level;
					dbg_idx++;
					level = 0;
					bit_idx = 0;
				}else{
					level = level | ((((int)ch - (int)'0') & 1) << bit_idx);
					bit_idx++;
				}
			}
		}
	}

#endif
// 	cout << "DEBUG_LEVEL";
// 	for(int i = 0; i < dbg_idx; i++){
// 		cout << " ";
// 		int level = global_debug_level[i];
// 		for(int j = 0; j < 8; j++){
// 			cout << (level & 1);
// 			level >>= 1;
// 		}
// 	}
// 	cout << endl;
	//assert(0);
	
#if 0
	Inst::wn_simplify_extract_adv = true;
	Inst::wn_simplify_extract = true;
	Inst::wn_simplify_concat = true;
	Inst::wn_simplify_const_pred = true;
	Inst::wn_simplify_const_num = true;
	Inst::wn_simplify_ite = true;
	Inst::wn_simplify_repetition = true;
	Inst::wn_1bit_dp_to_control = true;
	Inst::wn_simplify_eq = true;
#else
//	Inst::wn_simplify_extract_adv = false;

#ifdef ALL_SIMPLIFIED_EX_CC
	Inst::wn_simplify_extract = true;
	Inst::wn_simplify_concat = true;
#else
	Inst::wn_simplify_extract = false;
	Inst::wn_simplify_concat = false;
#endif

	Inst::wn_simplify_const_pred = true;
	//Inst::wn_simplify_const_pred = false;
	Inst::wn_simplify_const_num = false;
	Inst::wn_simplify_ite = false;
	Inst::wn_simplify_repetition = false;
	Inst::wn_1bit_dp_to_control = true;
	Inst::wn_simplify_eq = false;
#endif
	// check whether this thing below makes sense!
	/*  Inst::wn_simplify_const_num =
	 _config->get_arg(SIM_SIMPL_ARG)==CONFIG_ON &&
	 _config->get_arg(ABST_LOGIC_ARG)==CONFIG_CLU &&
	 _config->get_arg(ALG_T_ARG)==CONFIG_AR;*/

	init_solv();
}

// dump a formula with intermediate signals to save space

void Reach::new_print(ostream& fout, InstL &vel, bool init_visit) {
	for (InstL::iterator it = vel.begin(); it != vel.end(); ++it) {
		if(init_visit == true){
			new_print(fout, *it, true);
		}else{
			new_print(fout, *it, false);
		}
		init_visit = false;
	}
}

void Reach::new_print(ostream& fout, Inst* e, bool init_visit) {
	if (init_visit) {
		Inst::init_visit2();
	}

// 	if(e->get_type() == Num){
// 		NumInst* ve_num = NumInst::as(e);
// 		fout << ve_num->get_size() << "'d" << ve_num->get_num();
// 	}else if(e->get_type() == Sig){
// 		SigInst* ve_sig = SigInst::as(e);
// 		fout << ve_sig->get_name();
// 	}
	
	if (e->get_visit2()){
		return;
	}
	e->set_visit2();

	if(e->get_type() == Num){
		if((e->acex_coi != NULL) && (NumInst::as(e->acex_coi) != NULL) && (e->acex_coi->get_type() == Num)){
	//		cout << e->acex_coi << endl;
			fout << *(e->acex_coi) << "	";
		}
		fout << "n" << e->get_id() << "n" << " " << e->get_size() << " : ";
		NumInst* ve_num = NumInst::as(e);
		fout << ve_num->get_size() << "'d" << ve_num->get_num();
		fout << endl;
	}else if(e->get_type() == Sig){
		if((e->acex_coi != NULL) && (NumInst::as(e->acex_coi) != NULL) && (e->acex_coi->get_type() == Num)){
	//		cout << e->acex_coi << endl;
			fout << *(e->acex_coi) << "	";
		}
		fout << "n" << e->get_id() << "n" << " " << e->get_size() << " : ";
		SigInst* ve_sig = SigInst::as(e);
		fout << ve_sig->get_name();
		fout << endl;
	}else if(e->get_type() == Op){
		OpInst *ve_op = OpInst::as(e);
		const InstL* chs = e->get_children();
		OpInst::OpType e_op = ve_op->get_op();
		
		{
			InstL::const_iterator it = chs->begin();
			for (InstL::const_iterator end_it = chs->end(); it != end_it; ++it) {
				Inst *ch = *it;
				new_print(fout, ch);
			}
		}
		
		if((e->acex_coi != NULL) && (NumInst::as(e->acex_coi) != NULL) && (e->acex_coi->get_type() == Num)){
	//		cout << e->acex_coi << endl;
			fout << *(e->acex_coi) << "	";
		}
		fout << "n" << e->get_id() << "n" << " " << e->get_size() << " : ";
		if (e_op == OpInst::Future) {
			fout << OpInst::op2str(e_op) << "(";
			fout << "n" << (*(chs->begin()))->get_id() << "n";
			fout << ")";
		} else if (e_op == OpInst::Concat) {
			fout << "{";
			InstL::const_reverse_iterator it = chs->rbegin();
			fout << "n" << (*it)->get_id() << "n";
			it++;
			for (InstL::const_reverse_iterator end_it = chs->rend(); it != end_it; ++it){
				fout << " , " << "n" << (*it)->get_id() << "n";
			}
			fout << "}";
		} else if (e_op == OpInst::Ternary) {
			assert(chs->size() == 3);
			InstL::const_iterator it = chs->begin();
			fout << "(";
			fout << "n" << (*it)->get_id() << "n";
			fout << "?";
			it++;
			fout << "n" << (*it)->get_id() << "n";
			fout << ":";
			it++;
			fout << "n" << (*it)->get_id() << "n";
			fout << ")";
		} else if (e_op == OpInst::LogAnd) {
			InstL::const_iterator it = chs->begin();
	//		fout << "(" << endl << "	" << (*it)->get_id();
			fout << "(" << "n" << (*it)->get_id() << "n";
			it++;
			for (InstL::const_iterator end_it = chs->end(); it != end_it; ++it) {
	//			fout << " " << OpInst::op2str(e_op) << " " << endl << "	" << (*it)->get_id();
				fout << " " << OpInst::op2str(e_op) << " " << "n" << (*it)->get_id() << "n";
			}
			fout << ")";
		} else {
			unsigned sz = chs->size();
// 			if (sz == 1) {
// 				fout << OpInst::OpInst::op2str(e_op);
// 				ostringstream ss;
// 				ss << *(*(chs->begin()));
// 				if ((*(chs->begin()))->get_type() == Op || (*(chs->begin()))->get_type() == Ex)
// 					fout << "(" << ss.str() << ")";
// 				else
// 					fout << ss.str();
// 			} else 
			{
				assert(sz != 0);
				InstL::const_iterator it = chs->begin();
				fout << "(";
				if(chs->size() == 1){
					fout << OpInst::op2str(e_op);
				}
				fout << "n" << (*it)->get_id() << "n";
				it++;
				for (InstL::const_iterator end_it = chs->end(); it != end_it; ++it) {
					fout << " " << OpInst::op2str(e_op) << " " << "n" << (*it)->get_id() << "n";
				}
				fout << ")";
			}
		}
		fout << endl;
	}else if(e->get_type() == Ex){
		const InstL* chs = e->get_children();
		Inst *ch = chs->front();
		new_print(fout, ch);


		if((e->acex_coi != NULL) && (NumInst::as(e->acex_coi) != NULL) && (e->acex_coi->get_type() == Num)){
	//		cout << e->acex_coi << endl;
			fout << *(e->acex_coi) << "	";
		}
		fout << "n" << e->get_id() << "n" << " " << e->get_size() << " : ";
		ExInst *ve_ex = ExInst::as(e);
		bool complex = (ch->get_type() != Sig && ch->get_type() != Num);
		if (complex)
			fout << "(";
		fout << "n" << ch->get_id() << "n";
		if (complex)
			fout << ")";
		fout << "[" << ve_ex->get_hi() << ":" << ve_ex->get_lo() << "]";
		fout << endl;
	}else{
		assert(0);
	}
}

#ifdef AVR_DUMP_DOT

string shapes[29] = {
	"box", "ellipse",
	"triangle", "diamond", "trapezium", "parallelogram", "house",
	"pentagon", "hexagon", "septagon", "octagon", "doublecircle",
	"doubleoctagon", "tripleoctagon", "invtriangle", "invtrapezium", "invhouse",
	"Mdiamond", "Msquare", "Mcircle", "rect", "rectangle",
	"square", "note", "tab", "folder", "circle", "egg", "polygon"
};

/// mode = 0 => Complete expression
/// mode = 1 => Stop at known expression
unsigned Reach::dump_dot(int mode, ostream& fout, Inst* top, int depth, bool allowFade, bool init_visit){
	unsigned id = top->get_id();
	if (init_visit) {
		Inst::init_visit();
	}
	if (top->get_visit()) {
		return id;
	}
	top->set_visit();

	if (mode == 2) {
	  if (top->get_drVal(Inst::get_drkey()) == -1)
	    return id;
	}

	int width = top->get_size();
	string color = (width == 1) ? "blue" : "red";
	
	bool fade = false;
	if (allowFade)
		if (!top->get_hlVal(Inst::get_dckey()))
			fade = true;

	bool isInternal = false;

//	if (top == _ve_model || top == _ve_model_next)
//	{
//		if (mode == 1)
//			isInternal = true;
//	}

	bool filled = false;
  bool addVal = false;
	if (mode == 2) {
	  if (top->get_size() == 1) {
	    if (top->get_bval() == 1)
	      filled = true;
	    else if (top->get_bval() == 0)
	      fade = true;
    }
    else if (top->get_ival() != INVALID_SMPZ)
      addVal = true;
	}

	if(top->get_type() == Sig){
		string sname = SigInst::as(top)->get_name();
		fout << "\t" << id << "[label = \"" << sname
				<< "\n(" << width << "b)";
		if (addVal)
      fout << " (v" << top->get_ival()->get_si() << ")";
		fout << " (c" << top->ab_interpret.is_concrete() << top->ab_interpret.output_concrete() << ")"
				<< "\" shape = \"" << shapes[0] <<
				"\" color = " << (fade ? "grey": "green");
    if (filled)
      fout << " style=filled";
    fout << " ];" << endl;
	}else if(top->get_type() == Num){
		string snum = (NumInst::as(top)->get_mpz())->get_str();
		fout << "\t" << id << "[label = \"" << width << "'d" << snum;
    if (addVal)
      fout << " (v" << top->get_ival()->get_si() << ")";
		fout << " (c" << top->ab_interpret.is_concrete() << top->ab_interpret.output_concrete() << ")"
				<< "\" shape = \"" << shapes[0] << "\" color = " << (fade ? "grey": "yellow");
    if (filled)
      fout << " style=filled";
    fout << " ];" << endl;
	}else if(top->get_type() == Op){
		OpInst* op = OpInst::as(top);
		OpInst::OpType e_op = op->get_op();
		string name = "";
		Inst* w = op->get_wire();
		if (w)
		{
			name = WireInst::as(w)->get_name();
			if (mode == 1)
				isInternal = true;
		}
		fout << "\t" << id << "[label = \"" << name;
		string euf_func_name = op->get_euf_func_name();
		if (euf_func_name != "0")
		{
			fout << "\n" << euf_func_name;
			fout << " (" << OpInst::op2str(e_op) << ") ";
      if (addVal)
        fout << " (v" << top->get_ival()->get_si() << ")";
			fout << " (c" << top->ab_interpret.is_concrete() << top->ab_interpret.output_concrete() << ")"
					<< "\" shape = \"" << shapes[0];
			if (euf_func_name.length() > 6 && euf_func_name.substr(0, 6) == "Concat")
				fout << "\" color = " << (fade ? "grey": "brown");
			else
				fout << "\" color = " << (fade ? "grey": "orange");
		}
		else
		{
			fout << "\n(" << OpInst::op2str(e_op) << ") ";
      if (addVal)
        fout << " (v" << top->get_ival()->get_si() << ")";
			fout << " (c" << top->ab_interpret.is_concrete() << top->ab_interpret.output_concrete() << ")"
					<< "\" shape = \"" << shapes[0];
			fout << "\" color = " << (fade ? "grey": "violet");
		}

		if (isInternal)
		{
			fout << " style=filled";
		}
		else {
	    if (filled)
	      fout << " style=filled";
		}
		fout << " ];" << endl;


	}else if(top->get_type() == Ex){
		ExInst *vex = ExInst::as(top);
		string name = "";
		Inst* w = vex->get_wire();
		if (w)
		{
			name = WireInst::as(w)->get_name();
			if (mode == 1)
				isInternal = true;
		}
		fout << "\t" << id << "[label = \"" << name;
		string euf_func_name = vex->get_euf_func_name();
		fout << "\n" << euf_func_name;
		fout << " [" << vex->get_hi() << ":" << vex->get_lo() << "]";
    if (addVal)
      fout << " (v" << top->get_ival()->get_si() << ")";
		fout << " (c" << top->ab_interpret.is_concrete() << top->ab_interpret.output_concrete() << ")"
				<< "\" shape = \"" << shapes[0] << "\" color = " << (fade ? "grey": "brown") << endl;

		if (isInternal)
		{
			fout << " style=filled";
		}
		else {
      if (filled)
        fout << " style=filled";
		}
		fout << " ];" << endl;
	}
	else if(top->get_type() == Wire){
//		fout << "\t" << id << "[ label = \"" << "";
//		fout << "\" shape = \"" << shapes[26] << "\" fixedsize = \"" << "true" << "\" width = \"" << 0.05 << "\" height = \"" << 0.05 << "\" style = \"" << "filled" << "\" color = " << "black" << "];" << endl;
	}
	else{
		fout << "\t" << id << "[label = \"" << id << "#" << width << "\" shape = \"" << shapes[0] << "\" color = " << (fade ? "grey": color) << "];" << endl;
	}
	if(--depth == 0){
		return id;
	}

	if (!top->childrenInfo[WIRE])
		isInternal = false;

//	if (!isInternal)
//	if (!fade)
	{
		const InstL* ch = top->get_children();
		if (ch) {
			if(ch->size() == 1){
				Inst* tve = ch->front();
				if (tve->get_type() == Wire)
				{
					WireInst* w = WireInst::as(tve);
					assert(w);
					tve = w->get_port();
				}
				unsigned ret = dump_dot(mode, fout, tve, depth, allowFade, false);
				fout << "\t" << ret <<" -> " << id << ";" << endl;
			}else{
				int idx = 0;
				Inst* lastChild = NULL;
				bool skipRepeat = false;

				OpInst* opTop = OpInst::as(top);
				if (opTop && opTop->get_op() == OpInst::Concat)
				{
					skipRepeat = true;
				}

				for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it)
				{
					Inst* tve = *it;

					if (skipRepeat && (tve == lastChild))
						continue;
					lastChild = tve;

					if (tve->get_type() == Wire)
					{
						WireInst* w = WireInst::as(tve);
						assert(w);
						tve = w->get_port();
					}
					unsigned ret = dump_dot(mode, fout, tve, depth, allowFade, false);

					if (top->get_type() == Op)
					{
						OpInst* op = OpInst::as(top);
						assert(op);
						switch(op->get_op())
						{
						case OpInst::Ternary:
							if (idx == 0)
								fout << "\t" << ret <<" -> " << id << "[label = \"" << "C" << "\"";
							else if (idx == 1)
								fout << "\t" << ret <<" -> " << id << "[label = \"" << "T" << "\"";
							else if (idx == 2)
								fout << "\t" << ret <<" -> " << id << "[label = \"" << "F" << "\"";
							else
								assert(0);
							idx++;
							break;
						default:
							fout << "\t" << ret <<" -> " << id << "[label = \"" << idx++ << "\"";
						}
					}
					else
					{
						fout << "\t" << ret <<" -> " << id << "[label = \"" << idx++ << "\"";
					}
					fout << "];" << endl;
				}
			}
//			if(ch->size() == 1){
//				unsigned ret = dump_dot(fout, ch->front(), depth, dontCare, fade, false);
//				fout << "\t" << ret <<" -> " << id << ";" << endl;
//			}else{
//				int idx = 0;
//				for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it) {
//					unsigned ret = dump_dot(fout, *it, depth, dontCare, fade, false);
//					fout << "\t" << ret <<" -> " << id << "[label = \"" << idx++ << "\"];" << endl;
//				}
//			}
		}
	}
	return id;
}

// return the Inst* whose id is the same as the input "id"
Inst *Reach::find_node(Inst *top, unsigned id, bool init_visit) {
	if (init_visit) {
		Inst::init_visit();
	}
	if (top->get_visit()) {
		return NULL;
	}
	top->set_visit();

	if(top->get_id() == id){
		return top;
	}else{
		const InstL* ch = top->get_children();
		if (ch) {
			for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it) {
				Inst *tve = find_node(*it, id, false);
				if(tve != NULL){
					return tve;
				}
			}
		}
		return NULL;
	}
}

void Reach::draw_graph(int mode, Inst* top, string fname, int depth, bool allowFade){

	struct rusage usage;
	struct timeval start_time, end_time;
	long long time_diff;

	TIME_S(start_time);

	assert(top != NULL);

	string of_name, gif_name;
//	if (fname == "")
//	{
//		OpInst* op = OpInst::as(top);
//		if (op)
//		{
//			fname = op->get_v_name();
//		}
//		else
//		{
//			ostringstream ostr;
//			ostr << *top;
//			fname = ostr.str();
//		}
//	}
	if (fname == "")
		fname = "#" + to_string(top->get_id());

	assert(fname != "");

	size_t len = fname.length();
	if (len > 5 && (fname.substr(len - NEXT_SUFFIX_LENGTH) == NEXT_SUFFIX))
	{
		fname.replace(len - NEXT_SUFFIX_LENGTH, 1, "_");
	}

	{
		ostringstream ostr;
		ostr << _config->get_working_dir() << "/dot/" << fname << ".dot";
		of_name = ostr.str();
	}
	{
		ostringstream ostr;
		ostr << _config->get_working_dir() << "/gif/" << fname << ".gif";
		gif_name = ostr.str();
	}

	ofstream ofile;
	ofile.open (of_name.c_str());
	ofile<<"digraph tmp {"<<endl;

	//ofile<<"ratio=0.625;"<<endl;
	ofile<<"\tnode[fontsize=18];"<<endl;
//	ofile << "\tranksep = 0.75; rankdir=LR;" << endl;
	ofile << "\tranksep = 0.75; rankdir=BT;" << endl;

//	OpInst* op = OpInst::as(top);
//	if (op)
//	{
//		string name = op->get_v_name();
//		if (name != "")
//		{
//			ofile << "\tlabel=\"" << name << "\";" << "\n";
//			ofile << "\tlabelloc=\"top\";" << "\n";
//			ofile << "\tlabeljust=\"left\";" << "\n\n";
//		}
//	}

	dump_dot(mode, ofile, top, depth, allowFade, true);

	ofile<<"}"<<endl;

	//dot -Tgif scu_sym_v3.dot -o scu_sym_v3.gif
//	string cmd = "dot -Tgif " + of_name + " -o " + gif_name;
//	if (0 != system(cmd.c_str())) {
//		cout << "dot error!!!" << endl;
//		cout << cmd << endl;
//		assert(0);
//	}
	ofile.close();
//	cout << "draw_graph() succeed!!!" << endl;

	TIME_E(start_time, end_time, _draw_time);
}

void Reach::draw_graph(string fname, string sname, int depth){
	Inst *top;
	if(sname == _config->get_arg(PROP_SIG_ARG)){
		top = _ve_model;
	}else if(sname == "nsf"){
		top = _ve_model_nsf;
	}else{
		map<std::string, Inst*>::iterator hm_it = SigInst::hm_SigInst.find(sname);
		if(hm_it != SigInst::hm_SigInst.end()){
			Inst *ve_sig = hm_it->second;
			int width = ve_sig->get_size();
			SORT sort = ve_sig->get_sort();
			cout << "draw_graph: reg_name: " << sname << ", width: " << width << endl;
			top = SigInst::create(sname+"$next", width, sort);
			//top = _m_sn[top];
			top = Inst::fetch_trelation(top);
		}else{
			unsigned id = atoi(sname.c_str());
			top = find_node(OpInst::create(OpInst::LogAnd, _ve_model, _ve_model_nsf), id, true);
		}
	}
	assert(top != NULL);

	string of_name, gif_name;
	of_name = fname + ".dot";
	gif_name = fname + ".gif";

	ofstream ofile;
	ofile.open (of_name.c_str());
	ofile<<"digraph tmp {"<<endl;

	//ofile<<"ratio=0.625;"<<endl;
	ofile<<"node[fontsize=18];"<<endl;

	dump_dot(0, ofile, top, depth, false, true);

	ofile<<"}"<<endl;

	//dot -Tgif scu_sym_v3.dot -o scu_sym_v3.gif
	string cmd = "dot -Tgif "+of_name+" -o "+gif_name;
	cout<<cmd<<endl;
	if (0 != system(cmd.c_str())) {
		cout<<"dot error!!!"<<endl;
	}
	ofile.close();
	cout << "draw_graph() succeed!!!" << endl;

}

void Reach::draw_graph(int mode, Inst* top1, Inst* top2, string fname, int depth, bool allowFade){

	struct rusage usage;
	struct timeval start_time, end_time;
	long long time_diff;

	TIME_S(start_time);

	assert(top1 != NULL);
	assert(top2 != NULL);

	string of_name, gif_name;
	assert(fname != "");

	size_t len = fname.length();
	if (len > 5 && (fname.substr(len - NEXT_SUFFIX_LENGTH) == NEXT_SUFFIX))
	{
		fname.replace(len - NEXT_SUFFIX_LENGTH, 1, "_");
	}

	{
		ostringstream ostr;
		ostr << _config->get_working_dir() << "/dot/" << fname << ".dot";
		of_name = ostr.str();
	}
	{
		ostringstream ostr;
		ostr << _config->get_working_dir() << "/gif/" << fname << ".gif";
		gif_name = ostr.str();
	}

	ofstream ofile;
	ofile.open (of_name.c_str());
	ofile<<"digraph tmp1 {"<<endl;

	//ofile<<"ratio=0.625;"<<endl;
	ofile<<"\tnode[fontsize=18];"<<endl;
//	ofile << "\tranksep = 0.75; rankdir=LR;" << endl;
	ofile << "\tranksep = 0.75; rankdir=BT;" << endl;

	dump_dot(mode, ofile, top1, depth, allowFade, true);

	dump_dot(mode, ofile, top2, depth, allowFade, false);

	ofile<<"}"<<endl;

//	ofile<<"digraph tmp2 {"<<endl;
//
//	//ofile<<"ratio=0.625;"<<endl;
//	ofile<<"\tnode[fontsize=18];"<<endl;
////	ofile << "\tranksep = 0.75; rankdir=LR;" << endl;
//	ofile << "\tranksep = 0.75; rankdir=BT;" << endl;
//
//	dump_dot(mode, ofile, top2, depth, allowFade, true);
//
//	ofile<<"}"<<endl;

	//dot -Tgif scu_sym_v3.dot -o scu_sym_v3.gif
//	string cmd = "dot -Tgif " + of_name + " -o " + gif_name;
//	if (0 != system(cmd.c_str())) {
//		cout << "dot error!!!" << endl;
//		cout << cmd << endl;
//		assert(0);
//	}
	ofile.close();
//	cout << "draw_graph() succeed!!!" << endl;

	TIME_E(start_time, end_time, _draw_time);
}

#endif

void Reach::load(Trans& trans, string fname, string ftype, bool dump_modeling) {
	if (ftype == CONFIG_WN) {
		ifstream f;
		access_file(f, fname);
		if (trans.empty())
			trans.read_bin(f);
		else {
			Trans t;
			t.read_bin(f);
			for (Trans::iterator it = t.begin(), end_it = t.end(); it != end_it; ++it)
				trans.push_back(*it);
		}
	}else
		assert(0);
	trans.simplify();
}

void Reach::load_model() {
	string fname = _config->get_working_dir() + "/data/wn.dump";
 	load(_model, fname, "wn");

	if (!_model.check_consistency()) {
		AVR_COUT << "WRN: Model is not consistent!" << endl;
	}

// 	if (_config->get_arg(DUMP_MODEL_ARG) != "") {
// 		ofstream f;
// 		access_file(f, _config->get_working_dir() + "/" + _config->get_arg(DUMP_MODEL_ARG));
// 		f << _model;
// 		f.close();
// 		AVR_COUT << (string("model dumped to: ") + _config->get_arg(DUMP_MODEL_ARG)) << endl;
// 	}
}

void Reach::write_wn() {
	ofstream fout;
	string fname = _config->get_working_dir() + "/data/wn.dump";
	access_file(fout, fname);

	Trans::st_out = &fout;

	Trans::write_int(static_cast<int> (WN_VERSION * 10));

	Trans::write_str(Trans::m_module_name);
	Trans::st_ptr_to_id.clear();
	Trans::reachable.clear();
	Inst::init_visit();

// 	AVR_LOG(0, 1, "_ve_init:" << endl << *_ve_init << endl);
// 	AVR_LOG(0, 1, "_ve_model_nsf:" << endl << *_ve_model_nsf << endl);
// 	AVR_LOG(0, 1, "_ve_model:" << endl << *_ve_model << endl);
	
	Trans::collect_reachable(_ve_init);
	Trans::collect_reachable(_ve_model_nsf);
	Trans::collect_reachable(_ve_model);
	Trans::collect_reachable(_ve_assume);

	Trans::write_int(Trans::reachable.size());

	// writes types
	unsigned i = 0;
	for (InstL::iterator it = Trans::reachable.begin(), end_it = Trans::reachable.end(); it != end_it; ++it, i++) {
		Trans::write_int(static_cast<int> ((*it)->get_type()));
		(*it)->write_bin();
		Trans::st_ptr_to_id.insert(make_pair(*it, i));
	}

	Trans::write_int(Trans::ptr_to_id(_ve_init));
	Trans::write_int(Trans::ptr_to_id(_ve_model_nsf));
	Trans::write_int(Trans::ptr_to_id(_ve_model));
	Trans::write_int(Trans::ptr_to_id(_ve_assume));

	fout.close();
	AVR_LOG(0, 1, "Deisgn WN is dumped to " << fname << endl);
}

void Reach::read_wn() {
	ifstream fin;
	string fname = _config->get_working_dir() + "/data/wn.dump";
	access_file(fin, fname);
	Trans::st_in = &fin;

	int ver = Trans::read_int();
	if (ver != static_cast<int> (WN_VERSION * 10)) {
		AVR_COUT << "WRN: incompatible wn version, file: " << ver / 10.0 << ", reach: ";
		AVR_COUT << static_cast<int> (WN_VERSION * 10) / 10.0 << endl;
	}

	Trans::m_module_name = Trans::read_str();
	Trans::st_id_to_ptr.clear();

	int nodes_num = Trans::read_int();
	// read types & construct nodes
	int numUF = 0;
	int numEx = 0;
	int numCc = 0;
	for (int i = 0; i < nodes_num; i++) {
		Inst* e = 0;
		switch (static_cast<InstType> (Trans::read_int())) {
		case Sig:
			e = SigInst::read_bin();
			break;
		case Num:
			e = NumInst::read_bin();
			break;
		case Wire:
			e = WireInst::read_bin();
			break;
		case Const:
			e = ConstInst::read_bin();
			break;
		case Op:
			e = OpInst::read_bin();
			if (OpInst::as(e)) {
				if (OpInst::as(e)->get_op() == OpInst::Concat)
					numCc++;
				else if (OpInst::as(e)->get_euf_func_name() != "0")
				{
					numUF++;
//				cout << numUF << "  " << *e << endl;
//				if (e->fcLevel > 1)
//					cout << "(initial fl: " << e->fcLevel << "): " << *e << endl;
				}
//			cout << OpInst::as(e)->get_op() << "\t" << e->fcLevel << " (" << e->get_euf_func_name() << ") -> " << *e << endl;
			}
			break;
		case Ex:
			e = ExInst::read_bin();
			numEx++;
			break;
		case Mem:
			e = MemInst::read_bin();
			break;
		case UF:
			e = UFInst::read_bin();
			break;
		default:
			assert(0);
		}
		assert(e != 0);
		Trans::st_id_to_ptr.push_back(e);
	}

	_ve_init = Trans::id_to_ptr(Trans::read_int());
	_ve_model_nsf = Trans::id_to_ptr(Trans::read_int());
	_ve_model = Trans::id_to_ptr(Trans::read_int());
	_ve_assume = Trans::id_to_ptr(Trans::read_int());
	_ve_assume_orig = _ve_assume;

//  Inst::init_visit2();
//	_ve_init = add_missing_wires(_ve_init)->get_port();
//	_ve_model_nsf = add_missing_wires(_ve_model_nsf)->get_port();
//	_ve_model = add_missing_wires(_ve_model)->get_port();
//	_ve_assume = add_missing_wires(_ve_assume)->get_port();
	
//	cout << "I: " << *_ve_init << endl;
//	cout << "T: " << *_ve_model_nsf << endl;
//	cout << "P: " << *_ve_model << endl;
	fin.close();
	AVR_LOG(0, 1, "Deisgn WN is loaded from " << fname << endl);

//	for (SigInst::StrVM::iterator it = SigInst::hm_SigInst.begin(); it != SigInst::hm_SigInst.end(); it++)
//		cout << "Sig: " << *((*it).second) << endl;
//	for (NumInst::NumHashM::iterator it = NumInst::hm_NumInst.begin(); it != NumInst::hm_NumInst.end(); it++)
//		cout << "Num: " << *((*it).second) << endl;
//	for (OpInst::OpHashM::iterator it = ExInst::hm_ExInst.begin(); it != ExInst::hm_ExInst.end(); it++)
//		cout << "Ex: " << *((*it).second) << endl;
//	for (OpInst::OpHashM::iterator it = OpInst::hm_OpInst.begin(); it != OpInst::hm_OpInst.end(); it++)
//	{
//		if ((*it).second->get_euf_func_name() != "0")
//			cout << "Op: " << *((*it).second) << endl;
//	}
//	for (OpInst::OpHashMM::iterator it = OpInst::hm_ETCInst.begin(); it != OpInst::hm_ETCInst.end(); it++)
//	{
//		if ((*it).second->get_euf_func_name() != "0")
//			cout << "Op: " << *((*it).second) << endl;
//	}

#if 0	//read_wn()
 	AVR_LOG(0, 0, "_ve_init:" << endl);
 	new_print(cout, _ve_init, true);
	AVR_LOG(0, 0, "_ve_model_nsf:" << endl);
	new_print(cout, _ve_model_nsf, true);
 	AVR_LOG(0, 0, "_ve_model:" << endl);
 	new_print(cout, _ve_model, true);
 	AVR_LOG(0, 0, "_ve_model:" << endl << *_ve_model << endl);
	//assert(0);
//  	AVR_LOG(0, 0, "_ve_model:" << endl << *_ve_model << endl);
//  	AVR_LOG(0, 0, "_ve_model_nsf:" << endl << *_ve_model_nsf << endl);
#else
// 	AVR_LOG(0, 0, "_ve_init:" << endl << *_ve_init << endl);
// 	AVR_LOG(0, 0, "_ve_model_nsf:" << endl << *_ve_model_nsf << endl);
// 	AVR_LOG(0, 0, "_ve_model:" << endl << *_ve_model << endl);
#endif

	
// 	node_count(_ve_model, true);
// 	cout << "ve_model" << endl;
// 	cout << "int : " << _int_node_cnt << endl;
// 	cout << "bool : " << _bool_node_cnt << endl;
// 	cout << "sum : " << _node_cnt << endl;
//
// 	node_count(_ve_model_nsf, true);
// 	cout << "ve_model_nsf" << endl;
// 	cout << "int : " << _int_node_cnt << endl;
// 	cout << "bool : " << _bool_node_cnt << endl;
// 	cout << "sum : " << _node_cnt << endl;
//
// 	Inst *anded_models = OpInst::create(OpInst::LogAnd, _ve_model, _ve_model_nsf);
// 	node_count(anded_models, true);
// 	cout << "anded_models" << endl;
// 	cout << "int : " << _int_node_cnt << endl;
// 	cout << "bool : " << _bool_node_cnt << endl;
// 	cout << "sum : " << _node_cnt << endl;
//
//	assert(0);
}

//Solver* Reach::abst_solver() {
// 	if(!_euf_solver)	{
// 		_euf_solver = new SolverAPI(&_euf_mapper, 0);
// 	}
//	return _euf_solver;
//}

Solver* Reach::conc_solver() {
	return _last_allocated_solver;
}

void Reach::del_conc_solver() {
	if (_last_allocated_solver){
		delete static_cast<SOLVER_BV*>(_last_allocated_solver);
		_last_allocated_solver = NULL;
	}
}

Solver* Reach::new_conc_solver(bool is_inc, unsigned ba_idx, int type) {
	if (_last_allocated_solver){
		delete static_cast<SOLVER_BV*>(_last_allocated_solver);
		_last_allocated_solver = NULL;
	}
	_last_allocated_solver = new SOLVER_BV(_concrete_mapper, ba_idx, is_inc, type);
	return _last_allocated_solver;
}

bool Reach::retrieve_abst_cex() {
	return _config->get_arg(ALG_T_ARG) == CONFIG_AR;
}

bool Reach::abst_cex_is_top() {
	return _config->get_arg(ALG_T_ARG) == CONFIG_BB || _config->get_arg(ALG_T_ARG) == CONFIG_SMT;
}

Inst* node(unsigned id) {
	Inst* e = Inst::get_node(id);
	assert(e);
	return e;
}

void print(Inst* e, bool full = false) {
	if (full)
		cout << *e << endl;
	cout << e << endl;
	cout << "ID=" << e->get_id() << " SIZE=" << e->get_size() << endl;
	cout << "TYPE=" << e->get_type() << endl;
//	cout << "YICES=" << SolverAPI::get_yices_name(e) << endl;
	//gmp_printf("%Zd\n", e->cex_mpz);
	if (e->get_type() == Op) {
		OpInst* op = OpInst::as(e);
		OpInst::OpType t = op->get_op();
		cout << OpInst::op2str(t) << endl;
	}
	cout << "Children's IDs:" << endl;
	const InstL* ch = e->get_children();
	if (ch) {
		for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it)
			cout << (*it)->get_id() << " ";
	}
	cout << endl;
}

void print(unsigned id, bool full = false) {
	Inst* e = node(id);
	assert(e);
	print(e, full);
}

void Reach::uniqify_viol(InstL& viol) {
	InstS s;
	InstL newl;
	for (InstL::iterator it = viol.begin(), end_it = viol.end(); it != end_it; ++it) {
		if (s.find(*it) != s.end())
			continue;
		newl.push_back(*it);
		s.insert(*it);
	}
	viol = newl;
}

bool is_trivially_feasible(Inst* e) {
	Inst* me = e;
	if (me->get_type() == Op) {
		OpInst* op = OpInst::as(me);
		assert(op != 0);
		if (op->get_op() == OpInst::LogNot) {
			const InstL* ch = op->get_children();
			assert(ch != 0);
			assert(ch->size() == 1);
			me = *(ch->begin());
		}
	}
	if (me->get_type() == Sig && me->get_size() == 1)
		return true;
	if (me->get_type() == Op) {
		OpInst* op = OpInst::as(me);
		assert(op != 0);
		if (op->get_op() == OpInst::Eq) {
			const InstL* ch = op->get_children();
			assert(ch != 0);
			assert(ch->size() == 2);
			InstL::const_iterator cit = ch->begin(), cit2 = ch->begin();
			cit2++;

			// I am a constraint of the form A=false or A=true.
			if ((*cit)->get_size() == 1)
				return true;

			if ((*cit)->get_type() == Num && (*cit2)->get_type() == Num) {
				NumInst* num1 = NumInst::as(*cit);
				NumInst* num2 = NumInst::as(*cit2);
				assert(num1 != 0);
				assert(num2 != 0);

				// I am a constraint of the form A=A
				if ((me == e) && (num1->get_mpz() == num2->get_mpz())) {
					return true;
				}

				// I am a constraint of the form !(A=B)
				if ((me != e) && (num1->get_mpz() != num2->get_mpz())) {
					return true;
				}
			}
		}
	}
	return false;
}

void Reach::clean_viol(InstL& viol) {
	InstL trivials;
	InstL newl;
	for (InstL::iterator it = viol.begin(), end_it = viol.end(); it != end_it; ++it) {
		if (is_trivially_feasible(*it))
			trivials.push_back(*it);
		else
			newl.push_back(*it);
	}
	viol = newl;
	Inst* trivials_e = trivials.empty() ? 0 : (trivials.size() == 1) ? *(trivials.begin()) : OpInst::create(
			OpInst::LogAnd, trivials);
	if (trivials_e)
		viol.push_back(trivials_e);
}

int Reach::get_depth(string str) {
	size_t loc = str.find("$next");
	int next_length = str.length() - (int) loc;
	return next_length / 5;
}

// all_next2pre with error-check
// return NULL if the given formula contains present variables
Inst *Reach::all_next2pre_ec(Inst *e, bool init_visit) {
	Inst *res = e;
#if 0
	// this function is used in forward_propagation, and st_visit is already used in the function
	// Therefore, we should use init_visit2(), get_visit2(), set_visit2()

	if (init_visit) {
		Inst::init_visit();
		Inst::init_visit2();
	}
	if (e->get_visit()) {
		return e->acex_coi;
	}
	e->set_visit();
#else
	if (init_visit) {
		Inst::init_visit2();
	}
	if (e->get_visit2()) {
		return e->acex_coi;
	}
	e->set_visit2();
#endif
	const InstL* ch = e->get_children();
	if (ch) {
		bool changed = false;
		InstL newl;
		for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it) {
			if ((*it)->get_type() == Num) {
				newl.push_back(*it);
				continue;
			}
			SigInst* sig = SigInst::as(*it);
			Inst *tve;
			if (sig) {
				string t_str = sig->get_name();
// 				if (_m_sn.find(t_str) == _m_sn.end()) {
// 					string pre_name = t_str.substr(0, t_str.length() - 5) + "$pre";
// 					//					cout << "all_next2pre: " << t_str << " -> " << pre_name << endl;
// 					tve = SigInst::create(pre_name, sig->get_size());
// 				} else
				{
					if (_msv_all_next2pre_vars.find(t_str) != _msv_all_next2pre_vars.end()) {
						//cout << "^^^^^^^		" << t_str << endl;
						tve = _msv_all_next2pre_vars[t_str];
						assert(tve != sig);
// 						if(tve == sig){
// 							e->acex_coi = NULL;
// 							return NULL;
// 						}

						//cout << "tve: " << *tve << endl;
						//					cout << SigInst::as(tve)->get_name() << endl;
						//					e->replace_child(*it, _msv_all_next2pre_vars[t_str]);
					} else {
						e->acex_coi = NULL;
						return NULL;
					}
				}
			} else {
				tve = all_next2pre_ec(*it);
				if(tve == NULL){
					e->acex_coi = NULL;
					return NULL;
				}
			}
			newl.push_back(tve);
			if(tve != *it){
				changed = true;
			}
		}
		if (changed) {
// 			if (init_visit && (e->get_type() == Op) && ((OpInst::as(e))->get_op() == OpInst::LogAnd)) {
// 				// we should not disable the following line
// 				// set_contains() assumes that the children of a cube are sorted by their ids
// 				newl.sort(compare_inst);
// 			}
			res = e->apply_children(newl);
			if(res->ve_orig == NULL){
				if(e->ve_orig == NULL){
					res->ve_orig = e;
				}else{
					res->ve_orig = e->ve_orig;
				}
			}
		}
	} else {
		SigInst* sig = SigInst::as(e);
		if (sig) {
			string t_str = sig->get_name();
// 			if (_m_sn.find(t_str) == _m_sn.end()) {
// 				string pre_name = t_str.substr(0, t_str.length() - 5) + "$pre";
// 				//				cout << "all_next2pre: " << t_str << " -> " << pre_name << endl;
// 				res = SigInst::create(pre_name, sig->get_size());
// 			} else
			{
				if (_msv_all_next2pre_vars.find(t_str) != _msv_all_next2pre_vars.end()) {
										//cout << "2^^^^^^^		" << t_str << endl;
					res = _msv_all_next2pre_vars[t_str];
					assert(res != sig);
// 					if(res == sig){
// 						e->acex_coi = NULL;
// 						return NULL;
// 					}
					//cout << "res: " << *res << endl;
					//					cout << SigInst::as(res)->get_name() << endl;
					//					e->replace_child(*it, _msv_all_next2pre_vars[t_str]);
				}else{
					e->acex_coi = NULL;
					return NULL;
				}
			}
		}
	}
	e->acex_coi = res;
	return res;
}

#if 0
bool Reach::exist_str(Inst *top, string pattern, bool init_visit) {
	SigInst* sig = SigInst::as(top);
	if(sig) {
		string t_str = sig->get_name();
		if(t_str.find(pattern) != t_str.npos) {
			return true;
		}
	} else {
		const InstL* ch = top->get_children();
		if (ch) {
			for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it) {
				SigInst* sig = SigInst::as(*it);
				if(sig) {
					string t_str = sig->get_name();
					if(t_str.find(pattern) != t_str.npos) {
						return true;
					}
				} else {
					if(exist_str(*it, pattern) == true) {
						return true;
					}
				}
			}
		}
	}
	return false;
}
#else
bool Reach::exist_str(Inst *top, string pattern, bool init_visit) {
	if (init_visit) {
		Inst::init_visit();
		Inst::init_visit2();
	}
	if (top->get_visit()) {
		return false;// If it was true before, this function would not be called again
	}
	top->set_visit();

	SigInst* sig = SigInst::as(top);
	if (sig) {
		string t_str = sig->get_name();
		if (t_str.find(pattern) != t_str.npos) {
			return true;
		}
	} else {
		const InstL* ch = top->get_children();
		if (ch) {
			for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it) {
				if (exist_str(*it, pattern) == true) {
					return true;
				}
				// 				SigInst* sig = SigInst::as(*it);
				// 				if(sig){
				// 					string t_str = sig->get_name();
				// 					if(t_str.find(pattern) != t_str.npos){
				// 						return true;
				// 					}
				// 				} else {
				// 					if(exist_str(*it, pattern) == true){
				// 						return true;
				// 					}
				// 				}
			}
		}
	}
	return false;
}
#endif

void Reach::collect_nsfs(Inst *top, bool init_visit) {
	if (init_visit) {
		_collected_nsfs.clear();
		Inst::init_visit();
//		Inst::init_visit2();
	}
	if (top->get_visit()) {
		return;
	}
	top->set_visit();

	if((top->get_type() == Sig) && Inst::has_trelation(top)){
		_collected_nsfs.insert(Inst::fetch_trelation(top));
	}else{
		const InstL* ch = top->get_children();
		if (ch) {
			for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it) {
				collect_nsfs(*it);
			}
		}
	}
}

Inst *Reach::apply_const(Inst *e, InstToInstM& m_gref, InstS& useSet) {
	const InstL* ch = e->get_children();
	if (ch) {
		bool apply_new_ch = false;
		InstL newl;
		for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it) {
			Inst *tve = apply_const(*it, m_gref, useSet);
			newl.push_back(tve);
			if (tve != *it) {
				apply_new_ch = true;
			}
		}
		if (apply_new_ch) {
			Inst *res = e->apply_children(newl);
			if(res->ve_orig == NULL){
				if(e->ve_orig == NULL){
					res->ve_orig = e;
				}else{
					res->ve_orig = e->ve_orig;
				}
			}
			return res;
		}
	} else {
		SigInst* sig = SigInst::as(e);
		if (sig) {
			if (m_gref.find(sig) != m_gref.end()) {
				useSet.insert(sig);
				return m_gref[sig];
			}
		}
	}
	return e;
}

Inst *Reach::apply_const_with_wires(Inst *e, InstToInstM& m_gref, InstS& useSet) {

	if (e->get_type() == Sig || e->get_type() == Wire)
	{
		if (m_gref.find(e) != m_gref.end()) {
			useSet.insert(e);
			return m_gref[e];
		}
	}

	const InstL* ch = e->get_children();
	if (ch) {
		bool apply_new_ch = false;
		InstL newl;
		for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it) {
			Inst *tve = apply_const_with_wires(*it, m_gref, useSet);
			newl.push_back(tve);
			if (tve != *it) {
				apply_new_ch = true;
			}
		}
		if (apply_new_ch) {
			Inst *res = e->apply_children(newl);
			if(res->ve_orig == NULL){
				if(e->ve_orig == NULL){
					res->ve_orig = e;
				}else{
					res->ve_orig = e->ve_orig;
				}
			}
			return res;
		}
	}
	return e;
}

Inst *Reach::apply_const_gcube(Inst *e) {
	if (_m_gref.find(e) != _m_gref.end()) {
		return _m_gref[e];
	}

	const InstL* ch = e->get_children();
	if (ch) {
		bool apply_new_ch = false;
		InstL newl;
		for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it) {
			Inst *tve = apply_const_gcube(*it);
			newl.push_back(tve);
			if (tve != *it) {
				apply_new_ch = true;
			}
		}
		if (apply_new_ch) {
			Inst *res = e->apply_children(newl);
			InstToMpzM::iterator tit = _cube_partition->find(e);
			if(tit == _cube_partition->end()){
				AVR_LOG(6, 3, "e: " << *e << endl);
				AVR_LOG(6, 3, "res: " << *res << endl);
			}
			assert(tit != _cube_partition->end());
			(*_cube_partition)[res] = tit->second;

			if(res->ve_orig == NULL){
				if(e->ve_orig == NULL){
					res->ve_orig = e;
				}else{
					res->ve_orig = e->ve_orig;
				}
			}
			return res;
		}
	}
	return e;
}

void Reach::collect_consts(Inst *top, InstS &s_consts, bool init_visit) {
	if(init_visit){
		Inst::init_visit2();
	}
	if(top->get_visit2()){
		return;
	}
	top->set_visit2();

	const InstL* ch = top->get_children();
	if (ch) {
		for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it) {
			collect_consts(*it, s_consts, false);
		}
	}
	if(top->term_type == 0){
		s_consts.insert(top);
	}
}


Inst *Reach::propagate_const(Inst *e, InstToInstM& m_gref)
{
	Inst *new_ve = e;

	const InstL* ch = e->get_children();
	if (ch) {
		bool apply_new_ch = false;
		InstL newl;
		for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it)
		{
			Inst* tve = propagate_const(*it, m_gref);
			if (*it != tve)
			{
				apply_new_ch = true;
			}
			newl.push_back(tve);
		}
		if (apply_new_ch)
		{
			Inst *res = e->apply_children(newl);
			if(res->ve_orig == NULL){
				if(e->ve_orig == NULL){
					res->ve_orig = e;
				}else{
					res->ve_orig = e->ve_orig;
				}
			}
			new_ve = res;
		}
	}

	while(1)
	{
		InstToInstM::iterator mit = m_gref.find(new_ve);
		if(mit == m_gref.end()){
			break;
		}
		new_ve = mit->second;
//		AVR_LOG(4, 0, "new_ve: " << *new_ve << endl);
	}
	return new_ve;
}

// true if c_ref has been changed
Inst* Reach::propagate_internal_nodes(Inst* ref){
	AVR_LOG(4, 0, "> propagate_internal_nodes, before:" << *ref << endl);

	InstToInstM m_gref;

	collect_cubes(ref, true);
	for(InstL::iterator it = _collected_cubes.begin(); it != _collected_cubes.end(); it++){
		Inst *tve = *it;

		if((tve->get_type() == Op) && ((OpInst::as(tve))->get_op() == OpInst::Eq))
		{
			const InstL* ch = tve->get_children();
			InstL::const_iterator ch_it = ch->begin();
			Inst* lhs = *(ch_it++);
			Inst* rhs = *ch_it;

			if (is_gate_consistency(tve))
			{
				m_gref[lhs] = rhs;
//					cout << "debug1: " << s_l << " : " << *rhs << endl;
				continue;
			}
			else if((lhs->get_type() == Wire) && (rhs->get_type() == Wire))
			{
				m_gref[lhs] = rhs;
//					cout << "debug1: " << s_l << " : " << *rhs << endl;
				continue;
			}
			else if((lhs->get_type() == Sig) && (rhs->get_type() == Wire))
			{
				if (Inst::has_trelation(lhs))
				{
					m_gref[lhs] = rhs;
	//					cout << "debug1: " << s_l << " : " << *rhs << endl;
					continue;
				}
			}
		}else if((tve->get_type() == Op) && ((OpInst::as(tve))->get_op() == OpInst::LogNot)){
			const InstL* ch = tve->get_children();
			Inst* ve_child = ch->front();

			if(ve_child->get_type() == Sig){
				m_gref[ve_child] = NumInst::create(0, 1, SORT());
				continue;
			}
		}else if(tve->get_type() == Sig){
			m_gref[tve] = NumInst::create(1, 1, SORT());
			continue;
		}
	}

	if(m_gref.empty()){
		return ref;
	}

	cout << "Printing m_gref" << endl;
	for (InstToInstM::iterator it = m_gref.begin(); it != m_gref.end(); it++)
		cout << "m_gref[" << *(*it).first << "] = " << *(*it).second << endl;


	Inst* newRef = propagate_const(ref, m_gref);
	if (newRef == ref)
		return ref;
	else
	{
		return newRef;
	}

	AVR_LOG(4, 0, "propagate_internal_nodes, after:" << *newRef << endl);
	return newRef;
}

// true if c_ref has been changed
bool Reach::generalize_ref(InstL& c_ref){
	AVR_LOG(4, 5, "> generalize_ref, before:" << c_ref << endl);

	InstToInstM m_gref;

	InstL::iterator it;
	InstL tc_ref = c_ref;
	for(it = tc_ref.begin(); it != tc_ref.end();){
		Inst *tve = *it;

		if((tve->get_type() == Op) && ((OpInst::as(tve))->get_op() == OpInst::Eq)){
			const InstL* ch = tve->get_children();
			InstL::const_iterator ch_it = ch->begin();
			Inst* lhs = *(ch_it++);
			Inst* rhs = *ch_it;

			if(lhs->get_type() == Sig){
				if(!rhs->childrenInfo[SIG]){
//				if(rhs->get_type() == Num){
					m_gref[lhs] = rhs;
//					cout << "debug1: " << s_l << " : " << *rhs << endl;
					it = tc_ref.erase(it);
					continue;
				}
			}
		}else if((tve->get_type() == Op) && ((OpInst::as(tve))->get_op() == OpInst::LogNot)){
			const InstL* ch = tve->get_children();
			Inst* ve_child = ch->front();

			if(ve_child->get_type() == Sig){
				m_gref[ve_child] = NumInst::create(0, 1, SORT());
				it = tc_ref.erase(it);
				continue;
			}
		}else if(tve->get_type() == Sig){
			m_gref[tve] = NumInst::create(1, 1, SORT());
			it = tc_ref.erase(it);
			continue;
		}
		it++;
	}

	if(m_gref.empty()){
		return false;
	}

	for(it = tc_ref.begin(); it != tc_ref.end();){
		Inst *tve = *it;
		if((tve->get_type() == Op) && ((OpInst::as(tve))->get_op() == OpInst::Eq)){
			const InstL* ch = tve->get_children();
			InstL::const_iterator ch_it = ch->begin();
			Inst* lhs = *(ch_it++);
			Inst* rhs = *ch_it;
			if((lhs->get_type() == Sig) && (rhs->get_type() == Sig)){
				auto v_l = m_gref.find(lhs);
				auto v_r = m_gref.find(rhs);
				bool b_l = (v_l != m_gref.end());
				bool b_r = (v_r != m_gref.end());
				if(b_l && !b_r){
					m_gref[rhs] = (*v_l).second;
				}
				else if(!b_l && b_r){
					m_gref[lhs] = (*v_r).second;
				}
				else if(!b_l && !b_r){
					m_gref[lhs] = rhs;
				}
				else
				{
					if ((*v_l).second != (*v_r).second)
						m_gref[(*v_l).second] = (*v_r).second;
				}
				it = tc_ref.erase(it);
			}
			else{
				it++;
			}
		}
		else{
			it++;
		}
	}

//	cout << "Printing m_gref" << endl;
//	for (InstToInstM::iterator it = m_gref.begin(); it != m_gref.end(); it++)
//		cout << "m_gref[" << *(*it).first << "] = " << *(*it).second << endl;


	bool ret = false;
	c_ref.clear();
	InstS useSet;
	if(!tc_ref.empty()){
		for(it = tc_ref.begin(); it != tc_ref.end(); it++){
			Inst *tve = apply_const(*it, m_gref, useSet);
			if(tve != *it){
				ret = true;
			}
			c_ref.push_back(tve);
		}
	}

	for (auto& m : m_gref)
	{
		Inst* lhs = m.first;
		if (useSet.find(lhs) == useSet.end())
			c_ref.push_back(OpInst::create(OpInst::Eq, lhs, m.second));
	}

	AVR_LOG(4, 5, "generalize_ref, after:" << c_ref << endl);
	return ret;
}

// true if c_ref has been changed
bool Reach::generalize_ref_with_wires(InstL& c_ref){
	AVR_LOG(4, 1, "> generalize_ref with wires, before:" << c_ref << endl);

	InstToInstM m_gref;

	InstL::iterator it;
	InstL tc_ref = c_ref;
	for(it = tc_ref.begin(); it != tc_ref.end();){
		Inst *tve = *it;

		if((tve->get_type() == Op) && ((OpInst::as(tve))->get_op() == OpInst::Eq)){
			const InstL* ch = tve->get_children();
			InstL::const_iterator ch_it = ch->begin();
			Inst* lhs = *(ch_it++);
			Inst* rhs = *ch_it;

//			if(lhs->get_type() == Sig){
//				if(!rhs->childrenInfo[SIG]){
////				if(rhs->get_type() == Num){
//					m_gref[lhs] = rhs;
////					cout << "debug1: " << s_l << " : " << *rhs << endl;
//					it = tc_ref.erase(it);
//					continue;
//				}
//			}

			if(lhs->get_type() == Wire){
				if(rhs->get_type() == Wire || !rhs->childrenInfo[SIG]){
					m_gref[lhs] = rhs;
//					cout << "debug1: " << s_l << " : " << *rhs << endl;
					it = tc_ref.erase(it);
					continue;
				}
				else
				{
					WireInst* lw = WireInst::as(lhs);
					assert(lw);
					if(lw->get_port() == rhs){
						m_gref[lhs] = rhs;
	//					cout << "debug1: " << s_l << " : " << *rhs << endl;
						it = tc_ref.erase(it);
						continue;
					}
				}
			}
		}else if((tve->get_type() == Op) && ((OpInst::as(tve))->get_op() == OpInst::LogNot)){
			const InstL* ch = tve->get_children();
			Inst* ve_child = ch->front();

//			if(ve_child->get_type() == Sig || ve_child->get_type() == Wire){
			if(ve_child->get_type() == Wire){
				m_gref[ve_child] = NumInst::create(0, 1, SORT());
				it = tc_ref.erase(it);
				continue;
			}
		}
//		else if(tve->get_type() == Sig || tve->get_type() == Wire){
		else if(tve->get_type() == Wire){
			m_gref[tve] = NumInst::create(1, 1, SORT());
			it = tc_ref.erase(it);
			continue;
		}
		it++;
	}

	if(m_gref.empty()){
		return false;
	}

//	for(it = tc_ref.begin(); it != tc_ref.end();){
//		Inst *tve = *it;
//		if((tve->get_type() == Op) && ((OpInst::as(tve))->get_op() == OpInst::Eq)){
//			const InstL* ch = tve->get_children();
//			InstL::const_iterator ch_it = ch->begin();
//			Inst* lhs = *(ch_it++);
//			Inst* rhs = *ch_it;
//			if((lhs->get_type() == Sig) && (rhs->get_type() == Sig)){
//				auto v_l = m_gref.find(lhs);
//				auto v_r = m_gref.find(rhs);
//				bool b_l = (v_l != m_gref.end());
//				bool b_r = (v_r != m_gref.end());
//				if(b_l && !b_r){
//					m_gref[rhs] = (*v_l).second;
//				}
//				else if(!b_l && b_r){
//					m_gref[lhs] = (*v_r).second;
//				}
//				else if(!b_l && !b_r){
//					m_gref[lhs] = rhs;
//				}
//				else
//				{
//					if ((*v_l).second != (*v_r).second)
//						m_gref[(*v_l).second] = (*v_r).second;
//				}
//				it = tc_ref.erase(it);
//			}
//			else{
//				it++;
//			}
//		}
//		else{
//			it++;
//		}
//	}

//	cout << "Printing m_gref" << endl;
//	for (InstToInstM::iterator it = m_gref.begin(); it != m_gref.end(); it++)
//		cout << "m_gref[" << *(*it).first << "] = " << *(*it).second << endl;


	bool ret = false;
	c_ref.clear();
	InstS useSet;
	if(!tc_ref.empty()){
		for(it = tc_ref.begin(); it != tc_ref.end(); it++)
		{
			Inst* tve = (*it);
			if (!is_gate_consistency(tve))
				tve = apply_const_with_wires(*it, m_gref, useSet);
			if(tve != *it){
				ret = true;
			}
			c_ref.push_back(tve);
		}
	}

	for (auto& m : m_gref)
	{
		Inst* lhs = m.first;
		if (useSet.find(lhs) == useSet.end())
			c_ref.push_back(OpInst::create(OpInst::Eq, lhs, m.second));
	}

	AVR_LOG(4, 1, "generalize_ref with wires, after:" << c_ref << endl);
	return ret;
}

// true if c_ref has been changed
bool Reach::generalize_gcube(Inst *&gcube){
	//	How about std::InstToInstM m_gref;
	_m_gref.clear();
	InstL::iterator it;
	InstL tc_ref;
	Inst::check_term_type(gcube);
	const InstL* ch = gcube->get_children();
	if(ch){
		tc_ref = *ch;
	}
	for(it = tc_ref.begin(); it != tc_ref.end();){
		Inst *tve = *it;

		if((tve->get_type() == Op) && ((OpInst::as(tve))->get_op() == OpInst::Eq)){
			const InstL* ch = tve->get_children();
			InstL::const_iterator ch_it = ch->begin();
			Inst* lhs = *(ch_it++);
			Inst* rhs = *ch_it;

			if(lhs->term_type == 2){
				if(rhs->get_type() == Num || (rhs->term_type == 0)){
					_m_gref[lhs] = rhs;
					it = tc_ref.erase(it);
					continue;
				}
			}
// 		}else if((tve->get_type() == Op) && ((OpInst::as(tve))->get_op() == OpInst::LogNot)){
// 			const InstL* ch = tve->get_children();
// 			Inst* ve_child = ch->front();
//
// 			if((ve_child->get_type() != Op) || (((OpInst::as(ve_child))->get_op() != OpInst::Eq) && ((OpInst::as(ve_child))->get_op() != OpInst::NotEq))){
// 				if((ve_child->get_size() == 1) && (ve_child->term_type == 2)){
// 					_m_gref[ve_child] = NumInst::create(0, 1);
// 					it = tc_ref.erase(it);
// 					continue;
// 				}
// 			}
// 		}else if((tve->get_size() == 1) && (tve->term_type == 2)){
// 			if((tve->get_type() != Op) || (((OpInst::as(tve))->get_op() != OpInst::Eq) && ((OpInst::as(tve))->get_op() != OpInst::NotEq))){
// 				_m_gref[tve] = NumInst::create(1, 1);
// 				it = tc_ref.erase(it);
// 				continue;
// 			}
// 		}
		}else if((tve->get_type() == Op) && ((OpInst::as(tve))->get_op() == OpInst::LogNot)){
			const InstL* ch = tve->get_children();
			Inst* ve_child = ch->front();

			if((ve_child->get_type() == Sig) && (ve_child->term_type == 2)){
				_m_gref[ve_child] = NumInst::create(0, 1, SORT());
				it = tc_ref.erase(it);
				continue;
			}
		}else if((tve->get_type() == Sig) && (tve->term_type == 2)){
			_m_gref[tve] = NumInst::create(1, 1, SORT());
			it = tc_ref.erase(it);
			continue;
		}
		it++;
	}
	if(_m_gref.empty()){
		return false;
	}

// 	InstToInstM::iterator mg_it = _m_gref.begin();
// 	for(;mg_it != _m_gref.end(); ++mg_it){
// 		cout << "mg_it->first: " << *(mg_it->first) << endl;
// 		cout << "mg_it->second: " << *(mg_it->second) << endl;
// 	}

	for(it = tc_ref.begin(); it != tc_ref.end();){
		Inst *tve = *it;
		if((tve->get_type() == Op) && ((OpInst::as(tve))->get_op() == OpInst::Eq)){
			const InstL* ch = tve->get_children();
			InstL::const_iterator ch_it = ch->begin();
			Inst* lhs = *(ch_it++);
			Inst* rhs = *ch_it;
			if((lhs->get_type() == Sig) && (rhs->get_type() == Sig) && (Inst::_s_reg.find(lhs) == Inst::_s_reg.end()) && (Inst::_s_reg.find(rhs) == Inst::_s_reg.end())){
				bool b_l = (_m_gref.find(lhs) != _m_gref.end());
				bool b_r = (_m_gref.find(rhs) != _m_gref.end());
				if(b_l && !b_r){//TODO there are more complicated cases
					_m_gref[rhs] = _m_gref[lhs];
					it = tc_ref.erase(it);
				}else if(!b_l && b_r){
					_m_gref[lhs] = _m_gref[rhs];
					it = tc_ref.erase(it);
				}else{
					_m_gref[lhs] = rhs;
					it = tc_ref.erase(it);
					//it++;
				}
			}else{
				it++;
			}
		}else{
			it++;
		}
	}

	bool ret = false;
	if(!tc_ref.empty()){
		InstL c_ref;
		for(it = tc_ref.begin(); it != tc_ref.end(); it++){

// 			InstToMpz::iterator tit = _cube_partition->find(*it);
// 			if(tit == _cube_partition->end()){
// 				cout << "(*it): " << *(*it) << endl;
// 				assert(0);
// 			}else{
// 				cout << "(*it): " << *(*it) << endl;
// 				cout << "tit->second: " << tit->second << endl;
// 			}


			Inst *tve = apply_const_gcube(*it);

// 			cout << "(*it): " << *(*it) << endl;
// 			cout << "(tve): " << *tve << endl;

			if(tve != *it){
				ret = true;
			}
			c_ref.push_back(tve);
		}
		gcube = OpInst::create(OpInst::LogAnd, c_ref);
	}

//  	AVR_LOG(4, 0, "> generalize_gcube, before:" << *ve_orig << endl);
//  	AVR_LOG(4, 0, "generalize_gcube, after:" << *gcube << endl);
	return ret;
}

// TODO update modified frames
bool Reach::update_inc_solvers(int idx, Inst *ve) {
	struct rusage usage;
	struct timeval start_time, end_time;
	long long time_diff;

	TIME_S(start_time);

	Inst *ve_not = OpInst::create(OpInst::LogNot, ve);

	for (int i = 1; i <= idx; i++) {
//		cout << "asserting clause to F" << i << "\t" << *ve_not << endl;
		if (_reach_solvers[i].solver_main) {
			_reach_solvers[i].solver_main->s_assert(ve_not);
		}
#ifdef FRAME_SOLVER_MULTI
		if (_reach_solvers[i].solver1) {
			_reach_solvers[i].solver1->s_assert(ve_not);
//				if (find(_negated_cubes[i].begin(), _negated_cubes[i].end(), ve_not) == _negated_cubes[i].end())
//				{
//					cout << "containment idx: " << _containment_update_idx << endl;
//					cout << "F[" << i << "]" << endl;
//					cout << _negated_cubes[i] << endl;
//					assert(0);
//				}
		}
#endif
	}
	if(idx >= _frame_idx)
	{
//    if (find(_negated_cubes[idx].begin(), _negated_cubes[idx].end(), ve_not) == _negated_cubes[idx].end())
//    {
//      cout << "containment idx: " << _containment_update_idx << endl;
//      cout << "F[" << _frame_idx << "]" << endl;
//      cout << _negated_cubes[_frame_idx] << endl;
//      cout << "F[" << idx << "]" << endl;
//      cout << _negated_cubes[idx] << endl;
//      assert(0);
//    }

	  if (_cti_solver)
			_cti_solver->s_assert(ve_not);
	}
	TIME_E(start_time, end_time, _tb_updateincsolver_time);

	return true;
}

#ifdef AVR_DUMP_ACCUM_REFF
ofstream accum_reff;
#endif

// static InstToSetM m_pars;
// // TODO return ve_out, bit-blasted version of ve_in ?
// void collect_parents(Inst *ve_top, bool init_visit) {
// 	if(init_visit){
// 		m_pars.clear();
// 		Inst::init_visit2();
// 	}
// 	if(ve_top->get_visit2()){
// 		return;
// 	}
// 	ve_top->set_visit2();
//
// 	const InstL* chs = ve_top->get_children();
//
// 	if(chs){
// 		InstL::const_iterator it = chs->begin();
// 		for (InstL::const_iterator end_it = chs->end(); it != end_it; ++it) {
// 			Inst *ch = *it;
// 			if(m_pars[ch].find(ve_top) == m_pars[ch].end()){
// 				m_pars[ch].insert(ve_top);
// 			}
// 			collect_parents(ch, false);
// 		}
// 	}
// }
//

Inst *Reach::find_original_node(Inst *top, Inst *target_node, bool init_visit) {
	if(init_visit){
		Inst::init_visit2();
	}
	if(top->get_visit2()){
		return NULL;
	}
	top->set_visit2();

	const InstL* chs = top->get_children();

	if(chs){
		InstL::const_iterator it = chs->begin();
		for (InstL::const_iterator end_it = chs->end(); it != end_it; ++it) {
			Inst *ch = *it;
			if(ch->acex_coi == target_node){
				return ch->acex_coi;
			}
			Inst *ret = find_original_node(ch, target_node, false);
			if(ret != NULL){
				return ret;
			}
		}
	}
	return NULL;
}

void Reach::substitute_nodes(Inst *top, Inst *ve_old, Inst *ve_new, bool init_visit) {
	if(init_visit){
		Inst::init_visit2();
	}
	if(top->get_visit2()){
		return;
	}
	top->set_visit2();

	top->acex_coi = top;
	const InstL* chs = top->get_children();
	bool apply_new_ch = false;
	if(chs){
		InstL::const_iterator it = chs->begin();
		InstL newl;
		for (InstL::const_iterator end_it = chs->end(); it != end_it; ++it) {
			Inst *ch = *it;
			if(ch == ve_old){
// 				cout << "33333333333333" << endl;
				newl.push_back(ve_new);
				apply_new_ch = true;
			}else{
				substitute_nodes(ch, ve_old, ve_new, false);
				Inst *tve = ch->acex_coi;
				newl.push_back(tve);
				if(tve != ch){
					apply_new_ch = true;
				}
			}
		}
		if(apply_new_ch == true){
			top->acex_coi = top->apply_children(newl);
			if(top->acex_coi->ve_orig == NULL){
				if(top->ve_orig == NULL){
					top->acex_coi->ve_orig = top;
				}else{
					top->acex_coi->ve_orig = top->ve_orig;
				}
			}

// 			cout << "### top: " << *top << endl;
// 			cout << "### top->acex_coi: " << *top->acex_coi << endl;
		}
	}
}

// collect nodes (in m_nodes) with more than one parent
void Reach::collect_common_nodes(Inst *top, map<int, Inst*> &m_nodes, int depth, bool init_visit){
	top->inc_count();

	if(top->get_count() > 1){
		m_nodes[depth] = top;
	}

	if(init_visit){
		Inst::init_visit2();
	}
	if(top->get_visit2()){
		return;
	}
	top->set_visit2();

	const InstL* chs = top->get_children();

	if(chs){
		InstL::const_iterator it = chs->begin();
		for (InstL::const_iterator end_it = chs->end(); it != end_it; ++it) {
			Inst *ch = *it;
			collect_common_nodes(ch, m_nodes, depth+1, false);
		}
	}
}

// long long Reach::Timevaldiff(struct timeval *starttime, struct timeval *finishtime)
// {
//   long long msec;
//   msec=(finishtime->tv_sec-starttime->tv_sec)*1000000;
//   msec+=(finishtime->tv_usec-starttime->tv_usec);
//   return msec;
// }

Inst *Reach::frame_down(Inst *e) {
	const InstL* ch = e->get_children();
	if (ch) {
		bool apply_new_ch = false;
		InstL newl;
		for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it) {
			Inst *tve = frame_down(*it);
			newl.push_back(tve);
			if (tve != *it) {
				apply_new_ch = true;
			}
		}
		if (apply_new_ch) {
			Inst *res = e->apply_children(newl);
			if(res->ve_orig == NULL){
				if(e->ve_orig == NULL){
					res->ve_orig = e;
				}else{
					res->ve_orig = e->ve_orig;
				}
			}
			return res;
		}
	} else {
		if (Inst::has_trelation(e)) {
			return Inst::_m_sn[e].first;
		}
// 		SigInst* sig = SigInst::as(e);
// 		if (sig) {
// 			string s_str = sig->get_name();
// 			if (_m_sn.find(s_str) != _m_sn.end()) {
// 				return _m_sn[s_str];
// 			}
// 			// see exist_input
// 			// 			else if(_s_vars.find(s_str) == _s_vars.end()){
// 			// 				//means it's an input signal
// 			// 				if(e->get_size() == 1){
// 			//  					Inst *tve = NumInst::create(e->acex_val, 1);
// 			//  					return tve;
// 			// 				}
// 			// 			}
// 		}
	}
	return e;
}

void Reach::collect_cubes(Inst *top, bool init_visit) {
	if (init_visit) {
		//		Inst::init_visit();
		_collected_cubes.clear();
	}
	// 	if (top->get_visit()) {
	// 		return;
	// 	}
	// 	top->set_visit();
	OpInst* op = OpInst::as(top);
	if (op && (op->get_op() == OpInst::LogAnd)) {
		const InstL* ch = top->get_children();
		for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it) {
			Inst * tve = *it;
			OpInst* op2 = OpInst::as(tve);
			if (op2 && (op2->get_op() == OpInst::LogAnd)) {
				collect_cubes(tve);
			} else {
#ifdef AVR_SKIP_PROP_IN_VIOL
				if(exist_str(tve, _config->get_arg(PROP_SIG_ARG), true)) {
					// //					cout << "WRN_skipped: " << *tve<< endl;
				}
				else
#endif
				// 					if(exist_str(tve, "next")){
				// 					_collected_cubes.push_back(tve);
				// 				}
				// 				else
				{
					_collected_cubes.push_back(tve);
				}
			}
		}
	} else {
		Inst * tve = top;
#ifdef AVR_SKIP_PROP_IN_VIOL
		if(exist_str(tve, _config->get_arg(PROP_SIG_ARG), true)) {
			// //			cout << "WRN_skipped: " << *tve<< endl;
		}
		else
#endif
		// 			if(exist_str(tve, "next")){
		// 			_collected_cubes.push_back(tve);
		// 		}
		// 		else
		{
			_collected_cubes.push_back(tve);
		}
	}
	return;
}

void Reach::collect_all_cubes(Inst *top, bool init_visit) {
	if (init_visit) {
		_collected_cubes.clear();
	}

	top = top->get_port();

	OpInst* op = OpInst::as(top);
	if (op && (op->get_op() == OpInst::LogAnd)) {
		const InstL* ch = top->get_children();
		for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it) {
			Inst * tve = (*it)->get_port();

			OpInst* op2 = OpInst::as(tve);
			if (op2 && (op2->get_op() == OpInst::LogAnd)) {
				collect_all_cubes(tve);
			} else {
        _collected_cubes.push_back(tve);
			}
		}
	} else {
		Inst * tve = top;
    _collected_cubes.push_back(tve);
	}
	return;
}

void Reach::collect_nsfs(Inst *top, InstL &vel_nsfs, bool init_visit) {
	if (init_visit) {
		vel_nsfs.clear();
	}
	OpInst* op = OpInst::as(top);
	if (op && (op->get_op() == OpInst::LogAnd)) {
		const InstL* ch = top->get_children();
		for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it) {
			Inst * tve = *it;
			OpInst* op2 = OpInst::as(tve);
			if (op2 && (op2->get_op() == OpInst::LogAnd)) {
				collect_nsfs(tve, vel_nsfs);
			} else {
				vel_nsfs.push_back(tve);
			}
		}
	} else {
		Inst * tve = top;
		vel_nsfs.push_back(tve);
	}
	return;
}

// collect "present" wide state variables
// Note, we are not checking "next" state variables
void Reach::collect_wide_regs(Inst *top, map<int, InstS> &m_regs, bool init_visit) {
	if (init_visit) {
		Inst::init_visit();
	}
	if (top->get_visit()) {
		return;
	}
	top->set_visit();

	// we treat {q3, q2, q1, q0} as states
// 	if((top->get_type() == Op) && (OpInst::as(top)->get_op() == OpInst::Concat)){
// 		const InstL* ch = top->get_children();
// 		if (ch) {
// 			bool pattern_found = true;
// 			for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it) {
// 				if (_s_reg.find(*it) == _s_reg.end()) {
// 					pattern_found = false;
// 					break;
// 				}
// 			}
// 			if(pattern_found == true){
// 				int size = top->get_size();
// 				if(size > 1){
// 					m_regs[top->get_size()].insert(top);
// 				}
// 			}
// 			return;
// 		}
// 	}

	if (Inst::_s_reg.find(top) != Inst::_s_reg.end()) {
		int size = top->get_size();
		if(size > 1){
			m_regs[top->get_size()].insert(top);
		}
	}else {
		const InstL* ch = top->get_children();
		if (ch) {
			for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it) {
				collect_wide_regs(*it, m_regs);
			}
		}
	}
}

void Reach::collect_regs2(Inst *top, set<string> &s_reg_names, bool init_visit) {
	if (init_visit) {
		Inst::init_visit();
	}
	if (top->get_visit()) {
		return;
	}
	top->set_visit();

	SigInst *sve = SigInst::as(top);
//	if((top->get_size() > 1) && sve){	// we are considering to bit-blast the NSF of a single-bit FF
	if(sve){
		string reg_name = sve->get_name();
		map<std::string, Inst*>::iterator hm_it = SigInst::hm_SigInst.find(reg_name+"$next");
		if(hm_it != SigInst::hm_SigInst.end()){
			s_reg_names.insert(reg_name);
		}
	}else{
		const InstL* ch = top->get_children();
		if (ch) {
			for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it) {
				collect_regs2(*it, s_reg_names);
			}
		}
	}
}

Inst *Reach::rename_inputs(Inst *e, bool init_visit) {
	//	return e;
	Inst *res = e;
	static int postfix = 0;
	if (init_visit) {
		Inst::init_visit();
		postfix++;
	}
	if (e->get_visit()) {
		return e->acex_coi;
	}
	e->set_visit();

	SigInst* sig = SigInst::as(e);
	if (sig) {
		if (Inst::_s_reg.find(sig) == Inst::_s_reg.end()) {
			string str = sig->get_name();
			size_t loc = str.find("$");
			ostringstream oss;
			if (loc != str.npos) {
				oss << str.substr(0, loc + 1) << postfix;
			} else {
				oss << str << "$" << postfix;
			}
			res = SigInst::create(oss.str(), sig->get_size(), sig->get_sort());
		}
	} else {
		const InstL* ch = e->get_children();
		if (ch) {
			bool changed = false;
			InstL newl;
			for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it) {
				Inst *tve = rename_inputs(*it);
				if (tve != *it) {
					changed = true;
				}
				newl.push_back(tve);
			}
			if (changed) {
				res = e->apply_children(newl);
				if(res->ve_orig == NULL){
					if(e->ve_orig == NULL){
						res->ve_orig = e;
					}else{
						res->ve_orig = e->ve_orig;
					}
				}
			}
		}
	}

	e->acex_coi = res;
	return res;
}

Inst *Reach::rename_inputs_2(Inst *e, bool init_visit) {
	Inst *res = e;
	static int postfix = 0;
	postfix++;
	if (init_visit) {
		Inst::init_visit();
	}
	if (e->get_visit()) {
		return e->acex_coi;
	}
	e->set_visit();

	SigInst* sig = SigInst::as(e);
	if (sig) {
		if (Inst::_s_reg.find(sig) == Inst::_s_reg.end()) {
			string str = sig->get_name();
			ostringstream oss;
			oss << str.substr(0, str.length() - 4) << postfix;
			res = SigInst::create(oss.str(), sig->get_size(), sig->get_sort());
		}
	} else {
		const InstL* ch = e->get_children();
		if (ch) {
			bool changed = false;
			InstL newl;
			for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it) {
				Inst *tve = rename_inputs_2(*it);
				if (tve != *it) {
					changed = true;
				}
				newl.push_back(tve);
			}
			if (changed) {
				res = e->apply_children(newl);
				if(res->ve_orig == NULL){
					if(e->ve_orig == NULL){
						res->ve_orig = e;
					}else{
						res->ve_orig = e->ve_orig;
					}
				}
			}
		}
	}

	e->acex_coi = res;
	return res;
}

void Reach::get_func_applications(map<string, InstL>& func_list, Inst *top, bool init_visit)
{
	if (init_visit) {
		Inst::init_visit();
	}
	if (top->get_visit()) {
		return;
	}
	top->set_visit();

	OpInst *op_inst = OpInst::as(top);
	if(op_inst){
		string euf_func_name;
		ExInst *ex_inst = ExInst::as(top);
		if(ex_inst){
			euf_func_name = ex_inst->get_euf_func_name();
		}else{
			euf_func_name = op_inst->get_euf_func_name();
		}
		if(euf_func_name != "0")
		{
			bool matched = false;
			for(InstL::iterator lit = func_list[euf_func_name].begin(); lit != func_list[euf_func_name].end(); ++lit)
			{
				if(top == *lit)
				{
					matched = true;
					break;
				}
			}
			if(matched == false)
			{
				func_list[euf_func_name].push_back(top);
			}
		}
	}

	const InstL* tch = top->get_children();
	if (tch)
	{
		for (InstL::const_iterator tit = tch->begin(); tit != tch->end(); ++tit)
			get_func_applications(func_list, *tit, false);
	}
}

bool Reach::derive_euf_func_list(map<string, InstL>& func_list, Inst *top, bool init_visit) {
	if (init_visit) {
		Inst::init_visit();
	}
	if (top->get_visit()) {
		// if already visited, the return value of the initial call of derive_euf_func_list
		// does not depend on this return value.
		return 0;
	}
	bool ret = false;
	top->set_visit();

	OpInst *op_inst = OpInst::as(top);
	if(op_inst){
		string euf_func_name;
		ExInst *ex_inst = ExInst::as(top);
		if(ex_inst){
			euf_func_name = ex_inst->get_euf_func_name();
		}else{
			euf_func_name = op_inst->get_euf_func_name();
		}
		if(euf_func_name != "0"){
			if((top->is_invalid_state_term == 0) || (top->is_invalid_state_term == Inst::not_yet_computed))
			{
				// top->is_invalid_state_term == Inst::not_yet_computed if derive_euf_func_list() was called
				// at the beginning to fill "_func_list"
				bool matched = false;
				for(InstL::iterator lit = func_list[euf_func_name].begin(); lit != func_list[euf_func_name].end(); ++lit){
					if(top == *lit){
						matched = true;
						break;
					}
				}
				if(matched == false){
					func_list[euf_func_name].push_back(top);
					ret = true;
				}
			}
		}
	}

	const InstL* tch = top->get_children();
	if (tch) {
		for (InstL::const_iterator tit = tch->begin(); tit != tch->end(); ++tit) {
			bool t_ret = derive_euf_func_list(func_list, *tit, false);
			ret = ret | t_ret;
		}
	}
	return ret;
}

bool Reach::derive_euf_func_list_2(Inst *top, bool init_visit) {
	if (init_visit) {
		Inst::init_visit();
	}
	if (top->get_visit()) {
		// if already visited, the return value of the initial call of derive_euf_func_list_debug
		// does not depend on this return value.
		return 0;
	}
	bool ret = false;
	top->set_visit();

	OpInst *op_inst = OpInst::as(top);
	if(op_inst){
		string euf_func_name;
		ExInst *ex_inst = ExInst::as(top);
		if(ex_inst){
			euf_func_name = ex_inst->get_euf_func_name();
		}else{
			euf_func_name = op_inst->get_euf_func_name();
		}
		if(euf_func_name != "0"){
			if((Inst::check_term_type(top) & 2) != 2){	// if top is not an input
			//if((top->is_invalid_state_term == 0) || (top->is_invalid_state_term == Inst::not_yet_computed)){
				// top->is_invalid_state_term == Inst::not_yet_computed if derive_euf_func_list_debug() was called
				// at the beginning to fill "_func_list"
				bool matched = false;
				for(InstL::iterator lit = _func_list[euf_func_name].begin(); lit != _func_list[euf_func_name].end(); ++lit){
					if(top == *lit){
						matched = true;
						break;
					}
				}
				if(matched == false){
					_func_list[euf_func_name].push_back(top);
//					cout << "(added: " << *top << ")" << endl;
					ret = true;
				}
			}
		}
	}

	const InstL* tch = top->get_children();
	if (tch) {
		for (InstL::const_iterator tit = tch->begin(); tit != tch->end(); ++tit) {
			bool t_ret = derive_euf_func_list_2(*tit, false);
			ret = ret | t_ret;
		}
	}
	return ret;
}

#ifdef ABSTRACTION_COURSE
/// Returns max distance of an entry added to ufDistance
/// Note- top should be an expression in only present state. No $next allowed.
int Reach::compute_uf_distances(Inst* e, unsigned currDistance, InstToIntM& ufDistance, bool init_visit)
{
	int maxDistance = 1;
//	InstS sigsDone;
	deque < pair< Inst*, int > > q;
	q.push_back(make_pair(e, 1));

	Inst::init_visit();
	while (!q.empty())
	{
		bool ret = false;
		Inst* top = q.front().first;
		int currDistance = q.front().second;
		q.pop_front();
		top->set_visit();

//		AVR_LOG(15, 0, "top: " << *top << endl);

		SigInst* sig = SigInst::as(top);
		if (sig)
		{
//			InstS::iterator sit = sigsDone.find(sig);
//			if (sit == sigsDone.end())
			{
				string sigNextName = sig->get_name() + "$next";
				Inst* sigNext = SigInst::create(sigNextName, sig->get_size());
				assert(sigNext);
				InstToInstM::iterator mit = Inst::_m_sn.find(sigNext);
				if (mit != Inst::_m_sn.end())
				{
					if ((*mit).second->get_visit())
					{
					}
					else
						q.push_back(make_pair((*mit).second, (currDistance + 1)));
				}
//				sigsDone.insert(sig);
			}
		}
		else
		{
			if (top->get_type() == Op)
			{
				OpInst* op = OpInst::as(top);
				if (op->get_op() != OpInst::Concat)
				{
					string euf_func_name;
					euf_func_name = op->get_euf_func_name();
					if(euf_func_name != "0")
					{
						InstToIntM::iterator mit = ufDistance.find(top);
						if (mit != ufDistance.end())
						{
							if ((*mit).second > currDistance)
							{
								ufDistance[top] = currDistance;
//								AVR_LOG(15, 0, "\t(distance of UF (updated): " << *top << " @ " << currDistance << ")" << endl);
								if (maxDistance < currDistance)
									maxDistance = currDistance;
							}
						}
						else
						{
							ufDistance[top] = currDistance;
//							AVR_LOG(15, 0, "\t(distance of UF: " << *top << " @ " << currDistance << ")" << endl);
							if (maxDistance < currDistance)
								maxDistance = currDistance;
						}
					}
				}
			}
		}

		const InstL* tch = top->get_children();
		if (tch)
		{
			for (InstL::const_iterator tit = tch->begin(); tit != tch->end(); ++tit)
			{
				if ((*tit)->get_visit())
				{
				}
				else
					q.push_back(make_pair(*tit, currDistance));
			}
		}
	}
	return maxDistance;
}

void Reach::add_white_func(Inst *top)
{
	OpInst *op_inst = OpInst::as(top);
	assert (op_inst);
	string euf_func_name = op_inst->get_euf_func_name();
	assert (euf_func_name != "0");

	Inst::_whiteFlist[euf_func_name].push_back(top);
	Inst::_whiteFlist[euf_func_name].push_back(all_pre2next(top, true));
	AVR_LOG(15, 0, "\t(added white UF: " << *top << ")" << endl);
}

void Reach::add_black_func(Inst *top)
{
	OpInst *op_inst = OpInst::as(top);
	assert (op_inst);
	string euf_func_name = op_inst->get_euf_func_name();
	assert (euf_func_name != "0");
	Inst::_blackFlist[euf_func_name].push_back(top);
	Inst::_blackFlist[euf_func_name].push_back(all_pre2next(top, true));
	AVR_LOG(15, 0, "\t(added black UF: " << *top << ")" << endl);
}

bool Reach::convert_to_white(Inst *top, bool init_visit)
{
	if (init_visit) {
		Inst::init_visit();
	}
	if (top->get_visit()) {
		// if already visited, the return value of the initial call of derive_euf_func_list_debug
		// does not depend on this return value.
		return 0;
	}
	bool ret = false;
	top->set_visit();

	const InstL* tch = top->get_children();
	if (tch) {
		for (InstL::const_iterator tit = tch->begin(); tit != tch->end(); ++tit) {
			bool t_ret = convert_to_white(*tit, false);
			ret = ret | t_ret;
		}
	}

	OpInst *op_inst = OpInst::as(top);
	if(op_inst)
	{
		string euf_func_name;
		ExInst *ex_inst = ExInst::as(top);
		if (ex_inst || op_inst->get_op() == OpInst::Concat)
			return ret;

		if(ex_inst)
		{
			euf_func_name = ex_inst->get_euf_func_name();
		}
		else
		{
			euf_func_name = op_inst->get_euf_func_name();
		}

		if(euf_func_name != "0")
		{
			if (find_next(top))
			{
				cout << "Found an unusual case with a UF on $next signals: " << *top << endl;
				assert(0);
			}

			Inst* topNext = all_pre2next(top, true);
			int matched = 0;
			for(InstL::iterator lit = Inst::_blackFlist[euf_func_name].begin(); lit != Inst::_blackFlist[euf_func_name].end();)
			{
				if ((top == *lit) || Inst::is_matched(top, *lit))
				{
					matched++;
					lit = Inst::_blackFlist[euf_func_name].erase(lit);

					for(InstL::iterator lit2 = Inst::_blackFlist[euf_func_name].begin(); lit2 != Inst::_blackFlist[euf_func_name].end();)
					{
						if ((topNext == *lit2) || Inst::is_matched(topNext, *lit2))
						{
							matched++;
							lit2 = Inst::_blackFlist[euf_func_name].erase(lit2);
							break;
						}
						lit2++;
					}

					break;
				}
				lit++;
			}
			if(matched == 2)
			{
				Inst::_whiteFlist[euf_func_name].push_back(top);
				Inst::_whiteFlist[euf_func_name].push_back(topNext);
				AVR_LOG(15, 0, "\t(converting to white UF: " << *top << ")" << endl);
				ret = true;
			}
			else if (matched != 0)
			{
				assert(0);
			}
		}
	}
	return ret;
}

bool Reach::convert_to_important(Inst *top)
{
	if (Inst::check_v_important(top) == INVALID)
	{
		top->v_important = VALID;
		if (!find_next(top))
		{
			Inst* topNext = all_pre2next(top, true);
			topNext->v_important = VALID;
		}
		AVR_LOG(15, 0, "\t(converting to important: " << *top << ", fc: " << top->fcLevel << ")" << endl);
		return true;
	}
	return false;
}
#endif

// return true if there exists a wide multiplier
bool Reach::exist_wide_mult(Inst *top, bool init_visit){
	if (init_visit) {
		Inst::init_visit();
	}
	if (top->get_visit()) {
		return false;
	}
	top->set_visit();

	if((top->get_size() >= 32) && (top->get_type() == Op) && ((OpInst::as(top))->get_op() == OpInst::Mult)){
		return true;
	}else{
		const InstL* ch = top->get_children();
		if (ch) {
			for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it) {
				bool ret = exist_wide_mult(*it, false);
				if(ret == true){
					return true;
				}
			}
		}
	}
	return false;
}

// check_invalid_state_term() returns
// INVALID (1) : if top is invalid
// VALID   (0) : if top is valid
// recommended to call check_term_type(top) before calling this function
// for slightly better performance.
int Reach::check_invalid_state_term(Inst *top)
{
// 		int is_invalid_state_term;	// 16: not yet computed
// 									// 0: valid
// 									// 1: invalid (newly introduced term or term containing inputs)
	if(top->is_invalid_state_term != Inst::not_yet_computed)
	{
#ifdef TEMP_DEBUG_NEW_CUBE_DERIV_CIST
		cout << "check_invalid_state_term, top: " << *top << endl;
		cout << "check_invalid_state_term, ret_1: " << top->is_invalid_state_term << endl;
#endif
		return top->is_invalid_state_term;
	}

	// We want to fill the member variable, is_invalid_state_term,
	// of every children, so we cannot do this
// 	if((check_term_type(top) & 2) == 2){	// contains inputs
// 		top->is_invalid_state_term = 1;
// 		return 1;
// 	}
// 	int top_is_invalid_state_term = 0;
	//map<string, InstL> _func_list;

	const InstL* ch_top = top->get_children();
	if(ch_top)
	{
		bool all_valid = true;
		InstL::const_iterator it_top = ch_top->begin();
		for (; it_top != ch_top->end(); ++it_top)
		{
			Inst *t_inst = *it_top;
			int t_ist = t_inst->is_invalid_state_term;
			if(t_ist == Inst::not_yet_computed)
			{
				check_invalid_state_term(t_inst);
				t_ist = t_inst->is_invalid_state_term;
			}
			if(t_ist != 0)
			{
				all_valid = false;
			}
		}

		if(all_valid == true)
		{
			string top_euf_func_name;
			OpInst *op_inst = OpInst::as(top);
			if(op_inst)
			{
				ExInst *ex_inst = ExInst::as(top);
				if(ex_inst)
				{
					top_euf_func_name = ex_inst->get_euf_func_name();
				}
				else
				{
					top_euf_func_name = op_inst->get_euf_func_name();
				}
			}
			if(top_euf_func_name != "0")
			{
				InstL& apps = _func_list[top_euf_func_name];
				for(InstL::iterator it_apps = apps.begin(); it_apps != apps.end(); ++it_apps)
				{
					Inst *t_inst = *it_apps;
					if(Inst::is_matched(top, t_inst) == 1)
					{
						top->is_invalid_state_term = VALID;
//						cout << "(ist: " << *top << " -> " << VALID << ")" << endl;
						return 0;
					}
				}
			}
			else{	// the negation of a valid predicate should be VALID
				top->is_invalid_state_term = VALID;
//				cout << "(ist: " << *top << " -> " << VALID << ")" << endl;
				return 0;
			}
		}
	}
	else
	{
		int termType = Inst::check_term_type(top);
		if((termType & 2) != 2)
		{	// contains no inputs
			top->is_invalid_state_term = VALID;
//			cout << "(ist: " << *top << " -> " << VALID << ")" << endl;
			return 0;
		}
	}
	top->is_invalid_state_term = INVALID;
//	cout << "(ist: " << *top << " -> " << INVALID << ")" << endl;

#ifdef TEMP_DEBUG_NEW_CUBE_DERIV_CIST
	cout << "check_invalid_state_term, top: " << *top << endl;
	cout << "check_invalid_state_term, ret_2: " << top->is_invalid_state_term << endl;
#endif
	return 1;
}

void Reach::expand_avr1_style(InstL& viol)
{
	bool prop_next_found = false;
	for (InstL::iterator it = viol.begin(), end_it = viol.end(); it != end_it;)
	{
		//remove (r0 == r0) and !(r0 != r0) and terms of constants
		Inst *tve = *it;
		if(!prop_next_found && exist_str(tve, "prop$next", true)) {
			it = viol.erase(it);
			prop_next_found = true;
			continue;
		}

		// remove (a == a) or !(a != a)
		bool negated = false;
		OpInst* op = OpInst::as(tve);
		if(!op){
			it++;
			continue;
		}
		if (op->get_op() == OpInst::LogNot) {
			tve = tve->get_children()->front();
			op = OpInst::as(tve);
			if(!op){
				it++;
				continue;
			}
			negated = true;
		}
//		cout << "tve_2: " << *tve << ",negated: " << negated << endl;

		if (((op->get_op() == OpInst::Eq) && (negated == false)) ||
			((op->get_op() == OpInst::NotEq) && (negated == true))) {
			InstL::const_iterator ch_it = tve->get_children()->begin();
			InstL::const_iterator ch_it2 = ch_it;
			ch_it2++;
			if(*ch_it == *ch_it2){
				//cout << "Reach::trace_back, _viol.erase: " << *(*it) << endl;
				//trivial, so remove
				it = viol.erase(it);
				continue;
			}
		}
		it++;
	}

//	cout << "_viol2: " << _viol << endl;

	if(viol.empty()){
		AVR_LOG(4, 0, "viol.empty()" << endl);
	}
	assert(!viol.empty());

#ifdef AVR_CUBE_ADD_STATE_VAL_PARTITION_INFO_VIOL_ORIGINAL
	InstL viol_original = viol;
#endif

	map<string, InstL> func_list;
	map<string, list<pair<Inst*, Inst*> > > new_terms;
	Inst::init_visit();	//for derive_euf_func_list();

	for (InstL::iterator it = viol.begin(); it != viol.end(); ++it)
	{
		Inst *t_inst = *it;
		// TODO do we have to call init_invalid_state_field()?
//		init_invalid_state_field(t_inst, true);
		check_invalid_state_term(t_inst);
		derive_euf_func_list(func_list, t_inst, false);

		// we should analyze a functional consistency among the new terms as well
		OpInst* op_top = OpInst::as(t_inst);
		bool negated = false;
		if (op_top && (op_top->get_op() == OpInst::LogNot)) {
			t_inst = t_inst->get_children()->front();
			op_top = OpInst::as(t_inst);
			negated = true;
		}
		if(op_top && ((op_top->get_op() == OpInst::Eq) || (op_top->get_op() == OpInst::NotEq))){
			//assert(negated == false);
			if(negated == true){
				cout << "(negated == true): " << *t_inst << endl;
				cout << "(negated == true): " << *(*it) << endl;

			}

			Inst *inst_lhs = t_inst->get_children()->front();
			Inst *inst_rhs = t_inst->get_children()->back();
			// is_invalid_state_term == 0 if valid
			if(inst_lhs->is_invalid_state_term != 0){
				string euf_func_name = inst_lhs->get_euf_func_name();
				if(euf_func_name != "0"){
					new_terms[euf_func_name].push_back(make_pair(inst_lhs, inst_rhs));
// 					cout << "new_terms: " << euf_func_name << endl;
// 					cout << *inst_lhs << endl;
// 					cout << *inst_rhs << endl;
				}
			}
			if(inst_rhs->is_invalid_state_term != 0){
				string euf_func_name = inst_rhs->get_euf_func_name();
				if(euf_func_name != "0"){
					new_terms[euf_func_name].push_back(make_pair(inst_rhs, inst_lhs));
// 					cout << "new_terms: " << euf_func_name << endl;
// 					cout << *inst_rhs << endl;
// 					cout << *inst_lhs << endl;
				}
			}
		}else{
			string euf_func_name = t_inst->get_euf_func_name();
			if(euf_func_name != "0"){	// euf_func_name = "0" for control operators
				new_terms[euf_func_name].push_back(make_pair(t_inst, t_inst));
			}
		}
	}

	map<string, list<pair<Inst*, Inst*> > >::iterator nt_it = new_terms.begin();
	InstS to_add;
	for(; nt_it != new_terms.end(); ++nt_it)
	{
		if(nt_it->second.size() > 1)
		{
			list<pair<Inst*, Inst*> >::iterator pi_it1 = nt_it->second.begin();
			for(; pi_it1 != nt_it->second.end(); ++pi_it1){
				list<pair<Inst*, Inst*> >::iterator pi_it2 = pi_it1;
				++pi_it2;
				for(; pi_it2 != nt_it->second.end(); ++pi_it2)
				{
					if(pi_it1->first == pi_it1->second){	// predicate
						Inst* inst_lhs = pi_it1->first;
						Inst* inst_rhs = pi_it2->first;
						bool eq;
						if (inst_lhs->get_size() == 1)
							eq = (inst_lhs->get_bval() == inst_rhs->get_bval());
						else
							eq = (*inst_lhs->get_ival() == *inst_rhs->get_ival());
						if(eq)
						{
							Inst* t_inst = OpInst::create(OpInst::Eq, inst_lhs, inst_rhs);
							to_add.insert(t_inst);
						}
						else
						{
							Inst* t_inst = OpInst::create(OpInst::NotEq, inst_lhs, inst_rhs);
							to_add.insert(t_inst);
						}
					}
					else{	// term
						Inst* inst_lhs = pi_it1->first;
						Inst* inst_rhs = pi_it2->first;
						bool eq;
						if (inst_lhs->get_size() == 1)
							eq = (inst_lhs->get_bval() == inst_rhs->get_bval());
						else
							eq = (*inst_lhs->get_ival() == *inst_rhs->get_ival());
						if(eq)
						{
							Inst* t_inst = OpInst::create(OpInst::Eq, inst_lhs, inst_rhs);
							to_add.insert(t_inst);
						}
						else
						{
							Inst* t_inst = OpInst::create(OpInst::NotEq, inst_lhs, inst_rhs);
							to_add.insert(t_inst);
						}
						inst_lhs = pi_it1->second;
						inst_rhs = pi_it2->second;
						if (inst_lhs->get_size() == 1)
							eq = (inst_lhs->get_bval() == inst_rhs->get_bval());
						else
							eq = (inst_lhs->get_ival() == inst_rhs->get_ival());
						if(eq)
						{
							Inst* t_inst = OpInst::create(OpInst::Eq, inst_lhs, inst_rhs);
							to_add.insert(t_inst);
						}
						else
						{
							Inst* t_inst = OpInst::create(OpInst::NotEq, inst_lhs, inst_rhs);
							to_add.insert(t_inst);
						}
					}
				}
			}
		}
	}
	for(InstS::iterator ta_it = to_add.begin(); ta_it != to_add.end(); ++ta_it){
		viol.push_back(*ta_it);
		//cout << "_viol_added_new: " << *(*ta_it) << endl;
	}

//	cout << "_viol3: " << _viol << endl;

#ifdef FUNCTIONAL_CONSISTENCY_ANALYSIS
// if(_loop_idx < 50)
{
		InstS result;
		for (InstL::iterator it = viol.begin(); it != viol.end(); ++it)
		{
			Inst *t_inst = *it;
			functional_consistency_analysis(result, func_list, t_inst);
		}

		viol.clear();
		bool prop_next_found = false;
		for(InstS::iterator sit = result.begin(); sit != result.end(); ++sit)
		{
			Inst *tve = *sit;
			if(!prop_next_found && exist_str(tve, "prop$next", true))
			{
				//debug
				cout << "##	func_list	##" << endl;
				for(map<string, InstL>::iterator mit = func_list.begin(); mit != func_list.end(); ++mit){
					cout << "str: " << mit->first << endl;
					cout << mit->second << endl;
				}
				cout << "_viol after derive_euf_func_list(): " << viol << endl;
				assert(0);

				// TODO why does this happen?
				// we removed this before
				prop_next_found = true;
				continue;
			}
			viol.push_back(*sit);
		}
}
//cout << "_viol4: " << _viol << endl;
#endif

#ifdef AVR_CUBE_ADD_STATE_VAL_PARTITION_INFO
//cout << "_viol:: mode:" << mode << ", " << _viol << endl;

#ifdef AVR_CUBE_ADD_STATE_VAL_PARTITION_INFO_VIOL_ORIGINAL
	if(!viol_original.empty())
#else
		if(!viol.empty())
#endif
	{
		// TODO remove duplicated (redundant) predicates in _viol
		map<int, InstS> m_size_regs;
		//TODO very important bug fix
#ifdef AVR_CUBE_ADD_STATE_VAL_PARTITION_INFO_VIOL_ORIGINAL
		collect_wide_regs(OpInst::create(OpInst::LogAnd, viol_original), m_size_regs, true);
#else
		collect_wide_regs(OpInst::create(OpInst::LogAnd, viol), m_size_regs, true);
#endif

#ifdef TRACE_BACK_DERIVE_CORR_EQ
// derive relationships among related regs
// related regs : reg_fsm_88835_reg/q	reg_fsm_reg/q
		InstS regs_1;
		for(map<int, InstS>::iterator mit = m_size_regs.begin(); mit != m_size_regs.end(); ++mit){
	//		cout << "m_size_regs: " << endl << (mit->second) << endl;
			for(InstS::iterator sit = (mit->second).begin(); sit != (mit->second).end(); ++sit){
				Inst *tve = *sit;
				regs_1.insert(tve);
			}
		}

		for(InstS::iterator sit1 = regs_1.begin(); sit1 != regs_1.end(); ++sit1)
		{
			Inst *tve1 = *sit1;
			string name1 = SigInst::as(tve1)->get_name();
			int size1 = tve1->get_size();
			bool check_begin = false;
			int idx = name1.size()-1;
			int num_length = 0;
			for(; idx >= 0; --idx){
				char ch = name1[idx];
				if(check_begin == false){
					if((ch >= '0') && (ch <= '9')){
						check_begin = true;
					}
				}else{
					num_length++;
					if(!((ch >= '0') && (ch <= '9'))){
						break;
					}
				}
			}
	// 		cout << "name1: " << name1 << endl;
	// 		cout << "idx: " << idx << endl;
	// 		cout << "num_length: " << num_length << endl;

			if((idx > 1) && (num_length > 4)){
				name1 = name1.substr(0, idx);
	// 			cout << "name1 after: " << name1 << endl;
			}

			InstS regs_corr;
			regs_corr.insert(tve1);
			InstS::iterator sit2 = sit1;
			++sit2;
			for(; sit2 != regs_1.end();){
				Inst *tve2 = *sit2;
				string name2 = SigInst::as(tve2)->get_name();
				int size2 = tve2->get_size();
				if((size1 == size2) && (name2.substr(0, idx) == name1)){
					regs_corr.insert(tve2);
					InstS::iterator sit2_temp = sit2;
					++sit2;
					regs_1.erase(sit2_temp);
				}else{
					++sit2;
				}
			}

			if(regs_corr.size() < 2){
				continue;
			}

	// 		cout << "regs_corr: " << endl <<  regs_corr << endl;
			for(InstS::iterator sit3 = regs_corr.begin(); sit3 != regs_corr.end(); ++sit3){
				Inst* inst_lhs = *sit3;
				InstS::iterator sit4 = sit3;
				++sit4;
				for(; sit4 != regs_corr.end(); ++sit4){
					Inst* inst_rhs = *sit4;
					OpInst::OpType op_type;
					if(inst_lhs->cex_mpz == inst_rhs->cex_mpz){
						op_type = OpInst::Eq;
					}else{
						op_type = OpInst::NotEq;
					}
					Inst* inst_to_add = OpInst::create(op_type, inst_lhs, inst_rhs);
					viol.push_back(inst_to_add);

					//_viol.push_front(inst_to_add);
					//_viol.push_back(inst_to_add);
	// 				cout << "_viol added: " << *inst_to_add << endl;
				}
			}
		}
#else
// normal partition to cube transform
		for(map<int, InstS>::iterator mit = m_size_regs.begin(); mit != m_size_regs.end(); ++mit){
			map<mpz_class, Inst*> m_acex;

			//cout << "mit: " << mit->first << endl << mit->second << endl << endl;

			for(InstS::iterator sit = (mit->second).begin(); sit != (mit->second).end(); ++sit){
				Inst *tve = *sit;
				//long long aval = tve->cex_val;
				//int sit_size = tve->get_size();

				mpz_class& tveVal = tve->get_ival();
				if(m_acex.find(tveVal) == m_acex.end())
				{
					m_acex[tveVal] = tve;
				}
				else
				{
					Inst* inst_to_add = OpInst::create(OpInst::Eq, m_acex[tve->cex_mpz], tve);
					//_viol.push_back(OpInst::create(OpInst::Eq, m_acex[tve->cex_mpz], tve));
					//_viol.push_front(inst_to_add);
					viol.push_back(inst_to_add);
					//cout << "partition_added: " << *inst_to_add << endl;
				}
			}
			for(map<mpz_class, Inst*>::iterator mit1 = m_acex.begin(); mit1 != m_acex.end(); mit1++){
				map<mpz_class, Inst*>::iterator mit2 = mit1;
				mit2++;
				for(; mit2 != m_acex.end(); mit2++)
				{
					Inst* inst_to_add = OpInst::create(OpInst::LogNot, OpInst::create(OpInst::Eq, mit1->second, mit2->second));
					//_viol.push_back(OpInst::create(OpInst::LogNot, OpInst::create(OpInst::Eq, mit1->second, mit2->second)));
					//_viol.push_front(inst_to_add);
					viol.push_back(inst_to_add);
					//cout << "partition_added: " << *inst_to_add << endl;
				}
			}
		}
#endif
	}
#endif
}

void Reach::functional_consistency_analysis(InstS &result, map<string, InstL>& func_list, Inst *top)
{
	bool negated = false;
	Inst *top_orig = top;
	OpInst* op_top = OpInst::as(top);
	if (op_top && (op_top->get_op() == OpInst::LogNot)) {
		top = top->get_children()->front();
		negated = true;
	}
	OpInst::OpType op_type;
	op_top = OpInst::as(top);
#ifdef TEMP_DEBUG_NEW_CUBE_DERIV_FCA_INSERT
	cout << "functional_consistency_analysis, top: " << *top << endl;
#endif
	if(op_top)
	{
		op_type = op_top->get_op();
	}
	else
	{
		if(top->is_invalid_state_term == VALID)
		{
			// state vars or constants
			result.insert(top_orig);
#ifdef TEMP_DEBUG_NEW_CUBE_DERIV_FCA_INSERT
			cout << "FCA 1 insert: " << *top_orig << endl;
#endif
		}
		return;
	}
	if((negated == true) && ((op_type == OpInst::Eq) || (op_type == OpInst::NotEq)))
	{
		// WN should've converted this into NotEq and Eq respectively
		assert(0);
	}

	if((op_type == OpInst::Eq) || (op_type == OpInst::NotEq))
	{
		bool same_op = false;
		const InstL* chs_top = top->get_children();
		Inst *inst_lhs = chs_top->front();
		Inst *inst_rhs = chs_top->back();
		if(inst_lhs == inst_rhs)
		{
			return;
		}

		OpInst *op_lhs = OpInst::as(inst_lhs);
		OpInst *op_rhs = OpInst::as(inst_rhs);
		// to deal with a case, {a, (b == 3'd0)}
		// such kind of a state-literal is not created if we enable the routines
		// disabled by if(0) in eval_formula and eval_term
		bool either_eq = false;
		OpInst* t_op_inst = OpInst::as(inst_lhs);
		if(t_op_inst && ((t_op_inst->get_op() == OpInst::Eq) || (t_op_inst->get_op() == OpInst::NotEq)))
		{
			either_eq = true;
		}
		t_op_inst = OpInst::as(op_rhs);
		if(t_op_inst && ((t_op_inst->get_op() == OpInst::Eq) || (t_op_inst->get_op() == OpInst::NotEq)))
		{
			either_eq = true;
		}

		if(!((inst_lhs->is_invalid_state_term == VALID) && (inst_rhs->is_invalid_state_term == VALID)) &&
			(either_eq == true))
		{
			//((inst_lhs->get_size() == 1) || (inst_rhs->get_size() == 1)) ){
			// in fact, both sizes should be the same

			if(inst_lhs->get_bval() == 0)
			{
				inst_lhs = OpInst::create(OpInst::LogNot, inst_lhs);
			}
			if(inst_rhs->get_bval() == 0)
			{
				inst_rhs = OpInst::create(OpInst::LogNot, inst_rhs);
			}
			functional_consistency_analysis(result, func_list, inst_lhs);
			functional_consistency_analysis(result, func_list, inst_rhs);
			return;
		}

		if((!op_lhs && (inst_lhs->is_invalid_state_term != 0)) ||
			(!op_rhs && (inst_rhs->is_invalid_state_term != 0)))
		{
			// either lhs or rhs is an input (or both)
// 			assert(inst_lhs->get_size() != 1);
 			return;
		}

		if(op_lhs && op_rhs && (op_lhs->get_euf_func_name() == op_rhs->get_euf_func_name()))
		{
			same_op = true;
		}

// 	0	if((inst_lhs->is_invalid_state_term == 0) && (inst_rhs->is_invalid_state_term == 0))
// 	1	}else if((inst_lhs->is_invalid_state_term != 0) && (inst_rhs->is_invalid_state_term == 0)){
// 	2	}else if((inst_lhs->is_invalid_state_term == 0) && (inst_rhs->is_invalid_state_term != 0)){
// 	3	}else if((inst_lhs->is_invalid_state_term != 0) && (inst_rhs->is_invalid_state_term != 0)){
// 		int lhs_rhs_invalid = (inst_lhs->is_invalid_state_term == 0) ? 0 : 1;
// 		lhs_rhs_invalid = (inst_rhs->is_invalid_state_term == 0) ? lhs_rhs_invalid : (lhs_rhs_invalid + 2);
		Inst *equiv_app_lhs;
		Inst *equiv_app_rhs;
		list<InstsPair> pairs_equiv_chs_lhs;
		list<InstsPair> pairs_neq_chs_lhs;
		list<InstsPair> pairs_equiv_chs_rhs;
		list<InstsPair> pairs_neq_chs_rhs;

		if((inst_lhs->is_invalid_state_term == VALID) && (inst_rhs->is_invalid_state_term == VALID))
		{
			if(same_op == false)
			{
				result.insert(top_orig);
#ifdef TEMP_DEBUG_NEW_CUBE_DERIV_FCA_INSERT
				cout << "FCA 2 insert: " << *top_orig << endl;
#endif
			}
			else
			{
				if(op_type == OpInst::Eq)
				{
					result.insert(top_orig);
// 					// functional_consistency_analysis on each children pair
// 					const InstL* chs_lhs = inst_lhs->get_children();
// 					const InstL* chs_rhs = inst_rhs->get_children();
// 					if (chs_lhs && chs_rhs && (chs_lhs->size() == chs_rhs->size())){
//
// 						bool all_chs_equiv = true;
// 						InstL::const_iterator it_lhs = chs_lhs->begin();
// 						InstL::const_iterator it_rhs = chs_rhs->begin();
// 						for (; it_rhs != chs_rhs->end(); ++it_rhs, ++it_lhs){
// 							Inst *ch_rhs = *it_rhs;
// 							Inst *ch_lhs = *it_lhs;
//
// 							if(ch_rhs->cex_mpz != ch_lhs->cex_mpz){
// 								all_chs_equiv = false;
// 								break;
// 							}
// 						}
//
// 						if(all_chs_equiv == true){
// 							it_lhs = chs_lhs->begin();
// 							it_rhs = chs_rhs->begin();
// 							for (; it_rhs != chs_rhs->end(); ++it_rhs, ++it_lhs){
// 								Inst *ch_rhs = *it_rhs;
// 								Inst *ch_lhs = *it_lhs;
// 								functional_consistency_analysis(result, func_list,
// 										OpInst::create(op_type, ch_rhs, ch_lhs));
// 							}
// 						}else{
// 							result.insert(top_orig);
// #ifdef TEMP_DEBUG_NEW_CUBE_DERIV_FCA_INSERT
// 							cout << "FCA 2.5 insert: " << *top_orig << endl;
// #endif
// 						}
// 					}else{
// // 						cout << "inst_lhs: " << *inst_lhs << endl;
// // 						cout << "inst_rhs: " << *inst_rhs << endl;
//
// 						assert(0);
// 					}
				}
				else
				{
					result.insert(top_orig);
#ifdef TEMP_DEBUG_NEW_CUBE_DERIV_FCA_INSERT
					cout << "FCA 3 insert: " << *top_orig << endl;
#endif
				}
			}
		}
		else if((inst_lhs->is_invalid_state_term != VALID) && (inst_rhs->is_invalid_state_term == VALID))
		{
			equiv_app_lhs = lookup_func_list(pairs_equiv_chs_lhs, pairs_neq_chs_lhs, func_list, op_lhs);
			if(equiv_app_lhs != NULL)
			{
				if(same_op == false)
				{
					Inst* t_inst = OpInst::create(op_type, equiv_app_lhs, inst_rhs);
					result.insert(t_inst);
#ifdef TEMP_DEBUG_NEW_CUBE_DERIV_FCA_INSERT
					cout << "FCA 4 insert: " << *t_inst << endl;
#endif
				}
				else
				{
					list<InstsPair>::iterator it_eq_chs = pairs_equiv_chs_lhs.begin();
					InstL::const_iterator it_rhs = inst_rhs->get_children()->begin();
					if(op_type == OpInst::Eq)
					{
						Inst* t_inst = OpInst::create(OpInst::Eq, equiv_app_lhs, inst_rhs);
						result.insert(t_inst);
#ifdef TEMP_DEBUG_NEW_CUBE_DERIV_FCA_INSERT
						cout << "FCA 5 insert: " << *t_inst << endl;
#endif
// 						for(; it_eq_chs != pairs_equiv_chs_lhs.end(); ++it_eq_chs, ++it_rhs){
// 							functional_consistency_analysis(result, func_list,
// 								OpInst::create(OpInst::Eq, it_eq_chs->second, *it_rhs));
// 						}
					}
					else
					{
						Inst* t_inst = OpInst::create(OpInst::NotEq, equiv_app_lhs, inst_rhs);
						result.insert(t_inst);
#ifdef TEMP_DEBUG_NEW_CUBE_DERIV_FCA_INSERT
						cout << "FCA 5 insert: " << *t_inst << endl;
#endif
 					}
				}
				list<InstsPair>::iterator it_eq_chs = pairs_equiv_chs_lhs.begin();
				for(; it_eq_chs != pairs_equiv_chs_lhs.end(); ++it_eq_chs)
				{
					functional_consistency_analysis(result, func_list,
							OpInst::create(OpInst::Eq, it_eq_chs->first, it_eq_chs->second));
				}
			}
			else
			{
				list<InstsPair>::iterator it_neq_chs = pairs_neq_chs_lhs.begin();
				for(; it_neq_chs != pairs_neq_chs_lhs.end(); ++it_neq_chs)
				{
					functional_consistency_analysis(result, func_list,
						OpInst::create(OpInst::NotEq, it_neq_chs->first, it_neq_chs->second));
				}
			}
		}
		else if((inst_lhs->is_invalid_state_term == VALID) && (inst_rhs->is_invalid_state_term != VALID))
		{
			equiv_app_rhs = lookup_func_list(pairs_equiv_chs_rhs, pairs_neq_chs_rhs, func_list, op_rhs);
			if(equiv_app_rhs != NULL)
			{
				if(same_op == false)
				{
					Inst* t_inst = OpInst::create(op_type, inst_lhs, equiv_app_rhs);
					result.insert(t_inst);
#ifdef TEMP_DEBUG_NEW_CUBE_DERIV_FCA_INSERT
					cout << "FCA 6 insert: " << *t_inst << endl;
#endif
				}
				else
				{
					list<InstsPair>::iterator it_eq_chs = pairs_equiv_chs_rhs.begin();
					InstL::const_iterator it_lhs = inst_lhs->get_children()->begin();
					if(op_type == OpInst::Eq)
					{
						Inst* t_inst = OpInst::create(OpInst::Eq, inst_lhs, equiv_app_rhs);
						result.insert(t_inst);
#ifdef TEMP_DEBUG_NEW_CUBE_DERIV_FCA_INSERT
						cout << "FCA 7 insert: " << *t_inst << endl;
#endif

// 						for(; it_eq_chs != pairs_equiv_chs_rhs.end(); ++it_eq_chs, ++it_lhs){
// 							functional_consistency_analysis(result, func_list,
// 								OpInst::create(OpInst::Eq, *it_lhs, it_eq_chs->second));
// 						}
					}
					else
					{
						Inst* t_inst = OpInst::create(OpInst::NotEq, inst_lhs, equiv_app_rhs);
						result.insert(t_inst);
#ifdef TEMP_DEBUG_NEW_CUBE_DERIV_FCA_INSERT
						cout << "FCA 7 insert: " << *t_inst << endl;
#endif
					}
				}
				list<InstsPair>::iterator it_eq_chs = pairs_equiv_chs_rhs.begin();
				for(; it_eq_chs != pairs_equiv_chs_rhs.end(); ++it_eq_chs)
				{
					functional_consistency_analysis(result, func_list,
							OpInst::create(OpInst::Eq, it_eq_chs->first, it_eq_chs->second));
				}
			}
			else
			{
				list<InstsPair>::iterator it_neq_chs = pairs_neq_chs_rhs.begin();
				for(; it_neq_chs != pairs_neq_chs_rhs.end(); ++it_neq_chs)
				{
					functional_consistency_analysis(result, func_list,
						OpInst::create(OpInst::NotEq, it_neq_chs->first, it_neq_chs->second));
				}
			}
		}
		else if((inst_lhs->is_invalid_state_term != VALID) && (inst_rhs->is_invalid_state_term != VALID))
		{
			if(same_op == true)
			{
				const InstL* chs_lhs = inst_lhs->get_children();
				const InstL* chs_rhs = inst_rhs->get_children();
				if (chs_lhs && chs_rhs && (chs_lhs->size() == chs_rhs->size()))
				{
					InstL::const_iterator it_lhs = chs_lhs->begin();
					InstL::const_iterator it_rhs = chs_rhs->begin();
					for (; it_rhs != chs_rhs->end(); ++it_rhs, ++it_lhs)
					{
						Inst *ch_rhs = *it_rhs;
						Inst *ch_lhs = *it_lhs;

// 						if(op_type == OpInst::NotEq){	// this causes missing info
// 							if(ch_rhs->cex_mpz != ch_lhs->cex_mpz){
// 								functional_consistency_analysis(result, func_list,
// 										OpInst::create(OpInst::NotEq, ch_rhs, ch_lhs));
// 							}
// 						}else
						{
							bool eq;
							if (ch_rhs->get_size() == 1)
								eq = (ch_rhs->get_bval() == ch_lhs->get_bval());
							else
								eq = (*ch_rhs->get_ival() == *ch_lhs->get_ival());

							if(!eq)
							{
								functional_consistency_analysis(result, func_list,
										OpInst::create(OpInst::NotEq, ch_rhs, ch_lhs));
							}
							else
							{
								functional_consistency_analysis(result, func_list,
										OpInst::create(OpInst::Eq, ch_rhs, ch_lhs));
							}
						}
					}
				}
			}
			else
			{
				if (op_lhs->get_op() == OpInst::LogNot)
				{
					cout << "op_lhs: " << *op_lhs << endl;
					cout << "op_rhs: " << *op_rhs << endl;
					cout << "top: " << *top << endl;
					assert(0);
				}
				equiv_app_lhs = lookup_func_list(pairs_equiv_chs_lhs, pairs_neq_chs_lhs, func_list, op_lhs);
				equiv_app_rhs = lookup_func_list(pairs_equiv_chs_rhs, pairs_neq_chs_rhs, func_list, op_rhs);

				if((equiv_app_lhs != NULL) && (equiv_app_rhs != NULL))
				{
					if(same_op == false)
					{
						Inst* t_inst = OpInst::create(op_type, equiv_app_lhs, equiv_app_rhs);
						result.insert(t_inst);
#ifdef TEMP_DEBUG_NEW_CUBE_DERIV_FCA_INSERT
						cout << "FCA 8 insert: " << *t_inst << endl;
#endif
					}
					else
					{
						list<InstsPair>::iterator it_eq_chs_lhs = pairs_equiv_chs_lhs.begin();
						list<InstsPair>::iterator it_eq_chs_rhs = pairs_equiv_chs_rhs.begin();
						if(op_type == OpInst::Eq)
						{
							Inst* t_inst = OpInst::create(OpInst::Eq, equiv_app_lhs, equiv_app_rhs);
							result.insert(t_inst);
#ifdef TEMP_DEBUG_NEW_CUBE_DERIV_FCA_INSERT
							cout << "FCA 9 insert: " << *t_inst << endl;
#endif
	// 						for(; it_eq_chs_lhs != pairs_equiv_chs_lhs.end(); ++it_eq_chs_lhs, ++it_eq_chs_rhs){
	// 							functional_consistency_analysis(result, func_list,
	// 								OpInst::create(OpInst::Eq, it_eq_chs_lhs->second, it_eq_chs_rhs->second));
	// 						}
						}
						else
						{
							Inst* t_inst = OpInst::create(OpInst::NotEq, equiv_app_lhs, equiv_app_rhs);
							result.insert(t_inst);
#ifdef TEMP_DEBUG_NEW_CUBE_DERIV_FCA_INSERT
							cout << "FCA 9 insert: " << *t_inst << endl;
#endif
						}
					}
					list<InstsPair>::iterator it_eq_chs_lhs = pairs_equiv_chs_lhs.begin();
					list<InstsPair>::iterator it_eq_chs_rhs = pairs_equiv_chs_rhs.begin();
					for(; it_eq_chs_lhs != pairs_equiv_chs_lhs.end(); ++it_eq_chs_lhs)
					{
						functional_consistency_analysis(result, func_list,
								OpInst::create(OpInst::Eq, it_eq_chs_lhs->first, it_eq_chs_lhs->second));
					}
					for(; it_eq_chs_rhs != pairs_equiv_chs_rhs.end(); ++it_eq_chs_rhs)
					{
						functional_consistency_analysis(result, func_list,
								OpInst::create(OpInst::Eq, it_eq_chs_rhs->first, it_eq_chs_rhs->second));
					}
				}
				else
				{
					// If either equiv_app_lhs or equiv_app_rhs is NULL,
					// we ignore pairs_equiv_chs because it doesn't matter.
					// NEED to double-check the correctness of this approach though
					if(equiv_app_lhs == NULL)
					{
						list<InstsPair>::iterator it_neq_chs = pairs_neq_chs_lhs.begin();
						for(; it_neq_chs != pairs_neq_chs_lhs.end(); ++it_neq_chs)
						{
							functional_consistency_analysis(result, func_list,
								OpInst::create(OpInst::NotEq, it_neq_chs->first, it_neq_chs->second));
						}
					}
					if(equiv_app_rhs == NULL)
					{
						list<InstsPair>::iterator it_neq_chs = pairs_neq_chs_rhs.begin();
						for(; it_neq_chs != pairs_neq_chs_rhs.end(); ++it_neq_chs)
						{
							functional_consistency_analysis(result, func_list,
								OpInst::create(OpInst::NotEq, it_neq_chs->first, it_neq_chs->second));
						}
					}
				}
			}
		}
	}
	else
	{
		if(top->is_invalid_state_term == VALID)
		{
			result.insert(top_orig);
#ifdef TEMP_DEBUG_NEW_CUBE_DERIV_FCA_INSERT
			cout << "FCA 10 insert: " << *top_orig << endl;
#endif
			return;
		}

		list<InstsPair> pairs_equiv_chs;
		list<InstsPair> pairs_neq_chs;
		Inst *equiv_app = lookup_func_list(pairs_equiv_chs, pairs_neq_chs, func_list, op_top);

		if(equiv_app != NULL)
		{
			if(negated == true)
			{
				Inst* t_inst = OpInst::create(OpInst::LogNot, equiv_app);
				result.insert(t_inst);
#ifdef TEMP_DEBUG_NEW_CUBE_DERIV_FCA_INSERT
				cout << "FCA 11 insert: " << *t_inst << endl;
#endif
			}
			else
			{
				result.insert(equiv_app);
#ifdef TEMP_DEBUG_NEW_CUBE_DERIV_FCA_INSERT
				cout << "FCA 12 insert: " << *equiv_app << endl;
#endif
			}
			list<InstsPair>::iterator it_eq_chs = pairs_equiv_chs.begin();
			for(; it_eq_chs != pairs_equiv_chs.end(); ++it_eq_chs){
				functional_consistency_analysis(result, func_list,
					OpInst::create(OpInst::Eq, it_eq_chs->first, it_eq_chs->second));
			}
		}
		else
		{
			list<InstsPair>::iterator it_neq_chs = pairs_neq_chs.begin();
			for(; it_neq_chs != pairs_neq_chs.end(); ++it_neq_chs){
				//cout << "XXX: " << *(OpInst::create(OpInst::NotEq, it_neq_chs->first, it_neq_chs->second)) << endl;
				functional_consistency_analysis(result, func_list,
					OpInst::create(OpInst::NotEq, it_neq_chs->first, it_neq_chs->second));
			}
		}
	}
}

Inst* Reach::lookup_func_list(list<InstsPair>& pairs_equiv_chs, list<InstsPair>& pairs_neq_chs,
							 map<string, InstL>& func_list, OpInst *top)
{
	string top_euf_func_name;
	ExInst *ex_top = ExInst::as(top);
	if(ex_top)
	{
		top_euf_func_name = ex_top->get_euf_func_name();
	}
	else
	{
		top_euf_func_name = top->get_euf_func_name();
	}

	if(top_euf_func_name != "0")
	{
		// TODO check this
		InstL& apps = func_list[top_euf_func_name];
		Inst *app;
		for(InstL::iterator it_apps = apps.begin(); it_apps != apps.end(); ++it_apps)
		{
			app = *it_apps;
			//if(app->cex_mpz == top->cex_mpz)
			{
				const InstL* chs_app = app->get_children();
				const InstL* chs_top = top->get_children();
				if (chs_app && chs_top && (chs_app->size() == chs_top->size()))
				{
					InstL::const_iterator it_app = chs_app->begin();
					InstL::const_iterator it_top = chs_top->begin();
					bool all_chs_cex_same = true;
					pairs_equiv_chs.clear();
					for (; it_top != chs_top->end(); ++it_top, ++it_app)
					{
						Inst *ch_top = *it_top;
						Inst *ch_app = *it_app;

#ifdef TEMP_DEBUG_NEW_CUBE_DERIV_LFL
						cout << "ch_top: " << *ch_top << endl;
						cout << "ch_app: " << *ch_app << endl;
#endif

						bool eq;
						if (ch_top->get_size() == 1)
							eq = (ch_top->get_bval() == ch_app->get_bval());
						else
							eq = (*ch_top->get_ival() == *ch_app->get_ival());
						if(!eq)
						{
#ifdef TEMP_DEBUG_NEW_CUBE_DERIV_LFL
							cout << "ch_top->cex_mpz: " << ch_top->cex_mpz << ", ch_app->cex_mpz: " << ch_app->cex_mpz << endl;
#endif
							all_chs_cex_same = false;
							pairs_neq_chs.push_back(make_pair(ch_top, ch_app));
							break;
						}
						else
						{
#ifdef TEMP_DEBUG_NEW_CUBE_DERIV_LFL
							cout << "ch_top->cex_mpz: " << ch_top->cex_mpz << ", ch_app->cex_mpz: " << ch_app->cex_mpz << endl;
#endif
							pairs_equiv_chs.push_back(make_pair(ch_top, ch_app));
						}
					}
					if(all_chs_cex_same == true)
					{
						return app;
					}
					else
					{

					}
				}
			}
		}
	}
	else
	{	// If this happens, there's something wrong in eval_formula
		// no, this can happen : e.g. {a, (b == 3'd0)}
		cout << "top: " << *top << endl;
// 		{
// 			cout << "top	1: " << *top << endl;
// 			void* tracePtrs[100];
// 			int count = backtrace( tracePtrs, 100 );
// 			char** funcNames = backtrace_symbols( tracePtrs, count );
//
// 			// Print the stack trace
// 			for( int ii = 0; ii < count; ii++ )
// 				printf( "%s\n", funcNames[ii] );
//
// 			// Free the string pointers
// 			free( funcNames );
//
// 			assert(0);
// 		}
		assert(0);
	}
	return NULL;
}

void Reach::collect_terms(Inst *top, map<int, InstS> &m_terms, bool init_visit) {
	if (init_visit) {
		Inst::init_visit();
	}
	if (top->get_visit()) {
		return;
	}
	top->set_visit();

	const InstL* ch = top->get_children();
	if (ch) {
		for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it) {
			collect_terms(*it, m_terms);
		}
	}
	int size = top->get_size();
//	if((size > 1) && top->term_type != 2){
	if((size > 1) && top->term_type == 1){
		m_terms[size].insert(top);
	}
}

void Reach::derive_partition(Inst *ve_gcube_next, InstToMpzM* cube_partition, InstL& conjunct_partition){
#ifndef AVR_GCUBE_ADD_ALL_PARTITION_INFO
	return;
#endif
	map<int, InstS> m_terms;
	Inst::check_term_type(ve_gcube_next);
	collect_terms(ve_gcube_next, m_terms, true);

	for(map<int, InstS>::iterator mit = m_terms.begin(); mit != m_terms.end(); ++mit){
		map<mpz_class, Inst*> m_acex;
		for(InstS::iterator sit = (mit->second).begin(); sit != (mit->second).end(); ++sit){
			Inst *tve = *sit;
			InstToMpzM::iterator tit = cube_partition->find(tve);
			if(tit == cube_partition->end()){
				AVR_LOG(6, 0, "tve: " << *tve << endl);
			}
			assert(tit != cube_partition->end());
			mpz_class cex_mpz = tit->second;
			//int sit_size = tve->get_size();

			if(m_acex.find(cex_mpz) == m_acex.end()){
				m_acex[cex_mpz] = tve;
			}else{
				Inst *ve_to_add = m_acex[cex_mpz];
				if(ve_to_add->get_type() == Num){
					ve_to_add = OpInst::create(OpInst::Eq, tve, ve_to_add);
				}else{
					ve_to_add = OpInst::create(OpInst::Eq, ve_to_add, tve);
				}
				//if(check_term_type(ve_to_add) != 2){
				if(Inst::check_term_type(ve_to_add) == 1){
					conjunct_partition.push_back(ve_to_add);
				}
			}
		}
		for(map<mpz_class, Inst*>::iterator mit1 = m_acex.begin(); mit1 != m_acex.end(); mit1++){
			map<mpz_class, Inst*>::iterator mit2 = mit1;
			mit2++;
			for(; mit2 != m_acex.end(); mit2++){
				Inst *ve_to_add = mit1->second;
				if(ve_to_add->get_type() == Num){
					ve_to_add = OpInst::create(OpInst::Eq, mit2->second, ve_to_add);
				}else{
					ve_to_add = OpInst::create(OpInst::Eq, ve_to_add, mit2->second);
				}
				//if(check_term_type(ve_to_add) != 2){
				if(Inst::check_term_type(ve_to_add) == 1){
					conjunct_partition.push_back(OpInst::create(OpInst::LogNot, ve_to_add));
				}
			}
		}
	}

}

bool Reach::check_if_global(Inst *ve_gcube)
{
	SOLVER_CONTAIN fSolver(_abstract_mapper, AVR_EXTRA_IDX, false, regular);
//	fSolver->stop_ex_cc_interpret();

	fSolver.s_assert(ve_gcube);
	int tmpResult = fSolver.s_check(AB_QUERY_TIMEOUT, false);
	if (tmpResult != AVR_QSAT)
	{
		assert(tmpResult == AVR_QUSAT);
//		AVR_LOG(15, 0, "\n\t\t\t(solver check: global lemma)" << endl);
		return true;
	}

	/// Below can be false
//	if (!ve_gcube->childrenInfo[SIG])
//	{
//		if (tmpResult != AVR_QUSAT)
//		{
//			cout << *ve_gcube << endl;
//		}
//		assert(tmpResult == AVR_QUSAT);
//	}

//  AVR_LOG(15, 0, "\n\t\t\t(solver check: not global)" << endl);
//  fSolver->s_print_model();
	return false;
}

bool Reach::check_blocked(int g_idx, CLAUSE &gcube)
{
	struct rusage usage;
	struct timeval start_time, end_time;
	long long time_diff;

	TIME_S(start_time);
	bool res = false;
	for (int t_c = g_idx; t_c <= _frame_idx; t_c++)
	{
		for (vector<CLAUSE>::iterator it7 = (_cubes[t_c]).begin(); it7 != (_cubes[t_c]).end(); it7++)
		{
			// check if ve_gcube -> *it7
			if ((*it7).subsumes(gcube))
			{
				AVR_LOG(15, 0, "\n\t\t(cube check: already blocked in F[" << t_c << "])" << endl);
//				cout << "cube: " << *gcube.cube << endl;
				AVR_LOG(15, 0, "\t\t\t(blocker: " << *(*it7).cube << endl);
//				cout << "F: " << _cubes[t_c] << endl;
				res = true;
				if (Config::g_forward_check != FORWARDCHECK_ONESTEP)
					assert(0);
				break;
			}
		}
		if (res)
			break;
	}
	TIME_E(start_time, end_time, _tb_ct_isblocked_time);

	return res;
}

/// Checks SAT_a ? F[k] ^ conjunct_cube
/// returns true if UNSAT
bool Reach::check_blocked_using_solver(int k, InstL& conjunct_cube, InstL& conjunct_cone, int count)
{
//	return false;

	assert(k < _reach_solvers.size());

	if (conjunct_cube.empty())
		return false;

	Solver* y_solver = _reach_solvers[k].solver_main;
	assert(y_solver);
//	y_solver->stop_ex_cc_interpret();

	InstL conjunct_q = conjunct_cone;
	for (auto& c: conjunct_cube)
	  conjunct_q.push_back(c);

  int res = solveRelative(k, conjunct_q, regular, false, false);
	y_solver->s_retract_assertions();

	if (res == AVR_QUSAT)
	{
		if (count == 0)
		{
			cout << "Error: cube already blocked in frame " << k << endl;

//			cout << "Cube: " << conjunct_cube << endl;

			Inst* cube = OpInst::create(OpInst::LogAnd, conjunct_cube);

			ostringstream ostr;
			ostr << "error/cube_" << *cube;
			draw_graph(1, cube, ostr.str(), 0, false);

			InstL conjunct_tmp = conjunct_cube;
			conjunct_tmp.push_back(_ve_model);
			conjunct_tmp.push_back(_ve_prop_eq_1);

			for (InstL::iterator it3 = _negated_refs.begin(); it3 != _negated_refs.end(); ++it3)
			{
				conjunct_tmp.push_back(*it3);
			}
			SOLVER_AB tmpSolver(_abstract_mapper, AVR_EXTRA_IDX, true, regular);
//			tmpSolver->s_assert(OpInst::create(OpInst::LogAnd, conjunct_tmp));

//			cout << "Q: " << conjunct_tmp << endl;
//			cout << "_nCubes: " << _negated_cubes[k] << endl;

			negated_cubes(k, conjunct_tmp);

			InstLL muses;
//			int res = tmpSolver->get_muses_2(AB_QUERY_TIMEOUT, conjunct_tmp, muses, num_scalls_sat_correctness, num_scalls_unsat_correctness);
			assert(res == 1);
			int count = 0;
			cout << "(warning: cube unsat in F[" << k << "])" << endl;
			Inst::num_warnings++;
			cout << "MUSes:" << endl;
			for (InstLL::iterator it_muses2 = muses.begin(); it_muses2 != muses.end(); ++it_muses2)
			{
				count++;
				cout << "[" << count << "]: " << *it_muses2 << endl;
				for (auto& m: (*it_muses2))
				{
					ostringstream ostr;
					ostr << "error/mus_" << *m;
					draw_graph(1, m, ostr.str(), 0, false);
				}
			}
//			assert(0);
		}
		return true;
	}
	return false;
}

//	return value :
//	0 : negated_cubes is not updated
//	1 : negated_cubes is updated, and the property holds (terminal condition)
//	2 : negated_cubes is updated, but we don't know whether the property holds or not
int Reach::containment_check(int g_idx, CLAUSE &gcube, int count)
{
 	AVR_LOG(7, 5,  "containment_check: g_idx: " << g_idx << ", gcube: " << *gcube.cube << endl);
// 	AVR_LOG(7, 0,  "frame: " << g_idx << ", g_cube: " << endl << *ve_gcube << endl);
//  	AVR_LOG(7, 0,  "frame: " << g_idx << ", g_cube: " << endl);
// 	new_print(cout, ve_gcube, true);
// 	for (int i = 1; i <= _frame_idx; i++) {
// 		cout << "frame number : " << i << endl;
// 		cout << "&(_cubes[i])" << (_cubes[i]) << endl;
// 	}

// 			if ((*it7 == ve_gcube) && (set_contains (*it7, ve_gcube) != 1)) {
// 				AVR_LOG(7, 1, "##	case 1	##" << endl);
// 				AVR_LOG(7, 1, "*it7: " << *(*it7) << endl);
// 				AVR_LOG(7, 1, "ve_gcube: " << *ve_gcube << endl);
// 				assert(0);
// 			}
// 			if ((*it7 != ve_gcube) && (set_contains (*it7, ve_gcube) == 1)) {
// 				AVR_LOG(7, 3, "##	case 2	##" << endl);
// 				AVR_LOG(7, 3, "*it7: " << *(*it7) << endl);
// 				AVR_LOG(7, 3, "ve_gcube: " << *ve_gcube << endl);
// 				_set_containment_cnt++;
// 			}

#ifndef DISABLE_ABSTRACT_LEMMAS
 	if (check_if_global(ve_gcube))
 		return 4;
#endif

#ifdef CHECK_REDUNDANCY_IN_CONTAINMENT
 	{
		InstL conjunct_tmp = _negated_cubes[g_idx];
		conjunct_tmp.push_back(ve_gcube);
		conjunct_tmp.push_back(_ve_model);
		conjunct_tmp.push_back(_ve_prop_eq_1);

		for (InstL::iterator it3 = _negated_refs.begin(); it3 != _negated_refs.end(); ++it3)
		{
			conjunct_tmp.push_back(*it3);
		}

		Inst* ve_tmp = OpInst::create(OpInst::LogAnd, conjunct_tmp);

		z3_API* fSolver = new z3_API(&_abstract_mapper, AVR_EXTRA_IDX, false, true);
//		fSolver->disable_ex_cc_interpret();

		fSolver->s_assert(ve_tmp);
		int tmpResult = fSolver->s_check(AB_QUERY_TIMEOUT);

		if (tmpResult != AVR_QSAT)
		{
			assert(tmpResult == AVR_QUSAT);

			if (count == 1)
			{
				ostringstream ostr;
				ostr << "error/" << *ve_gcube;
				draw_graph(1, ve_gcube, ostr.str(), 0, false);

				cout << g_idx << endl;
				cout << "Error while restricting a frame:  F[" << g_idx << "] & cubeBlock is " << tmpResult << endl;
				cout << "Cube: " << *ve_gcube << endl;

				InstL conjunct_tmp;
				conjunct_tmp.push_back(ve_gcube);
				conjunct_tmp.push_back(_ve_model);
				conjunct_tmp.push_back(_ve_prop_eq_1);

				for (InstL::iterator it3 = _negated_refs.begin(); it3 != _negated_refs.end(); ++it3)
				{
					conjunct_tmp.push_back(*it3);
				}
				z3_API* tmpSolver = new z3_API(&_abstract_mapper, AVR_EXTRA_IDX, true, false);
	//			tmpSolver->s_assert(OpInst::create(OpInst::LogAnd, conjunct_tmp));

				cout << "Q: " << conjunct_tmp << endl;
				cout << "_nCubes: " << _negated_cubes[g_idx] << endl;

				for (auto& nc: _negated_cubes[g_idx])
				{
					conjunct_tmp.push_back(nc);
				}

				InstLL muses;
				int res = tmpSolver->get_muses_2(AB_QUERY_TIMEOUT, conjunct_tmp, muses, num_scalls_sat_correctness, num_scalls_unsat_correctness);
				assert(res == 1);
				int count = 0;
				cout << "MUSes:" << endl;
				for (InstLL::iterator it_muses2 = muses.begin(); it_muses2 != muses.end(); ++it_muses2)
				{
					count++;
					cout << "[" << count << "]: " << *it_muses2 << endl;
					for (auto& m: (*it_muses2))
					{
						ostringstream ostr;
						ostr << "error/" << *m;
						draw_graph(1, m, ostr.str(), 0, false);
					}
				}
				delete tmpSolver;
			}

			AVR_LOG(15, 0, "\n\t\t\t(solver check: redundant)" << endl);
			assert(0);
			return 0;
		}
		delete fSolver;
 	}
#endif

	struct rusage usage;
	struct timeval start_time, end_time;
	long long time_diff;

	TIME_S(start_time);
 	int res = -1;
  for (size_t d = 1; d <= g_idx; ++d) {
      vector<CLAUSE>& fd = _cubes[d];
      size_t j = 0;
      for (size_t i = 0; i < fd.size(); ++i) {
          if (!gcube.subsumes(fd[i])) {
              fd[j++] = fd[i];
          } else {
              ++CLAUSE::_numSubsumedCube;
              if (d == g_idx) {
              	if (gcube.cube == fd[i].cube) {
              		res = 0;
              	}
              }
          }
      }
      fd.resize(j);
//  		if ((d < _frame_idx) && fd.empty()) {
//  			res = 1;
//  			break; //property holds
//  		}
  }

	_cubes[g_idx].push_back(gcube);
//	cout << "adding clause to F" << g_idx << "\t" << *gcube.clause << endl;

	if (res == -1)
		res = 2;

	TIME_E(start_time, end_time, _tb_ct_containment_time);
	return res;
}

void Reach::forward_frame_clause(int g_idx, int blockIdx, CLAUSE &gcube)
{
	struct rusage usage;
	struct timeval start_time, end_time;
	long long time_diff;

	TIME_S(start_time);
  for (size_t d = g_idx; d <= blockIdx; ++d) {
      vector<CLAUSE>& fd = _cubes[d];
      size_t j = 0;
      for (size_t i = 0; i < fd.size(); ++i) {
          if (!gcube.subsumes(fd[i])) {
              fd[j++] = fd[i];
          } else {
              ++CLAUSE::_numSubsumedCube;
          }
      }
      fd.resize(j);
  }
	_cubes[blockIdx].push_back(gcube);
	TIME_E(start_time, end_time, _tb_ct_containment_time);
}


#if 0
// return true if a given cube contains init states
bool Reach::cube_contain_inits(Inst *cube, bool tb_cube){
	// four patterns if tb_cube is false
	// q0, !q0, (s0 == s1), !(s0 == s1)
	bool negated = false;
	if(tb_cube == false){
		OpInst* op = OpInst::as(cube);
		if (op && (op->get_op() == OpInst::LogNot)) {
			cube = cube->get_children()->front();
			negated = true;
		}
	}

	SigInst *sig = SigInst::as(cube);
	if(sig){
		if(_init_values[sig] == 1){
			return !negated;
		}else{
// 			if(tb_cube == true){
// 				cout << "cube_contain_inits: " << endl << *cube << endl;
// 			}
			return negated;
		}
	}else{
		if(tb_cube){
			InstL conjunct_ct;
			conjunct_ct = _negated_cubes[0];
			conjunct_ct.push_back(cube);
			for (InstL::iterator it3 = _negated_refs.begin(); it3 != _negated_refs.end(); ++it3)
				conjunct_ct.push_back(*it3);
			Inst *ve_ct = OpInst::create(OpInst::LogAnd, conjunct_ct);
			z3_API int_solver(&_abstract_mapper, 1);
			bool res = int_solver.check_sat(ve_ct);
			//cout << "cube_contain_inits, res: " << res << endl << *ve_ct << endl;
			return res;
		}else{
			const InstL* ch = cube->get_children();
			InstL::const_iterator it = ch->begin();
			Inst *lhs = *it++;
			Inst *rhs = *it;
			if(_init_values[lhs] == _init_values[rhs]){
				return !negated;
			}else{
				return negated;
			}
		}
	}
}
#else
// return true if a given cube contains init states
bool Reach::cube_contain_inits(Inst *top){
  if (top->hasNegInit != DEFAULT_VAL) {
    return (top->hasNegInit == 1) ? false : true;
  }

//	cout << "top: " << *top << endl;

	struct rusage usage;
	struct timeval start_time, end_time;
	long long time_diff;

	TIME_S(start_time);

	collect_cubes(top, true);

	bool res = true;

	// Stage 1: Syntactic check
	{
		for (auto& v: _collected_cubes) {
		  if (v->hasNegInit != DEFAULT_VAL) {
		    res = (v->hasNegInit == 1) ? false : true;
		  }
		  else {
				if (_neg_init.count(v)) {
					res = false;
			  	v->hasNegInit = 1;
				}
		  }
		  if (!res)
		  	break;
		}
	}

	// Stage 2: Use solver query SAT ? [ I & cube ]
	if (res)
	{
		InstL conjunct_ct;
		conjunct_ct = _conjunct_init;
		for (auto& v: _collected_cubes)
			conjunct_ct.push_back(v);
		conjunct_ct.push_back(_ve_assume);
		for (auto& v: _assume_T)
			conjunct_ct.push_back(v.first);

		for (InstL::iterator it3 = _negated_refs.begin(); it3 != _negated_refs.end(); ++it3) {
			if (!(*it3)->find_next())
				conjunct_ct.push_back(*it3);
		}
		Inst *ve_ct = OpInst::create(OpInst::LogAnd, conjunct_ct);
		SOLVER_CONTAIN int_solver(_abstract_mapper, AVR_EXTRA_IDX, false, regular);
		res = int_solver.check_sat(ve_ct, AB_QUERY_TIMEOUT, false);
	}

	TIME_E(start_time, end_time, _tb_ct_initial_time);

	top->hasNegInit = res ? 0 : 1;
	return res;
}
#endif




bool Reach::restrict_cube(Inst* full_cube, Inst* &gen_cube)
{
	InstL restrict_cube;
	collect_cubes(gen_cube, true);
	restrict_cube.swap(_collected_cubes);

	InstS initSet;
	for (auto& v: _conjunct_init)
		initSet.insert(v);

	bool changed = false;
	collect_cubes(full_cube, true);
	for (auto& v: _collected_cubes)
	{
		if (initSet.find(v) == initSet.end())
		{
			restrict_cube.push_back(v);
			changed = true;
			break;
		}
	}
	if (changed)
	{
		gen_cube = OpInst::create(OpInst::LogAnd, restrict_cube);
		cout << "\t\t(restricting cube to " << *gen_cube << ")" << endl;
	}
	return changed;
}

// return 0 in a normal operation
// return 1 if a counter-example is found <- this is a very complicated case.
int Reach::add_inits_to_gcube(Inst *cube, Inst *&gcube, bool tb_cube){
#ifdef ADD_INITS_TO_GCUBE_TB_CUBE_ENABLE
	if(tb_cube == true){
		InstL new_ch;
		OpInst* op_gcube = OpInst::as(gcube);
		if (op_gcube && (op_gcube->get_op() == OpInst::LogAnd)) {
			const InstL* g_ch = gcube->get_children();
			for (InstL::const_iterator it = g_ch->begin(); it != g_ch->end(); it++) {
//				cout << "Searching for " << *(*it) << " in _s_neg_inits" << endl;
				if(_s_negated_ff_inits.find(*it) != _s_negated_ff_inits.end()){
//					cout << "Found" << endl;
					return 0;
				}
//				cout << "Not found, inserting in new_ch" << endl;
				new_ch.push_back(*it);
			}
		}else{
//			cout << "Searching for " << *gcube << " in _s_neg_inits" << endl;
			if(_s_negated_ff_inits.find(gcube) != _s_negated_ff_inits.end()){
//				cout << "Found" << endl;
					return 0;
			}
//			cout << "Not found, inserting in new_ch" << endl;
			new_ch.push_back(gcube);
		}
//		cout << "new_ch: " << new_ch << endl;

//		cout << "Checking if gcube contains init states" << endl;
		if(cube_contain_inits(gcube) == false){
//			cout << "No" << endl;
			return 0;
		}
//		cout << "Yes" << endl;

		const InstL* gch = gcube->get_children();
		InstS gcubes;
//		cout << *gcube << endl;
//		cout << *cube << endl;

		/// Aman
		/// Following if needed if suppose there is only single bit positive literal in initial state I
		if (op_gcube && (op_gcube->get_op() == OpInst::LogAnd))
//		if (gch)
		{
			for (InstL::const_iterator git = gch->begin(); git != gch->end(); git++) {
//				cout << "Adding to gcubes: " << *(*git) << endl;
				gcubes.insert(*git);
			}
		}
		else
		{
			gcubes.insert(gcube);
		}
//		cout << "Gcubes (new): " << gcubes << endl;
		/// END

//		cout << "Iterating over children of cube: " << *cube << endl;
		const InstL* ch = cube->get_children();
		for (InstL::const_iterator it = ch->begin(); it != ch->end(); it++)
		{
//			cout << "Searching for " << *(*it) << " in gcubes" << endl;
			if(gcubes.find(*it) == gcubes.end()){
//				cout << "Not found, adding " << *(*it) << " to new_ch" << endl;
				new_ch.push_back(*it);

				gcube = OpInst::create(OpInst::LogAnd, new_ch);
//				cout << "New gcube: " << *gcube << endl;
//				cout << "Checking if gcube contains init states" << endl;
				if(cube_contain_inits(gcube) == false){
//					cout << "No" << endl;
					return 0;
				}
//				cout << "Yes" << endl;
			}
		}

		return 1;
	}else
#endif
	{
// 		OpInst* op = OpInst::as(cube);
// 		if (op && (op->get_op() == OpInst::LogAnd)) {
// 			// will be handled at the end of this function
// 		}else{
// 			if(cube_contain_inits(cube, tb_cube) == false){
// 				return 0;
// 			}else{
// 			// nothing we can do (original cube consists of only literal)
// 				return 1;
// 			}
// 		}

		InstL new_ch;
// 		OpInst* op_gcube = OpInst::as(gcube);
// 		if (op_gcube && (op_gcube->get_op() == OpInst::LogAnd)) {
// 			const InstL* ch = gcube->get_children();
// 			for (InstL::const_iterator it = ch->begin(); it != ch->end(); it++) {
// 				if(cube_contain_inits(*it, tb_cube) == false){
// 					return 0;
// 				}
// 				new_ch.push_back(*it);
// 			}
// 		}else{
			if(cube_contain_inits(gcube) == false){
				return 0;
			}
			new_ch.push_back(gcube);
// 		}

		// add a predicate to a gcube so that it does not contain init states
		const InstL* ch = cube->get_children();
		InstS ffs;
		InstS regs;
		for (InstL::const_iterator it = ch->begin(); it != ch->end(); it++) {
			Inst *tve = *it;
			OpInst* op = OpInst::as(tve);
			if (op && (op->get_op() == OpInst::LogNot)) {
				tve = tve->get_children()->front();
			}
			SigInst *sig = SigInst::as(tve);
			if(sig){
				ffs.insert(*it);
			}else{
				regs.insert(*it);
			}
		}

		// I put higher priority to the bit-level literals
		// In addition, the priority among the bit-level literals is fixed
		for (InstL::reverse_iterator it = _l_negated_ff_inits.rbegin(); it != _l_negated_ff_inits.rend(); it++) {
			if(ffs.find(*it) != ffs.end()){
				new_ch.push_back(*it);
				gcube = OpInst::create(OpInst::LogAnd, new_ch);
				return 0;
			}
		}

	// 	for (InstL::iterator it = _l_negated_ff_inits.begin(); it != _l_negated_ff_inits.end(); it++) {
	// 		if(ffs.find(*it) != ffs.end()){
	// 			new_ch.push_back(*it);
	// 			gcube = OpInst::create(OpInst::LogAnd, new_ch);
	// 			return 0;
	// 		}
	// 	}
		for (InstS::iterator it = regs.begin(); it != regs.end(); it++) {
			if(cube_contain_inits(*it) == false){
				new_ch.push_back(*it);
				gcube = OpInst::create(OpInst::LogAnd, new_ch);
				return 0;
			}
		}
	}
// 	cout << "TT  gcube: " << *gcube << endl;
// 	cout << "TT  cube: " << *cube << endl;
	return 1;
}

void Reach::dump_execution_time(int exit_val) {
	cout.setf(ios::fixed, ios::floatfield);
	cout.precision(2);

//	dump_hm_sizes();

	/****************************************************************************************************
	 * Block	: # of CTI checks
	 * BlockT	: BlockS + BlockU
	 * BlockS	: # of SAT prop checks
	 * BlockU	: # of UNSAT prop checks
	 *
	 * Oblig	: # of backward-reachability checks
	 * ObligT	: ObligS + ObligU
	 * ObligS	: # of SAT backward-reachability checks
	 * ObligU	: # of UNSAT backward-reachability checks
	 *
	 * FPT		: # of solver calls during forward propagation
	 * FPS		: # of SAT solver calls during forward propagation
	 * FPU		: # of UNSAT solver calls during forward propagation
	 * MUST		: # of solver calls during MUS(es) derivations including the derivations during DP refinement
	 * MUSS		: # of SAT solver calls during MUS(es) derivations including the derivations during DP refinement
	 * MUSU		: # of UNSAT solver calls during MUS(es) derivations including the derivations during DP refinement
	 *
	 * CallT	: # of every solver call including FPT but excluding MUST (MUST + CallT is # of total solver calls)
	 * CallS	: # of every SAT solver call including FPS but excluding MUSS
	 * CallU	: # of every UNSAT solver call including FPU but excluding MUSU
	 *
	 * All_clauses	: # of clauses derived during reachability analysis
	 * All_literals	: # of literals derived during reachability analysis
	 * Clauses		: # of clauses left at the end (i.e. survived from sub-sumption checks)
	 * Literals		: # of literals left at the end (i.e. survived from sub-sumption checks)
	 *
	 * *************************************************************************************************/


	//return;
//  2 : 0 20 4 s: 24
//L 2 : 0 60 8 s: 68
//Block =   25  Oblig =    29  all_cls =    24  Call =   141 (sat=78.7%)  Start =   0  Clauses =    24  Literals =    68
	
	//cout << "/*====================================" << endl;
	//_nFramesL.clear();

	print_frame_summary(_frame_idx);
#ifdef PRINT_FRAME_SUMMARY
	cerr << "\r" << endl;
#endif

	int sum_cubes = 0;
	for (int i = 0; i <= _frame_idx; i++)
	{
		sum_cubes += _cubes[i].size();
	}
	for (int i = _frame_idx+1; i < _cubes.size(); i++) {
		sum_cubes += _cubes[i].size();
	}

	int sum_literals = 0;

	for (int i = 0; i < _cubes.size(); i++) {
		int literals = 0;
		for(vector<CLAUSE>::iterator pc_it = _cubes[i].begin(); pc_it != _cubes[i].end(); pc_it++){
			Inst *tve = (*pc_it).cube;
			if (!tve)
				assert(0);

			literals += (*pc_it).literals.size();

		}
		sum_literals += literals;
	}

#ifdef ARM_RELEASE
	cout << " s: " << sum_literals << endl;
#else
	cout.precision(6);
	//cout << "memUsed(): " << memUsed() << endl;
	cout.precision(2);
#endif

	_resFile << "#constants-total:\t" << NumInst::hm_NumInst.size() << endl;
	_resFile << "#uf-total:\t" << OpInst::_numUF << endl;
	_resFile << "#extract-total:\t" << ExInst::hm_ExInst.size() << endl;
	_resFile << "#concat-total:\t" << OpInst::_numConcat << endl;

//	for (SigInst::StrVM::iterator it = SigInst::hm_SigInst.begin(); it != SigInst::hm_SigInst.end(); it++)
//		cout << "Sig: " << *((*it).second) << endl;
//	for (NumInst::NumHashM::iterator it = NumInst::hm_NumInst.begin(); it != NumInst::hm_NumInst.end(); it++)
//		cout << "Num: " << *((*it).second) << endl;
//	for (OpInst::OpHashM::iterator it = ExInst::hm_ExInst.begin(); it != ExInst::hm_ExInst.end(); it++)
//		cout << "Ex: " << *((*it).second) << endl;
//	for (OpInst::OpHashM::iterator it = OpInst::hm_OpInst.begin(); it != OpInst::hm_OpInst.end(); it++)
//	{
//		if ((*it).second->get_euf_func_name() != "0")
//			cout << "Op: " << *((*it).second) << endl;
//	}
//	for (OpInst::OpHashMM::iterator it = OpInst::hm_ETCInst.begin(); it != OpInst::hm_ETCInst.end(); it++)
//	{
//		if ((*it).second->get_euf_func_name() != "0")
//			cout << "Op: " << *((*it).second) << endl;
//	}

	AVR_LOG(15, 0, endl);
	AVR_LOG(15, 0, "-----------" << endl);
	AVR_LOG(15, 0, "Refinements" << endl);
	AVR_LOG(15, 0, "-----------" << endl);
	int count = 0;
	for (auto& r: _negated_refs)
	{
		count++;
		AVR_LOG(15, 0, "[" << count << "]\t" << (*r) << endl);
	}
	AVR_LOG(15, 0, "-----------" << endl);

	if(exit_val == EXIT_HOLD){
		check_correct_lemmas();
		check_correctness();
		Inst::g_result = h;
	}
	/// Aman
	else if (exit_val == EXIT_VIOL)
	{
		check_correct_lemmas();
		if (Config::g_print_witness) {
			print_cex();
		}
		Inst::g_result = v;
	}
	else if (exit_val == EXIT_HOLD_TRIV)
	{
		Inst::g_result = h_triv;
	}
	/// END

	struct rusage usage;
	struct timeval end_time;
	long long time_diff;

	getrusage(RUSAGE_SELF, &usage);
	timeradd(&usage.ru_utime, &usage.ru_stime, &end_time);
	time_diff = Timevaldiff(&_start_time, &end_time);
	long long total_time = time_diff;

	_totalTime = total_time;
//	_numRefinements = _accum_dp_lemmas;

//	getrusage(RUSAGE_SELF, &usage);
//	end_time = usage.ru_utime;
//	time_diff = Timevaldiff(&_start_time, &end_time);
	double elapsed_time = ((double) total_time / 1000000);
	unsigned memory_usage = usage.ru_maxrss/1024;	// accurate memory usage in Mbytes
	if (_global_memory_limit < memory_usage)
		Inst::g_result = f_mo;

	cout << " s: " << sum_literals << ", mem: " << memory_usage << ", time: " << elapsed_time << endl;

#ifdef ARM_RELEASE


	int total_solver_calls = Solver::num_scalls_unsat + Solver::num_scalls_sat;
	int num_scalls_sat_mus = Solver::num_scalls_sat_mus_pme + Solver::num_scalls_sat_muses_dpr + Solver::num_scalls_sat_muses_reach;
	int num_scalls_unsat_mus = Solver::num_scalls_unsat_mus_pme + Solver::num_scalls_unsat_muses_dpr + Solver::num_scalls_unsat_muses_reach;
	int total_solver_calls_mus = num_scalls_unsat_mus + num_scalls_sat_mus;

	cout << endl << "CTI= " << _nBlocks << " Oblig= " << _nObligs;

	cout << " Solver_calls= " << (total_solver_calls + total_solver_calls_mus) << " (SAT =" << (Solver::num_scalls_sat + num_scalls_sat_mus) << ")" << endl;

	cout << "All_clauses= " << _nCubes << "	All_literals= " << _nLiterals << endl;
	cout << "Learnt_clauses= " << sum_cubes << " Learnt_Literals= " << sum_literals << endl;
// 	cout.precision(6);
// 	cout << "Mem= " << memory_usage << "MB Time= " << elapsed_time << "sec" << endl;
// 	cout.precision(2);
	cout << endl;


	if(_nFramesL.size() <= 1){
		cout << "Frames explored (" << _nFramesL.size() << " datapath refinement) : " << endl;
	}else{
		cout << "Frames explored (" << _nFramesL.size() << " datapath refinements) : " << endl;
	}
	for (list<int>::iterator it = _nFramesL.begin(); it != _nFramesL.end(); it++) {
		cout << *it << " ";
	}
	cout << endl << endl;
	return;

#else

	cout << "Frames explored (" << _nFramesL.size() << " datapath refinements) : " << endl;
	for (list<int>::iterator it = _nFramesL.begin(); it != _nFramesL.end(); it++) {
		cout << *it << " ";
	}
	cout << endl;

	cout << "CEXT lengths (" << _nLegnthsCEXTL.size() << " feasibility checks) : " << endl;
	for (list<int>::iterator it = _nLegnthsCEXTL.begin(); it != _nLegnthsCEXTL.end(); it++) {
		cout << *it << " ";
	}
	cout << endl;

	cout << "DP lemmas (" << _nDPLemmasL.size() << " feasibility checks) : " << endl;
	for (list<int>::iterator it = _nDPLemmasL.begin(); it != _nDPLemmasL.end(); it++) {
		cout << *it << " ";
	}
	cout << endl;



//Block =    2  BlockT =     4  BlockS =     2  BlockU =     2  Oblig =    6  ObligT=     6  ObligS =     5  ObligU =     1  FPT =     1  FPS =     1  FPU =     0  MUST =     0  MUS_T =     0  MUSS =     0  MUSU =     0  Start =   0  All_clauses =     1  Clauses =     1  Literals =     1

	// Block = 2508  Oblig =  4694  Clause =  3842  Call = 26228 (sat=49.1%)  Start =  75
	int total_solver_calls = Solver::num_scalls_unsat + Solver::num_scalls_sat + Solver::num_scalls_timeout;

	int num_scalls_ab_mus = Solver::num_ab_sat_mus + Solver::num_ab_unsat_mus;
	int num_scalls_bv_mus = Solver::num_bv_sat_mus + Solver::num_bv_unsat_mus;

	int num_scalls_sat_mus = Solver::num_ab_sat_mus + Solver::num_bv_sat_mus;
	int num_scalls_unsat_mus = Solver::num_ab_unsat_mus + Solver::num_bv_unsat_mus;

	int total_solver_calls_mus = num_scalls_unsat_mus + num_scalls_sat_mus;
	int total_solver_calls_mus_sim = Reach::num_scalls_unsat_mus_sim + Reach::num_scalls_sat_mus_sim;
	int total_solver_calls_muses_dpr = Reach::num_scalls_unsat_muses_dpr + Reach::num_scalls_sat_muses_dpr;
	int total_solver_calls_muses_reach = Reach::num_scalls_unsat_muses_reach + Reach::num_scalls_sat_muses_reach;

//	int total_solver_calls_ct = Solver::num_scalls_unsat_ct + Solver::num_scalls_sat_ct;
	cout << "Block= " << _nBlocks << " BlockT= " << (_nBlocksS + _nBlocksU) << " BlockS= " << _nBlocksS << " BlockU= " << _nBlocksU;
	cout << " Oblig= " << _nObligs << " ObligT= " << (_nObligsS + _nObligsU) << " ObligS= " << _nObligsS << " ObligU= " << _nObligsU;
	cout << " FPT= " << (Solver::num_scalls_sat_fp + Solver::num_scalls_unsat_fp) << " FPS= " << Solver::num_scalls_sat_fp << " FPU= " << Solver::num_scalls_unsat_fp;
	cout << " CallT= " << total_solver_calls << " CallS= " << Solver::num_scalls_sat << " CallU= " << Solver::num_scalls_unsat;
	cout << " MUST= " << total_solver_calls_mus << " MUSS= " << num_scalls_sat_mus << " MUSU= " << num_scalls_unsat_mus;

	cout << " sMUST= " << total_solver_calls_mus_sim << " sMUSS= " << Reach::num_scalls_sat_mus_sim << " sMUSU= " << Reach::num_scalls_unsat_mus_sim;
	cout << " dMUST= " << total_solver_calls_muses_dpr << " dMUSS= " << Reach::num_scalls_sat_muses_dpr << " dMUSU= " << Reach::num_scalls_unsat_muses_dpr;
	cout << " rMUST= " << total_solver_calls_muses_reach << " rMUSS= " << Reach::num_scalls_sat_muses_reach << " rMUSU= " << Reach::num_scalls_unsat_muses_reach;

	cout << " All_clauses= " << _nCubes << " All_literals= " << _nLiterals;
	cout << " Clauses= " << sum_cubes << " Literals= " << sum_literals;
	cout << " DPLemmas= " << _accum_dp_lemmas << " DPrefsNoDPL= " << _num_dp_refs_zero_lemmas << " DPRefs= " << _nFramesL.size();
	cout << endl << endl;
	cout << "pme_fail: " << _pme_fail_cnt << ", pme_succ: " << _pme_succ_cnt << ", lit_before: " << _pme_literals_before << ", lit_after: " << _pme_literals_after << endl;
	cout << "coi_before: " << _coi_literals_before << ", coi_after: " << _coi_literals_after << endl;
	cout << "mus_before: " << _mus_before << " mus_lit: " << _mus_lit << " mus_cls: " << _mus_cls << " mus_cnt: " << _mus_cnt << endl;

	cout << "S+M\tCall = " << total_solver_calls + total_solver_calls_mus << " (sat=" << Solver::num_scalls_sat
			+ num_scalls_sat_mus << ", " << ((double) (Solver::num_scalls_sat + num_scalls_sat_mus) * 100
			/ (total_solver_calls + total_solver_calls_mus)) << "%)" << endl;
	cout << "SAT\tCall = " << total_solver_calls << " (sat=" << Solver::num_scalls_sat << ", "
			<< ((double) Solver::num_scalls_sat * 100 / total_solver_calls) << "%)" << endl;
	cout << "MUS\tCall = " << total_solver_calls_mus << " (sat=" << num_scalls_sat_mus << ", "
			<< ((double) num_scalls_sat_mus * 100 / total_solver_calls_mus) << "%)" << endl;
// 	cout << "CT\tCall = " << total_solver_calls_ct << " (sat=" << Solver::num_scalls_sat_ct << ", "
// 			<< ((double) Solver::num_scalls_sat_ct * 100 / total_solver_calls_ct) << "%)" << endl;

	_resFile << "#cti-check:\t" << (_nBlocksS + _nBlocksU) << endl;
	_resFile << "#cti-check-sat:\t" << _nBlocksS << endl;
	_resFile << "#cti-check-unsat:\t" << _nBlocksU << endl;

	_resFile << "br-#check:\t" << _nObligs << endl;
	_resFile << "br-#check-sat:\t" << _nObligsS << endl;
	_resFile << "br-#check-unsat:\t" << _nObligsU << endl;

	_resFile << "br-total-clauses:\t" << _nCubes << endl;
	_resFile << "br-total-literals:\t" << _nLiterals << endl;

//	cout << "bp_reach_time:\t\t" << ((double) _bp_reach_time / 1000000) << " (" << (double) _bp_reach_time
//			* 100 / total_time << "%)" << endl;
// 	cout << "bp_SAT_camus_time:\t" << ((double) _bp_SAT_camus_time / 1000000) << " ("
// 			<< (double) _bp_SAT_camus_time * 100 / total_time << "%)" << endl;
//	cout << "bp_UNSAT_camus_time:\t" << ((double) _bp_UNSAT_camus_time / 1000000) << " ("
//			<< (double) _bp_UNSAT_camus_time * 100 / total_time << "%)" << endl;
//	cout << "bp_gidx_time:\t\t" << ((double) _bp_gidx_time / 1000000) << " (" << (double) _bp_gidx_time
//			* 100 / total_time << "%)" << endl;
//	cout << "bp_ct_time:\t\t" << ((double) _bp_ct_time / 1000000) << " (" << (double) _bp_ct_time * 100
//			/ total_time << "%)" << endl;

	cout << endl << "Detailed Stats:" << endl;

	cout << endl << "  (reachability)" << endl;

	cout << "\t#Frame Restrictions:\t" << _numFrameRes << endl;
	cout << "\t#TB                :\t" << _numTbCalls << endl;
	cout << "\t#cubes-subsumed    :\t" << CLAUSE::_numSubsumedCube << endl;
	cout << "\t#context reset     :\t" << numResetContext << endl;
#ifdef _Y2
	cout << "\t#Y2 reset          :\t" << y2_API::g_num_reset << endl;
#endif
	cout << "\t#frame solver reset:\t" << FRAME_SOLVER::numResetFrames << endl;

	double avg_sz_frame_restrict = (_numFrameRes != 0) ? ((double) _sumFrameRes / _numFrameRes) : 0;
	cout << "\tavg-sz-frame-restriction:  \t" << avg_sz_frame_restrict << endl;

	cout << endl;

	double avg_sz_ab_cube = (_numTbCalls != 0) ? ((double) _sizeAbCube / _numTbCalls) : 0;
	cout << "\tavg-sz-ab-cube:  \t" << avg_sz_ab_cube << endl;

	double perc_t1_ab_cube = (_sizeAbCube != 0) ? (((double) _szT1 * 100) / _sizeAbCube) : 0;
	double perc_t1_sel_ab_cube = (_sumFrameRes != 0) ? (((double) _selT1 * 100) / _sumFrameRes) : 0;
	cout << "\t\t%t1-ab-cube:   \t" << perc_t1_ab_cube << "%\t[sel: " << perc_t1_sel_ab_cube << "% ]" << endl;

	double perc_t2_ab_cube = (_sizeAbCube != 0) ? (((double) _szT2 * 100) / _sizeAbCube) : 0;
	double perc_t2_sel_ab_cube = (_sumFrameRes != 0) ? (((double) _selT2 * 100) / _sumFrameRes) : 0;
	cout << "\t\t%t2-ab-cube:   \t" << perc_t2_ab_cube << "%\t[sel: " << perc_t2_sel_ab_cube << "% ]" << endl;

	double perc_t3_ab_cube = (_sizeAbCube != 0) ? (((double) _szT3 * 100) / _sizeAbCube) : 0;
	double perc_t3_sel_ab_cube = (_sumFrameRes != 0) ? (((double) _selT3 * 100) / _sumFrameRes) : 0;
	cout << "\t\t%t3-ab-cube:   \t" << perc_t3_ab_cube << "%\t[sel: " << perc_t3_sel_ab_cube << "% ]" << endl;

	double perc_t4_ab_cube = (_sizeAbCube != 0) ? (((double) _szT4 * 100) / _sizeAbCube) : 0;
	double perc_t4_sel_ab_cube = (_sumFrameRes != 0) ? (((double) _selT4 * 100) / _sumFrameRes) : 0;
	cout << "\t\t%t4-ab-cube:   \t" << perc_t4_ab_cube << "%\t[sel: " << perc_t4_sel_ab_cube << "% ]" << endl;

	cout << endl;


  cout << "\t\tab-cube info:\t" << endl;
	double perc_coi_sig_eq_sig_ab_cube = (_sizeAbCube != 0) ? (((double) _cube_ab_SigEqSig * 100) / _sizeAbCube) : 0;
	double perc_coi_sig_eq_sig_sel_ab_cube = (_sumFrameRes != 0) ? (((double) _cube_ab_SigEqSig_sel * 100) / _sumFrameRes) : 0;
	cout << "\t\t\ts == s:\t" << perc_coi_sig_eq_sig_ab_cube << "%\t[sel: " << perc_coi_sig_eq_sig_sel_ab_cube << "% ]" << endl;

  double perc_coi_sig_eq_num_ab_cube = (_sizeAbCube != 0) ? (((double) _cube_ab_SigEqNum * 100) / _sizeAbCube) : 0;
  double perc_coi_sig_eq_num_sel_ab_cube = (_sumFrameRes != 0) ? (((double) _cube_ab_SigEqNum_sel * 100) / _sumFrameRes) : 0;
  cout << "\t\t\ts == n:\t" << perc_coi_sig_eq_num_ab_cube << "%\t[sel: " << perc_coi_sig_eq_num_sel_ab_cube << "% ]" << endl;

  double perc_coi_sig_eq_oth_ab_cube = (_sizeAbCube != 0) ? (((double) _cube_ab_SigEqOther * 100) / _sizeAbCube) : 0;
  double perc_coi_sig_eq_oth_sel_ab_cube = (_sumFrameRes != 0) ? (((double) _cube_ab_SigEqOther_sel * 100) / _sumFrameRes) : 0;
  cout << "\t\t\ts == o:\t" << perc_coi_sig_eq_oth_ab_cube << "%\t[sel: " << perc_coi_sig_eq_oth_sel_ab_cube << "% ]" << endl;

  double perc_coi_num_eq_oth_ab_cube = (_sizeAbCube != 0) ? (((double) _cube_ab_NumEqOther * 100) / _sizeAbCube) : 0;
  double perc_coi_num_eq_oth_sel_ab_cube = (_sumFrameRes != 0) ? (((double) _cube_ab_NumEqOther_sel * 100) / _sumFrameRes) : 0;
  cout << "\t\t\tn == o:\t" << perc_coi_num_eq_oth_ab_cube << "%\t[sel: " << perc_coi_num_eq_oth_sel_ab_cube << "% ]" << endl;

  double perc_coi_oth_eq_oth_ab_cube = (_sizeAbCube != 0) ? (((double) _cube_ab_OtherEqOther * 100) / _sizeAbCube) : 0;
  double perc_coi_oth_eq_oth_sel_ab_cube = (_sumFrameRes != 0) ? (((double) _cube_ab_OtherEqOther_sel * 100) / _sumFrameRes) : 0;
  cout << "\t\t\to == o:\t" << perc_coi_oth_eq_oth_ab_cube << "%\t[sel: " << perc_coi_oth_eq_oth_sel_ab_cube << "% ]" << endl;


  double perc_coi_sig_neq_sig_ab_cube = (_sizeAbCube != 0) ? (((double) _cube_ab_SigNeqSig * 100) / _sizeAbCube) : 0;
  double perc_coi_sig_neq_sig_sel_ab_cube = (_sumFrameRes != 0) ? (((double) _cube_ab_SigNeqSig_sel * 100) / _sumFrameRes) : 0;
  cout << "\t\t\ts != s:\t" << perc_coi_sig_neq_sig_ab_cube << "%\t[sel: " << perc_coi_sig_neq_sig_sel_ab_cube << "% ]" << endl;

  double perc_coi_sig_neq_num_ab_cube = (_sizeAbCube != 0) ? (((double) _cube_ab_SigNeqNum * 100) / _sizeAbCube) : 0;
  double perc_coi_sig_neq_num_sel_ab_cube = (_sumFrameRes != 0) ? (((double) _cube_ab_SigNeqNum_sel * 100) / _sumFrameRes) : 0;
  cout << "\t\t\ts != n:\t" << perc_coi_sig_neq_num_ab_cube << "%\t[sel: " << perc_coi_sig_neq_num_sel_ab_cube << "% ]" << endl;

  double perc_coi_sig_neq_oth_ab_cube = (_sizeAbCube != 0) ? (((double) _cube_ab_SigNeqOther * 100) / _sizeAbCube) : 0;
  double perc_coi_sig_neq_oth_sel_ab_cube = (_sumFrameRes != 0) ? (((double) _cube_ab_SigNeqOther_sel * 100) / _sumFrameRes) : 0;
  cout << "\t\t\ts != o:\t" << perc_coi_sig_neq_oth_ab_cube << "%\t[sel: " << perc_coi_sig_neq_oth_sel_ab_cube << "% ]" << endl;

  double perc_coi_num_neq_oth_ab_cube = (_sizeAbCube != 0) ? (((double) _cube_ab_NumNeqOther * 100) / _sizeAbCube) : 0;
  double perc_coi_num_neq_oth_sel_ab_cube = (_sumFrameRes != 0) ? (((double) _cube_ab_NumNeqOther_sel * 100) / _sumFrameRes) : 0;
  cout << "\t\t\tn != o:\t" << perc_coi_num_neq_oth_ab_cube << "%\t[sel: " << perc_coi_num_neq_oth_sel_ab_cube << "% ]" << endl;

  double perc_coi_oth_neq_oth_ab_cube = (_sizeAbCube != 0) ? (((double) _cube_ab_OtherNeqOther * 100) / _sizeAbCube) : 0;
  double perc_coi_oth_neq_oth_sel_ab_cube = (_sumFrameRes != 0) ? (((double) _cube_ab_OtherNeqOther_sel * 100) / _sumFrameRes) : 0;
  cout << "\t\t\to != o:\t" << perc_coi_oth_neq_oth_ab_cube << "%\t[sel: " << perc_coi_oth_neq_oth_sel_ab_cube << "% ]" << endl;

  double perc_coi_sig_bool_ab_cube = (_sizeAbCube != 0) ? (((double) _cube_ab_SigBool * 100) / _sizeAbCube) : 0;
  double perc_coi_sig_bool_sel_ab_cube = (_sumFrameRes != 0) ? (((double) _cube_ab_SigBool_sel * 100) / _sumFrameRes) : 0;
  cout << "\t\t\ts bool:\t" << perc_coi_sig_bool_ab_cube << "%\t[sel: " << perc_coi_sig_bool_sel_ab_cube << "% ]" << endl;

  double perc_coi_up_ab_cube = (_sizeAbCube != 0) ? (((double) _cube_ab_Up * 100) / _sizeAbCube) : 0;
  double perc_coi_up_sel_ab_cube = (_sumFrameRes != 0) ? (((double) _cube_ab_Up_sel * 100) / _sumFrameRes) : 0;
  cout << "\t\t\tup    :\t" << perc_coi_up_ab_cube << "%\t[sel: " << perc_coi_up_sel_ab_cube << "% ]" << endl;

  double perc_coi_oth_ab_cube = (_sizeAbCube != 0) ? (((double) _cube_ab_Other * 100) / _sizeAbCube) : 0;
  double perc_coi_oth_sel_ab_cube = (_sumFrameRes != 0) ? (((double) _cube_ab_Other_sel * 100) / _sumFrameRes) : 0;
  cout << "\t\t\toth   :\t" << perc_coi_oth_ab_cube << "%\t[sel: " << perc_coi_oth_sel_ab_cube << "% ]" << endl;

  cout << endl;


  double perc_coi_ab_cube = (_sizeAbCube != 0) ? (((double) _sizeCoiAbCube * 100) / _sizeAbCube) : 0;
  double perc_coi_sel_ab_cube = (_sumFrameRes != 0) ? (((double) _selCoiAbCube * 100) / _sumFrameRes) : 0;
  cout << "\t\t%coi-ab-cube  :\t" << perc_coi_ab_cube << "%\t[sel: " << perc_coi_sel_ab_cube << "% ]" << endl;

  double perc_coi_sig_eq_ab_cube = (_sizeAbCube != 0) ? (((double) _sizeCoiSigEqAbCube * 100) / _sizeAbCube) : 0;
  double perc_coi_sig_eq_sel_ab_cube = (_sumFrameRes != 0) ? (((double) _selCoiSigEqAbCube * 100) / _sumFrameRes) : 0;
  cout << "\t\t\ts (==):\t" << perc_coi_sig_eq_ab_cube << "%\t[sel: " << perc_coi_sig_eq_sel_ab_cube << "% ]" << endl;

  double perc_coi_sig_neq_ab_cube = (_sizeAbCube != 0) ? (((double) _sizeCoiSigNeqAbCube * 100) / _sizeAbCube) : 0;
  double perc_coi_sig_neq_sel_ab_cube = (_sumFrameRes != 0) ? (((double) _selCoiSigNeqAbCube * 100) / _sumFrameRes) : 0;
  cout << "\t\t\ts (!=):\t" << perc_coi_sig_neq_ab_cube << "%\t[sel: " << perc_coi_sig_neq_sel_ab_cube << "% ]" << endl;

  double perc_coi_num_eq_ab_cube = (_sizeAbCube != 0) ? (((double) _sizeCoiNumEqAbCube * 100) / _sizeAbCube) : 0;
  double perc_coi_num_eq_sel_ab_cube = (_sumFrameRes != 0) ? (((double) _selCoiNumEqAbCube * 100) / _sumFrameRes) : 0;
  cout << "\t\t\tn (==):\t" << perc_coi_num_eq_ab_cube << "%\t[sel: " << perc_coi_num_eq_sel_ab_cube << "% ]" << endl;

  double perc_coi_num_neq_ab_cube = (_sizeAbCube != 0) ? (((double) _sizeCoiNumNeqAbCube * 100) / _sizeAbCube) : 0;
  double perc_coi_num_neq_sel_ab_cube = (_sumFrameRes != 0) ? (((double) _selCoiNumNeqAbCube * 100) / _sumFrameRes) : 0;
  cout << "\t\t\tn (!=):\t" << perc_coi_num_neq_ab_cube << "%\t[sel: " << perc_coi_num_neq_sel_ab_cube << "% ]" << endl;

  double perc_coi_other_ab_cube = (_sizeAbCube != 0) ? (((double) _sizeCoiOtherAbCube * 100) / _sizeAbCube) : 0;
  double perc_coi_other_sel_ab_cube = (_sumFrameRes != 0) ? (((double) _selCoiOtherAbCube * 100) / _sumFrameRes) : 0;
  cout << "\t\t\tother :\t" << perc_coi_other_ab_cube << "%\t[sel: " << perc_coi_other_sel_ab_cube << "% ]" << endl;


  double perc_pred_ab_cube = (_sizeAbCube != 0) ? (((double) _sizePredAbCube * 100) / _sizeAbCube) : 0;
	double perc_pred_sel_ab_cube = (_sumFrameRes != 0) ? (((double) _selPredAbCube * 100) / _sumFrameRes) : 0;
	cout << "\t\t%pred-ab-cube :\t" << perc_pred_ab_cube << "%\t[sel: " << perc_pred_sel_ab_cube << "% ]" << endl;


	double perc_fproj_ab_cube = (_sizeAbCube != 0) ? (((double) _sizefProjAbCube * 100) / _sizeAbCube) : 0;
	double perc_fproj_sel_ab_cube = (_sumFrameRes != 0) ? (((double) _selfProjAbCube * 100) / _sumFrameRes) : 0;
	cout << "\t\t%fproj-ab-cube:\t" << perc_fproj_ab_cube << "%\t[sel: " << perc_fproj_sel_ab_cube << "% ]" << endl;

	double perc_fproj_sig_eq_ab_cube = (_sizeAbCube != 0) ? (((double) _sizefProjSigEqAbCube * 100) / _sizeAbCube) : 0;
	double perc_fproj_sig_eq_sel_ab_cube = (_sumFrameRes != 0) ? (((double) _selfProjSigEqAbCube * 100) / _sumFrameRes) : 0;
	cout << "\t\t\ts (==):\t" << perc_fproj_sig_eq_ab_cube << "%\t[sel: " << perc_fproj_sig_eq_sel_ab_cube << "% ]" << endl;

	double perc_fproj_sig_neq_ab_cube = (_sizeAbCube != 0) ? (((double) _sizefProjSigNeqAbCube * 100) / _sizeAbCube) : 0;
	double perc_fproj_sig_neq_sel_ab_cube = (_sumFrameRes != 0) ? (((double) _selfProjSigNeqAbCube * 100) / _sumFrameRes) : 0;
	cout << "\t\t\ts (!=):\t" << perc_fproj_sig_neq_ab_cube << "%\t[sel: " << perc_fproj_sig_neq_sel_ab_cube << "% ]" << endl;

	double perc_fproj_num_eq_ab_cube = (_sizeAbCube != 0) ? (((double) _sizefProjNumEqAbCube * 100) / _sizeAbCube) : 0;
	double perc_fproj_num_eq_sel_ab_cube = (_sumFrameRes != 0) ? (((double) _selfProjNumEqAbCube * 100) / _sumFrameRes) : 0;
	cout << "\t\t\tn (==):\t" << perc_fproj_num_eq_ab_cube << "%\t[sel: " << perc_fproj_num_eq_sel_ab_cube << "% ]" << endl;

	double perc_fproj_num_neq_ab_cube = (_sizeAbCube != 0) ? (((double) _sizefProjNumNeqAbCube * 100) / _sizeAbCube) : 0;
	double perc_fproj_num_neq_sel_ab_cube = (_sumFrameRes != 0) ? (((double) _selfProjNumNeqAbCube * 100) / _sumFrameRes) : 0;
	cout << "\t\t\tn (!=):\t" << perc_fproj_num_neq_ab_cube << "%\t[sel: " << perc_fproj_num_neq_sel_ab_cube << "% ]" << endl;


	double perc_proj_ab_cube = (_sizeAbCube != 0) ? (((double) _sizeProjAbCube * 100) / _sizeAbCube) : 0;
	double perc_proj_sel_ab_cube = (_sumFrameRes != 0) ? (((double) _selProjAbCube * 100) / _sumFrameRes) : 0;
	cout << "\t\t%proj-ab-cube :\t" << perc_proj_ab_cube << "%\t[sel: " << perc_proj_sel_ab_cube << "% ]" << endl;

	double perc_proj_sig_eq_ab_cube = (_sizeAbCube != 0) ? (((double) _sizeProjSigEqAbCube * 100) / _sizeAbCube) : 0;
	double perc_proj_sig_eq_sel_ab_cube = (_sumFrameRes != 0) ? (((double) _selProjSigEqAbCube * 100) / _sumFrameRes) : 0;
	cout << "\t\t\ts (==):\t" << perc_proj_sig_eq_ab_cube << "%\t[sel: " << perc_proj_sig_eq_sel_ab_cube << "% ]" << endl;

	double perc_proj_sig_neq_ab_cube = (_sizeAbCube != 0) ? (((double) _sizeProjSigNeqAbCube * 100) / _sizeAbCube) : 0;
	double perc_proj_sig_neq_sel_ab_cube = (_sumFrameRes != 0) ? (((double) _selProjSigNeqAbCube * 100) / _sumFrameRes) : 0;
	cout << "\t\t\ts (!=):\t" << perc_proj_sig_neq_ab_cube << "%\t[sel: " << perc_proj_sig_neq_sel_ab_cube << "% ]" << endl;

	double perc_proj_num_eq_ab_cube = (_sizeAbCube != 0) ? (((double) _sizeProjNumEqAbCube * 100) / _sizeAbCube) : 0;
	double perc_proj_num_eq_sel_ab_cube = (_sumFrameRes != 0) ? (((double) _selProjNumEqAbCube * 100) / _sumFrameRes) : 0;
	cout << "\t\t\tn (==):\t" << perc_proj_num_eq_ab_cube << "%\t[sel: " << perc_proj_num_eq_sel_ab_cube << "% ]" << endl;

	double perc_proj_num_neq_ab_cube = (_sizeAbCube != 0) ? (((double) _sizeProjNumNeqAbCube * 100) / _sizeAbCube) : 0;
	double perc_proj_num_neq_sel_ab_cube = (_sumFrameRes != 0) ? (((double) _selProjNumNeqAbCube * 100) / _sumFrameRes) : 0;
	cout << "\t\t\tn (!=):\t" << perc_proj_num_neq_ab_cube << "%\t[sel: " << perc_proj_num_neq_sel_ab_cube << "% ]" << endl;


	double perc_subs_ab_cube = (_sizeAbCube != 0) ? (((double) _sizeSubsAbCube * 100) / _sizeAbCube) : 0;
	double perc_subs_sel_ab_cube = (_sumFrameRes != 0) ? (((double) _selSubsAbCube * 100) / _sumFrameRes) : 0;
	cout << "\t\t%subs-ab-cube :\t" << perc_subs_ab_cube << "%\t[sel: " << perc_subs_sel_ab_cube << "% ]" << endl;


	double avg_num_sv_ab_cube = (_numTbCalls != 0) ? (_numSvAbCube / _numTbCalls) : 0;
	cout << "\tavg-#sv-ab-cube:  \t" << avg_num_sv_ab_cube << endl;

	double avg_tsb_ab_cube = (_numTbCalls != 0) ? (_tsbSvAbCube / _numTbCalls) : 0;
	cout << "\tavg-tsb-ab-cube:  \t" << avg_tsb_ab_cube << endl;

	double relevantPercent = (_queryT != 0) ? (((double) _relevantT * 100) / _queryT) : 0;
	cout << "\trelevancy:       \t" << relevantPercent << "%" << endl;

	cout << endl;

	double avg_sz_cc_cube = (_numTbCalls != 0) ? (_sizeCcCube / _numTbCalls) : 0;
	cout << "\tavg-sz-cc-cube:  \t" << avg_sz_cc_cube << endl;

	double perc_coi_cc_cube = (_sizeCcCube != 0) ? (((double) _sizeCoiCcCube * 100) / _sizeCcCube) : 0;
	cout << "\t\t%coi-cc-cube  :\t" << perc_coi_cc_cube << "%" << endl;

	double perc_pred_cc_cube = (_sizeCcCube != 0) ? (((double) _sizePredCcCube * 100) / _sizeCcCube) : 0;
	cout << "\t\t%pred-cc-cube :\t" << perc_pred_cc_cube << "%" << endl;


	double perc_fproj_cc_cube = (_sizeCcCube != 0) ? (((double) _sizefProjCcCube * 100) / _sizeCcCube) : 0;
	cout << "\t\t%fproj-cc-cube:\t" << perc_fproj_cc_cube << "%" << endl;

	double perc_fproj_sig_eq_cc_cube = (_sizeCcCube != 0) ? (((double) _sizefProjSigEqCcCube * 100) / _sizeCcCube) : 0;
	cout << "\t\t\ts (==):\t" << perc_fproj_sig_eq_cc_cube << "%" << endl;

	double perc_fproj_sig_neq_cc_cube = (_sizeCcCube != 0) ? (((double) _sizefProjSigNeqCcCube * 100) / _sizeCcCube) : 0;
	cout << "\t\t\ts (!=):\t" << perc_fproj_sig_neq_cc_cube << "%" << endl;

	double perc_fproj_num_eq_cc_cube = (_sizeCcCube != 0) ? (((double) _sizefProjNumEqCcCube * 100) / _sizeCcCube) : 0;
	cout << "\t\t\tn (==):\t" << perc_fproj_num_eq_cc_cube << "%" << endl;

	double perc_fproj_num_neq_cc_cube = (_sizeCcCube != 0) ? (((double) _sizefProjNumNeqCcCube * 100) / _sizeCcCube) : 0;
	cout << "\t\t\tn (!=):\t" << perc_fproj_num_neq_cc_cube << "%" << endl;


	double perc_proj_cc_cube = (_sizeCcCube != 0) ? (((double) _sizeProjCcCube * 100) / _sizeCcCube) : 0;
	cout << "\t\t%proj-cc-cube :\t" << perc_proj_cc_cube << "%" << endl;

	double perc_proj_sig_eq_cc_cube = (_sizeCcCube != 0) ? (((double) _sizeProjSigEqCcCube * 100) / _sizeCcCube) : 0;
	cout << "\t\t\ts (==):\t" << perc_proj_sig_eq_cc_cube << "%" << endl;

	double perc_proj_sig_neq_cc_cube = (_sizeCcCube != 0) ? (((double) _sizeProjSigNeqCcCube * 100) / _sizeCcCube) : 0;
	cout << "\t\t\ts (!=):\t" << perc_proj_sig_neq_cc_cube << "%" << endl;

	double perc_proj_num_eq_cc_cube = (_sizeCcCube != 0) ? (((double) _sizeProjNumEqCcCube * 100) / _sizeCcCube) : 0;
	cout << "\t\t\tn (==):\t" << perc_proj_num_eq_cc_cube << "%" << endl;

	double perc_proj_num_neq_cc_cube = (_sizeCcCube != 0) ? (((double) _sizeProjNumNeqCcCube * 100) / _sizeCcCube) : 0;
	cout << "\t\t\tn (!=):\t" << perc_proj_num_neq_cc_cube << "%" << endl;

	cout << endl;


	double tb_cube_time_percent = (total_time == 0) ? 0 : (double) _tb_cube_time * 100 / total_time;
	cout << "\ttb_cube_time:     \t" << ((double) _tb_cube_time / 1000000) << " ("
			<< tb_cube_time_percent << "%)" << endl;

	double cube_eval_time_percent = (total_time == 0) ? 0 : (double) _tb_eval_time * 100 / total_time;
	cout << "\t\tcube_eval_time: \t" << ((double) _tb_eval_time / 1000000) << " ("
			<< cube_eval_time_percent << "%)" << endl;

	double cube_pred_time_percent = (total_time == 0) ? 0 : (double) _tb_pred_time * 100 / total_time;
	cout << "\t\tcube_pred_time: \t" << ((double) _tb_pred_time / 1000000) << " ("
			<< cube_pred_time_percent << "%)" << endl;

	double cube_fproj_time_percent = (total_time == 0) ? 0 : (double) _tb_fproj_time * 100 / total_time;
	cout << "\t\tcube_fproj_time:\t" << ((double) _tb_fproj_time / 1000000) << " ("
			<< cube_fproj_time_percent << "%)" << endl;

	double cube_proj_time_percent = (total_time == 0) ? 0 : (double) _tb_proj_time * 100 / total_time;
	cout << "\t\tcube_proj_time: \t" << ((double) _tb_proj_time / 1000000) << " ("
			<< cube_proj_time_percent << "%)" << endl;

	double cube_subs_time_percent = (total_time == 0) ? 0 : (double) _tb_subs_time * 100 / total_time;
	cout << "\t\tcube _subs_time:\t" << ((double) _tb_subs_time / 1000000) << " ("
			<< cube_subs_time_percent << "%)" << endl;

	long long total_cube_time = _tb_eval_time +
							  _tb_pred_time +
							  _tb_fproj_time +
							  _tb_proj_time +
							  _tb_subs_time;

	double sum_cube_time_percent = (_tb_cube_time == 0) ? 0 : (double) total_cube_time * 100 / _tb_cube_time;
	cout << "\t\tsum:            \t" << ((double) total_cube_time / 1000000) << " (" << sum_cube_time_percent << "% of tb_cube_time)" << endl;
	cout << endl;

	double tb_ct_time_percent = (total_time == 0) ? 0 : (double) _tb_ct_time * 100 / total_time;
	cout << "\ttb_ct_time:      \t" << ((double) _tb_ct_time / 1000000) << " ("
			<< tb_ct_time_percent << "%)" << endl;

	double ct_isblocked_time_percent = (total_time == 0) ? 0 : (double) _tb_ct_isblocked_time * 100 / total_time;
	cout << "\t\tct isblocked_time:  \t" << ((double) _tb_ct_isblocked_time / 1000000) << " ("
			<< ct_isblocked_time_percent << "%)" << endl;

	double ct_isinitial_time_percent = (total_time == 0) ? 0 : (double) _tb_ct_initial_time * 100 / total_time;
	cout << "\t\tct isinitial_time:  \t" << ((double) _tb_ct_initial_time / 1000000) << " ("
			<< ct_isinitial_time_percent << "%)" << endl;

	double ct_containment_time_percent = (total_time == 0) ? 0 : (double) _tb_ct_containment_time * 100 / total_time;
	cout << "\t\tct containment_time:\t" << ((double) _tb_ct_containment_time / 1000000) << " ("
			<< ct_containment_time_percent << "%)" << endl;

	double ct_fastforward_time_percent = (total_time == 0) ? 0 : (double) _tb_ct_forwardfast_time * 100 / total_time;
	cout << "\t\tct fastforward_time:\t" << ((double) _tb_ct_forwardfast_time / 1000000) << " ("
			<< ct_fastforward_time_percent << "%)" << endl;

	long long total_ct_time = _tb_ct_initial_time +
							  _tb_ct_isblocked_time +
							  _tb_ct_containment_time +
							  _tb_ct_forwardfast_time;

	double sum_ct_time_percent = (_tb_ct_time == 0) ? 0 : (double) total_ct_time * 100 / _tb_ct_time;
	cout << "\t\tsum:                \t" << ((double) total_ct_time / 1000000) << " (" << sum_ct_time_percent << "% of tb_ct_time)" << endl;
	cout << endl;

	double setcontain_time_percent = (total_time == 0) ? 0 : (double) _tb_setcontain_time * 100 / total_time;
	cout << "\tsetcontain_time:\t" << ((double) _tb_setcontain_time / 1000000) << " ("
			<< setcontain_time_percent << "%)" << endl;
	cout << endl;

	double updateincsolver_time_percent = (total_time == 0) ? 0 : (double) _tb_updateincsolver_time * 100 / total_time;
	cout << "\tupdatesolver_time:\t" << ((double) _tb_updateincsolver_time / 1000000) << " ("
			<< updateincsolver_time_percent << "%)" << endl;
	cout << endl;

	double tb_time_percent = (total_time == 0) ? 0 : (double) _tb_time * 100 / total_time;
	cout << "\ttb_time:\t" << ((double) _tb_time / 1000000) << " ("
			<< tb_time_percent << "%)" << endl;

	double tb_reach_time_percent = (total_time == 0) ? 0 : (double) _tb_reach_time * 100 / total_time;
	cout << "\t\ttb_reach_time:    \t" << ((double) _tb_reach_time / 1000000) << " ("
			<< tb_reach_time_percent << "%)" << endl;

	double tb_val_time_percent = (total_time == 0) ? 0 : (double) _tb_val_time * 100 / total_time;
	double cti_val_time_percent = (total_time == 0) ? 0 : (double) _cti_val_time * 100 / total_time;
	cout << "\t\ttb_val_time:    \t" << ((double) _tb_val_time / 1000000) << " ("
			<< tb_val_time_percent << "%) [ ";
	cout << "cti_val_time: " << ((double) _cti_val_time / 1000000) << " ("
			<< cti_val_time_percent << "%) ]" << endl;

	cout << "\t\ttb_cube_time:      \t" << ((double) _tb_cube_time / 1000000) << " ("
			<< tb_cube_time_percent << "%)" << endl;

	double tb_mus_time_percent = (total_time == 0) ? 0 : (double) _tb_UNSAT_camus_time * 100 / total_time;
	cout << "\t\ttb_mus_time:      \t" << ((double) _tb_UNSAT_camus_time / 1000000) << " ("
			<< tb_mus_time_percent << "%)" << endl;

		double tb_mus_core_time_percent = (total_time == 0) ? 0 : (double) _tb_reach_mus_core * 100 / total_time;
		cout << "\t\t\ttb_mus_core_time:      \t" << ((double) _tb_reach_mus_core / 1000000) << " ("
				<< tb_mus_core_time_percent << "%)" << endl;

		double tb_mus_min_time_percent = (total_time == 0) ? 0 : (double) _tb_reach_mus_min * 100 / total_time;
		cout << "\t\t\ttb_mus_min_time:      \t" << ((double) _tb_reach_mus_min / 1000000) << " ("
				<< tb_mus_min_time_percent << "%)" << endl;

	cout << "\t\ttb_ct_time:       \t" << ((double) _tb_ct_time / 1000000) << " ("
			<< tb_ct_time_percent << "%)" << endl;

	double tb_extra_time_percent = (total_time == 0) ? 0 : (double) _cc_extra_tb_time * 100 / total_time;
	cout << "\t\ttb_extra_time:    \t" << ((double) _cc_extra_tb_time / 1000000) << " (" << tb_extra_time_percent << "%)" << endl;

	long long total_tb_time = _tb_reach_time +
//							  _tb_val_time +
							  _tb_cube_time +
							  _tb_UNSAT_camus_time +
							  _tb_ct_time +
							  _cc_extra_tb_time;

	double sum_tb_time_percent = (_tb_time == 0) ? 0 : (double) total_tb_time * 100 / _tb_time;
	cout << "\t\tsum:           \t" << ((double) total_tb_time / 1000000) << " (" << sum_tb_time_percent << "% of tb_time)" << endl;
	cout << endl;

	cout << endl << "  (refinement)" << endl;

	double sim_time_percent = (total_time == 0) ? 0 : (double) _sim_time * 100 / total_time;
	cout << "\tsim_time:\t\t" << ((double) _sim_time / 1000000) << " ("
			<< sim_time_percent << "%) \t [" << (double) _sim_time * 100 / _dpr_time << "% of dpr_time]" << endl;
	cout << endl;

	_cti_time += _cti_i_time;
	_pme_time += _pme_i_time;
//	_bp_time += _bp_i_time;


#ifdef AVR_PME_SOLVER_ENABLE
//	long long total_time2 = _pre_time + _cti_time + _pme_time + _bp_time + _fp_time + _tb_time + _dpr_time + _cc_time;
	long long total_time2 = _pre_time + _cti_time + _pme_time + _bp_i_time + _fp_time + _tb_time + _dpr_time + _cc_time;
#else
//	long long total_time2 = _pre_time + _cti_time + _bp_time + _fp_time + _tb_time + _dpr_time + _cc_time;
	long long total_time2 = _pre_time + _cti_time + _solver_set_time + _fp_time + _tb_time + _dpr_time + _cc_time;
#endif


	double pre_time_percent = (total_time == 0) ? 0 : (double) _pre_time * 100 / total_time;
	cout << "  pre_time:\t" << ((double) _pre_time / 1000000) << " (" << pre_time_percent << "%)" << endl;

	double cti_time_percent = (total_time == 0) ? 0 : (double) _cti_time * 100 / total_time;
	double cti_i_time_percent = (total_time == 0) ? 0 : (double) _cti_i_time * 100 / total_time;
	cout << "  cti_time:\t" << ((double) _cti_time / 1000000) << " (" << cti_time_percent << "%)	[";
	cout << "cti_i_time:\t" << ((double) _cti_i_time / 1000000) << " (" << cti_i_time_percent << "%) ";
	cout<< "]" << endl;

#ifdef AVR_PME_SOLVER_ENABLE
	double pme_time_percent = (double) _pme_time * 100 / total_time;
	double pme_i_time_percent = (double) _pme_i_time * 100 / total_time;
	cout << "pme_time:\t" << ((double) _pme_time / 1000000) << " (" << pme_time_percent << "%)	[";
	cout << "pme_i_time:\t" << ((double) _pme_i_time / 1000000) << " (" << pme_i_time_percent << "%) ]" << endl;
#endif

	cout << "  tb_time:\t" << ((double) _tb_time / 1000000) << " ("
			<< tb_time_percent << "%)" << endl;

	double fp_time_percent = (total_time == 0) ? 0 : (double) _fp_time * 100 / total_time;
	double fp_extra_time_percent = (total_time == 0) ? 0 : (double) _cc_extra_fp_time * 100 / total_time;
	cout << "  fp_time:\t" << ((double) _fp_time / 1000000) << " (" << fp_time_percent << "%)	[";
	cout << "fp_extra_time:\t" << ((double) _cc_extra_fp_time / 1000000) << " (" << fp_extra_time_percent << "%) ]" << endl;

	double refine_time_percent = (total_time == 0) ? 0 : (double) _dpr_time * 100 / total_time;
	cout << "  refine_time:\t" << ((double) _dpr_time / 1000000) << " (" << refine_time_percent << "%)" << endl;

	double solver_set_time_percent = (total_time == 0) ? 0 : (double) _solver_set_time * 100 / total_time;
	cout << "  sol_set_time:\t" << ((double) _solver_set_time / 1000000) << " (" << solver_set_time_percent << "%)" << endl;

	double inv_check_time_percent = (total_time == 0) ? 0 : (double) _cc_time * 100 / total_time;
	double induction_check_time_percent = (total_time == 0) ? 0 : (double) _cc_inv_time * 100 / total_time;
	cout << "  inv_time:\t" << ((double) _cc_time / 1000000) << " (" << inv_check_time_percent << "%)	[";
	cout << "induct_time:\t" << ((double) _cc_inv_time / 1000000) << " (" << induction_check_time_percent << "%) ]" << endl;

	double draw_time_percent = (total_time == 0) ? 0 : (double) _draw_time * 100 / total_time;
	cout << "  draw_time:\t" << ((double) _draw_time / 1000000) << " (" << draw_time_percent << "%)" << endl;

	double sum_time_percent = (total_time == 0) ? 0 : (double) total_time2 * 100 / total_time;
	cout << "  sum:\t\t" << ((double) total_time2 / 1000000) << " (" << sum_time_percent << "%)" << endl;

	long long extra_time = _cc_extra_tb_time + _cc_extra_fp_time + _draw_time;
	double extra_time_percent = (total_time == 0) ? 0 : (double) extra_time * 100 / total_time;
	cout << endl << "  extra_time:\t" << ((double) extra_time / 1000000) << " (" << extra_time_percent << "%)" << endl;

	long long timeout_time = (Solver::time_ab_timeout + Solver::time_bv_timeout);
	double timeout_time_percent = (total_time == 0) ? 0 : (double) timeout_time * 100 / total_time;
	cout << endl << "  timeout_time:\t" << ((double) timeout_time / 1000000) << " (" << timeout_time_percent << "%)" << endl;

	cout << endl;

//	cout << endl << ">>>	total_time:\t" << ((double) total_time / 1000000) << endl;

//	cout << "_set_containment_cnt: " << _set_containment_cnt << endl;
//	cout << "_redundant_cube_cnt: " << _redundant_cube_cnt << endl;
	//cout << "====================================*/" << endl << endl;

//	cout << "##############################################" << endl;
//	cout << "num_pred_lit: " << num_pred_lit << endl;
//	cout << "num_term: " << num_term << endl;
//	cout << "log2_state_space: " << log2_state_space << endl;
//	cout << "##############################################" << endl;
#endif


	int count_ex = 0;
	int count_cc = 0;
	int count_ot = 0;

	OpInst::OpHashM::iterator mit = ExInst::hm_ExInst.begin();
	for (; mit != ExInst::hm_ExInst.end(); mit++)
	{
		ExInst* ex = ExInst::as((*mit).second);
		if (ex && ex->t_simple && (ex != ex->t_simple))
		{
			count_ex++;
//			cout << *ex << " -> " << *(ex->t_simple) << endl;
		}
	}

	OpInst::OpHashM::iterator mit2 = OpInst::hm_OpInst.begin();
	for (; mit2 != OpInst::hm_OpInst.end(); mit2++)
	{
		OpInst* op = OpInst::as((*mit2).second);
//		if (op && op->get_euf_func_name() != "0")
//		{
//			cout << *op << " -- Op" << endl;
//		}
		if (op && op->t_simple && (op != op->t_simple))
		{
			if (op->get_op() == OpInst::Concat)
				count_cc++;
			else
				count_ot++;
//			cout << *op << " -> " << *(op->t_simple) << endl;
		}
	}
	OpInst::OpHashMM::iterator mit3 = OpInst::hm_ETCInst.begin();
	for (; mit3 != OpInst::hm_ETCInst.end(); mit3++)
	{
		OpInst* op = OpInst::as((*mit3).second);
//		if (op && op->get_euf_func_name() != "0")
//		{
//			cout << *op << " -- Op" << endl;
//		}
		if (op && op->t_simple && (op != op->t_simple))
		{
			if (op->get_op() == OpInst::Concat)
				count_cc++;
			else
				count_ot++;
//			cout << *op << " -> " << *(op->t_simple) << endl;
		}
	}
	cout << "[simplified] " << count_ex << " (ex), " << count_cc << " (cc), " << count_ot << " (ot)" << endl;

	string result = "";
	switch(Inst::g_result) {
	case h: {
			AVR_LOG(15, 0, "\n===     HOLD     ===" << endl);
			result = "h";
			assert(exit_val == EXIT_HOLD);
			_prFile << "avr-h";
	}
		break;
	case h_triv: {
			AVR_LOG(15, 0, "\n===  HOLD (trivial) ===" << endl);
			result = "h";
			assert(exit_val == EXIT_HOLD_TRIV);
			_prFile << "avr-h_triv";
		}
		break;
	case v: {
			AVR_LOG(15, 0, "\n===   VIOLATED   ===" << endl);
			result = "v";
			assert(exit_val == EXIT_VIOL);
			_prFile << "avr-v";
		}
		break;
	case f_to: {
			AVR_LOG(15, 0, "\n===   TIMED OUT   ===" << endl);
			result = "f_to";
			_prFile << "avr-f_to";
		}
		break;
	case f_to_query: {
			AVR_LOG(15, 0, "\n===   TIMED OUT (query)   ===" << endl);
			result = "f_to_q";
			_prFile << "avr-f_to_q";
		}
		break;
	case f_mo: {
			AVR_LOG(15, 0, "\n===   OUT OF MEMORY   ===" << endl);
			result = "f_mo";
			_prFile << "avr-f_mo";
		}
		break;
	case f_poor_ab: {
			AVR_LOG(15, 0, "\n===   TOO MANY REFINEMENTS (poor abstraction)   ===" << endl);
			result = "f_poor_ab";
			_prFile << "avr-f_poor_ab";
		}
		break;
	case f_err: {
			AVR_LOG(15, 0, "\n===   ERROR   ===" << endl);
			result = "f_err";
			_prFile << "avr-f_err";
		}
		break;
	default:
		AVR_LOG(15, 0, "\t(error: unrecognized result)" << endl);
		result = "f_err";
		_prFile << "avr-f_err";
	}

	//#################################//

	cout<<endl<<"Averroes finished."<<endl<<endl;

	double avg_sz_hard_core_muses_reach = (Reach::num_muses_reach == 0) ? 0 : ((double) Reach::sz_hard_core_muses_reach) / Reach::num_muses_reach;
	double avg_sz_soft_core_muses_reach = (Reach::num_muses_reach == 0) ? 0 : ((double) Reach::sz_soft_core_muses_reach) / Reach::num_muses_reach;
	double avg_sz_out_core_muses_reach  = (Reach::num_muses_reach == 0) ? 0 : ((double) Reach::sz_out_core_muses_reach) / Reach::num_muses_reach;
#ifdef Y2_EXPENSIVE_CORE_EXTRACTION
  double avg_sz_red_core2_muses_reach  = (Reach::num_muses_reach == 0) ? 0 : ((double) Solver::core1_size - Reach::sz_out_core_muses_reach) / Reach::num_muses_reach;
#endif

	double avg_sz_hard_min_muses_reach = (Reach::num_muses_reach == 0) ? 0 : ((double) Reach::sz_hard_min_muses_reach) / Reach::num_muses_reach;
	double avg_sz_soft_min_muses_reach = (Reach::num_muses_reach == 0) ? 0 : ((double) Reach::sz_soft_min_muses_reach) / Reach::num_muses_reach;
	double avg_sz_out_min_muses_reach  = (Reach::num_muses_reach == 0) ? 0 : ((double) Reach::sz_out_min_muses_reach) / Reach::num_muses_reach;

	TableFormat out;
	out << "br-#mus" << Reach::num_muses_reach << "\n";
	out << "hard" << "soft" << "out" << "\n";
#ifdef Y2_EXPENSIVE_CORE_EXTRACTION
  out << "" << "" << "" << " " << "(br-core2 avg. red.)" << avg_sz_red_core2_muses_reach;
#endif
  out << "\n";
	out << avg_sz_hard_core_muses_reach << avg_sz_soft_core_muses_reach << avg_sz_out_core_muses_reach;
#ifdef Y2_EXPENSIVE_CORE_EXTRACTION
	out << " " << "(br-core + br-core2)" << "\n";
#else
  out << " " << "(br-core)" << "\n";
#endif
	out << avg_sz_hard_min_muses_reach << avg_sz_soft_min_muses_reach << avg_sz_out_min_muses_reach;
	out << " " << "(br-min)" << "\n\n";

	out << "sat" << "unsat" << "\n";

	out << " " << " " << " ";
	out << "#Calls" << "\n";
	out << Reach::num_scalls_sat_core_muses_reach << Reach::num_scalls_unsat_core_muses_reach;
	out << "(br-core)" << "\n";
  out << Solver::num_scalls_sat_core2_muses_reach << Solver::num_scalls_unsat_core2_muses_reach;
  out << "(br-core2)" << "\n";
	out << Reach::num_scalls_sat_min_muses_reach << Reach::num_scalls_unsat_min_muses_reach;
	out << "(br-min)" << "\n";

	out << " " << " " << " ";
	out << "Time (sec)" << "\n";
	out << Solver::time_sat_core_muses_reach / 1000000.0 << Solver::time_unsat_core_muses_reach / 1000000.0;
	out << "(br-core)" << "\n";
  out << Solver::time_sat_core2_muses_reach / 1000000.0 << Solver::time_unsat_core2_muses_reach / 1000000.0;
  out << "(br-core2)" << "\n";
	out << Solver::time_sat_min_muses_reach / 1000000.0 << Solver::time_unsat_min_muses_reach / 1000000.0;
	out << "(br-min)" << "\n";

	out << " " << " " << " ";
	out << "Avg. Time (microsec)" << "\n";
	int avg_time_sat_core_muses_reach = (Reach::num_scalls_sat_core_muses_reach != 0) ? Solver::time_sat_core_muses_reach / Reach::num_scalls_sat_core_muses_reach : 0;
	int avg_time_unsat_core_muses_reach = (Reach::num_scalls_unsat_core_muses_reach != 0) ? Solver::time_unsat_core_muses_reach / Reach::num_scalls_unsat_core_muses_reach : 0;
  int avg_time_sat_core2_muses_reach = (Solver::num_scalls_sat_core2_muses_reach != 0) ? Solver::time_sat_core2_muses_reach / Solver::num_scalls_sat_core2_muses_reach : 0;
  int avg_time_unsat_core2_muses_reach = (Solver::num_scalls_unsat_core2_muses_reach != 0) ? Solver::time_unsat_core2_muses_reach / Solver::num_scalls_unsat_core2_muses_reach : 0;
	int avg_time_sat_min_muses_reach = (Reach::num_scalls_sat_min_muses_reach != 0) ? Solver::time_sat_min_muses_reach / Reach::num_scalls_sat_min_muses_reach : 0;
	int avg_time_unsat_min_muses_reach = (Reach::num_scalls_unsat_min_muses_reach != 0) ? Solver::time_unsat_min_muses_reach / Reach::num_scalls_unsat_min_muses_reach : 0;
	out << avg_time_sat_core_muses_reach << avg_time_unsat_core_muses_reach;
	out << "(br-core)" << "\n";
  out << avg_time_sat_core2_muses_reach << avg_time_unsat_core2_muses_reach;
  out << "(br-core2)" << "\n";
	out << avg_time_sat_min_muses_reach << avg_time_unsat_min_muses_reach;
	out << "(br-min)" << "\n";

	out << " " << " " << " ";
	out << "Max Time (microsec)" << "\n";
	out << Solver::time_max_sat_core_muses_reach << Solver::time_max_unsat_core_muses_reach;
	out << "(br-core)" << "\n";
  out << Solver::time_max_sat_core2_muses_reach << Solver::time_max_unsat_core2_muses_reach;
  out << "(br-core2)" << "\n";
	out << Solver::time_max_sat_min_muses_reach << Solver::time_max_unsat_min_muses_reach;
	out << "(br-min)" << "\n\n";


	out << " " << "ab" << " " << "bv" << "\n";
	out << "sat" << "unsat" << "sat" << "unsat" << "\n";

	out << " " << " " << " " << " ";
	out << "#Calls" << "\n";
	out << Solver::num_ab_sat_oneshot << Solver::num_ab_unsat_oneshot << Solver::num_bv_sat_oneshot << Solver::num_bv_unsat_oneshot;
	out << "(oneshot)" << "\n";
	out << Solver::num_ab_sat_inc << Solver::num_ab_unsat_inc << Solver::num_bv_sat_inc << Solver::num_bv_unsat_inc;
	out << "(inc)" << "\n";
	out << Solver::num_ab_sat_mus << Solver::num_ab_unsat_mus << Solver::num_bv_sat_mus << Solver::num_bv_unsat_mus;
	out << "(assume)" << "\n";
	out << "   " << Solver::num_ab_timeout << "   " << Solver::num_bv_timeout;
	out << "(timeout)" << "\n\n";


	out << " " << " " << " " << " ";
	out << "Time (sec)" << "\n";
	out << Solver::time_ab_sat_oneshot / 1000000.0 << Solver::time_ab_unsat_oneshot / 1000000.0 << Solver::time_bv_sat_oneshot / 1000000.0 << Solver::time_bv_unsat_oneshot / 1000000.0;
	out << "(oneshot)" << "\n";
	out << Solver::time_ab_sat_inc / 1000000.0 << Solver::time_ab_unsat_inc / 1000000.0 << Solver::time_bv_sat_inc / 1000000.0 << Solver::time_bv_unsat_inc / 1000000.0;
	out << "(inc)" << "\n";
	out << Solver::time_ab_sat_mus / 1000000.0 << Solver::time_ab_unsat_mus / 1000000.0 << Solver::time_bv_sat_mus / 1000000.0 << Solver::time_bv_unsat_mus / 1000000.0;
	out << "(assume)" << "\n";
	out << "   " << Solver::time_ab_timeout / 1000000.0 << "   " << Solver::time_bv_timeout / 1000000.0;
	out << "(timeout)" << "\n\n";

	out << " " << " " << " " << " ";
	out << "Avg. Time (microsec)\n";
	int avg_time_ab_sat_oneshot = (Solver::num_ab_sat_oneshot != 0) ? Solver::time_ab_sat_oneshot / Solver::num_ab_sat_oneshot : 0;
	int avg_time_ab_unsat_oneshot = (Solver::num_ab_unsat_oneshot != 0) ? Solver::time_ab_unsat_oneshot / Solver::num_ab_unsat_oneshot : 0;
	int avg_time_bv_sat_oneshot = (Solver::num_bv_sat_oneshot != 0) ? Solver::time_bv_sat_oneshot / Solver::num_bv_sat_oneshot : 0;
	int avg_time_bv_unsat_oneshot = (Solver::num_bv_unsat_oneshot != 0) ? Solver::time_bv_unsat_oneshot / Solver::num_bv_unsat_oneshot : 0;
	out << avg_time_ab_sat_oneshot << avg_time_ab_unsat_oneshot << avg_time_bv_sat_oneshot << avg_time_bv_unsat_oneshot;
	out << "(oneshot)" << "\n";

	int avg_time_ab_sat_inc = (Solver::num_ab_sat_inc != 0) ? Solver::time_ab_sat_inc / Solver::num_ab_sat_inc : 0;
	int avg_time_ab_unsat_inc = (Solver::num_ab_unsat_inc != 0) ? Solver::time_ab_unsat_inc / Solver::num_ab_unsat_inc : 0;
	int avg_time_bv_sat_inc = (Solver::num_bv_sat_inc != 0) ? Solver::time_bv_sat_inc / Solver::num_bv_sat_inc : 0;
	int avg_time_bv_unsat_inc = (Solver::num_bv_unsat_inc != 0) ? Solver::time_bv_unsat_inc / Solver::num_bv_unsat_inc : 0;
	out << avg_time_ab_sat_inc << avg_time_ab_unsat_inc << avg_time_bv_sat_inc << avg_time_bv_unsat_inc;
	out << "(inc)" << "\n";

	int avg_time_ab_sat_mus = (Solver::num_ab_sat_mus != 0) ? Solver::time_ab_sat_mus / Solver::num_ab_sat_mus : 0;
	int avg_time_ab_unsat_mus = (Solver::num_ab_unsat_mus != 0) ? Solver::time_ab_unsat_mus / Solver::num_ab_unsat_mus : 0;
	int avg_time_bv_sat_mus = (Solver::num_bv_sat_mus != 0) ? Solver::time_bv_sat_mus / Solver::num_bv_sat_mus : 0;
	int avg_time_bv_unsat_mus = (Solver::num_bv_unsat_mus != 0) ? Solver::time_bv_unsat_mus / Solver::num_bv_unsat_mus : 0;
	out << avg_time_ab_sat_mus << avg_time_ab_unsat_mus << avg_time_bv_sat_mus << avg_time_bv_unsat_mus;
	out << "(assume)" << "\n";

	int avg_time_ab_timeout = (Solver::num_ab_timeout != 0) ? Solver::time_ab_timeout / Solver::num_ab_timeout : 0;
	int avg_time_bv_timeout = (Solver::num_bv_timeout != 0) ? Solver::time_bv_timeout / Solver::num_bv_timeout : 0;
	out << "   " << avg_time_ab_timeout << "   " << avg_time_bv_timeout;
	out << "(timeout)" << "\n";


	double total_calls_ab = (Solver::num_ab_sat_oneshot + Solver::num_ab_unsat_oneshot
							+ Solver::num_ab_sat_inc + Solver::num_ab_unsat_inc
							+ Solver::num_ab_sat_mus + Solver::num_ab_unsat_mus
							+ Solver::num_ab_timeout);
	double total_calls_bv = (Solver::num_bv_sat_oneshot + Solver::num_bv_unsat_oneshot
							+ Solver::num_bv_sat_inc + Solver::num_bv_unsat_inc
							+ Solver::num_bv_sat_mus + Solver::num_bv_unsat_mus
							+ Solver::num_bv_timeout);

	double avr_time_ab = (total_calls_ab == 0) ? 0 : (double) (Solver::time_ab_sat_oneshot + Solver::time_ab_unsat_oneshot + Solver::time_ab_sat_inc + Solver::time_ab_unsat_inc + Solver::time_ab_sat_mus + Solver::time_ab_unsat_mus + Solver::time_ab_timeout) / (1000.0 * total_calls_ab);
	double avr_time_bv = (total_calls_bv == 0) ? 0 : (double) (Solver::time_bv_sat_oneshot + Solver::time_bv_unsat_oneshot + Solver::time_bv_sat_inc + Solver::time_bv_unsat_inc + Solver::time_bv_sat_mus + Solver::time_bv_unsat_mus + Solver::time_bv_timeout) / (1000.0 * total_calls_bv);

	out.width = 12;
	double totalTime = ((double) _totalTime / 1000000);
	double timeReason = ((double) (_totalTime - _draw_time - _cc_time) / 1000000);
	out << "\n";
//	out << "Time" << "#Refs" << "Res" << "Mem." << "ag_ab" << "ag_bv" << "mx_ab" << "mx_bv" << "mx_abm" << "mx_bvm" << "\n";
//	out << "sec"<< " "     << " "   << "MB" << "msec"<< "msec"<< "msec"<< "msec"<< "msec" << "msec" << "\n";
//	out << totalTime << _numRefinements << result << memory_usage
//			<< avr_time_ab << avr_time_bv
//			<< (Solver::time_max_ab_query / 1000.0) << (Solver::time_max_bv_query / 1000.0)
//			<< (Solver::time_max_ab_mus_query / 1000.0) << (Solver::time_max_bv_mus_query / 1000.0);
	out << "Result" << "Time" << "Mem." << "#Refs" << "\n";
	out << " "      << "sec"  << "MB"   << " "     << "\n";
	out << result << totalTime << memory_usage << _numRefinements;
	cout.flush();

	_resFile << "#extract-simplified:\t" << count_ex << endl;
	_resFile << "#concat-simplified:\t" << count_cc << endl;
	_resFile << "#other-simplified:\t" << count_ot << endl;

	_resFile << "total-restrictions:\t" << sum_cubes << endl;
	_resFile << "#literals-restrictions:\t" << sum_literals << endl;
	_resFile << "max-func-level:\t" << _max_funcLevel << endl;
#ifdef LIMIT_WLP_USING_FCLEVEL
	_resFile << "wp-allowed-fclevel:\t" << _allowed_funcLevel << endl;
#else
	_resFile << "wp-allowed-fclevel:\t" << "-" << endl;
#endif
	_resFile << "#-wp-constraints:\t" << num_path_constraints << endl;
#ifdef REACH_ADD_PATH_CONSTRAINTS
	double wp_factor = (num_path_constraints == 0) ? 1 : ((double) num_path_constraints_taken / num_path_constraints);
	_resFile << "wp-factor:\t" << wp_factor << endl;
#else
	assert(num_path_constraints_taken == 0);
	_resFile << "wp-factor:\t" << 0 << endl;
#endif

	if (Config::g_bmc_en)
		_resFile << "bmc-max-safe-bound:\t" << bm.safe_bound << endl;
	else
		_resFile << "bmc-max-safe-bound:\t" << "-1" << endl;

	_resFile << "scalls:\t" << total_solver_calls << endl;
	_resFile << "scalls-sat:\t" << Solver::num_scalls_sat << endl;
	_resFile << "scalls-unsat:\t" << Solver::num_scalls_unsat << endl;

	_resFile << "scalls-assume:\t" << total_solver_calls_mus << endl;
	_resFile << "scalls-assume-sat:\t" << num_scalls_sat_mus << endl;
	_resFile << "scalls-assume-unsat:\t" << num_scalls_unsat_mus << endl;

	_resFile << "scalls-ab:\t" << total_calls_ab << endl;
	_resFile << "scalls-bv:\t" << total_calls_bv << endl;

	_resFile << "scalls-assume-ab:\t" << num_scalls_ab_mus << endl;
	_resFile << "scalls-assume-bv:\t" << num_scalls_bv_mus << endl;

	_resFile << "br-mus-scalls-core-sat:\t" << Reach::num_scalls_sat_core_muses_reach << endl;
	_resFile << "br-mus-scalls-core-unsat:\t" << Reach::num_scalls_unsat_core_muses_reach << endl;
	_resFile << "br-mus-scalls-min-sat:\t" << Reach::num_scalls_sat_min_muses_reach << endl;
	_resFile << "br-mus-scalls-min-unsat:\t" << Reach::num_scalls_unsat_min_muses_reach << endl;

	_resFile << "br-mus-time-q-sat-core-sat:\t" << Solver::time_sat_core_muses_reach << endl;
	_resFile << "br-mus-time-q-unsat-core-sat:\t" << Solver::time_unsat_core_muses_reach << endl;
	_resFile << "br-mus-time-q-sat-min-sat:\t" << Solver::time_sat_min_muses_reach << endl;
	_resFile << "br-mus-time-q-unsat-min-sat:\t" << Solver::time_unsat_min_muses_reach << endl;

	_resFile << "br-mus-avg-time-q-sat-core-sat:\t" << avg_time_sat_core_muses_reach << endl;
	_resFile << "br-mus-avg-time-q-unsat-core-sat:\t" << avg_time_unsat_core_muses_reach << endl;
	_resFile << "br-mus-avg-time-q-sat-min-sat:\t" << avg_time_sat_min_muses_reach << endl;
	_resFile << "br-mus-avg-time-q-unsat-min-sat:\t" << avg_time_unsat_min_muses_reach << endl;

	_resFile << "br-mus-max-time-q-sat-core-sat:\t" << Solver::time_max_sat_core_muses_reach << endl;
	_resFile << "br-mus-max-time-q-unsat-core-sat:\t" << Solver::time_max_unsat_core_muses_reach << endl;
	_resFile << "br-mus-max-time-q-sat-min-sat:\t" << Solver::time_max_sat_min_muses_reach << endl;
	_resFile << "br-mus-max-time-q-unsat-min-sat:\t" << Solver::time_max_unsat_min_muses_reach << endl;

	_resFile << "time-dist-cube_eval:\t" << cube_eval_time_percent << endl;
	_resFile << "time-dist-cube_pred:\t" << cube_pred_time_percent << endl;
	_resFile << "time-dist-cube_fproj:\t" << cube_fproj_time_percent << endl;
	_resFile << "time-dist-cube_proj:\t" << cube_proj_time_percent << endl;
	_resFile << "time-dist-cube_subs:\t" << cube_subs_time_percent << endl;

	_resFile << "time-dist-ct_isblocked:\t" << ct_isblocked_time_percent << endl;
	_resFile << "time-dist-ct_isinitial:\t" << ct_isinitial_time_percent << endl;
	_resFile << "time-dist-ct_containment:\t" << ct_containment_time_percent << endl;
	_resFile << "time-dist-ct_fastforward:\t" << ct_fastforward_time_percent << endl;

	_resFile << "time-dist-setcontain:\t" << setcontain_time_percent << endl;
	_resFile << "time-dist-updatesolver:\t" << updateincsolver_time_percent << endl;


	_resFile << "time-dist-br-reach:\t" << tb_reach_time_percent << endl;
	_resFile << "time-dist-br-val:\t" << tb_val_time_percent << endl;
	_resFile << "time-dist-br-cube:\t" << tb_cube_time_percent << endl;
	_resFile << "time-dist-br-mus:\t" << tb_mus_time_percent << endl;
	_resFile << "br-mus-time-dist-core:\t" << tb_mus_core_time_percent << endl;
	_resFile << "br-mus-time-dist-min:\t" << tb_mus_min_time_percent << endl;
	_resFile << "time-dist-br-ct:\t" << tb_ct_time_percent << endl;
	_resFile << "time-dist-br-extra:\t" << tb_extra_time_percent << endl;

	_resFile << "#sim-pred:\t" << _s_conditions_pre.size() << endl;
#ifdef LIMIT_SIMULATION_ITERATIONS
	_resFile << "self-loop-allowance:\t" << Reach::sim_self_loop_allowance << endl;
#else
	_resFile << "self-loop-allowance:\t" << 0 << endl;
#endif
	_resFile << "#sim-it:\t" << num_sim_iterations << endl;
	_resFile << "time-dist-refine-sim:\t" << sim_time_percent << endl;

	_resFile << "time-dist-pre:\t" << pre_time_percent << endl;
	_resFile << "time-dist-cti:\t"  << cti_time_percent << endl;
	_resFile << "time-dist-br:\t" << tb_time_percent << endl;
	_resFile << "time-dist-fp:\t" << fp_time_percent << endl;
	_resFile << "time-dist-refine:\t" << refine_time_percent << endl;
	_resFile << "time-dist-solv_set:\t"  << solver_set_time_percent << endl;
	_resFile << "time-dist-inv-check:\t" << inv_check_time_percent << endl;
	_resFile << "time-dist-sum:\t" << sum_time_percent << endl;

	_resFile << "time-dist-inv-induct-check:\t" << induction_check_time_percent << endl;
	_resFile << "time-dist-cti-set:\t"  << cti_i_time_percent << endl;
	_resFile << "time-dist-cti-val:\t"  << cti_val_time_percent << endl;
	_resFile << "time-dist-extra-fp:\t" << fp_extra_time_percent << endl;

	_resFile << "time-dist-extra:\t" << extra_time_percent << endl;
	_resFile << "time-dist-timeout:\t" << timeout_time_percent << endl;

	_resFile << "time-q-avg-ab:\t" << avr_time_ab << endl;
	_resFile << "time-q-avg-bv:\t" << avr_time_bv << endl;
	_resFile << "time-q-max-ab:\t" << (Solver::time_max_ab_query / 1000.0) << endl;
	_resFile << "time-q-max-bv:\t" << (Solver::time_max_bv_query / 1000.0) << endl;
	_resFile << "time-q-max-ab-assume:\t" << (Solver::time_max_ab_mus_query / 1000.0) << endl;
	_resFile << "time-q-max-bv-assume:\t" << (Solver::time_max_bv_mus_query / 1000.0) << endl;

	_resFile << "avg-time-q-oneshot-ab-sat:\t"   << ((Solver::num_ab_sat_oneshot == 0) ? 0 : ((double) Solver::time_ab_sat_oneshot / Solver::num_ab_sat_oneshot / 1000.0)) << endl;
	_resFile << "avg-time-q-oneshot-ab-unsat:\t" << ((Solver::num_ab_unsat_oneshot == 0) ? 0 : ((double) Solver::time_ab_unsat_oneshot / Solver::num_ab_unsat_oneshot / 1000.0)) << endl;
	_resFile << "avg-time-q-inc-ab-sat:\t"       << ((Solver::num_ab_sat_inc == 0) ? 0 : ((double) Solver::time_ab_sat_inc / Solver::num_ab_sat_inc / 1000.0)) << endl;
	_resFile << "avg-time-q-inc-ab-unsat:\t"     << ((Solver::num_ab_unsat_inc == 0) ? 0 : ((double) Solver::time_ab_unsat_inc / Solver::num_ab_unsat_inc / 1000.0)) << endl;
	_resFile << "avg-time-q-assume-ab-sat:\t"       << ((Solver::num_ab_sat_mus == 0) ? 0 : ((double) Solver::time_ab_sat_mus / Solver::num_ab_sat_mus / 1000.0)) << endl;
	_resFile << "avg-time-q-assume-ab-unsat:\t"     << ((Solver::num_ab_unsat_mus == 0) ? 0 : ((double) Solver::time_ab_unsat_mus / Solver::num_ab_unsat_mus / 1000.0)) << endl;
	_resFile << "avg-time-q-ab-timeout:\t"       << ((Solver::num_ab_timeout == 0) ? 0 : ((double) Solver::time_ab_timeout / Solver::num_ab_timeout / 1000.0)) << endl;

	_resFile << "#q-oneshot-ab-sat:\t" << Solver::num_ab_sat_oneshot << endl;
	_resFile << "#q-oneshot-ab-unsat:\t" << Solver::num_ab_unsat_oneshot << endl;
	_resFile << "#q-inc-ab-sat:\t" << Solver::num_ab_sat_inc << endl;
	_resFile << "#q-inc-ab-unsat:\t" << Solver::num_ab_unsat_inc << endl;
	_resFile << "#q-assume-ab-sat:\t" << Solver::num_ab_sat_mus << endl;
	_resFile << "#q-assume-ab-unsat:\t" << Solver::num_ab_unsat_mus << endl;
	_resFile << "#q-ab-timeout:\t" << Solver::num_ab_timeout << endl;

	_resFile << "time-q-oneshot-ab-sat:\t" << ((double) Solver::time_ab_sat_oneshot / 1000000) << endl;
	_resFile << "time-q-oneshot-ab-unsat:\t" << ((double) Solver::time_ab_unsat_oneshot / 1000000) << endl;
	_resFile << "time-q-inc-ab-sat:\t" << ((double) Solver::time_ab_sat_inc / 1000000) << endl;
	_resFile << "time-q-inc-ab-unsat:\t" << ((double) Solver::time_ab_unsat_inc / 1000000) << endl;
	_resFile << "time-q-assume-ab-sat:\t" << ((double) Solver::time_ab_sat_mus / 1000000) << endl;
	_resFile << "time-q-assume-ab-unsat:\t" << ((double) Solver::time_ab_unsat_mus / 1000000) << endl;
	_resFile << "time-q-ab-timeout:\t" << ((double) Solver::time_ab_timeout / 1000000) << endl;

	_resFile << "avg-time-q-oneshot-bv-sat:\t"   << ((Solver::num_bv_sat_oneshot == 0) ? 0 : ((double) Solver::time_bv_sat_oneshot / Solver::num_bv_sat_oneshot / 1000.0)) << endl;
	_resFile << "avg-time-q-oneshot-bv-unsat:\t" << ((Solver::num_bv_unsat_oneshot == 0) ? 0 : ((double) Solver::time_bv_unsat_oneshot / Solver::num_bv_unsat_oneshot / 1000.0)) << endl;
	_resFile << "avg-time-q-inc-bv-sat:\t"       << ((Solver::num_bv_sat_inc == 0) ? 0 : ((double) Solver::time_bv_sat_inc / Solver::num_bv_sat_inc / 1000.0)) << endl;
	_resFile << "avg-time-q-inc-bv-unsat:\t"     << ((Solver::num_bv_unsat_inc == 0) ? 0 : ((double) Solver::time_bv_unsat_inc / Solver::num_bv_unsat_inc / 1000.0)) << endl;
	_resFile << "avg-time-q-assume-bv-sat:\t"       << ((Solver::num_bv_sat_mus == 0) ? 0 : ((double) Solver::time_bv_sat_mus / Solver::num_bv_sat_mus / 1000.0)) << endl;
	_resFile << "avg-time-q-assume-bv-unsat:\t"     << ((Solver::num_bv_unsat_mus == 0) ? 0 : ((double) Solver::time_bv_unsat_mus / Solver::num_bv_unsat_mus / 1000.0)) << endl;
	_resFile << "avg-time-q-bv-timeout:\t"       << ((Solver::num_bv_timeout == 0) ? 0 : ((double) Solver::time_bv_timeout / Solver::num_bv_timeout / 1000.0)) << endl;

	_resFile << "#q-oneshot-bv-sat:\t" << Solver::num_bv_sat_oneshot << endl;
	_resFile << "#q-oneshot-bv-unsat:\t" << Solver::num_bv_unsat_oneshot << endl;
	_resFile << "#q-inc-bv-sat:\t" << Solver::num_bv_sat_inc << endl;
	_resFile << "#q-inc-bv-unsat:\t" << Solver::num_bv_unsat_inc << endl;
	_resFile << "#q-assume-bv-sat:\t" << Solver::num_bv_sat_mus << endl;
	_resFile << "#q-assume-bv-unsat:\t" << Solver::num_bv_unsat_mus << endl;
	_resFile << "#q-bv-timeout:\t" << Solver::num_bv_timeout << endl;

	_resFile << "time-q-oneshot-bv-sat:\t" << ((double) Solver::time_bv_sat_oneshot / 1000000) << endl;
	_resFile << "time-q-oneshot-bv-unsat:\t" << ((double) Solver::time_bv_unsat_oneshot / 1000000) << endl;
	_resFile << "time-q-inc-bv-sat:\t" << ((double) Solver::time_bv_sat_inc / 1000000) << endl;
	_resFile << "time-q-inc-bv-unsat:\t" << ((double) Solver::time_bv_unsat_inc / 1000000) << endl;
	_resFile << "time-q-assume-bv-sat:\t" << ((double) Solver::time_bv_sat_mus / 1000000) << endl;
	_resFile << "time-q-assume-bv-unsat:\t" << ((double) Solver::time_bv_unsat_mus / 1000000) << endl;
	_resFile << "time-q-bv-timeout:\t" << ((double) Solver::time_bv_timeout / 1000000) << endl;

	double avg_sz_muses_inp_ab = (Solver::num_ab_muses_calls != 0) ? ((double) Solver::total_sz_ab_muses_input / Solver::num_ab_muses_calls) : 0;
	double avg_sz_muses_inp_bv = (Solver::num_bv_muses_calls != 0) ? ((double) Solver::total_sz_bv_muses_input / Solver::num_bv_muses_calls) : 0;

	double avg_num_itr_muses_ab = (Solver::num_ab_muses_calls != 0) ? ((double) Solver::total_itr_ab_muses_input / Solver::num_ab_muses_calls) : 0;
	double avg_num_itr_muses_bv = (Solver::num_bv_muses_calls != 0) ? ((double) Solver::total_itr_bv_muses_input / Solver::num_bv_muses_calls) : 0;

	_resFile << "avg-size-in-muses-ab:\t" << avg_sz_muses_inp_ab << endl;
	_resFile << "avg-size-in-muses-bv:\t" << avg_sz_muses_inp_bv << endl;
	_resFile << "avg-#it-muses-ab:\t" << avg_num_itr_muses_ab << endl;
	_resFile << "avg-#it-muses-bv:\t" << avg_num_itr_muses_bv << endl;
	_resFile << "max-size-in-muses-ab:\t" << Solver::max_sz_ab_muses_input << endl;
	_resFile << "max-size-in-muses-bv:\t" << Solver::max_sz_bv_muses_input << endl;

	double avg_sz_query_ab = (total_calls_ab != 0) ? ((double) Solver::total_sz_ab_query / total_calls_ab) : 0;
	double avg_sz_query_bv = (total_calls_bv != 0) ? ((double) Solver::total_sz_bv_query / total_calls_bv) : 0;

	_resFile << "avg-size-query-ab:\t" << avg_sz_query_ab << endl;
	_resFile << "avg-size-query-bv:\t" << avg_sz_query_bv << endl;
	_resFile << "max-size-query-ab:\t" << Solver::max_sz_ab_query << endl;
	_resFile << "max-size-query-bv:\t" << Solver::max_sz_bv_query << endl;

	double num_core_ab = Solver::num_ab_mus_core;
	double num_core_bv = Solver::num_bv_mus_core;
	double avg_sz_core_ab = (num_core_ab != 0) ? ((double) Solver::total_sz_ab_core / num_core_ab) : 0;
	double avg_sz_core_bv = (num_core_bv != 0) ? ((double) Solver::total_sz_bv_core / num_core_bv) : 0;

	_resFile << "avg-size-core-ab:\t" << avg_sz_core_ab << endl;
	_resFile << "avg-size-core-bv:\t" << avg_sz_core_bv << endl;
	_resFile << "max-size-core-ab:\t" << Solver::max_sz_ab_core << endl;
	_resFile << "max-size-core-bv:\t" << Solver::max_sz_bv_core << endl;

	_resFile << "br-mus-#mus:\t" << Reach::num_muses_reach << endl;
	_resFile << "br-mus-avg-sz-hard-core:\t" << avg_sz_hard_core_muses_reach << endl;
	_resFile << "br-mus-avg-sz-soft-core:\t" << avg_sz_soft_core_muses_reach << endl;
	_resFile << "br-mus-avg-sz-out-core:\t"  << avg_sz_out_core_muses_reach << endl;
	_resFile << "br-mus-avg-sz-hard-min:\t" << avg_sz_hard_min_muses_reach << endl;
	_resFile << "br-mus-avg-sz-soft-min:\t" << avg_sz_soft_min_muses_reach << endl;
	_resFile << "br-mus-avg-sz-out-min:\t"  << avg_sz_out_min_muses_reach << endl;


	_resFile << "#frame-restrictions:\t" << _numFrameRes << endl;
	_resFile << "#cubes:\t" << _numTbCalls << endl;
	_resFile << "#cubes-subsumed:\t" << CLAUSE::_numSubsumedCube << endl;
	_resFile << "avg-sz-frame-restriction:\t" << avg_sz_frame_restrict << endl;
	_resFile << "max-sz-frame-restriction:\t" << _maxFrameRes << endl;

	_resFile << "reset-context-#:\t" << numResetContext << endl;
	_resFile << "reset-frame-solver-#:\t" << FRAME_SOLVER::numResetFrames << endl;
	_resFile << "reset-context-threshold:\t" << Inst::maxContextCalls << endl;
	_resFile << "reset-frame-solver-threshold:\t" << REFRESH_FRAMES_THRESHOLD << endl;
	_resFile << "reset-frame-solver-query-threshold:\t" << REFRESH_FRAMES_QUERY_THRESHOLD << endl;
#ifdef RESET_CONTEXT_AFTER_FP
	_resFile << "reset-context-fp:\t" << "true" << endl;
#else
	_resFile << "reset-context-fp:\t" << "false" << endl;
#endif
#ifdef RESET_FRAME_SOLVERS_AFTER_FP
	_resFile << "reset-frame-fp:\t" << "true" << endl;
#else
	_resFile << "reset-frame-fp:\t" << "false" << endl;
#endif
#ifdef NEW_SOLVER_FOR_AB_MUS
	_resFile << "reset-new-mus-solver:\t" << "true" << endl;
#else
	_resFile << "reset-mus-solver:\t" << "false" << endl;
#endif
#ifdef REFRESH_FRAME_SOLVERS_QUERY
	_resFile << "refresh-frame-solver-query:\t" << "true" << endl;
#else
	_resFile << "refresh-frame-solver-query:\t" << "false" << endl;
#endif
#ifdef REFRESH_FRAME_SOLVERS
	_resFile << "refresh-frame-solver:\t" << "true" << endl;
#else
	_resFile << "refresh-frame-solver:\t" << "false" << endl;
#endif
#ifdef _Y2
	_resFile << "y2-force-reset-#:\t" << y2_API::g_num_reset << endl;
#endif

	_resFile << "avg-sz-ab-cube:\t" << avg_sz_ab_cube << endl;
	_resFile << "max-sz-ab-cube:\t" << _maxSzAbCube << endl;

	_resFile << "avg-sz-cc-cube:\t" << avg_sz_cc_cube << endl;
	_resFile << "max-sz-cc-cube:\t" << _maxSzCcCube << endl;

	_resFile << "#local-eq:\t" << num_local_eq << endl;
	_resFile << "#local-eq-sig:\t" << num_local_eq_sig << endl;
	_resFile << "#local-eq-num:\t" << num_local_eq_num << endl;
	_resFile << "#local-eq-uf:\t" << num_local_eq_uf << endl;

	_resFile << "%t1-ab-cube:\t" << perc_t1_ab_cube << endl;
	_resFile << "%t2-ab-cube:\t" << perc_t2_ab_cube << endl;
	_resFile << "%t3-ab-cube:\t" << perc_t3_ab_cube << endl;
	_resFile << "%t4-ab-cube:\t" << perc_t4_ab_cube << endl;

	_resFile << "%t1-ab-mus:\t" << perc_t1_sel_ab_cube << endl;
	_resFile << "%t2-ab-mus:\t" << perc_t2_sel_ab_cube << endl;
	_resFile << "%t3-ab-mus:\t" << perc_t3_sel_ab_cube << endl;
	_resFile << "%t4-ab-mus:\t" << perc_t4_sel_ab_cube << endl;

	_resFile << "#t1-ab:\t" << _nT1 << endl;
	_resFile << "#t2-ab:\t" << _nT2 << endl;
	_resFile << "#t3-ab:\t" << _nT3 << endl;
	_resFile << "#t4-ab:\t" << _nT4 << endl;

  _resFile << "%cube-ab-sig-eq-sig:\t"  << perc_coi_sig_eq_sig_ab_cube << endl;
  _resFile << "%cube-ab-sig-eq-num:\t"  << perc_coi_sig_eq_num_ab_cube << endl;
  _resFile << "%cube-ab-sig-eq-oth:\t"  << perc_coi_sig_eq_oth_ab_cube << endl;
  _resFile << "%cube-ab-num-eq-oth:\t"  << perc_coi_num_eq_oth_ab_cube << endl;
  _resFile << "%cube-ab-oth-eq-oth:\t"  << perc_coi_oth_eq_oth_ab_cube << endl;
  _resFile << "%cube-ab-sig-neq-sig:\t"  << perc_coi_sig_neq_sig_ab_cube << endl;
  _resFile << "%cube-ab-sig-neq-num:\t"  << perc_coi_sig_neq_num_ab_cube << endl;
  _resFile << "%cube-ab-sig-neq-oth:\t"  << perc_coi_sig_neq_oth_ab_cube << endl;
  _resFile << "%cube-ab-num-neq-oth:\t"  << perc_coi_num_neq_oth_ab_cube << endl;
  _resFile << "%cube-ab-oth-neq-oth:\t"  << perc_coi_oth_neq_oth_ab_cube << endl;
  _resFile << "%cube-ab-sig-bool:\t"  << perc_coi_sig_bool_ab_cube << endl;
  _resFile << "%cube-ab-up:\t"  << perc_coi_up_ab_cube << endl;
  _resFile << "%cube-ab-oth:\t"  << perc_coi_oth_ab_cube << endl;

  _resFile << "%cube-ab-sel-sig-eq-sig:\t"  << perc_coi_sig_eq_sig_sel_ab_cube << endl;
  _resFile << "%cube-ab-sel-sig-eq-num:\t"  << perc_coi_sig_eq_num_sel_ab_cube << endl;
  _resFile << "%cube-ab-sel-sig-eq-oth:\t"  << perc_coi_sig_eq_oth_sel_ab_cube << endl;
  _resFile << "%cube-ab-sel-num-eq-oth:\t"  << perc_coi_num_eq_oth_sel_ab_cube << endl;
  _resFile << "%cube-ab-sel-oth-eq-oth:\t"  << perc_coi_oth_eq_oth_sel_ab_cube << endl;
  _resFile << "%cube-ab-sel-sig-neq-sig:\t"  << perc_coi_sig_neq_sig_sel_ab_cube << endl;
  _resFile << "%cube-ab-sel-sig-neq-num:\t"  << perc_coi_sig_neq_num_sel_ab_cube << endl;
  _resFile << "%cube-ab-sel-sig-neq-oth:\t"  << perc_coi_sig_neq_oth_sel_ab_cube << endl;
  _resFile << "%cube-ab-sel-num-neq-oth:\t"  << perc_coi_num_neq_oth_sel_ab_cube << endl;
  _resFile << "%cube-ab-sel-oth-neq-oth:\t"  << perc_coi_oth_neq_oth_sel_ab_cube << endl;
  _resFile << "%cube-ab-sel-sig-bool:\t"  << perc_coi_sig_bool_sel_ab_cube << endl;
  _resFile << "%cube-ab-sel-up:\t"  << perc_coi_up_sel_ab_cube << endl;
  _resFile << "%cube-ab-sel-oth:\t"  << perc_coi_oth_sel_ab_cube << endl;

  _resFile << "%coi-ab-cube:\t" << perc_coi_ab_cube << endl;
  _resFile << "%pred-ab-cube:\t" << perc_pred_ab_cube << endl;
  _resFile << "%fproj-ab-cube:\t" << perc_fproj_ab_cube << endl;
  _resFile << "%proj-ab-cube:\t" << perc_proj_ab_cube << endl;

  _resFile << "%coi-ab-mus:\t" << perc_coi_sel_ab_cube << endl;
  _resFile << "%pred-ab-mus:\t" << perc_pred_sel_ab_cube << endl;
  _resFile << "%fproj-ab-mus:\t" << perc_fproj_sel_ab_cube << endl;
  _resFile << "%proj-ab-mus:\t" << perc_proj_sel_ab_cube << endl;

  _resFile << "%coi-sig-eq-ab-cube:\t"  << perc_coi_sig_eq_ab_cube << endl;
  _resFile << "%coi-sig-neq-ab-cube:\t" << perc_coi_sig_neq_ab_cube << endl;
  _resFile << "%coi-num-eq-ab-cube:\t"  << perc_coi_num_eq_ab_cube << endl;
  _resFile << "%coi-num-neq-ab-cube:\t" << perc_coi_num_neq_ab_cube << endl;
  _resFile << "%coi-other-ab-cube:\t" << perc_coi_other_ab_cube << endl;

  _resFile << "%coi-sig-eq-ab-mus:\t"  << perc_coi_sig_eq_sel_ab_cube << endl;
  _resFile << "%coi-sig-neq-ab-mus:\t" << perc_coi_sig_neq_sel_ab_cube << endl;
  _resFile << "%coi-num-eq-ab-mus:\t"  << perc_coi_num_eq_sel_ab_cube << endl;
  _resFile << "%coi-num-neq-ab-mus:\t" << perc_coi_num_neq_sel_ab_cube << endl;
  _resFile << "%coi-other-ab-mus:\t" << perc_coi_other_sel_ab_cube << endl;

	_resFile << "%fproj-sig-eq-ab-cube:\t"  << perc_fproj_sig_eq_ab_cube << endl;
	_resFile << "%fproj-sig-neq-ab-cube:\t" << perc_fproj_sig_neq_ab_cube << endl;
	_resFile << "%fproj-num-eq-ab-cube:\t"  << perc_fproj_num_eq_ab_cube << endl;
	_resFile << "%fproj-num-neq-ab-cube:\t" << perc_fproj_num_neq_ab_cube << endl;

	_resFile << "%fproj-sig-eq-ab-mus:\t"  << perc_fproj_sig_eq_sel_ab_cube << endl;
	_resFile << "%fproj-sig-neq-ab-mus:\t" << perc_fproj_sig_neq_sel_ab_cube << endl;
	_resFile << "%fproj-num-eq-ab-mus:\t"  << perc_fproj_num_eq_sel_ab_cube << endl;
	_resFile << "%fproj-num-neq-ab-mus:\t" << perc_fproj_num_neq_sel_ab_cube << endl;

	_resFile << "%proj-sig-eq-ab-cube:\t"  << perc_proj_sig_eq_ab_cube << endl;
	_resFile << "%proj-sig-neq-ab-cube:\t" << perc_proj_sig_neq_ab_cube << endl;
	_resFile << "%proj-num-eq-ab-cube:\t"  << perc_proj_num_eq_ab_cube << endl;
	_resFile << "%proj-num-neq-ab-cube:\t" << perc_proj_num_neq_ab_cube << endl;

	_resFile << "%proj-sig-eq-ab-mus:\t"  << perc_proj_sig_eq_sel_ab_cube << endl;
	_resFile << "%proj-sig-neq-ab-mus:\t" << perc_proj_sig_neq_sel_ab_cube << endl;
	_resFile << "%proj-num-eq-ab-mus:\t"  << perc_proj_num_eq_sel_ab_cube << endl;
	_resFile << "%proj-num-neq-ab-mus:\t" << perc_proj_num_neq_sel_ab_cube << endl;

	_resFile << "%subs-ab-cube:\t" << perc_subs_ab_cube << endl;
	_resFile << "%subs-ab-mus:\t" << perc_subs_sel_ab_cube << endl;

	_resFile << "avg-#sv-ab-cube:\t" << avg_num_sv_ab_cube << endl;
	_resFile << "max-#sv-ab-cube:\t" << _maxNumSvAbCube << endl;
	_resFile << "avg-tsb-ab-cube:\t" << avg_tsb_ab_cube << endl;
	_resFile << "max-tsb-ab-cube:\t" << _maxTsbSvAbCube << endl;

	_resFile << "%ab-relevancy:\t" << relevantPercent << endl;

	_resFile << "%coi-cc-cube:\t" << perc_coi_cc_cube << endl;
	_resFile << "%pred-cc-cube:\t" << perc_pred_cc_cube << endl;
	_resFile << "%fproj-cc-cube:\t" << perc_fproj_cc_cube << endl;
	_resFile << "%proj-cc-cube:\t" << perc_proj_cc_cube << endl;

	_resFile << "%fproj-sig-eq-cc-cube:\t"  << perc_fproj_sig_eq_cc_cube << endl;
	_resFile << "%fproj-sig-neq-cc-cube:\t" << perc_fproj_sig_neq_cc_cube << endl;
	_resFile << "%fproj-num-eq-cc-cube:\t"  << perc_fproj_num_eq_cc_cube << endl;
	_resFile << "%fproj-num-neq-cc-cube:\t" << perc_fproj_num_neq_cc_cube << endl;

	_resFile << "%proj-sig-eq-cc-cube:\t"  << perc_proj_sig_eq_cc_cube << endl;
	_resFile << "%proj-sig-neq-cc-cube:\t" << perc_proj_sig_neq_cc_cube << endl;
	_resFile << "%proj-num-eq-cc-cube:\t"  << perc_proj_num_eq_cc_cube << endl;
	_resFile << "%proj-num-neq-cc-cube:\t" << perc_proj_num_neq_cc_cube << endl;

#ifdef LEARN_INIT_PREDICATE
	_resFile << "learn-init-preds:\t" << "true" << endl;
#else
	_resFile << "learn-init-preds:\t" << "false" << endl;
#endif
#ifdef LEARN_INIT_PREDICATE_ADD_PRED
	_resFile << "learn-init-preds-add:\t" << "true" << endl;
#else
	_resFile << "learn-init-preds-add:\t" << "false" << endl;
#endif
#ifdef LEARN_INIT_PREDICATE_PROCESS_PRED
	_resFile << "learn-init-preds-process:\t" << "true" << endl;
#else
	_resFile << "learn-init-preds-process:\t" << "false" << endl;
#endif
#ifdef LEARN_INIT_PREDICATE_TRAVERSE_INIT
	_resFile << "learn-init-preds-traverse:\t" << "true" << endl;
#else
	_resFile << "learn-init-preds-traverse:\t" << "false" << endl;
#endif
	_resFile << "assumption-orig-#:\t" << numAssume << endl;
	_resFile << "assumption-orig-#sig:\t" << numAssumeSig << endl;
	_resFile << "assumption-orig-#reg:\t" << numAssumeReg << endl;
	_resFile << "assumption-#regnext:\t" << _assume_regNext.size() << endl;
	_resFile << "assumption-#lemmas:\t" << numAssumeLemmas << endl;
	_resFile << "assumption-#init:\t" << numAssumeInit << endl;

	_resFile << "max-frame:\t" << _frame_idx << endl;
	_resFile << "#ref-it:\t" << _num_dp_refine << endl;

	_resFile << "time:\t" << totalTime << endl;
	_resFile << "time-avr:\t" << timeReason << endl;
	_resFile << "#refs:\t" << _numRefinements << endl;
	_resFile << "memory:\t" << memory_usage << endl;

	_resFile << "result-avr:\t" << result << endl;
	if(exit_val == EXIT_HOLD)
	{
		_resFile << "#invariants:\t" << (_numStrongInvariant + _numWeakInvariant) << endl;
		_resFile << "sz-invariant:\t" << _szInvariant << endl;
		_resFile << "#implications:\t" << _numImplications << endl;
		_resFile << "acext-length:\t-1" << endl;
		_resFile << "cext-length:\t-1" << endl;
	}
	else if (exit_val == EXIT_VIOL)
	{
		_resFile << "frame-conv:\t-1" << endl;
		_resFile << "#invariants:\t-1" << endl;
		_resFile << "sz-invariant:\t-1" << endl;
		_resFile << "#implications:\t-1" << endl;
		_resFile << "acext-length:\t" << _rcext_orig.size() << endl;
		_resFile << "cext-length:\t" << _cext_idx.size() << endl;
	}
	else if(exit_val == EXIT_HOLD_TRIV)
	{
		_resFile << "frame-conv:\t0" << endl;
		_resFile << "#invariants:\t1" << endl;
		_resFile << "sz-invariant:\t1" << endl;
		_resFile << "#implications:\t-1" << endl;
		_resFile << "acext-length:\t-1" << endl;
		_resFile << "cext-length:\t-1" << endl;
	}
	else
	{
		_resFile << "frame-conv:\t-1" << endl;
		_resFile << "#invariants:\t-1" << endl;
		_resFile << "sz-invariant:\t-1" << endl;
		_resFile << "#implications:\t-1" << endl;
		_resFile << "acext-length:\t-1" << endl;
		_resFile << "cext-length:\t-1" << endl;
//		exit(1);
	}
	_resFile << "#warnings:\t" << Inst::num_warnings << endl;

	_resFile << "y2-#terms:\t" << yices_num_terms() << endl;
	_resFile << "y2-#types:\t" << yices_num_types() << endl;
	for (auto& v: Solver::g_solver_stats)
		v.second.print(_resFile, v.first);

#ifdef TEST_REFINE_FLUSH
	#ifdef TEST_REFINE_PARTIAL_FLUSH
		_resFile << "flush-mode:\tpartial" << endl;
	#else
		#ifdef TEST_REFINE_FULL_FLUSH
			_resFile << "flush-mode:\tfull" << endl;
		#else
			#ifdef TEST_REFINE_FP
				_resFile << "flush-mode:\tfp" << endl;
			#else
				assert(0);
			#endif
		#endif
	#endif
#else
	_resFile << "flush-mode:\tnone" << endl;
#endif

	double avg_len_acext = (refine_flush_count != 0) ? ((double) refine_flush_len_acext / refine_flush_count) : 0;
	double avg_position_acext = (refine_flush_count != 0) ? ((double) refine_flush_level / refine_flush_count) : 0;

	_resFile << "flush-count:\t" << refine_flush_count << endl;
	_resFile << "flush-avg-len-acext:\t" << avg_len_acext << endl;
	_resFile << "flush-avg-position:\t" << avg_position_acext << endl;
	_resFile << "flush-#frames:\t" << refine_flush_frames << endl;
	_resFile << "flush-#clauses:\t" << refine_flush_clauses << endl;

#ifdef Y2_EXP
	y2_API::print_solv_statistic(_resFile, y2_API::g_stat_cti,  "cti-");
  y2_API::print_solv_statistic(_resFile, y2_API::g_stat_br ,  "br--");
  y2_API::print_solv_statistic(_resFile, y2_API::g_stat_fp ,  "fp--");
  y2_API::print_solv_statistic(_resFile, y2_API::g_stat_core, "cor-");
  y2_API::print_solv_statistic(_resFile, y2_API::g_stat_min,  "min-");
  y2_API::print_solv_statistic(_resFile, y2_API::g_stat_reg,  "reg-");

  y2_statistic total;
  total.merge_stats(y2_API::g_stat_cti);
  total.merge_stats(y2_API::g_stat_br);
  total.merge_stats(y2_API::g_stat_fp);
  total.merge_stats(y2_API::g_stat_core);
  total.merge_stats(y2_API::g_stat_min);
  total.merge_stats(y2_API::g_stat_reg);
  y2_API::print_solv_statistic(_resFile, total,  "tot-");
#endif

	double tmp_ccext_time = ((double) Solver::time_ccext) / 1000000;
	_resFile << "time-ccext:\t" << tmp_ccext_time << endl;

	double tmp_time = ((double) Solver::time_tmp) / 1000000;
	_resFile << "time-tmp:\t" << tmp_time << endl;

	AVR_REF("\n(local equalities) #" << num_local_eq << endl);
	for (auto& p: _s_local_eq)
	{
    if (!p.first->find_next() && !p.second->find_next()) {
    	if (p.first->get_type() != Num) {
    		AVR_REF("            " << *p.first << " == " << *p.second << endl);
    	}
    	else {
    		AVR_REF("            " << *p.second << " == " << *p.first << endl);
    	}
    }
	}

	AVR_REF("\n(learned predicates) #" << _s_conditions_pre.size() << endl);
	for (auto& p: _s_conditions_pre)
	{
		AVR_REF("            " << *p << endl);
	}

  AVR_REF("\n(learned constants)  #" << _s_constants.size() << endl);
  for (auto& p: _s_constants)
  {
    AVR_REF("            " << *p << endl);
  }

  AVR_REF("\n(learned signals)    #" << _s_signals.size() << endl);
  for (auto& p: _s_signals)
  {
    AVR_REF("            " << *p << endl);
  }

  AVR_REF("\n(learned UFs)        #" << _s_uf.size() << endl);
  for (auto& p: _s_uf)
  {
    OpInst* op = OpInst::as(p);
    if (op) {
      Inst* w = op->get_wire();
      if (w) {
        AVR_REF("            " << *p << "\t:= " << *w << endl);
        continue;
      }
    }
    AVR_REF("            " << *p << endl);
  }

  AVR_REF("\n");
  AVR_REF("(#sim. iterations) " << num_sim_iterations  << "\n");
  AVR_REF("(#ref. iterations) " << _num_dp_refine << "\n");
  AVR_REF("(#refs) " << _numRefinements << "\n");
  AVR_REF("(#assump. lemmas)  " << numAssumeLemmas << "\n");
  AVR_REF("(#lemmas)          " << _negated_refs.size() << "\n");
}

bool Reach::node_count(Inst *top, bool init_visit) {
	if (init_visit) {
		Inst::init_visit();
		_int_node_cnt = 0;
		_bool_node_cnt = 0;
		_node_cnt = 0;
		_int_op_cnt = 0;
		_bool_op_cnt = 0;
		_op_stats.clear();
	}
	if (top->get_visit()) {
		return true;
	}
	top->set_visit();
	_node_cnt++;
	if (top->get_size() == 1) {
		_bool_node_cnt++;
	} else {
		_int_node_cnt++;
	}

	OpInst* op = OpInst::as(top);
	if(op){
		bool is_bool_operator = (op->get_euf_type_name() == "0");

		if(is_bool_operator == false){
#if 1
// op_stats with the index of operator string
			ostringstream oss;
			oss << OpInst::op2str(op->get_op());

			if( (op->get_op() != OpInst::Extract) &&
				(op->get_op() != OpInst::Concat)){
				const InstL* ch = op->get_children();
				if (ch) {
					for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it) {
						oss  << "_" << (*it)->get_size();
					}
				}
			}
#else
// op_stats with the index of operator type
#endif

			if(_op_stats.find(oss.str()) == _op_stats.end()){
				_op_stats[oss.str()] = 1;
			}else{
				_op_stats[oss.str()] += 1;
			}
			_int_op_cnt++;
		}else{

			ostringstream oss;
			oss << OpInst::op2str(op->get_op());

			for(auto& child: *(op->get_children()))
			{
				if (child->get_size() != 1)
				{
					oss << "_int";
					break;
				}
			}

			if(_op_stats.find(oss.str()) == _op_stats.end()){
				_op_stats[oss.str()] = 1;
			}else{
				_op_stats[oss.str()] += 1;
			}

			_bool_op_cnt++;
		}
	}

	const InstL* ch = top->get_children();
	if (ch) {
		for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it) {
			node_count(*it);
		}
	}

	return true;
}

//#ifdef DUMP_CEX_VAL
map<mpz_class, InstS > map_cex_insts;
InstS dump_cex_zeros;
InstS dump_cex_ones;
//#endif

void Reach::print_node(ostream& fout, Inst *e){
	if(e->get_type() == Num){
		NumInst* ve_num = NumInst::as(e);
		fout << ve_num->get_size() << "'d" << ve_num->get_num();
	}else if(e->get_type() == Sig){
		SigInst* ve_sig = SigInst::as(e);
		fout << ve_sig->get_name();
	}else if(e->get_type() == Op){
		fout << "n" << e->get_id() << "n";
	}else if(e->get_type() == Ex){
		fout << "n" << e->get_id() << "n";
	}else{
		assert(0);
	}
}

void Reach::setup_signal(int signum) {
	struct sigaction act;
//	if (signum == SIGXCPU)
	if (signum == SIGXCPU || signum == SIGABRT)
		act.sa_handler = SIGXCPU_handler;
	else
		act.sa_handler = SIGSEGV_handler;

	sigemptyset(&act.sa_mask);
//	sigaddset(&act.sa_mask, signum);
	act.sa_flags = 0;
	sigaction(signum, &act, NULL);
}

void Reach::global_init() {

	sigxcpu_handler_inst = this;
	signal(SIGALRM, solver_interrupt_handler);
//	setup_signal(SIGXCPU);
//	setup_signal(SIGABRT);
//	setup_signal(SIGSEGV);
	signal(SIGXCPU,	SIGXCPU_handler);
	signal(SIGABRT,	SIGXCPU_handler);
 	signal(SIGSEGV,	SIGSEGV_handler);

	_cube_partition = NULL;

	_derive_eq_corr_regs = (_config->get_arg(AVR_CORR_REGS_ARG) == "on") ? true : false;
	int eq_mode = atoi(_config->get_arg(AVR_DERIVE_EQ_MODE).c_str());
	_derive_eq_init_enabled = (eq_mode % 10 == 1);
	eq_mode /= 10;
	_derive_eq_coi_enabled = (eq_mode % 10 == 1);
	eq_mode /= 10;
	_derive_eq_ordering_mode = eq_mode % 10;
// 	cout << "###############################" << endl;
// 	cout << "derive_eq_init_enabled: " << _derive_eq_init_enabled << endl;
// 	cout << "derive_eq_coi_enabled: " << _derive_eq_coi_enabled<< endl;
// 	cout << "derive_eq_ordering_mode: " << _derive_eq_ordering_mode<< endl;
// 	cout << "###############################" << endl;
//
	//cout << "_config->get_arg(AVR_TIMEOUT_ARG): " << _config->get_arg(AVR_TIMEOUT_ARG) << endl;
	if(_config->get_arg(AVR_TIMEOUT_ARG) != "0"){
	 	_global_timeout = atoi(_config->get_arg(AVR_TIMEOUT_ARG).c_str());
	}else{
#ifdef ARM_RELEASE
		_global_timeout = 0;
#else
		_global_timeout = AVR_TIMEOUT;
#endif
//		_global_timeout = INT32_MAX;
	}

	if(_config->get_arg(AVR_MEM_LIMIT_ARG) != "0"){
	 	_global_memory_limit = atoi(_config->get_arg(AVR_MEM_LIMIT_ARG).c_str());
	}else{
#ifdef ARM_RELEASE
		_global_memory_limit = 0;
#else
		_global_memory_limit = AVR_MEMOUT;
#endif
//		_global_memory_limit = INT32_MAX;
	}


	AVR_LOG(15, 0, "Timeout: " << _global_timeout << ", Memory_limit: " << _global_memory_limit << endl);
#ifndef MICRO_ALARM
	AVR_LOG(15, 0, "\t" << AB_QUERY_TIMEOUT << " (abstract query)" << endl);
	AVR_LOG(15, 0, "\t" << BV_QUERY_TIMEOUT << " (concrete query)" << endl);
#else
	AVR_LOG(15, 0, "\t" << AB_QUERY_TIMEOUT / 1000000.0 << " (abstract query)" << endl);
	AVR_LOG(15, 0, "\t" << BV_QUERY_TIMEOUT / 1000000.0 << " (concrete query)" << endl);
#endif


	int cpu_lim = _global_timeout;
	int mem_lim = _global_memory_limit;
	if ((cpu_lim != 0) && (cpu_lim != INT32_MAX)){
		rlimit rl;
		getrlimit(RLIMIT_CPU, &rl);
		if(rl.rlim_max == RLIM_INFINITY || (rlim_t)cpu_lim < rl.rlim_max){
			rl.rlim_cur = cpu_lim;
			if (setrlimit(RLIMIT_CPU, &rl) == -1)
				printf("WARNING! Could not set resource limit: CPU-time.\n");
		} }

	// Set limit on virtual memory:
	if ((mem_lim != 0) && (mem_lim != INT32_MAX)){
		rlim_t new_mem_lim = (rlim_t)mem_lim * 1024*1024;
		rlimit rl;
		getrlimit(RLIMIT_AS, &rl);
		if(rl.rlim_max == RLIM_INFINITY || new_mem_lim < rl.rlim_max){
			rl.rlim_cur = new_mem_lim;
			if (setrlimit(RLIMIT_AS, &rl) == -1)
				printf("WARNING! Could not set resource limit: Virtual memory.\n");
		} }
// this will generate a "src/core" file which is loadable from any GUI debugger
// NOTE: you should disable "signal(SIGABRT,	SIGXCPU_handler);" to dump "core"
// NOTE: Instead, you can run "ulimit -c unlimited" on the shell
// 	rlimit core_limit = { RLIM_INFINITY, RLIM_INFINITY };
// 	if(setrlimit(RLIMIT_CORE, &core_limit) != 0){ // enable core dumps for debug builds
// 		printf("WARNING! Could not enable core dumps.\n");
// 	}
	_prop_timeout = atoi(_config->get_arg(AVR_PROP_TIMEOUT_ARG).c_str());
	_reach_timeout = atoi(_config->get_arg(AVR_REACH_TIMEOUT_ARG).c_str());

	_set_containment_cnt = 0;
	_redundant_cube_cnt = 0;
	_pme_fail_cnt = 0;
	_pme_succ_cnt = 0;


	/// Aman - Below mode removed in Averroes 2
//	_num_reach_solvers = atoi(_config->get_arg(AVR_NUM_REACH_SOLVER).c_str());
	/// END

	numResetContext = 0;
	numAssume = 0;
	numAssumeSig = 0;
	numAssumeReg = 0;
	numAssumeInit = 0;
	numAssumeLemmas = 0;

	_numTbCalls = 0;

	_maxSzAbCube = 0;
	_maxSzCcCube = 0;

	_sizeAbCube = 0;
	_sizeCcCube = 0;

	_numSvAbCube = 0;
	_tsbSvAbCube = 0;
	_maxNumSvAbCube = 0;
	_maxTsbSvAbCube = 0;

	_szT1 = 0;
	_szT2 = 0;
	_szT3 = 0;
	_szT4 = 0;

	_selT1 = 0;
	_selT2 = 0;
	_selT3 = 0;
	_selT4 = 0;

	_nT1 = 0;
	_nT2 = 0;
	_nT3 = 0;
	_nT4 = 0;

	_sizeCoiAbCube = 0;
	_sizeCoiCcCube = 0;
	_sizePredAbCube = 0;
	_sizePredCcCube = 0;
	_sizefProjAbCube = 0;
	_sizefProjCcCube = 0;
	_sizeProjAbCube = 0;
	_sizeProjCcCube = 0;
	_sizeSubsAbCube = 0;

  _cube_ab_SigEqSig = 0;
  _cube_ab_SigEqNum = 0;
  _cube_ab_SigEqOther = 0;
  _cube_ab_NumEqOther = 0;
  _cube_ab_OtherEqOther = 0;
  _cube_ab_SigNeqSig = 0;
  _cube_ab_SigNeqNum = 0;
  _cube_ab_SigNeqOther = 0;
  _cube_ab_NumNeqOther = 0;
  _cube_ab_OtherNeqOther = 0;
  _cube_ab_SigBool = 0;
  _cube_ab_Up = 0;
  _cube_ab_Other = 0;

  _sizeCoiNumEqAbCube = 0;
  _sizeCoiNumNeqAbCube = 0;
  _sizeCoiSigEqAbCube = 0;
  _sizeCoiSigNeqAbCube = 0;
  _sizeCoiOtherAbCube = 0;

	_sizefProjNumEqAbCube = 0;
	_sizefProjNumNeqAbCube = 0;
	_sizefProjSigEqAbCube = 0;
	_sizefProjSigNeqAbCube = 0;

	_sizefProjNumEqCcCube = 0;
	_sizefProjNumNeqCcCube = 0;
	_sizefProjSigEqCcCube = 0;
	_sizefProjSigNeqCcCube = 0;

	_sizeProjNumEqAbCube = 0;
	_sizeProjNumNeqAbCube = 0;
	_sizeProjSigEqAbCube = 0;
	_sizeProjSigNeqAbCube = 0;

	_sizeProjNumEqCcCube = 0;
	_sizeProjNumNeqCcCube = 0;
	_sizeProjSigEqCcCube = 0;
	_sizeProjSigNeqCcCube = 0;

	_numFrameRes = 0;
	_sumFrameRes = 0;
	_maxFrameRes = 0;

	_selCoiAbCube = 0;
	_selPredAbCube = 0;
	_selfProjAbCube = 0;
	_selProjAbCube = 0;
	_selSubsAbCube = 0;

  _cube_ab_SigEqSig_sel = 0;
  _cube_ab_SigEqNum_sel = 0;
  _cube_ab_SigEqOther_sel = 0;
  _cube_ab_NumEqOther_sel = 0;
  _cube_ab_OtherEqOther_sel = 0;
  _cube_ab_SigNeqSig_sel = 0;
  _cube_ab_SigNeqNum_sel = 0;
  _cube_ab_SigNeqOther_sel = 0;
  _cube_ab_NumNeqOther_sel = 0;
  _cube_ab_OtherNeqOther_sel = 0;
  _cube_ab_SigBool_sel = 0;
  _cube_ab_Up_sel = 0;
  _cube_ab_Other_sel = 0;

  _selCoiNumEqAbCube = 0;
  _selCoiNumNeqAbCube = 0;
  _selCoiSigEqAbCube = 0;
  _selCoiSigNeqAbCube = 0;
  _selCoiOtherAbCube = 0;

	_selfProjNumEqAbCube = 0;
	_selfProjNumNeqAbCube = 0;
	_selfProjSigEqAbCube = 0;
	_selfProjSigNeqAbCube = 0;

	_selProjNumEqAbCube = 0;
	_selProjNumNeqAbCube = 0;
	_selProjSigEqAbCube = 0;
	_selProjSigNeqAbCube = 0;

//	_ppc_solver = NULL;
//	_pme_solver = NULL; // the solver for the maximum expansion
	_cti_solver = NULL; // the solver that checks property

	_frame_idx = 0;
	_loop_idx = 0;
	_max_depth = 0;

	_relevantT = 0;
	_queryT = 0;

	_tb_eval_time = 0;
	_tb_pred_time = 0;
	_tb_fproj_time = 0;
	_tb_proj_time = 0;
	_tb_subs_time = 0;

	_tb_ct_initial_time = 0;
	_tb_ct_isblocked_time = 0;
	_tb_ct_containment_time = 0;
	_tb_ct_forwardfast_time = 0;

	_tb_setcontain_time = 0;
	_tb_updateincsolver_time = 0;

	_tb_cube_time = 0;
	_tb_reach_time = 0;
	_tb_val_time = 0;
	_tb_UNSAT_camus_time = 0;
	_tb_ct_time = 0;

	_tb_reach_mus_core = 0;
	_tb_reach_mus_min = 0;
	_tb_tmp_time = 0;

//	_bp_reach_time = 0;
//	_bp_SAT_camus_time = 0;
//	_bp_UNSAT_camus_time = 0;
//	_bp_gidx_time = 0;
//	_bp_ct_time = 0;
	_pre_time = 0;
	_cti_time = 0;
	_pme_time = 0;
//	_bp_time = 0;
	_cti_i_time = 0;
	_pme_i_time = 0;
	_solver_set_time = 0;

	_sim_time = 0;

	_cc_extra_tb_time = 0;
	_cc_extra_fp_time = 0;

	_draw_time = 0;

	_cc_time = 0;
	_fp_time = 0;
	_tb_time = 0;
	_dpr_time = 0;

	_cc_inv_time = 0;
	
	_nBlocks = 0; // the number of times blockState was called
	_nBlocksS = 0;
	_nBlocksU = 0;
	_nObligs = 0; // the number of proof obligations derived
	_nObligsS = 0;
	_nObligsU = 0;
	_nCubes = 0; // the number of cubes derived
	_nLiterals = 0;

	_pme_clauses_before = 0;
	_pme_literals_before = 0;
	_pme_clauses_after = 0;
	_pme_literals_after = 0;

	_coi_literals_before = 0;
	_coi_literals_after = 0;

	_mus_before = 0;
	_mus_lit = 0;
	_mus_cls = 0;
	_mus_cnt = 0;

	_node_cnt = 0;
	_bool_node_cnt = 0;
	_int_node_cnt = 0;
	_int_op_cnt = 0;
	_bool_op_cnt = 0;

	_refine_idx = 0;
	_num_dp_refine = 0;
	_refine_seq_idx = 0;

	_sat_res = false;
	_feas_sat_res = false;
	_iter = 0;
	_finished = false;

	_accum_dp_lemmas = 0;
	_num_dp_refs_zero_lemmas = 0;

	_max_funcLevel = 0;
}

void Reach::dp_refinement_cleanup() {
	struct rusage usage;
	struct timeval start_time, end_time;
	long long time_diff;
	TIME_S(start_time);

	cext.reset();

	int size_negated_refs = _negated_refs.size();
	int num_learnt_lemmas = size_negated_refs - _accum_dp_lemmas;
	if(num_learnt_lemmas == 0){
		_num_dp_refs_zero_lemmas++;
	}
	_accum_dp_lemmas = size_negated_refs;

	_nDPLemmasL.push_back(num_learnt_lemmas);
	_nFramesL.push_back(_frame_idx);
	_queue.PQ_clear();
	_tb_queue.PQ_clear();
#ifndef AVR_INCREMENTAL_DP_REFINEMENT
	_frame_idx = 0;
	_negated_cubes.clear();
	_negated_cubes[0] = _conjunct_init;
	_cubes.clear();
#endif
	//	_cubes.clear();
	AVR_LOG(4, 1, "########		DATAPATH REFINEMENT END" << endl);
	AVR_LOG(4, 1, "##############################################" << endl);
	//dump_execution_time();
#ifdef AVR_DUMP_DP_FRAME
	{
		for (int i = 1; i <= _frame_idx; i++) {
			ostringstream str;
			str << _config->get_working_dir() << "/dp_frame" << "_" << _num_dp_refine << "_" << i << ".txt";
			ofstream framef;
			access_file(framef, str.str());
			framef << _cubes[i] << endl;
			framef.close();
		}
	}
#endif
	_num_dp_refine++;
	TIME_E(start_time, end_time, _dpr_time);

	print_frame_summary(_frame_idx);

  if (_num_dp_refine > MAX_REF_ITERATIONS) {
  	Inst::g_result = f_poor_ab;
  	cout << "\t(error: too many refinement iterations)" << endl;
  	cout << "\t\t(try improving abstraction technique)" << endl;
  	cout << "\t\t(exiting)" << endl;
  	assert(0);
  }
}

// Check the correctness of the CEXT returned by AVR
// This also dumps a bit-level partial CEXT showing the path from I to ~P
/// Aman
// 	Corrupted
void Reach::print_cex() {

	/// Aman
//	return;
//
////	AVR_LOG(8, 0, endl);
////	AVR_LOG(8, 0, "Printing CEXT_tbq2" << endl);
////	AVR_LOG(8, 0, "CEXT-length: " << _tb_queue2.PQ_size() << endl);
////	for(PQElement* pq_elem = _tb_queue2.PQ_head(); pq_elem != NULL; pq_elem = pq_elem->pNext)
////	{
////		AVR_LOG(8, 0, "F[ " << pq_elem->frame << "] - " << *(pq_elem->cube) << endl);
////	}
////	AVR_LOG(8, 0, endl);
//
//	AVR_LOG(8, 0, endl);
//	AVR_LOG(8, 0, "Printing CEXT_tbq1" << endl);
//	AVR_LOG(8, 0, "CEXT-length: " << _tb_queue.PQ_size() << endl);
//	for(PQElement* pq_elem = _tb_queue.PQ_head(); pq_elem != NULL; pq_elem = pq_elem->pNext)
//	{
//		AVR_LOG(8, 0, "F[ " << pq_elem->frame << "] - " << *(pq_elem->cube) << endl);
//	}
//	AVR_LOG(8, 0, endl);
//
//	AVR_LOG(8, 0, endl << "####	CEXT validation" << endl);
//	AVR_LOG(8, 0, "CEXT-length: " << _tb_queue.PQ_size() << endl);
//
//	vector<PQElement*> list_cext;
//	for(PQElement* pq_elem = _tb_queue2.PQ_head(); pq_elem != NULL; pq_elem = pq_elem->pNext)
//	{
//		list_cext.push_back(pq_elem);
//	}
//
//	AVR_LOG(8, 6, "list_cext: " << list_cext.size() << endl);
//	for (vector<PQElement*>::iterator it = list_cext.begin(); it != list_cext.end(); it++)
//	{
//		AVR_LOG(8, 6, "F[ " << (*it)->frame << "] - " << *((*it)->cube) << endl);
//	}
//	AVR_LOG(8, 6, endl);
//
//	PQElement *head = list_cext[0];
//	Inst *cube = head->cube;
//	int idx = head->frame;
//
//	InstL conjunct_reach;
//	Inst *ve_reach;
//
//	/// 0 step check (Does cube[0] contains I ?)
//	conjunct_reach = _negated_cubes[0];
//	conjunct_reach.push_back(cube);
//	cout << "conjunct_reach: " << conjunct_reach << endl;
//	ve_reach = OpInst::create(OpInst::LogAnd, conjunct_reach);
//
//	SolverAPI* bv_solver;
//	bool bv_res;
//
//	bv_solver = dynamic_cast<SolverAPI*> (new_conc_solver(1));
//	bv_res = bv_solver->check_sat(ve_reach);
//	AVR_LOG(8, 0, " cube[" << idx << "] " << (bv_res ? "VALID" : "INVALID") << endl);
//	assert(bv_res == true);
//
//	retrieve_cex_val(ve_reach, bv_solver, false, true);
//	print_concrete_min_term();
//
//	for (int i = 1; i < list_cext.size(); i++)
//	{
//		conjunct_reach.clear();
//
//		/// Start from previous cube
//		conjunct_reach.push_back(list_cext[i - 1]->cube);
//		cout << "Asserting " << *(list_cext[i - 1]->cube) << endl;
//
////		/// Start from I
////		if (i == 1)
////		{
////			conjunct_reach = _negated_cubes[0];
////			cout << "Asserting " << _negated_cubes[0] << endl;
////		}
////		/// Else start from states with previous set of assignments
////		else
////		{
////			InstL l_cex_regs;
////			for(InstToInstM::iterator mit = _m_sn.begin(); mit != _m_sn.end(); ++mit){
////				Inst *tve = mit->first; // next state variable
////				SigInst *sig_tve = SigInst::as(tve);
////
////				Inst* coi = tve->acex_coi;
////				SigInst *sig_temp = SigInst::as(tve->acex_coi);
////				if (sig_temp)
////				{
////					coi = sig_temp->acex_coi;
////				}
//////				cout << "ORIG_CEX: " << *sig_tve << "	=	" << *(coi) << endl;
////
////				string sname = sig_tve->get_name();
////				size_t loc = sname.find("$next");
////				assert(loc != sname.npos);
////				string sname_orig = sname.substr(0, loc);
////				Inst *sig_orig = SigInst::create(sname_orig, tve->get_size());
////
////				l_cex_regs.push_back(OpInst::create(OpInst::Eq, sig_orig, coi));
////			}
////			for (InstL::iterator it = l_cex_regs.begin(); it != l_cex_regs.end(); it++)
////			{
////				conjunct_reach.push_back(*it);
////			}
////			cout << "Asserting " << l_cex_regs << endl;
////		}
//
//		/// Add P && T
//		conjunct_reach.push_back(_ve_model);
//		conjunct_reach.push_back(_ve_prop_eq_1);
//		conjunct_reach.push_back(_ve_model_nsf);
//		cout << "Asserting " << "P && T" << endl;
//
//		/// End to !P+
//		if (i == (list_cext.size() - 1))
//		{
//			conjunct_reach.push_back(_ve_model_next);
//			conjunct_reach.push_back(_ve_prop_next_eq_0);
//			cout << "Asserting " << "!P+" << endl;
//		}
//		/// or P+ (if not end)
//		else
//		{
//			conjunct_reach.push_back(_ve_model_next);
//			conjunct_reach.push_back(_ve_prop_next_eq_1);
//			cout << "Asserting " << "P+" << endl;
//		}
//
//		/// Adding cube$next
//		cube = list_cext[i]->cube;
//		Inst* cube_next = all_pre2next(cube, true);
//		conjunct_reach.push_back(cube_next);
//		cout << "Asserting " << *cube_next << endl;
//
////		cout << "conjunct_reach: " << conjunct_reach << endl;
//		ve_reach = OpInst::create(OpInst::LogAnd, conjunct_reach);
//
//		/// Check Query for SAT
//		SolverAPI* bv_solver_2;
//		bool bv_res_2;
//
//		bv_solver_2 = dynamic_cast<SolverAPI*> (new_conc_solver(1));
//		bv_res_2 = bv_solver_2->check_sat(ve_reach);
//		AVR_LOG(8, 0, " cube[" << i << "] " << (bv_res_2 ? "VALID" : "INVALID") << endl);
//
//		/// Assert SAT for Query
//		if (bv_res_2 == false)
//		{
//			InstL dummy_list;
//			InstLL muses;
//
//			AVR_LOG(8, 0, "Finding Muses" << endl);
//			int get_muses_input_size = _viol.size();
//
//			int res = bv_solver_2->get_muses(0, dummy_list, conjunct_reach, muses);
//
//			int num_muses_terms = 0;
//			for (InstLL::iterator it_muses2 = muses.begin(); it_muses2 != muses.end(); ++it_muses2) {
//				num_muses_terms += it_muses2->size();
//			}
//			AVR_LOG(8, 0, "bv_solver_2->get_muses(): " << get_muses_input_size << " => " << muses.size() << ", " << num_muses_terms << " : res = " << res << endl);
//
//			int it_count = 0;
//			cout << "Printing muses" << endl;
//			for (InstLL::iterator it = muses.begin(); it != muses.end(); it++)
//				cout << it_count++ << *it << endl;
//
//		}
//		assert(bv_res_2 == true);
//
//		retrieve_cex_val(ve_reach, bv_solver_2, false, true);
//		print_concrete_min_term();
//
//	}
//	/// END

//	return; //TODO keep this while debugging the new cube derivation

#ifdef ARM_RELEASE
	return;
#endif

	struct rusage usage;
	struct timeval start_time, end_time;
	long long time_diff, accum_time = 0;

  if (Config::g_print_witness) {
		string fname = _config->get_working_dir() + "/cex.witness";
		ofstream out;
		out.open(fname.c_str(), ios_base::app);
		Inst* dest = (_cext_idx.size() == 0) ? _ve_model : _ve_model_next;
		InstL propList;
		OpInst* op = OpInst::as(dest);
		if (op && op->get_op() == OpInst::Eq) {
			Inst* rhs = op->get_children()->back();
			collect_all_cubes(rhs, true);
			propList.swap(_collected_cubes);
		}
		else
			propList.push_back(dest);
		cext.print(out, _cext_idx.size(), propList);
		out.close();
  }

	AVR_LOG(8, 0, "==================================================" << endl);
	AVR_LOG(8, 0, "ACEXT-length: " << _rcext_orig.size() << endl);
	AVR_LOG(8, 0, "CEXT-length : " << _cext_idx.size() << endl);
	AVR_LOG(8, 0, "==================================================" << endl);

#ifdef AVR_REMOVE_INPUT_FROM_CUBE
	// the first proof_oblig should have the smallest priority
	// derive CEXT in reverse order from the elements in tb_queue
	vector<PQElement*> list_cext;
	for(PQElement* pq_elem = _tb_queue.PQ_head(); pq_elem != NULL; pq_elem = pq_elem->pNext){
		list_cext.push_back(pq_elem);
		AVR_LOG(8, 0, "pq_elem->cube: " << pq_elem->frame << ", " << *(pq_elem->cube) << endl);
		AVR_LOG(8, 0, "pq_elem->cube: " << pq_elem->frame << ":" << endl);
		new_print(cout, pq_elem->cube, true);
	}

	if(list_cext.empty()){
		return;
	}

//				list<PQElement*>::iterator q_it = list_cext.begin();
	PQElement *head = list_cext[0];
//		PQElement *head = _tb_queue.PQ_head();

	int idx = head->frame;
	_refine_seq_idx = idx;
	Inst *cube = head->cube;

#ifdef DEBUG_CEXT_VALIDATION
	AVR_LOG(8, 0, "cube[0]: " << endl);
	new_print(cout, cube, true);
	//cout << "cube[0]: " << *cube << endl;
#endif
	InstL conjunct_reach;
	Inst *ve_reach;

	unsigned frame_idx = 0;
	InstL l_cex_regs;
	z3_API* bv_solver;
	bool bv_res;

	InstS s_inputs;
	collect_inputs(OpInst::create(OpInst::LogAnd, _ve_model_nsf, _ve_model), s_inputs, true);

	for(frame_idx = 0; frame_idx < list_cext.size(); ++frame_idx){
		bool first_path = (frame_idx == 0);
		bool last_path = (frame_idx == (list_cext.size() - 1));
		conjunct_reach.clear();

		if(first_path == false){
			conjunct_reach.clear();
			if(!l_cex_regs.empty()){
				conjunct_reach.push_back(OpInst::create(OpInst::LogAnd, l_cex_regs));
			}
			//conjunct_reach = l_cex_regs;
			conjunct_reach.push_back(_ve_model);
			conjunct_reach.push_back(_ve_prop_eq_1);
		}else{
			//conjunct_reach.push_back(OpInst::create(OpInst::LogAnd, _negated_cubes[0]));
			conjunct_reach = _negated_cubes[0];
		}

		conjunct_reach.push_back(_ve_model_nsf);
		if(last_path){
			conjunct_reach.push_back(_ve_model_next);
			conjunct_reach.push_back(_ve_prop_next_eq_0);
		}else{
			head = list_cext[frame_idx+1];
			cube = head->cube;
			Inst *cube_next = all_pre2next(cube, true);
			conjunct_reach.push_back(cube_next);
		}
		ve_reach = OpInst::create(OpInst::LogAnd, conjunct_reach);
// 			collect_cubes(ve_reach, true);
// 			ve_reach = OpInst::create(OpInst::LogAnd, _collected_cubes);

		TIME_S(start_time);
		bv_solver = dynamic_cast<z3_API*> (new_conc_solver(1));
		bv_res = bv_solver->check_sat(ve_reach);
		TIME_E(start_time, end_time, accum_time);
		AVR_LOG(8, 0, (bv_res ? "VALID" : "INVALID") << " path from R" << frame_idx << " to ");
		if(last_path){
			AVR_LOG(8, 0, "!p");
		}else{
			AVR_LOG(8, 0, "R" << (frame_idx+1));
		}
		AVR_LOG(8, 0, ", runtime: " << double(time_diff)/1000000 << " sec" << endl);
		assert(bv_res == true);
		//cout << "ve_reach: " << *ve_reach << endl;
		retrieve_cex_val(ve_reach, bv_solver, false, true);
		l_cex_regs.clear();

		map<string, Inst*> debug_cex;
		for(InstToInstM::iterator mit = _m_sn.begin(); mit != _m_sn.end(); ++mit){
			Inst *tve = mit->first; // next state variable
			SigInst *sig_tve = SigInst::as(tve);
			string sname = sig_tve->get_name();
			size_t loc = sname.find("$next");
			assert(loc != sname.npos);
			string sname_orig = sname.substr(0, loc);
			Inst *sig_orig = SigInst::create(sname_orig, tve->get_size());
#ifdef DEBUG_CEXT_VALIDATION
			if(tve->acex_coi != NumInst::create(0, tve->get_size())){
				debug_cex[sname_orig] = tve->acex_coi;
			}
			//cout << "CEX: " << *sig_orig << "	=	" << *(tve->acex_coi) << endl;
#endif
			l_cex_regs.push_back(OpInst::create(OpInst::Eq, sig_orig, tve->acex_coi));
		}

		for(InstS::iterator sit = s_inputs.begin(); sit != s_inputs.end(); ++sit){
			Inst *tve = *sit;
			SigInst *sig_tve = SigInst::as(tve);
			string sname_orig = sig_tve->get_name();
#ifdef DEBUG_CEXT_VALIDATION
			if(tve->acex_coi != NumInst::create(0, tve->get_size())){
				debug_cex[sname_orig] = tve->acex_coi;
			}
			//cout << "CEX: " << *sig_orig << "	=	" << *(tve->acex_coi) << endl;
#endif
		}

		for(map<string, Inst*>::iterator mit2 = debug_cex.begin(); mit2 != debug_cex.end(); ++mit2){
			//if((mit2->first).find("vo_d601") != string::npos)
			{
				AVR_LOG(8, 0, "CEX: " << (mit2->first) << "	=	" << *(mit2->second) << endl);
			}
		}

	}
#else	//AVR_REMOVE_INPUT_FROM_CUBE
//	return;
// 	if(_config->get_arg(AVR_CORR_REGS_ARG) == "on"){
// 		AVR_LOG(4, 1, "^^^^		print_cex" << endl);
// 		InstS check_dup;
// 		for (InstToInstM::iterator it = _m_corr_regs.begin(); it != _m_corr_regs.end(); it++) {
// 			Inst *sig_a = it->first;
// 			Inst *sig_b = it->second;
//
// 			if (check_dup.find(sig_a) != check_dup.end()) {
// 				continue;
// 			}
// 			check_dup.insert(sig_b);
//
// 			bool res = conc_solver()->get_assignment(sig_a, sig_a->cex_mpz);
// 			bool res2 = conc_solver()->get_assignment(sig_b, sig_b->cex_mpz);
// // 			bool res = _refine_bv_solver->get_assignment(sig_a, sig_a->cex_mpz);
// // 			bool res2 = _refine_bv_solver->get_assignment(sig_b, sig_b->cex_mpz);
// 			if (res && res2) {
// 				if (sig_a->cex_mpz != sig_b->cex_mpz) {
// 					cout << *sig_a << " : " << *sig_b << "	=>	";
// //					gmp_printf("%Zd : %Zd\n", sig_a->cex_mpz, sig_b->cex_mpz);
// 					cout << sig_a->cex_mpz << " : " << sig_b->cex_mpz << endl;
// 				}
// 			}
// 			// 		else{
// 			// 			cout << "#ERR# " << *sig_a << " : " << *sig_b << "	=>	";
// 			// 			cout << sig_a->cex_val << " : " << sig_b->cex_val << endl;
// 			// 		}
// 		}
// 	}else
	{
#if 1
//		// the first proof_oblig should have the smallest priority
//		// derive CEXT in reverse order from the elements in tb_queue
//		int count = 0;
//		for(vector< int >::iterator it = _cext_idx.begin(); it != _cext_idx.end(); it++)
//		{
//			if (count == 0)
//			{
//				AVR_LOG(8, 0, "C[" << count++ << "] @ " << "F[" << _rcext_orig[(*it)].frame << "] - I && " << *(_rcext_orig[(*it)].cube) << endl);
//			}
//			else
//			{
//				AVR_LOG(8, 0, "C[" << count++ << "] @ " << "F[" << _rcext_orig[(*it)].frame << "] - " << *(_rcext_orig[(*it)].cube) << endl);
//			}
//		}
//		AVR_LOG(8, 0, "C[End] !P" << endl);
		AVR_LOG(8, 0, endl << "Verified via simulation" << endl);
		AVR_LOG(8, 0, "==================================================" << endl);
		return;

		vector<ABSTRACT_CUBE*> list_cext;
		for(deque< ABSTRACT_CUBE >::iterator it = _rcext_orig.begin(); it != _rcext_orig.end(); it++)
		{
			list_cext.push_back(&(*it));
		}

//				list<PQElement*>::iterator q_it = list_cext.begin();
		ABSTRACT_CUBE* head = list_cext[0];
#endif
//		PQElement *head = _tb_queue.PQ_head();
		int idx = head->frame;
		_refine_seq_idx = idx;
		Inst *cube = head->cube;

#ifdef DEBUG_CEXT_VALIDATION
		AVR_LOG(8, 0, "cube[0]: " << endl);
		new_print(cout, cube, true);
		//cout << "cube[0]: " << *cube << endl;
#endif
		InstL conjunct_reach;
		Inst *ve_reach;
		conjunct_reach = _conjunct_init;
		conjunct_reach.push_back(cube);
		ve_reach = OpInst::create(OpInst::LogAnd, conjunct_reach);
// 		collect_cubes(ve_reach, true);
// 		ve_reach = OpInst::create(OpInst::LogAnd, _collected_cubes);

//ve_reach = cube;

//		cout << "conjunct_reach: " << conjunct_reach << endl;

		unsigned frame_idx = 0;
		InstL l_cex_regs;
		bool bv_res;

		TIME_S(start_time);
		Solver* bv_solver = (new_conc_solver(false, AVR_BV_IDX, mdl));
		bv_res = bv_solver->check_sat(ve_reach, BV_QUERY_TIMEOUT, true);
//assert(0);
		TIME_E(start_time, end_time, accum_time);
		AVR_LOG(8, 0, (bv_res ? "VALID" : "INVALID") << " C[" << frame_idx << "]" << ", runtime: " << double(time_diff)/1000000 << " sec" << endl);
		assert(bv_res == true);

		retrieve_cex_val(ve_reach, bv_solver, false, true);
		map<int, InstL> m_cext;
		InstS s_inputs;
		collect_inputs(cube, s_inputs, true);

		InstS s_inputs2;
		map<int, InstS> m_cext2;
		collect_inputs(OpInst::create(OpInst::LogAnd, _ve_model_nsf, _ve_model), s_inputs2, true);

//		cout << "s_inputs : " << s_inputs << endl;
//		cout << "s_inputs2 : " << s_inputs2 << endl;


		for(InstS::iterator sit = s_inputs.begin(); sit != s_inputs.end(); ++sit){
			Inst *tve = *sit;

			SigInst *sig_tve = SigInst::as(tve);
			string sname = sig_tve->get_name();

			int seq_depth = 0;
			size_t loc = sname.find("$next");
			string sname_orig = (loc == sname.npos) ? sname : sname.substr(0, loc);

//			cout << "sname: " << sname << endl;
			while(loc != sname.npos){
				++seq_depth;
				loc = sname.find("$next", loc+1);
//				cout << "loc: " << loc << ", seq_depth: " << seq_depth << endl;
			}
			Inst *sig_orig = SigInst::create(sname_orig, tve->get_size(), tve->get_sort());
			m_cext[seq_depth].push_back(OpInst::create(OpInst::Eq, sig_orig, tve->acex_coi));
			m_cext2[seq_depth].insert(sig_orig);

#ifdef DEBUG_CEXT_VALIDATION
 			cout << "####	" << *tve << " <= " << tve->get_size() << "'d" << tve->cex_mpz << endl;
 			AVR_LOG(8, 0, *sig_orig << " : " << tve->get_size() << " @ " << seq_depth << " : " << *(tve->acex_coi) << endl);
#endif
		}

		for(frame_idx = 0; frame_idx < list_cext.size(); ++frame_idx){
			bool first_path = (frame_idx == 0);
			bool last_path = (frame_idx == (list_cext.size() - 1));
			conjunct_reach.clear();

			if(first_path == false){
/// Aman
#if 0	// cube validity check is optional
//#if 1	// cube validity check is optional
/// END
				// check to see if the cube includes the cex derived in the previous step
				head = list_cext[frame_idx];
				cube = head->cube;
				cout << "cube : " << *cube << endl;
				if(!l_cex_regs.empty()){
					conjunct_reach.push_back(OpInst::create(OpInst::LogAnd, l_cex_regs));
			 		cout << "1	conjunct_reach:" << endl << conjunct_reach << endl;
				}
				//conjunct_reach = l_cex_regs;
				if(!m_cext[frame_idx].empty()){
					conjunct_reach.push_back(OpInst::create(OpInst::LogAnd, m_cext[frame_idx]));
			 		cout << "2	conjunct_reach:" << endl << conjunct_reach << endl;
				}
				conjunct_reach.push_back(cube);
				
		 		cout << endl << "####	conjunct_reach:" << endl << conjunct_reach << endl;
				ve_reach = OpInst::create(OpInst::LogAnd, conjunct_reach);
// 				collect_cubes(ve_reach, true);
// 				ve_reach = OpInst::create(OpInst::LogAnd, _collected_cubes);

				TIME_S(start_time);
				bv_solver = dynamic_cast<z3_API*> (new_conc_solver(1));
				bv_res = bv_solver->check_sat(ve_reach);
				TIME_E(start_time, end_time, accum_time);
				AVR_LOG(8, 0, (bv_res ? "VALID" : "INVALID") << " cube[" << frame_idx << "]");
				AVR_LOG(8, 0, ", runtime: " << double(time_diff)/1000000 << " sec" << endl);
				assert(bv_res == true);
#endif
				// path check
				conjunct_reach.clear();
				if(!l_cex_regs.empty()){
					conjunct_reach.push_back(OpInst::create(OpInst::LogAnd, l_cex_regs));
				}
				//conjunct_reach = l_cex_regs;
			}else{
				//conjunct_reach.push_back(OpInst::create(OpInst::LogAnd, _negated_cubes[0]));
				conjunct_reach = _conjunct_init;
			}

			/// Aman
//			conjunct_reach.push_back(list_cext[frame_idx]->cube);
			/// END

			for(InstS::iterator sit = s_inputs2.begin(); sit != s_inputs2.end(); ++sit){
				Inst *tve = *sit;
				if(m_cext2[frame_idx].find(tve) == m_cext2[frame_idx].end()){
					SigInst* sig = SigInst::as(tve);
					if (sig && !sig->get_name().compare(SigInst::as(_ve_prop_eq_1)->get_name()))
					{
						tve = OpInst::create(OpInst::Eq, tve, NumInst::create(1, tve->get_size(), tve->get_sort()));
					}
					else
						tve = OpInst::create(OpInst::Eq, tve, NumInst::create(0, tve->get_size(), tve->get_sort()));
					conjunct_reach.push_back(tve);
				}else{
//					AVR_LOG(8, 0, "tve: " << *tve << endl);
				}
			}

			if(!m_cext[frame_idx].empty()){
				conjunct_reach.push_back(OpInst::create(OpInst::LogAnd, m_cext[frame_idx]));
			}


			conjunct_reach.push_back(_ve_model_nsf);
			if(last_path){
				conjunct_reach.push_back(_ve_model_next);
				conjunct_reach.push_back(_ve_prop_next_eq_0);
			}

//			cout << "conjunct_reach : " << conjunct_reach << endl;

			ve_reach = OpInst::create(OpInst::LogAnd, conjunct_reach);
// 			collect_cubes(ve_reach, true);
// 			ve_reach = OpInst::create(OpInst::LogAnd, _collected_cubes);

			TIME_S(start_time);
			bv_solver = dynamic_cast<SOLVER_BV*> (new_conc_solver(false, AVR_BV_IDX, mdl));
			bv_res = bv_solver->check_sat(ve_reach, BV_QUERY_TIMEOUT, true);
			TIME_E(start_time, end_time, accum_time);
			ostringstream out;
			out << (bv_res ? "VALID" : "INVALID") << " path from R" << frame_idx << " to ";
			if(last_path){
				out << "!P";
			}else{
				out << "R" << (frame_idx+1);
			}
			AVR_LOG(8, 0, out.str() << ", runtime: " << double(time_diff)/1000000 << " sec" << endl);
			assert(bv_res == true);
//			cout << "ve_reach: " << *ve_reach << endl;
			retrieve_cex_val(ve_reach, bv_solver, false, true);
			l_cex_regs.clear();

			map<string, Inst*> debug_cex;
			for(InstToPairBoolM::iterator mit = Inst::_m_sn.begin(); mit != Inst::_m_sn.end(); ++mit){
				Inst *tve = mit->first; // next state variable
				SigInst *sig_tve = SigInst::as(tve);
//				cout << "ORIG_CEX: " << *sig_tve << "	=	" << *(tve->acex_coi) << endl;
				string sname = sig_tve->get_name();
				size_t loc = sname.find("$next");
				assert(loc != sname.npos);
				string sname_orig = sname.substr(0, loc);
				Inst *sig_orig = SigInst::create(sname_orig, tve->get_size(), tve->get_sort());
#ifdef DEBUG_CEXT_VALIDATION
				if(tve->acex_coi != NumInst::create(0, tve->get_size())){
					debug_cex[sname_orig] = tve->acex_coi;
				}
				cout << "CEX: " << *sig_orig << "	=	" << *(tve->acex_coi) << endl;
#endif
				l_cex_regs.push_back(OpInst::create(OpInst::Eq, sig_orig, tve->acex_coi));
			}
			for(map<string, Inst*>::iterator mit2 = debug_cex.begin(); mit2 != debug_cex.end(); ++mit2){
				//if((mit2->first).find("vo_d601") != string::npos)
				{
					AVR_LOG(8, 0, "CEX: " << (mit2->first) << "	=	" << *(mit2->second) << endl);
				}
			}
			AVR_LOG(8, 0, endl);
// cout << endl << "vo_d601_reg/q$7_0$next : " << endl;
// new_print(cout, _m_sn[SigInst::create("vo_d601_reg/q$7_0$next", 8)], true);
// //assert(0);


// 			for(InstS::iterator sit = s_inputs2.begin(); sit != s_inputs2.end(); ++sit){
// 				Inst *tve = *sit;
// 				if(tve->acex_coi != NumInst::create(0, tve->get_size())){
// 					cout << "tve: " << *tve << ", " << *(tve->acex_coi) << endl;
// 				}
// 			}


		}
	}
#endif	//AVR_REMOVE_INPUT_FROM_CUBE
	AVR_LOG(8, 0, "CEXT-check successful!" << endl);
	AVR_LOG(8, 0, "==================================================" << endl);
	return;
}

void Reach::dump_hm_sizes() {
#ifdef DETAILED_STAT_DUMP
	int total = ExInst::hm_ExInst.size() + SigInst::hm_SigInst.size() + NumInst::hm_NumInst.size()
			+ OpInst::hm_OpInst.size() + OpInst::hm_ITEInst.size() + OpInst::hm_ETCInst.size();
	AVR_LOG(15, 0, endl);
	AVR_LOG(15, 0, "\t# of Inst.                  : " << Inst::total_nodes()        << "\t(" << sizeof(Inst)    << " bytes each)" << endl);
	AVR_LOG(15, 0, "\t  ExInst::hm_ExInst.size()  : " << ExInst::hm_ExInst.size()   << "\t(" << sizeof(ExInst)  << " bytes each)" << endl);
	AVR_LOG(15, 0, "\t  SigInst::hm_SigInst.size(): " << SigInst::hm_SigInst.size() << "\t(" << sizeof(SigInst) << " bytes each)" << endl);
	AVR_LOG(15, 0, "\t  NumInst::hm_NumInst.size(): " << NumInst::hm_NumInst.size() << "\t(" << sizeof(NumInst) << " bytes each)" << endl);
	AVR_LOG(15, 0, "\t  OpInst::hm_OpInst.size()  : " << OpInst::hm_OpInst.size()   << "\t(" << sizeof(OpInst)  << " bytes each)" << endl);
	AVR_LOG(15, 0, "\t  OpInst::hm_ITEInst.size() : " << OpInst::hm_ITEInst.size()  << "\t(" << sizeof(OpInst)  << " bytes each)" << endl);
	AVR_LOG(15, 0, "\t  OpInst::hm_ETCInst.size() : " << OpInst::hm_ETCInst.size()  << "\t(" << sizeof(OpInst)  << " bytes each)" << endl);
	AVR_LOG(15, 0, "\tTotal                       : " << total << endl);
	AVR_LOG(15, 0, endl);
	AVR_LOG(15, 0, "\tMemory (est.)               : " << ((Inst::total_nodes()        * sizeof(Inst))    / 1024.0 / 1024.0) << " MB" << endl);
	AVR_LOG(15, 0, "\t  ExInst                    : " << ((ExInst::hm_ExInst.size()   * sizeof(ExInst))  / 1024.0 / 1024.0) << " MB" << endl);
	AVR_LOG(15, 0, "\t  SigInst                   : " << ((SigInst::hm_SigInst.size() * sizeof(SigInst)) / 1024.0 / 1024.0) << " MB" << endl);
	AVR_LOG(15, 0, "\t  NumInst                   : " << ((NumInst::hm_NumInst.size() * sizeof(NumInst)) / 1024.0 / 1024.0) << " MB" << endl);
	AVR_LOG(15, 0, "\t  OpInst::OP                : " << ((OpInst::hm_OpInst.size()   * sizeof(OpInst))  / 1024.0 / 1024.0) << " MB" << endl);
	AVR_LOG(15, 0, "\t  OpInst::ITE               : " << ((OpInst::hm_ITEInst.size()  * sizeof(OpInst))  / 1024.0 / 1024.0) << " MB" << endl);
	AVR_LOG(15, 0, "\t  OpInst::ETC               : " << ((OpInst::hm_ETCInst.size()  * sizeof(OpInst))  / 1024.0 / 1024.0) << " MB" << endl);
#endif
}


void Reach::add_zero_lemmas(Inst *top, bool init_visit) {
	if (init_visit) {
		Inst::init_visit();
	}
	if (top->get_visit())
		return;
	top->set_visit();
	if (top->get_type() == Ex) {
		const InstL* ch = top->get_children();
		if (ch) {
			// a -> b
			// !a + b
			Inst *tve = ch->front();
			ExInst *t_ex = ExInst::as(top);
			if(t_ex){
				Inst *ve_zero = ExInst::create(NumInst::create(0, tve->get_size(), tve->get_sort()), t_ex->get_hi(), t_ex->get_lo());
				Inst *dp_lemma = OpInst::create(OpInst::Eq, ve_zero, NumInst::create(0, top->get_size(), tve->get_sort()));
				if(_s_dpl.find(dp_lemma) == _s_dpl.end()){
					_s_dpl.insert(dp_lemma);
					_negated_refs.push_back(dp_lemma);
				}
			}
		}
	}
	if (top->get_type() == Op) {
		OpInst *t_op = OpInst::as(top);
		if (t_op) {
			OpInst::OpType t = t_op->get_op();
			switch (t) {
			case OpInst::Mult:
				break;
			case OpInst::Add:
			case OpInst::AddC:
			case OpInst::Sub:
			case OpInst::BitWiseAnd:
			case OpInst::BitWiseOr:
			case OpInst::Minus:
			case OpInst::ReductionAnd:
			case OpInst::ReductionOr:
			case OpInst::Gr:
			case OpInst::Le:
			case OpInst::Concat:{
				const InstL* ch = top->get_children();
// 				if(t == OpInst::Le){
// 					if(ch->front()->get_size() != ch->back()->get_size()){
// 						//cout << *ch->front() << t << *ch->back() << endl;
// 						//cout << endl <<*ch->front() << endl << t << endl ;//<< *ch->back() << endl;
// // 						cout <<"ch->front()" << endl;
// // 						new_print(cout, ch->front(), true);
// // 						cout <<"ch->back()" << endl;
// // 						new_print(cout, ch->back(), true);
// 						cout <<"top" << endl;
// 						new_print(cout, top, true);
//
// 						assert(0);
// 					}
// 				}
				
				if (ch) {
					InstL new_chs;
					for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it){
						Inst *tve = *it;
						new_chs.push_back(NumInst::create(0, tve->get_size(), tve->get_sort()));
					}
					Inst *ve_zero = OpInst::create(t, new_chs, top->get_size());
					Inst *dp_lemma = OpInst::create(OpInst::Eq, ve_zero, NumInst::create(0, top->get_size(), top->get_sort()));
					if(_s_dpl.find(dp_lemma) == _s_dpl.end()){
						_s_dpl.insert(dp_lemma);
						_negated_refs.push_back(dp_lemma);
					}
				}
			}break;
			case OpInst::ReductionNand:
			case OpInst::ReductionNor:
			case OpInst::GrEq:
			case OpInst::LeEq:{
				const InstL* ch = top->get_children();
				if (ch) {
					InstL new_chs;
					for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it){
						Inst *tve = *it;
						new_chs.push_back(NumInst::create(0, tve->get_size(), tve->get_sort()));
					}
					Inst *ve_zero = OpInst::create(t, new_chs);
					Inst *dp_lemma = OpInst::create(OpInst::Eq, ve_zero, NumInst::create(1, top->get_size(), top->get_sort()));
					if(_s_dpl.find(dp_lemma) == _s_dpl.end()){
						_s_dpl.insert(dp_lemma);
						_negated_refs.push_back(dp_lemma);
					}
				}
			}break;
			case OpInst::BitWiseXor:{
				if(top->get_size() <= 64){
					Inst *num_zero = NumInst::create(0, top->get_size(), top->get_sort());
					long long num = (1 << top->get_size()) - 1;
					Inst *num_m1 = NumInst::create(num, top->get_size(), top->get_sort());
					Inst *dp_lemma_1 = OpInst::create(OpInst::Eq, OpInst::create(OpInst::BitWiseXor, num_zero, num_zero), num_zero);
					Inst *dp_lemma_2 = OpInst::create(OpInst::Eq, OpInst::create(OpInst::BitWiseXor, num_zero, num_m1), num_m1);
					Inst *dp_lemma_3 = OpInst::create(OpInst::Eq, OpInst::create(OpInst::BitWiseXor, num_m1, num_zero), num_m1);
					Inst *dp_lemma_4 = OpInst::create(OpInst::Eq, OpInst::create(OpInst::BitWiseXor, num_m1, num_m1), num_zero);
					if(_s_dpl.find(dp_lemma_1) == _s_dpl.end()){
						_s_dpl.insert(dp_lemma_1);
						_negated_refs.push_back(dp_lemma_1);
					}
					if(_s_dpl.find(dp_lemma_2) == _s_dpl.end()){
						_s_dpl.insert(dp_lemma_2);
						_negated_refs.push_back(dp_lemma_2);
					}
					if(_s_dpl.find(dp_lemma_3) == _s_dpl.end()){
						_s_dpl.insert(dp_lemma_3);
						_negated_refs.push_back(dp_lemma_3);
					}
					if(_s_dpl.find(dp_lemma_4) == _s_dpl.end()){
						_s_dpl.insert(dp_lemma_4);
						_negated_refs.push_back(dp_lemma_4);
					}
				}
			}break;
			case OpInst::BitWiseNot:{
				if(top->get_size() <= 64){
					Inst *num_zero = NumInst::create(0, top->get_size(), top->get_sort());
					long long num = (((long long)1) << top->get_size()) - 1;
					//long long num = (1 << top->get_size()) - 1;
					Inst *num_m1 = NumInst::create(num, top->get_size(), top->get_sort());
					Inst *dp_lemma_1 = OpInst::create(OpInst::Eq, OpInst::create(OpInst::BitWiseNot, num_zero), num_m1);
					Inst *dp_lemma_2 = OpInst::create(OpInst::Eq, OpInst::create(OpInst::BitWiseNot, num_m1), num_zero);
					if(_s_dpl.find(dp_lemma_1) == _s_dpl.end()){
						_s_dpl.insert(dp_lemma_1);
						_negated_refs.push_back(dp_lemma_1);
					}
					if(_s_dpl.find(dp_lemma_2) == _s_dpl.end()){
						_s_dpl.insert(dp_lemma_2);
						_negated_refs.push_back(dp_lemma_2);
					}
				}
			}break;
			case OpInst::ShiftL:
			case OpInst::ShiftR:
			case OpInst::AShiftR:
			case OpInst::AShiftL:
			case OpInst::RotateL:
			case OpInst::RotateR:
			case OpInst::VShiftL:
			case OpInst::VShiftR:
			case OpInst::VAShiftL:
			case OpInst::VAShiftR:
			case OpInst::VRotateL:
			case OpInst::VRotateR:
			case OpInst::VEx:{
				const InstL* ch = top->get_children();
				if (ch) {
					// a -> b
					// !a + b
					Inst *num_zero = NumInst::create(0, top->get_size(), top->get_sort());
					Inst *tve = ch->front();
					if(tve->get_type() != Num){
						Inst *ve_neq = OpInst::create(OpInst::NotEq, tve, NumInst::create(0, tve->get_size(), tve->get_sort()));
						Inst *dp_lemma = OpInst::create(OpInst::LogOr, ve_neq, OpInst::create(OpInst::Eq, top, num_zero));
						if(_s_dpl.find(dp_lemma) == _s_dpl.end()){
							_s_dpl.insert(dp_lemma);
							_negated_refs.push_back(dp_lemma);
						}
					}
				}
			}break;
			case OpInst::ReductionXor:
//  				cout << "not supported yet: " << t << endl;
//  				break;
			{
				const InstL* ch = top->get_children();
				if (ch) {
					InstL new_chs;
					for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it){
						Inst *tve = *it;
						new_chs.push_back(NumInst::create(0, tve->get_size(), tve->get_sort()));
					}
					Inst *ve_zero = OpInst::create(t, new_chs);
					Inst *dp_lemma = OpInst::create(OpInst::Eq, ve_zero, NumInst::create(0, top->get_size(), top->get_sort()));
					if(_s_dpl.find(dp_lemma) == _s_dpl.end()){
						_s_dpl.insert(dp_lemma);
						_negated_refs.push_back(dp_lemma);
					}
				}
			}break;
			case OpInst::Ternary:
			case OpInst::LogXor:
			case OpInst::LogXNor:
			case OpInst::LogAnd:
			case OpInst::LogOr:
			case OpInst::LogNor:
			case OpInst::LogNand:
			case OpInst::LogNot:
			case OpInst::Eq:
			case OpInst::NotEq:
				break;
			case OpInst::ReductionXNor:
			case OpInst::Future:
			case OpInst::BitWiseXNor:
			case OpInst::BitWiseNor:
			case OpInst::BitWiseNand:
			case OpInst::Unknown:
			case OpInst::Div:
			case OpInst::Rem:
// 				assert(0);
 				AVR_LOG(0, 0, "not supported yet: " << t << endl);
 				break;
			default:
				AVR_COUT << t << endl;
				assert(0);
			}
		}

	}

	const InstL* ch2 = top->get_children();
	if (ch2) {
		for (InstL::const_iterator it2 = ch2->begin(); it2 != ch2->end(); ++it2)
			add_zero_lemmas(*it2);
	}
}

void PriorityQueue::PQ_ref(PQElement* pq_elem){
	if(pq_elem != NULL){
		pq_elem->refs++;
	}
}

void PriorityQueue::PQ_deref(PQElement* pq_elem){
	if(--pq_elem->refs == 0){
		if(pq_elem->pNext != NULL){
			PQ_deref(pq_elem->pNext);
		}
		pq_elem->abViol.clear();
		delete pq_elem;
	}
}

bool PriorityQueue::PQ_empty(){
// 	if(head == NULL){
// 		PQ_clear();
// 	}
	
	return (head == NULL);
	//return (queue_size == 0);
}

PQElement* PriorityQueue::PQ_head(){
	return head;
}

PQElement* PriorityQueue::PQ_push(int prio, int frame, ABSTRACT_REACH_VIOL cube, PQElement* pNext){
	PQElement *pq_elem = new PQElement(prio*frame, frame, cube, pNext);
	queue_size++;
//	debug_queue.insert(pq_elem);
	PQ_ref(pNext);
	
	if(head == NULL){
		head = pq_elem;
		//PQ_print("PQ_push");
		return pq_elem;
	}
	PQElement* pq_prev = NULL;
	PQElement* pq_cur = head;
	for(; pq_cur != NULL; pq_cur = pq_cur->pLink){
		if(pq_cur->prio > pq_elem->prio){
		// TODO check which one is better (bottom one is what AVR does)
		//if(pq_cur->frame > pq_elem->frame || (pq_cur->frame == pq_elem->frame && pq_cur->prio < pq_elem->prio)){

		//if(pq_cur->frame > pq_elem->frame || (pq_cur->frame == pq_elem->frame && pq_cur->prio > pq_elem->prio)){
			break;
		}
		pq_prev = pq_cur;
	}
	if(pq_cur == head){
		head = pq_elem;
		pq_elem->pLink = pq_cur;
	}else{
		//assert(pq_prev);
		pq_prev->pLink = pq_elem;
		pq_elem->pLink = pq_cur;
	}
	//PQ_print("PQ_push");
	return pq_elem;
}

void PriorityQueue::PQ_pop(){
	if(head != NULL){
		if(to_remove != NULL){
			PQ_deref(to_remove);
//			debug_queue.erase(to_remove);
			//to_remove = NULL;
		}
		to_remove = head;
		head = head->pLink;
		queue_size--;
	}
	//PQ_print("PQ_pop");
}

void PriorityQueue::PQ_clear(){
	while(head != NULL){
		PQ_pop();
	}
	if(to_remove != NULL){
		PQ_deref(to_remove);
//		debug_queue.erase(to_remove);
		to_remove = NULL;
	}
	head = NULL;
	queue_size = 0;
}

void PriorityQueue::PQ_print(string loc){
	return;
	//TODO dump elements that are not in the queue (but still alive)
//	PQElement* pq_elem;

	cout << loc << ": HEAD = " << head << endl;
//	for(set<PQElement*>::iterator it = debug_queue.begin(); it != debug_queue.end(); ++it){
//		pq_elem = *it;
//		cout << loc << ":" << "pq_elem = " << pq_elem << ", abViol = " << pq_elem->abViol << ", Next = " << pq_elem->pNext << ", Link = " << pq_elem->pLink << ", Frame = " << pq_elem->frame << ", Prio = " << pq_elem->prio << ", Ref = " << pq_elem->refs << endl;
//	}
}

//####################################################################
//DUMP_BLIF
//####################################################################

void Reach::gather_rhs(StrToSExpM *sem, Inst *ve) {
	if (ve->get_visit())
		return;
	ve->set_visit();
	assert(sem);
	const InstL* ch = ve->get_children();
	if (ch) {
		for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it) {
			gather_rhs(sem, *it);
		}
	}
	SigInst* sig = SigInst::as(ve);
	if (sig && (sem->find(sig->get_name()) == sem->end())) {
		sem->insert(make_pair(sig->get_name(), sig));
	}
}

void Reach::print_module_as_blif(ostream& out, Trans*top) {
	out << ".model " << Trans::m_module_name << endl;

	StrToSExpM rhs;// TODO check if set is enough
	StrToSExpM lhs;

	Inst::init_visit();
	for (Trans::const_iterator it = top->begin(); it != top->end(); ++it) {
		gather_rhs(&rhs, it->rhs);
		SigInst* sig = SigInst::as(it->lhs);
		if (sig) {
			lhs.insert(make_pair(sig->get_name(), sig));
		}
	}
	Inst::init_visit();
	for (StrToSExpM::iterator it_rhs = rhs.begin(); it_rhs != rhs.end(); it_rhs++) {
		StrToSExpM::iterator it_lhs = lhs.find(it_rhs->first);
		if (it_lhs == lhs.end()) {
			SigInst * sig = it_rhs->second;
			assert(sig);
//			if (sig->get_name().find('$') != string::npos) {
			if (sig->get_name().find("$next") != string::npos) {
				continue;
			}
			out << ".inputs";
			if (sig->get_size() == 1)
				out << " " << sig->get_name() << endl;
			else {
				for (size_t i = 0; i < sig->get_size(); i++) {
					out << " " << sig->get_name() << Inst::blif_suffix(i);
				}
				// out << " clk_0" << endl;
				out << endl;
			}
		}
	}

// 	for (size_t i = 0; i < top->m_output_ports.size(); i++) {
// 		out << ".outputs";
// 		string n = top->m_output_ports[i].port_name;
// 		long msb = top->m_output_ports[i].msb;
// 		long lsb = top->m_output_ports[i].lsb;
// 		if (msb != lsb) {
// 			for (long i = msb; i >= lsb; i--)
// 				out << " " << n << Inst::blif_suffix(i);
// 		} else
// 			out << " " << top->m_output_ports[i].port_name;
// 		out << endl;
// 	}
	out << ".outputs " << _config->get_arg(PROP_SIG_ARG) << endl;

	string clk_name = "clk";
	if (_config->get_arg(CLOCK_SIG_ARG) != "") {
		clk_name = _config->get_arg(CLOCK_SIG_ARG);
	}

	// CSF
	for (Trans::const_iterator it = top->begin(); it != top->end(); it++) {
		if (it->type != 1) {// if not CSF
			continue;
		}

		Inst *lhs = it->lhs;
		Inst *rhs = it->rhs;

//		out << endl << "# CSF" << endl;
//		out << "# rhs (" << *rhs << ")" << endl;
		rhs->is_rhs = true;
		print_as_blif(out, rhs);

//		out << "# => lhs (" << *lhs << ")" << endl;

		InstType lhs_type = lhs->get_type();
		assert(lhs_type == Sig || lhs_type == Ex);
		lhs->is_rhs = false;
		print_as_blif(out, lhs);

		MemInst *v_m = MemInst::as(rhs);
		if (!v_m || (v_m->get_mem_type() != MemInst::Write)) {
			SigInst *sige = SigInst::as(lhs);
			if(sige && sige->get_name() == _config->get_arg(PROP_SIG_ARG)){
				OpInst::print_blif_table(out, OpInst::LogNot, rhs->get_blif_name(), rhs->get_size(), "", 0, "", 0, lhs->get_blif_name(), lhs->get_size());
			}else{
				OpInst::print_blif_table(out, OpInst::Identity, rhs->get_blif_name(), rhs->get_size(), "", 0, "", 0, lhs->get_blif_name(), lhs->get_size());
			}
		}
	}

	// INIT
	map<string, Inst*> init_map;
	for (Trans::const_iterator it = top->begin(); it != top->end(); ++it) {
		if (it->type != 0) {// if not INIT
			continue;
		}

		Inst *lhs = it->lhs;
		Inst *rhs = it->rhs;
		string lhs_name = "";

		//TODO We do not support ExInst in both lhs and rhs
		SigInst *sige = SigInst::as(lhs);
		if (sige) {
			lhs_name = sige->get_name();
		}

		ExInst *exe = ExInst::as(lhs);
		if (exe) {
			ostringstream ostr;
			cout << "Exe: " << *exe << endl;
			ostr << *exe;
			lhs_name = ostr.str();
		}

		if (!sige && !exe) {
			continue;
		}

		if (init_map.count(lhs_name) != 0) {
			cout << "ERR " << lhs_name << "has multiple INIT statements" << endl;
			assert(0);
		}

		init_map[lhs_name] = rhs;
	}

	// NSF
	for (Trans::const_iterator it = top->begin(); it != top->end(); it++) {
		if (it->type != 2) {// if not NSF
			continue;
		}

		Inst *lhs = it->lhs;
		Inst *rhs = it->rhs;
		Inst *d_of_latch = rhs;
		string lhs_name = "";
		string edge = "";

		SigInst *sige = SigInst::as(lhs);
		if (sige) {
			lhs_name = sige->get_name();
			if (lhs_name == clk_name) {
				continue;
			}
		}
		ExInst *exe = ExInst::as(lhs);
		if (exe) {
			ostringstream ostr;
			cout << "Exe: " << *exe << endl;
			ostr << *exe;
			lhs_name = ostr.str();
		}

		out << endl << "# NSF" << endl;

		OpInst *ite = OpInst::as(rhs);
		if ((sige || exe) && ite && (ite->get_op() == OpInst::Ternary)) {
			assert(ite->get_exps().size() == 3);
			InstL::const_iterator it2 = ite->get_exps().begin();
			OpInst *conde = OpInst::as(*it2++);
			Inst *thene = *it2++;
			SigInst *elsee = SigInst::as(*it2);

			ExInst *exe2 = ExInst::as(lhs);
			string exe2_name;
			if (exe2) {
				ostringstream ostr;
				cout << "Exe2: " << *exe2 << endl;
				ostr << *exe2;
				exe2_name = ostr.str();
			}

			if ((conde && elsee && (elsee->get_name() == lhs_name)) || (conde && exe2 && (exe2_name == lhs_name))) {
				OpInst *ande_2 = OpInst::as(conde); // ###_2 means level 2
				if (ande_2 && (ande_2->get_op() == OpInst::LogAnd) && (ande_2->get_exps().size() == 2)) {
					InstL::const_iterator it3 = ande_2->get_exps().begin();
					OpInst *clocke_3 = OpInst::as(*it3);
					SigInst *clocke_3_sig = SigInst::as(*it3++);
					OpInst *futuree_3 = OpInst::as(*it3);

					if (clocke_3 && futuree_3) { // posedge clock
						if (clocke_3->get_op() == OpInst::LogNot && futuree_3->get_op() == OpInst::Future) {
							assert(clocke_3->get_exps().size() == 1);
							assert(futuree_3->get_exps().size() == 1);

							SigInst *clocke_4 = SigInst::as(clocke_3->get_exps().front());
							SigInst *futuree_4 = SigInst::as(futuree_3->get_exps().front());
							if (clocke_4 && futuree_4 && (clocke_4->get_name() == futuree_4->get_name())) {
								clk_name = clocke_4->get_name();
								edge = "re";
								d_of_latch = thene;
							}
						}
					} else if (clocke_3_sig && futuree_3) { // negative clock
						if (futuree_3->get_op() == OpInst::LogNot) {
							assert(futuree_3->get_exps().size() == 1);

							OpInst *futuree_4 = OpInst::as(futuree_3->get_exps().front());
							if (futuree_4 && (futuree_4->get_op() == OpInst::Future)) {
								assert(futuree_4->get_exps().size() == 1);
								SigInst *futuree_5 = SigInst::as(futuree_4->get_exps().front());
								if (clocke_3_sig->get_name() == futuree_5->get_name()) {
									clk_name = clocke_3_sig->get_name();
									edge = "fe";
									d_of_latch = thene;
								}
							}
						}
					}
				}
			}
		}

		//out << "# rhs (" << *d_of_latch << ")" << endl;
		d_of_latch->is_rhs = true;
		print_as_blif(out, d_of_latch);

		if (edge == "") { // unusual case
			//cout << "WRN in blif : exceptional case to be handled" << endl;
			edge = "re";
			//cout << "# => lhs (" << *lhs << ")" << endl;
			
			//out << "# => lhs (" << *lhs << ")" << endl;
			lhs->is_rhs = false;
			print_as_blif(out, lhs);
		}

		string init = "";
		if (init_map.count(lhs_name) > 0) {
			Inst *e = init_map[lhs_name];

			NumInst *nume = NumInst::as(e);
			if (nume) {
				assert(e->get_size() == lhs->get_size());
				init = (nume->get_mpz())->get_str(2);
				while (init.length() < nume->get_size())
				{
					init =  "0" + init;
				}
			} else {
				init = e->get_blif_name();
				cout << "ERR invalid INIT value: " << lhs->get_blif_name() << " = " << init << endl;
			}
		} else {
			//			init = "0";
			init = "3";
			cout << "ERR no INIT value: " << lhs_name << " " << lhs->get_blif_name() << endl;
		}
		TransElem::print_blif_latch(out, edge, lhs->get_blif_name(), lhs->get_size(), d_of_latch->get_blif_name(), d_of_latch->get_size(), clk_name, init);
		if (exe) {//TODO might be buggy
			//out << "# TODO LHS" << endl;
			rhs->is_rhs = false;
			print_as_blif(out, lhs);
		}
		out << endl;
	}

	out << ".end" << endl;
}

void Reach::print_as_blif(ostream& out, Inst*e) {
	if (e->get_visit()) {
		return;
	}
	e->set_visit();
	const InstL* ch = e->get_children();
	if (ch) {
		for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it) {
			(*it)->is_rhs = e->is_rhs;
			print_as_blif(out, *it);
		}
	}

	e->print_blif(out);
}

// return 0 if holds, 1 if violated, -1 others
int Reach::write_blif_file() {
	global_init();
	cout.setf(ios::fixed, ios::floatfield);
	cout.precision(2);

	InstL conjunct_prop_dp2;

	InstL conjunct_csf, conjunct_nsf, conjunct_init;
	InstL conjunct_prop;
	InstL conjunct_me; // based on the approach of maximum expansion
	InstL conjunct_r0;
	//	ofstream tempf0;
	//	access_file(tempf0, _config->get_working_dir() + "/m_with_camus.txt");

	OpInst *t_op;
// 	_ve_init;
// 	_ve_model_nsf;
// 	_ve_model;
// 	OpInst *t_op = OpInst::as(_ve_init);
// 	if (t_op && (t_op->get_op() == OpInst::LogAnd)) {
// 		const InstL* ch = t_op->get_children();
// 		for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it) {
// 			_conjunct_init.push_back(*it);
// 		}
// 	}else{
// 		_conjunct_init.push_back(_ve_init);
// 	}
#ifndef RESET_INIT_PATCH
	collect_nsfs(_ve_init, _conjunct_init, true);
	
//	cout << "_conjunct_init:" << _conjunct_init << endl;
	
	for (InstL::iterator it = _conjunct_init.begin(); it != _conjunct_init.end(); ++it) {
		Inst *t_ve = *it;
		t_op = OpInst::as(t_ve);
		if (t_op && t_op->get_op() == OpInst::Eq) {	// r = 5'd0
			const InstL* ch = t_op->get_children();
			InstL::const_iterator cit = ch->begin(), cit2 = ch->begin();
			cit2++;
			Inst * ve_lhs = *cit;
			Inst * ve_rhs = *cit2;

			if(ve_lhs->get_size() == 1){
				cout << *ve_lhs << " = " << *ve_rhs << endl;
				assert(ve_lhs->get_size() != 1);
			}
			
// 			if(ve_lhs->get_size() == 1){
// 				NumInst *nve = NumInst::as(ve_rhs);
// 				assert(nve);
// 				if((*(nve->get_mpz()) == 1)){
// 					_init_values[ve_lhs] = 1;
// 					_l_negated_ff_inits.push_back(OpInst::create(OpInst::LogNot, ve_lhs));
// 					_s_negated_ff_inits.insert(OpInst::create(OpInst::LogNot, ve_lhs));
// 				}else{
// 					_init_values[ve_lhs] = 0;
// 					_l_negated_ff_inits.push_back(ve_lhs);
// 					_s_negated_ff_inits.insert(ve_lhs);
// 				}
// 				
// 				continue;
// 			}
			
			_m_reg_init[ve_lhs] = ve_rhs;

			NumInst* num = NumInst::as(ve_rhs);
			if (!num) {
				cout << "Unable to handle init states with non-trivial conditions, exiting)" << endl;
				assert(0);
			}
			_init_values[ve_lhs] = num;
		}else{
			if (t_op && t_op->get_op() == OpInst::LogNot){	// !q
				Inst * ve_lhs = t_op->get_children()->front();
				_init_values[ve_lhs] = NumInst::create(0, 1, SORT());
			}else{	// q
				_init_values[t_ve] = NumInst::create(1, 1, SORT());
			}
			_l_negated_ff_inits.push_back(OpInst::create(OpInst::LogNot, t_ve));
			_s_negated_ff_inits.insert(OpInst::create(OpInst::LogNot, t_ve));
		}
	}
#endif
	collect_nsfs(_ve_model_nsf, conjunct_nsf, true);
	_ve_model_nsf = OpInst::create(OpInst::LogAnd, conjunct_nsf);
	
// 	AVR_LOG(0, 1, "_ve_model_nsf:" << endl);
// 	new_print(cout, _ve_model_nsf, true);
	
// 	t_op = OpInst::as(_ve_model_nsf);
// 	if (t_op && (t_op->get_op() == OpInst::LogAnd)) {
// 		const InstL* ch = t_op->get_children();
// 		for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it) {
// 			conjunct_nsf.push_back(*it);
// 		}
// 	}else{
// 		conjunct_nsf.push_back(_ve_model_nsf);
// 	}

//	cout << "conjunct_nsf:" << conjunct_nsf << endl;
	
	int num_bits = 0;
	int num_regs = 0;
	int num_total_bits = 0;
	map<int, int> reg_stats;
	Inst::init_visit();
	// TODO recover !cnt$1$next -> cnt$1$next = 1'b0
	for (InstL::iterator it = conjunct_nsf.begin(); it != conjunct_nsf.end(); ++it) {
		Inst *tve = *it;
		Inst *lhs;
		Inst *rhs;
		if(tve->get_children()){
			InstL::const_iterator it2 = tve->get_children()->begin();
			lhs = *it2++;
			if((tve->get_type() == Op) && (OpInst::as(tve)->get_op() == OpInst::LogNot)){
				rhs = NumInst::create(0, 1, SORT());
			}else{
				rhs = *it2;
			}
		}else{
			lhs = tve;
			rhs = NumInst::create(1, 1, SORT());
		}
			
		if(reg_stats.find(lhs->get_size()) == reg_stats.end()){
			reg_stats[lhs->get_size()] = 1;
		}else{
			reg_stats[lhs->get_size()]++;
		}
		if(lhs->get_size() == 1){
			num_bits++;
			num_total_bits++;
		}else{
			num_regs++;
			num_total_bits += lhs->get_size();
		}
		
		SigInst* sig = SigInst::as(lhs);
		if(!sig)	cout << *lhs << endl;
		assert(sig);
		string str_lhs = sig->get_name();
		Inst::_m_sn[lhs] = make_pair(rhs, true);
		string str_lhs_wo_next = str_lhs.substr(0, str_lhs.find_last_of('$'));
#ifdef INSERT_ZERO_LEMMAS
		add_zero_lemmas(rhs);
#endif
		Inst::_s_reg.insert(SigInst::create(str_lhs_wo_next, sig->get_size(), sig->get_sort()));
	}
	
	
	

	//cout << "_ve_init: " << *_ve_init << endl;
	
// _ve_init = Trans::id_to_ptr(Trans::read_int());
// _ve_model_nsf = Trans::id_to_ptr(Trans::read_int());
// _ve_model = Trans::id_to_ptr(Trans::read_int());

#ifdef RESET_INIT_PATCH
	for (InstS::iterator it = _s_reg.begin(); it != _s_reg.end(); it++) {
		Inst *ve_lhs = *it;
		Inst *t_ve;
		
		if(ve_lhs->get_size() == 1){
			t_ve = OpInst::create(OpInst::LogNot, ve_lhs);
		}else{
			t_ve = OpInst::create(OpInst::Eq, ve_lhs, NumInst::create(0, ve_lhs->get_size()));
		}

		_init_values[ve_lhs] = 0;

		_l_negated_ff_inits.push_back(ve_lhs);
		_s_negated_ff_inits.insert(ve_lhs);
		_conjunct_init.push_back(t_ve);
	}
	
	//cout << "_conjunct_init:" << endl << _conjunct_init << endl;
	_ve_init = OpInst::create(OpInst::LogAnd, _conjunct_init);
#endif
	
	Trans model;
	Trans::m_module_name = "seqx";
	{
		Trans::Port t_p;
		t_p.port_name = _config->get_arg(PROP_SIG_ARG);
		t_p.msb = 1;
		t_p.lsb = 1;
		model.m_output_ports.push_back(t_p);

		OpInst *tve = OpInst::as(_ve_model);
		if(tve && tve->get_op() == OpInst::Eq){
			const InstL* eq_ch = tve->get_children();
			InstL::const_iterator eq_ch_it = eq_ch->begin();
			TransElem e;
			e.lhs = *eq_ch_it++;
			e.rhs = *eq_ch_it;
			e.type = 1;
			model.push_back(e);
		}
	}
	
	t_op = OpInst::as(_ve_init);
	if (t_op && (t_op->get_op() == OpInst::LogAnd)) {
		const InstL* ch = t_op->get_children();
		for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it) {
			Inst *tve = *it;
			conjunct_init.push_back(tve);
			OpInst *t_and_op = OpInst::as(tve);
			if(t_and_op && t_and_op->get_op() == OpInst::Eq){
				const InstL* eq_ch = tve->get_children();
				InstL::const_iterator eq_ch_it = eq_ch->begin();
				TransElem e;
				e.lhs = *eq_ch_it++;
				e.rhs = *eq_ch_it;
				e.type = 0;
				model.push_back(e);
			}else{
				Inst * ve_lhs;
				Inst * ve_rhs;
				assert(tve->get_size() == 1);
				OpInst *t_and_op = OpInst::as(tve);
				if (t_and_op && t_and_op->get_op() == OpInst::LogNot){	// !q
					ve_lhs = t_and_op->get_children()->front();
					ve_rhs = NumInst::create(0, 1, SORT());
				}else{
					ve_lhs = tve;
					ve_rhs = NumInst::create(1, 1, SORT());
				}
				TransElem e;
				e.lhs = ve_lhs;
				e.rhs = ve_rhs;
				e.type = 0;
				model.push_back(e);
			}
		}
	}else{
		Inst *tve = _ve_init;
		conjunct_init.push_back(tve);
		OpInst *t_and_op = OpInst::as(tve);
		if(t_and_op && t_and_op->get_op() == OpInst::Eq){
			const InstL* eq_ch = tve->get_children();
			TransElem e;
			InstL::const_iterator eq_ch_it = eq_ch->begin();
			e.lhs = *eq_ch_it++;
			e.rhs = *eq_ch_it;
			e.type = 0;
			model.push_back(e);
		}else{
			Inst * ve_lhs;
			Inst * ve_rhs;
			assert(tve->get_size() == 1);
			OpInst *t_and_op = OpInst::as(tve);
			if (t_and_op && t_and_op->get_op() == OpInst::LogNot){	// !q
				ve_lhs = t_and_op->get_children()->front();
				ve_rhs = NumInst::create(0, 1, SORT());
			}else{
				ve_lhs = tve;
				ve_rhs = NumInst::create(1, 1, SORT());
			}
			TransElem e;
			e.lhs = ve_lhs;
			e.rhs = ve_rhs;
			e.type = 0;
			model.push_back(e);
		}
	}

	t_op = OpInst::as(_ve_model_nsf);
	if (t_op && (t_op->get_op() == OpInst::LogAnd)) {
		const InstL* ch = t_op->get_children();
		for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it) {
			Inst *tve = *it;
			conjunct_nsf.push_back(tve);
			OpInst *t_and_op = OpInst::as(tve);
			//assert(t_and_op && t_and_op->get_op() == OpInst::Eq);
			const InstL* eq_ch = tve->get_children();
			Inst *pre_ve;
			Inst *rhs_ve;

			if(eq_ch){
				InstL::const_iterator eq_ch_it = eq_ch->begin();
				pre_ve = *eq_ch_it++;
				if(t_and_op && t_and_op->get_op() == OpInst::Eq){
				//if(eq_ch_it != eq_ch->end())	// this should work
					rhs_ve = *eq_ch_it;
				}else{
					rhs_ve = NumInst::create(0, 1, SORT());
				}
			}else{
				pre_ve = tve;
				rhs_ve = NumInst::create(1, 1, SORT());
			}

			SigInst* pre_sig = SigInst::as(pre_ve);
			if (pre_sig) {
				string pre_name = pre_sig->get_name();
				pre_name = pre_name.substr(0, pre_name.length() - 5);
				pre_ve = SigInst::create(pre_name, pre_sig->get_size(), pre_sig->get_sort());
			}else{
				//TODO temp fix (partial_bit_blast introduce some junks)
				continue;
			}
			
			TransElem e;
			e.lhs = pre_ve;
			e.rhs = rhs_ve;
			e.type = 2;
			model.push_back(e);
		}
	}else{
		Inst *tve = _ve_model_nsf;
		conjunct_nsf.push_back(tve);
		OpInst *t_and_op = OpInst::as(tve);
		assert(t_and_op && t_and_op->get_op() == OpInst::Eq);

		const InstL* eq_ch = tve->get_children();
		InstL::const_iterator eq_ch_it = eq_ch->begin();
		
		Inst *pre_ve = *eq_ch_it++;
		SigInst* pre_sig = SigInst::as(pre_ve);
		if (pre_sig) {
			string pre_name = pre_sig->get_name();
			pre_name = pre_name.substr(0, pre_name.length() - 5);
			pre_ve = SigInst::create(pre_name, pre_sig->get_size(), pre_sig->get_sort());
		}
		
		TransElem e;
		e.lhs = pre_ve;
		e.rhs = *eq_ch_it;
		e.type = 2;
		model.push_back(e);
	}
	
// 		cout << "conjunct_nsf:" << conjunct_nsf << endl;
// 		cout << "conjunct_init:" << conjunct_init << endl;
	
	string blif_file_name;
	if (_config->get_arg(DUMP_BLIF_ARG) == "on") {
		//			blif_file_name = "../" + string(_model.m_module_name) + "_" + _config->get_arg(PROP_CYCLE_ARG) + ".blif";
		//blif_file_name = _config->get_working_dir() + "/" + string(_model.m_module_name) + "_" + _config->get_arg(PROP_CYCLE_ARG) + ".blif";
		blif_file_name = _config->get_working_dir() + "/seqx_0.blif";
		cout << "Writing blif file " << blif_file_name << endl;
	} else {
		ostringstream str;
		str << _config->get_arg(DUMP_BLIF_ARG);
		blif_file_name = str.str();
	}
	//		print_module_as_blif(cout, &_model);
	ofstream f_blif(blif_file_name.c_str());
	print_module_as_blif(f_blif, &model);
	f_blif.close();

	cout << "BLIF file dump is done !!!" << endl;
	return 0;
}

//####################################################################
//	PARTIAL BIT BLAST
//####################################################################

// inputs: T, P, inst that needs to be bit-blasted
// TODO return ve_out, bit-blasted version of ve_in ?
void Reach::partial_bit_blast(Inst **ve_prop, Inst **ve_nsf, Inst *ve_in) {
	collect_parents(*ve_nsf, true);
	collect_parents(*ve_prop, false);
	
	//set<InstsPair> to_bb;
	InstToInstM to_bb;
	ve_in->bit_blast(to_bb, true);

	*ve_nsf = update_chs(*ve_nsf, to_bb, true);
	*ve_prop = update_chs(*ve_prop, to_bb, false);
}

// for the quick and easy use
void Reach::partial_bit_blast(InstL &in_regs) {

	collect_parents(_ve_model_nsf, true);
	collect_parents(_ve_model, false);
	collect_parents(_ve_init, false);
	
// 	for(InstToSetM::iterator mit = _m_pars.begin(); mit != _m_pars.end(); ++mit){
// 		cout << "key: " << *(mit->first) << endl;
// 		
// 		for(InstS::iterator sit = (mit->second).begin(); sit != (mit->second).end(); ++sit){
// 			cout << "par: " << *(*sit) << endl;
// 		
// 		}
// 		
// 	}
	
	InstToInstM to_bb;
	Inst::init_visit();
	InstL to_examine;
	for(InstL::iterator ir_it = in_regs.begin(); ir_it != in_regs.end(); ++ir_it){
		SigInst *ve_reg = SigInst::as(*ir_it);
		if(!ve_reg){
			cout << "ERR	partial_bit_blast: " << ve_reg << "does not exist!!" << endl;
		}
		
		string str = ve_reg->get_name();
		int width = ve_reg->get_size();
		SORT sort = ve_reg->get_sort();
		Inst *ve_sig = SigInst::create(str+"$next", width, sort);
		Inst *ve_in = *(_m_pars[ve_sig].begin());
		to_examine.push_back(ve_in);
		
		if(width > 1){
		//	cout << "partial_bit_blast, ve_in: " << *ve_in << endl;
			
			//set<InstsPair> to_bb;

			InstL vel_concat;
			for(int i = 0; i < (int)width; ++i){
				ostringstream oss;
				oss << str << "$" << i << "$next";
				
				Inst *ve_bit = SigInst::create(oss.str(), 1, SORT());
				vel_concat.push_back(ve_bit);
				
			}
			Inst *ve_res = OpInst::create(OpInst::Concat, vel_concat);
			ve_sig->set_visit();
			to_bb[ve_sig] = ve_res;

			vel_concat.clear();
			ve_sig = SigInst::create(str, width, sort);
			for(int i = 0; i < (int)width; ++i){
				ostringstream oss;
				oss << str << "$" << i;
				
				Inst *ve_bit = SigInst::create(oss.str(), 1, SORT());
				vel_concat.push_back(ve_bit);
				
			}
			ve_res = OpInst::create(OpInst::Concat, vel_concat);
			ve_sig->set_visit();
			to_bb[ve_sig] = ve_res;		
		}
	}
	
	for(InstL::iterator eit = to_examine.begin(); eit != to_examine.end(); ++eit){
		(*eit)->bit_blast(to_bb, false);
	}
	(_ve_model)->bit_blast(to_bb, false);
	
//	int idx = 0;
	
	// I think _m_pars should be updated !!!
// 	InstS to_bb_new;
// 	for(InstToInstM::iterator mit = to_bb.begin(); mit != to_bb.end(); ++mit){
// // 		cout << "to_bb: " << idx++ << endl;
// // 		cout << *(mit->first) << endl;
// // 		cout << *(mit->second) << endl;
// 		Inst *ve_key = mit->first;
// //		if(ve_key->get_size() != 1)
// 		{
// 			InstS &s_par = _m_pars[ve_key];
// 			for(InstS::iterator sit = s_par.begin(); sit != s_par.end(); ++sit){
// 				//if(to_bb_new.find(*sit) == to_bb_new.end()){
// 				if((to_bb_new.find(*sit) == to_bb_new.end()) && (to_bb.find(*sit) == to_bb.end())){
// 					to_bb_new.insert(*sit);
// 				}
// 			}
// 		}
// 	}
// 	
// 	for(InstS::iterator sit = to_bb_new.begin(); sit != to_bb_new.end(); ++sit){
// 		Inst *ve_bb = *sit;
//  		//cout << "ve_bb: " << *ve_bb << endl;
// 		ve_bb->bit_blast(to_bb, false);
// 		//cout << "ve_bb after: " << *(to_bb[ve_bb]) << endl;
// 	}

// 	idx = 0;
// 	for(InstToInstM::iterator mit = to_bb.begin(); mit != to_bb.end(); ++mit){
// 		cout << "to_bb: " << idx++ << endl;
// 		cout << "mit->first" << endl;
// 		new_print(cout, (mit->first), true);
// 		cout << "mit->second" << endl;
// 		new_print(cout, (mit->second), true);
// // 		cout << *(mit->first) << endl;
// // 		cout << *(mit->second) << endl;
// 	}
	
	
	//cout << "NOW UPDATE CHS" << endl;
	_ve_model_nsf = update_chs(_ve_model_nsf, to_bb, true);
	_ve_model = update_chs(_ve_model, to_bb, false);
	_ve_init = update_chs(_ve_init, to_bb, false);
	_m_pars.clear();
}

// TODO return ve_out, bit-blasted version of ve_in ?
void Reach::collect_parents(Inst *ve_top, bool init_visit) {
	if(init_visit){
		Inst::init_visit();
	}
	if(ve_top->get_visit()){
		return;
	}
	ve_top->set_visit();

	const InstL* chs = ve_top->get_children();

	if(chs){
		InstL::const_iterator it = chs->begin();
		for (InstL::const_iterator end_it = chs->end(); it != end_it; ++it) {
			Inst *ch = *it;
			if(_m_pars[ch].find(ve_top) == _m_pars[ch].end()){
				_m_pars[ch].insert(ve_top);
			}
			collect_parents(ch, false);
		}
	}
}

Inst *Reach::update_chs(Inst *ve_top, InstToInstM& bb_map, bool init_visit) {
	if (init_visit) {
		Inst::init_visit();
	}
	if (ve_top->get_visit()){
		return ve_top->acex_coi;
	}
	ve_top->set_visit();
	ve_top->acex_coi = ve_top;	//TODO temporary use of acex_coi

	if((ve_top->get_type() == Num) || (ve_top->get_type() == Sig))
	{
		InstToInstM::iterator mit = bb_map.find(ve_top);
		Inst *ve_res;
		if(mit != bb_map.end()){
			ve_res = mit->second;
		}else{
// 			if(ve_top->get_type() == Sig){
// 				cout << *ve_top << endl;
// 			}
			
			ve_res = ve_top;
		}
		ve_top->acex_coi = ve_res;
		return ve_res;
	}else{
		InstToInstM::iterator mit = bb_map.find(ve_top);
		if(mit != bb_map.end()){
			Inst *ve_res;
			ve_res = mit->second;
			ve_top->acex_coi = ve_res;
			return ve_res;
		}
	}

	InstL new_ch;
	bool need_new = false;
	const InstL* chs = ve_top->get_children();
	if(chs){
		InstL::const_iterator it = chs->begin();
		for(; it != chs->end(); ++it) {
			Inst *ch = *it;
			Inst *ch_new = update_chs(ch, bb_map);
			if(ch != ch_new){
				need_new = true;
			}
		
			new_ch.push_back(ch_new);
		}
	}else{
		assert(0);
	}

	// for the (mult_bit_reg == width'd0) in init
	if((ve_top->get_type() == Op) && (OpInst::as(ve_top)->get_op() == OpInst::Eq)){
		InstL::iterator cit = new_ch.begin();
		Inst *ve_ch0 = *cit++;
		Inst *ve_ch1 = *cit;
// 		cout << "####$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$" << endl;
// 		cout << "ve_ch0: " << *ve_ch0 << ", size: " << ve_ch0->get_size() << endl;
// 		cout << "ve_ch1: " << *ve_ch1 << ", size: " << ve_ch1->get_size() << endl;
		int op_size = ve_ch0->get_size();
		if(op_size == 1){
			Inst *ve_res = OpInst::create(OpInst::LogXNor, ve_ch0, ve_ch1);
			//cout << "table, ve_res1: " << *ve_res << endl;
			ve_top->acex_coi = ve_res;
			return ve_res;
		}else{
			if((ve_ch0->get_type() == Op) && (OpInst::as(ve_ch0)->get_op() == OpInst::Concat)){
				if( ((ve_ch1->get_type() == Op) && (OpInst::as(ve_ch1)->get_op() == OpInst::Concat)) &&
					((ve_ch0->get_children())->size() == (ve_ch1->get_children())->size()) ){
					InstL::const_iterator cit_0 = (ve_ch0)->get_children()->begin();
					InstL::const_iterator cit_1 = (ve_ch1)->get_children()->begin();
					Inst *ve_res = NULL;
					for (int i = 0; i < op_size; ++i, ++cit_0, ++cit_1) {
						ve_ch0 = *cit_0;
						ve_ch1 = *cit_1;
						Inst *ve_bit = OpInst::create(OpInst::LogXNor, ve_ch0, ve_ch1);
	// 					if(!ve_bit){
	// 						cout << "ve_ch0: " << *ve_ch0 << ", size: " << ve_ch0->get_size() << endl;
	// 						cout << "ve_ch1: " << *ve_ch1 << ", size: " << ve_ch1->get_size() << endl;	
	// 					}
						if(i != 0){
							ve_res = OpInst::create(OpInst::LogAnd, ve_res, ve_bit);
						}else{
							ve_res = ve_bit;
						}
					}
					//cout << "table, ve_res2: " << *ve_res << ", ve_ch0->get_size():" << op_size << endl;
					ve_top->acex_coi = ve_res;
					return ve_res;
				}else if(op_size == (int)(ve_ch0->get_children()->size())){
					InstL::const_iterator cit_0 = ve_ch0->get_children()->begin();
					Inst *ve_res = NULL;
// 					if(op_size != ve_ch0->get_children()->size()){
// 						cout << *ve_ch0 << endl;
// 						cout << "op_size: " << op_size << ", ve_ch0->get_children()->size(): " << ve_ch0->get_children()->size() << endl;
// 						assert(0);
// 					}
					
					for (int i = 0; i < op_size; ++i, ++cit_0) {
						ve_ch0 = *cit_0;
						Inst *ve_bit = OpInst::create(OpInst::LogXNor, ve_ch0, ExInst::create(ve_ch1, i, i));
						if(i != 0){
							ve_res = OpInst::create(OpInst::LogAnd, ve_res, ve_bit);
						}else{
							ve_res = ve_bit;
						}
					}
					//cout << "table, ve_res2: " << *ve_res << ", ve_ch0->get_size():" << op_size << endl;
					ve_top->acex_coi = ve_res;
					return ve_res;
				}
			}
		}
	}
	
	// if need_new is false, we don't need to proceed this routine.
	// however, I'm checking two cases just in case (this should be unnecessary
	//	due to the simplification routines in vwn).
	
	if(need_new == true){	// TODO check possible BUG s
		if(ve_top->get_type() == Ex){
			ExInst *ve_ex = ExInst::as(ve_top);
			InstL vel_concat;
			Inst *ve_ch = new_ch.front();
			if((ve_ch->get_type() == Op) && (OpInst::as(ve_ch)->get_op() == OpInst::Concat) && (ve_ch-> get_size() == ve_ch->get_children()->size())){
				const InstL* concat_ch = ve_ch->get_children();
				if(concat_ch){
	// 				cout << "ve_top: " << *ve_top << endl;
	// 				cout << "concat_ch->size(): " << concat_ch->size() << endl;
	// 				cout << "ve_ch->get_size(): " << ve_ch->get_size() << endl;
					
					InstL::const_iterator cit = concat_ch->begin();
					for(int i = 0; i < (int)ve_ex->get_lo(); ++i){
						++cit;
					}
					for(int i = 0; i < (int)ve_ex->get_size(); ++i){
						vel_concat.push_back(*cit);
						++cit;
					}
				}else{
					assert(0);
				}
				Inst *ve_res = OpInst::create(OpInst::Concat, vel_concat);
				ve_top->acex_coi = ve_res;
				return ve_res;
			}
		}
		
		if((ve_top->get_type() == Op) && (OpInst::as(ve_top)->get_op() == OpInst::Concat)){
			InstL vel_concat;
			for(InstL::iterator cit = new_ch.begin(); cit != new_ch.end(); ++cit){
				Inst *ve_ch = *cit;
				if((ve_ch->get_type() == Op) && (OpInst::as(ve_ch)->get_op() == OpInst::Concat)){
					const InstL* concat_ch = ve_ch->get_children();
					if(concat_ch){
						for(InstL::const_iterator cit2 = concat_ch->begin(); cit2 != concat_ch->end(); ++cit2){
							vel_concat.push_back(*cit2);
						}
					}else{
						assert(0);
					}
				}else{
					vel_concat.push_back(ve_ch);
				}
			}
			Inst *ve_res = OpInst::create(OpInst::Concat, vel_concat);
			ve_top->acex_coi = ve_res;
			return ve_res;
		}
	}
	
	if(need_new){
		//if(new_ch.size() == 0)
// 		{
// 			cout << "ve_top: " << *ve_top << endl;
// 			cout << "new_ch (" << new_ch.size() << "): " << new_ch << endl;
// 		}
		
		Inst *ve_res = ve_top->apply_children(new_ch);
		if(ve_res->ve_orig == NULL){
			if(ve_top->ve_orig == NULL){
				ve_res->ve_orig = ve_top;
			}else{
				ve_res->ve_orig = ve_top->ve_orig;
			}
		}
		ve_top->acex_coi = ve_res;
		return ve_res;
	}
	return ve_top;
}

}
