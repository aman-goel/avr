/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


#ifndef AVERROES_FLOW_COMMON_H__
#define AVERROES_FLOW_COMMON_H__

#include <string>
#include <iostream>
#include <vector>
#include <map>
#include <fstream>
#include <cstdlib>
#include <cstring>

#define AVERROES_VERSION 2.1

#include "avr_util.h"

#ifndef OPTIMIZE
#define DEBUG_TRANS
#endif

#ifdef DEBUG_TRANS
#define DEBUG_TRANS_SIZE
#endif

//#define RANDOMNESS

#define NAME_SAUF   "sa+uf"
#define NAME_SABV   "sa"

#define DEFAULT_ABSTRACT NAME_SAUF


class Config {
public:
	static bool g_random;
	static string g_abstraction_name;
	static bool g_ab_interpret;
	static int g_ab_interpret_limit;

	Config(){}
	~Config(){}
	Config(std::string wdir,std::string bdir):working_dir(wdir),binary_dir(bdir) {}
	std::string  get_working_dir() { return working_dir;}
	std::string  get_binary_dir() { return binary_dir;}
	void load_args(bool picky = true);
	std::string& get_arg(std::string arg) { return args[arg].first;}
	void override_arg(std::string arg,std::string val) {args[arg] = make_pair(val,0);}
	void dump_args(std::ostream& os);

private:
	std::string working_dir;      
	std::string binary_dir;      
	// arg name to (value,flag), when flag tells whether its mandatory or not!
	typedef std::map<std::string,std::pair<std::string,bool> > Args;	
	Args args;      

	bool read_arg(std::ifstream&f,char*);

	void get_arg_val(string arg, bool& orig);

	#define CONFIG_FILE_NAME "fconfig"
	
	void set_abstraction(string& name);

	// New arguments
	#define EN_RANDOM "random"
	#define ABSTRACTION_TYPE "abstraction_type"

	#define DUMP_BLIF_ARG "dump_blif"
	// Argument Names in config file
	// the design clock
	#define CLOCK_SIG_ARG "clock_sig"
	// intialize the clock with zero and oscillate
	#define CLOCK_MODEL_ARG "clock_model"
	// the name for the design's top-module (in case there are more than one!)
	#define TOP_MODULE_ARG "top_module"
	// the file name for the design
	#define DESIGN_ARG "design_file"
	// the type of the design input: wn for a *.wn file and verilog for a *.v file
	#define DESIGN_T_ARG "design_type"
	// the file name for the property
	#define PROP_ARG "prop_file"
	// the type of the property input: wn for a *.wn file and verilog for *.v file
	#define PROP_T_ARG "prop_type"
	// the file name for the design
	#define AUX_F_ARG "aux_file"
	// the cycle in which the property signal should be sampled
	#define PROP_CYCLE_ARG "prop_cycle"
	// the signal that represents the actual property in the property file
	#define PROP_SIG_ARG "prop_sig"
	// the type of the solving algorithm
	#define ALG_T_ARG "alg_type"
	// the type of abstract CEX minimization
	#define ABST_MIN_T_ARG "abst_min_type"
	// the type of concrete CEX minimization
	#define CONC_MIN_T_ARG "conc_min_type"
	// the verbosity level
	#define VERB_ARG "verbosity"
	// dump the WN textually
	#define DUMP_MODEL_ARG "dump_model"
	// dump the violations textually
	#define DUMP_VIOL_ARG "dump_viol"
	// dump the refinements textually
	#define DUMP_REF_ARG "dump_ref"
	// dump statistics
	#define DUMP_STATS_ARG "dump_stats"
	// dump the counterexample, if any, to this specified file
	#define DUMP_CEX_ARG "dump_cex"
	// interactively debug the verification result
	#define INT_DEB_ARG "interactive_debugger"
	// a list of signals to dump to the trace file
	#define TRACE_SIGS_ARG "trace_signals"
	// a list of signals to dump while simulating
	#define SIM_SIGS_ARG "sim_signals"
	// a file of mappings for intial memories!
	#define MEM_MAP_ARG "mem_map"
	// the solver (YICES/ARIO/etc.) in the abstract level
	#define ABST_SOLVER_ARG "abst_solver"

	#define DUMP_DOT_ARG "dump_dot"
	#define DUMP_DOT_DEPTH_ARG "dump_dot_depth"
	
	//avr debug level
	#define AVR_TO_CONCRETIZE_ARG "to_concretize"
	#define AVR_VERB_ARG "vlevel"
		// timeout value of an SMT solver
	#define AVR_MEM_LIMIT_ARG "memory_limit"
	#define AVR_TIMEOUT_ARG "timeout"
	#define AVR_PROP_TIMEOUT_ARG "prop_timeout"
	#define AVR_REACH_TIMEOUT_ARG "reach_timeout"
	#define AVR_CORR_REGS_ARG "corr_regs"
	#define AVR_NUM_REACH_SOLVER "num_rsolver"
	#define AVR_DERIVE_EQ_MODE "eq_mode"
	#define AVR_NEW_CLT_MODE "new_clt_mode"
	
	// the logic for the abstract solver
	#define ABST_LOGIC_ARG "abst_logic"
	#define EXPERIMENT_ARG "experiment"
	#define EXPERIMENT_COI_ARG "experiment_coi"
	// the timeout for CAMUS (in seconds)
	#define CAMUS_TIMEOUT_ARG "camus_timeout"
	// the number of groups to divide the constraints for camus!
	#define CAMUS_GROUPS_ARG "camus_groups"
	// the size of each group!
	#define CAMUS_GROUP_SIZE_ARG "camus_group_size"
	// maximal number of MUSes!
	#define CAMUS_MAX_MUSES_ARG "camus_max_muses"
	// what are variables (and constants) abstracted to!
	#define VARS_ABST_ARG "variables_abstraction"
	// the file name where the modeling of Vapor should be dumped!
	#define DUMP_DESIGN_MODELING_ARG "dump_design_modeling"
	// if 1, Vapor will truncate RHS to match its size with the LHS
	#define TRUNCATE_RHS_ARG "truncate_rhs"
	// if 1, Vapor will extend RHS to match its size with the LHS
	#define EXTEND_RHS_ARG "extend_rhs"
	// put bounds on the int variables in the abstract (just for experimental purposes).
	#define ABST_BOUND_ARG "bound_on_abst_vars"
	// dump the wn representation of the TR of the design
	#define DUMP_DESIGN_WN_ARG "dump_design_wn"
	// the maximum number of refinement iterations (use for debugging only)
	#define MAX_ITER_ARG "max_iter"
	// turn on/off the simplifications in the simulation engine
	#define SIM_SIMPL_ARG "sim_simplifications"
	// dump the initial verification condition in Verilog syntax
	#define DUMP_INIT_FORMULA_VERILOG_ARG "dump_init_formula_in_verilog"
	// dump the final verification condition (i.e. after refinement!) in Verilog syntax
	#define DUMP_FINAL_FORMULA_VERILOG_ARG "dump_final_formula_in_verilog"
	// dump the initial verification condition in Uclid syntax
	#define DUMP_INIT_FORMULA_UCLID_ARG "dump_init_formula_in_uclid"
	// dump the final verification condition (i.e. after refinement!) in Uclid syntax
	#define DUMP_FINAL_FORMULA_UCLID_ARG "dump_final_formula_in_uclid"
	// use lemma database w/ the given file.
	#define LEMMA_DB_ARG "lemma_db"
#ifndef LIMITED_RELEASE1
	// make concatenation and extraction interpreted.. .has an effect only with BV variables!
	#define INTPD_CONCAT_EXTRACT_ARG "interpret_concat_extract"
	// make all UFs equal (via lambda) to BV operators!
	#define INTPD_ALL_ARG "interpret_all"
	// refinement type: refutation, or concretization
	#define REF_TYPE_ARG "ref_type"
	// use templates?
	#define TEMPLATES_ARG "templates"
	// use an external solver for SMT(BV). No counterexample will be given in case the property fails.
	#define EXT_BV_SOLVER_ARG "external_smt(bv)_solver"
#endif
	// 0 to prevent showing CEX.
	#define SHOW_CEX_ARG "show_counterexample"
	// 1 to force unbounded addition in all cases (i.e., not only for constants!)
	#define UBADD_ARG "unbounded_addition"

	// Argumetn Options in config file
	#define CONFIG_WN "wn"
	#define CONFIG_VERILOG "verilog"
	#define CONFIG_INIT0_OSCILLATING "init_0_oscillating"
	#define CONFIG_INIT0_POSEDGE "init_0_posedge"
	#define CONFIG_AR "abst_ref"
	#define CONFIG_BB "bit_blast"
	#define CONFIG_SMT "smt"
	#define CONFIG_NONE "none"
	#define CONFIG_ONE_MUS "one_mus"
	#define CONFIG_ALL_MUSES "all_muses"
	#define CONFIG_YICES_API "yices_api"
	#define CONFIG_YICES "yices"
	#define CONFIG_Z3 "z3"
	#define CONFIG_STP "stp"
	#define CONFIG_ARIO "ario"
	#define CONFIG_BAT "bat"
	#define CONFIG_INTS "ints"
	#define CONFIG_INTS_IC "ints_interpreted_consts"
	#define CONFIG_BV "bit_vectors"
	#define CONFIG_EUF "euf"
	#define CONFIG_CLU "clu"
	#define CONFIG_ON "on"
	#define CONFIG_OFF "off"
	#define CONFIG_REF "refutation"
	#define CONFIG_CONCR "concretization"
	
	
};

#endif
