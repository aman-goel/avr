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

#include "avr_def.h"
#include "avr_util.h"

#define AVERROES_VERSION 2.1
#define WN_VERSION 0.1

//#define I4

#define EN_BMC
#define BMC_MAX_BOUND_DEFAULT		1000

//#define TEST_REFINE_FLUSH
#ifdef TEST_REFINE_FLUSH
	#define TEST_REFINE_FULL_FLUSH
//	#define TEST_REFINE_FP
//	#define TEST_REFINE_PARTIAL_FLUSH
#endif

//#define BIT_PRECISE

#ifdef BIT_PRECISE
	#define CONCRETE_BIT_WIDTH_LIMIT 9999999
#endif

//#define SUBSTITUTE
#define AB_SUBSTITUTE

#define PRINT_FRAME_SUMMARY

#define PERFORMANCE

//#define PERFORMANCE_NODRAW
#define PERFORMANCE_NOCHECK

#define AVOID_LARGE_PRINTING
#define USE_INTERMEDIATE_NAMES

#ifndef PERFORMANCE_NOCHECK
#define CHECK_EXCC    // Checks concrete correctness of all Ex/Cc simplifications after building the system
#endif

#ifndef PERFORMANCE_NODRAW
	#define DRAW_SYSTEM			0
	#define DRAW_T					1
	#define DRAW_A					2
	#define DRAW_EXCC				3
	#define DRAW_EXCC_UF		4
	#define DRAW_TRANSITION	5
	#define DRAW_REFINEMENT	6
#endif

#define CORRECT_GENERALIZATION
#ifdef CORRECT_GENERALIZATION
//	#define GENERALIZATION_SKIP_CONCRETE
#endif

#define ASSERT_DISTINCT_NUMBERS

//#define DISABLE_UNSAT_CORE_MINIMIZATION

//#define ENABLE_DONT_CARES_FROM_SOLVER

//#define PRINT_RELEVANT_WIRES

/// Abstraction of our abstraction
//#define ABSTRACTION_COURSE

//#define ADD_CUBE_IN_SRC
#ifdef ADD_CUBE_IN_SRC
	#define ALLOW_MULTIPLE_LEVELS
#endif

#define DISABLE_ABSTRACT_LEMMAS			// Option to switch off all abstract lemmas

#ifndef DISABLE_ABSTRACT_LEMMAS
	#define FIND_SUB_EXPRESSION
#endif

//#define TEST_FULL_MUS_REACH
//#define TEST_SEMI_MUS_REACH

/// C2
#define INTERPRET_EX_CC
#ifdef INTERPRET_EX_CC
  #define INTERPRET_EX_UF

//  #define INTERPRET_UF_UNORDERED
//	#define INTERPRET_UF_SIG
//	#define INTERPRET_UF_NUM
//	#define INTERPRET_UF_OP
//	#define INTERPRET_UF_EXCC

	#define EX_CC_LEVEL1
	#define EX_CC_LEVEL2

//  #define EX_CC_LEVEL3
#endif

#define AB_GRANULARITY_NONE		0
#define AB_GRANULARITY_MIXED	1
#define AB_GRANULARITY_INPUT	2

#define AB_GRANULARITY_DEFAULT		AB_GRANULARITY_NONE
#define AB_GRANULARITY_MAX				AB_GRANULARITY_INPUT

#define MININV_NONE 0
#define MININV_AB_FAST 1
#define MININV_AB_SLOW 2
#define MININV_BV_FAST 3
#define MININV_BV_SLOW 4

#define MININV_DEFAULT MININV_NONE
//#define MININV_DEFAULT MININV_BV_SLOW

#define INTERPOLATION_NONE 0
#define INTERPOLATION_END 1

#define INTERPOLATION_DEFAULT	INTERPOLATION_NONE
#define INTERPOLATION_MAX		INTERPOLATION_END

#define FORWARDCHECK_NONE    0
#define FORWARDCHECK_ONESTEP 1
#define FORWARDCHECK_FAST    2

#define FORWARDCHECK_DEFAULT	FORWARDCHECK_NONE
#define FORWARDCHECK_MAX		  FORWARDCHECK_FAST

#define FINENESS_NONE			0
#define FINENESS_EQLOCAL	1
#define FINENESS_EQSIG		2
#define FINENESS_EXCCSIG	3
#define FINENESS_UP				4
#define FINENESS_EQUF			5

#define FINENESS_DEFAULT		FINENESS_EQSIG
#define FINENESS_MAX				FINENESS_EQUF

#define LAZY_ASSUME_NONE	0
#define LAZY_ASSUME_L1		1
#define LAZY_ASSUME_L2		2

#define LAZY_ASSUME_DEFAULT		LAZY_ASSUME_NONE
#define LAZY_ASSUME_MAX				LAZY_ASSUME_L2

#define INTERPRET_UF_MAX_WIDTH 8

#ifdef INTERPRET_UF_SIG
	#define INTERPRET_UF_SIG_LIMIT INTERPRET_UF_MAX_WIDTH
#endif

#ifdef INTERPRET_UF_NUM
	#define INTERPRET_UF_NUM_LIMIT INTERPRET_UF_MAX_WIDTH
#endif

#ifdef INTERPRET_UF_OP
	#define INTERPRET_UF_OP_OUTLIMIT INTERPRET_UF_MAX_WIDTH
	#define INTERPRET_UF_OP_INPLIMIT INTERPRET_UF_MAX_WIDTH
#endif


#define NAME_SAUF   "sa+uf"
#define NAME_SABV   "sa"
#define NAME_EXCC   "ec"

#define NAME_UF_UNORDERED   "+unordered"
#define NAME_UF_MULT_ONLY   "+mult"
#define NAME_UF_NO_BITWISE  "+nobitwise"
#define NAME_UF_NO_SEXT     "+nosignex"
#define NAME_UF_NO_SHIFT    "+noshift"

#define DEFAULT_ABSTRACT NAME_SAUF

#define LEVEL_EXCC_NONE			0
#define LEVEL_EXCC_DEFAULT	1
#define LEVEL_EXCC_ALL			2

//#define PREDICATE_ABSTRACTION

#define SINGLE_TIER
//#define DOUBLE_TIER
//#define MULTI_TIER

//#define DEFAULT_PROJECTION
//#define STRUCTURAL_PROJECTION

//#define PRINT_PROJECTION
#ifdef PRINT_PROJECTION
	#define DEFAULT_PROJECTION
#endif

#ifdef DEFAULT_PROJECTION
//	#define STRUCTURAL_PROJECTION

	#ifdef MULTI_TIER
		#define FULL_PROJECTION
	#endif

//	#define RESTRICT_PROJECTION_DISEQUALITIES
//	#define LIMIT_USING_STRUCTURAL_INFORMATION
//	#define LIMIT_CONCRETE_PROJECTION_USING_STRUCTURAL_INFORMATION
//	#define RESTRICT_PROJECTION_NUMBERS_IN_CONCRETE_CUBE
	//#define RESTRICT_ALL_PROJECTION_CONSTRAINTS_IN_CONCRETE_CUBE
#endif

//#define SUBSTITUTION
#ifdef SUBSTITUTION
	//#define PROJECTION_SUBSTITUTION

	#define TWO_STEP_SUBSTITUTION
	#define SEQUENTIAL_SUBSTITUTION
	#ifdef SEQUENTIAL_SUBSTITUTION
		#define SEQUENTIAL_SUBSTITUTION_LEVEL1

		/// Dangerous!
		#define SEQUENTIAL_SUBSTITUTION_LEVEL2
	#endif
#endif

//#define DO_CORRECTNESS_CHECKS
#ifndef PERFORMANCE
	#define DO_CORRECTNESS_CHECKS
#endif


//#ifndef INTERPRET_EX_CC
	/// Flag to assert abstract cube definitely goes to destination.
	/// Should be OFF when Ex/Cc interpretation is set
//	#define EXTRA_CHECKS
//#endif

#ifndef OPTIMIZE
#define DEBUG_TRANS
#endif

#ifdef DEBUG_TRANS
#define DEBUG_TRANS_SIZE
#endif

//#define RANDOMNESS
//#define ALLOW_INPUTS

class Config {
public:
	static bool g_random;
	static int g_ab_granularity;
	static int g_interpret_uf_max_width;
	static int g_minimize_inv_effort;
	static string g_abstraction_name;
	static int g_interpolation;
	static int g_forward_check;
	static int g_fineness;
	static int g_lazy_assume;
	static bool g_uf_unordered;
	static bool g_uf_mult_only;
	static bool g_uf_no_bitwise;
	static bool g_uf_no_sext;
	static bool g_uf_no_shift;
	static string g_print_dot;
	static bool g_print_witness;
	static bool g_bmc_en;
	static bool g_kind_en;
	static int g_bmc_max_bound;

	Config(){}
	~Config(){}
	Config(std::string wdir,std::string bdir):working_dir(wdir),binary_dir(bdir) {}
	std::string  get_working_dir() { return working_dir;}
	std::string  get_binary_dir() { return binary_dir;}
	void load_args(bool picky = true);
	std::string& get_arg(std::string arg) { return args[arg].first;}
	void override_arg(std::string arg,std::string val) {args[arg] = make_pair(val,0);}
	void dump_args(std::ostream& os);

	void get_arg_val(string arg, bool& orig);
	void get_arg_val(string arg, int& orig);

	static bool g_ab_interpret;
	static int g_ab_interpret_limit;
	static int g_ab_interpret_excc;

	static int g_correctness_check;
	static string g_verbosity;
private:
	std::string working_dir;      
	std::string binary_dir;      
	// arg name to (value,flag), when flag tells whether its mandatory or not!
	typedef std::map<std::string,std::pair<std::string,bool> > Args;	
	Args args;      

	bool read_arg(std::ifstream&f,char*);

	void set_abstraction(string& name);

	#define CONFIG_FILE_NAME "fconfig"
	
	// New arguments
	#define AB_GRANULARITY_ARG "ab_granularity"
	#define EN_RANDOM "random"
	#define EN_INTERPRET_UF_MAX_WIDTH "interpret_uf_max_width"
	#define MININV_EFFORT "minimize_inv_effort"
	#define ABSTRACTION_TYPE "abstraction_type"
	#define INTERPOLATION_ARG "interpolation"
	#define FORWARDCHECK_ARG "forward_check"
	#define FINENESS_ARG "fineness"
	#define LAZY_ASSUME_ARG "lazy_assume"
	#define PRINT_SMT2_DESIGN "print_smt2_design"
  #define PRINT_WITNESS "print_witness"
	#define PRINT_DOT "print_dot"
	#define VERBOSITY "verbosity"
	#define BMC_EN "bmc"
	#define KIND_EN "kind"
	#define BMC_MAX_BOUND "bmc_max_bound"

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
