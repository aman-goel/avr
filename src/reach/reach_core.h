/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


#ifndef AVERROES_FLOW_FLOWSERVICES_H__
#define AVERROES_FLOW_FLOWSERVICES_H__

#include <stdint.h>
#include <fstream>
#include <algorithm>
#include <cmath>
#include <sys/time.h>
#include <sys/resource.h>
#include <csignal>
#include <math.h>
#include <ctime>
#include <iomanip>
#include <unordered_set>
#include "avr_util.h"
#include "reach_sa.h"
#include "reach_cube.h"
#include "reach_evaluate.h"
#include "reach_tsim.h"
#include "reach_cex.h"
#include "reach_bmc.h"

//#define SUGGEST_TRACE_VIEWER
using namespace std;

#ifdef _Z3
	#include "reach_z3.h"
	using namespace _z3;
#endif

#ifdef _Y2
	#include "reach_y2.h"
	using namespace _y2;
#endif

#ifdef _M5
	#include "reach_m5.h"
	using namespace _m5;
#endif

#ifdef _BT
	#include "reach_bt.h"
	using namespace _bt;
#endif

#ifdef _MS
	#include "reach_ms.h"
	using namespace _ms;
#endif

namespace reach
{

#ifndef ARM_RELEASE
	//#define BIT_LEVEL_AVR
	//#define PATCH_FOR_154
	//#define _DEBUG_MODE_
	//	RESET_INIT_PATCH : assume every FF is 0 at the beginning
	//#define RESET_INIT_PATCH
#endif

#define DETAILED_STAT_DUMP

//#define GEN_DP_LEMMAS_BY_INTERNAL_NODES

//#define AVR_GENERALIZE_REF

// the following option slow-downs the performance
//#define GCUBE_HIGHER_PRIORITY_EQ_REGS

/// Added by Aman
//#define GENERALIZE_WITH_CELL
//#define GENERALIZE_WO_DISEQ

#ifdef _M5
	#define PRINT_DESIGN_SMT2
	#define PRINT_INV_SMT2
#endif

#ifdef _BT
	#define PRINT_DESIGN_BTOR2
#endif

//	#define INTERACTIVE_CUBE

//#define FRAME_SOLVER_MULTI

//#define LEARN_INIT_PREDICATE								// learn from initial state formula to make it part of ic3
#ifdef LEARN_INIT_PREDICATE
//	#define LEARN_INIT_PREDICATE_ADD_PRED		// learn but don't add init formula predicate as compulsory in cube
	#define LEARN_INIT_PREDICATE_PROCESS_PRED		// process init pred formula
//	#define LEARN_INIT_PREDICATE_TRAVERSE_INIT		// traverse init during COI pruning
#endif

//#define GENERALIZE_OFF

//#define GENERALIZE_WITH_LESSTHAN
#ifdef GENERALIZE_WITH_LESSTHAN
	#define GENERALIZE_WITH_LESSTHAN_LINEAR
//	#define GENERALIZE_WITH_LESSTHAN_QUADRATIC
#endif

//#define ALLOW_INPUTS_IN_PREFIX					// Allow conditions with inputs in prefix conditions
#define ALLOW_INPUTS_IN_SUBPREFIX				// Allow conditions with inputs in substituted prefix conditions

//#define PRINT_ALL_ABSTRACT_CUBES
//#define PRINT_ALL_ABSTRACT_TRANSITIONS
//#define ASSERT_ALL_SRC_TO_DEST

//#define USE_SIMPLIFIED_LEMMAS
#define PRINT_SIMPLIFIED_LEMMAS
//#define LEARN_ALL_PREDICATES
#define FP_EARLY_EXIT

//#define FP_RECURSIVE

#define AVR_TIMEOUT  18000         // in seconds
#define AVR_MEMOUT   16000         // in MBs

#define MAX_REF_ITERATIONS 20000

//#define BMC
//#ifdef BMC
//	#define BMC_DEFAULT_LENGTH 9
//#endif

/// Aman - Enabling below flag makes bv_yices very slow in simulation check
//#define SIM_SIMPLIFY_CONSTANT_RELATIONS

#ifdef PRINT_ALL_ABSTRACT_CUBES
	#define ASSERT_DIFFERENT_CONSTANTS
//	#define ASSERT_UF_NOT_IDENTITY
#else
//	#define ASSERT_DIFFERENT_CONSTANTS
//	#define ASSERT_UF_NOT_IDENTITY
#endif

//	#define SIMULATION_CHECK_SELF_LOOPS
//	#define SW_LOOP_EXAMPLE
//	#define SW_INPUT_EXAMPLE

#ifdef INTERPRET_EX_CC
//	#define ALL_SIMPLIFIED_EX_CC
//	#define SIM_SIMPLIFY_EX_CC
#endif

//#define INDUCTIVE_BLOCKING

//#define VERIFY_MUS

//#define CHECK_BAD_CUBE
//#define CHECK_ALL_CUBES
//#define ABSTRACT_CHECK_ACEXT

//#define EXPAND_FROM_MINTERM
//#define EXPAND_CUBE_USING_SOLVER

#define SIMULATION_CHECK_LIMIT_INSTANTIATION				// Limits simulation check learning to avoid only instantiated predicates

/// Aman Tests

#ifdef ABSTRACTION_COURSE
	/// Abstraction of our abstraction (by limiting constraints in a cube using v_important)
	#define AB_COURSE_AUTO

	/// Abstraction of our abstraction (by limiting constraints in a cube using Averroes 1 style cube expansion)
//	#define AB_COURSE_AS_AVR1

	/// AB_COURSE_REFINE_USING_LEMMAS
//	#define AB_COURSE_REFINE_USING_LEMMAS

	#ifdef REACH_ADD_PATH_CONSTRAINTS
		/// Perform WLP check on ACEXT (Course)
		#define ACEXT_WLP_CHECK_COURSE
	#endif
#endif

#ifdef ACEXT_WLP_CHECK_COURSE
	/// ACEXT WLP CHECK AB_COURSE_REFINE_USING_LEMMAS
//	#define ACEXT_WLP_COURSE_REFINE_USING_LEMMAS
#endif

#ifdef AB_COURSE_AUTO
	/// Abstraction of our abstraction (by further limiting constraints in a cube using function composition level)
//	#define AB_COURSE_AUTO_LIMIT_FC
#endif

//#define AB_COURSE_AS_AVR1
#ifdef AB_COURSE_AS_AVR1
	#define FUNCTIONAL_CONSISTENCY_ANALYSIS
//	#define AVR_CUBE_ADD_STATE_VAL_PARTITION_INFO
//	#define AVR_CUBE_ADD_STATE_VAL_PARTITION_INFO_VIOL_ORIGINAL
//	#define TRACE_BACK_DERIVE_CORR_EQ
#endif

/// Expand a frame F[k] s.t. (F[k] & P & T & !P+) is UNSAT by extracting an MUS out of this unsat query
//#define FP_EXPAND_FRAME

//#define REACH_ADD_PATH_CONSTRAINTS
#ifdef REACH_ADD_PATH_CONSTRAINTS
	#define LIMIT_WLP_USING_FCLEVEL
//	#define LIMIT_WLP_NO_EXTRA_FC

	/// Perform WLP check on ACEXT (Fine)
	//#define ACEXT_WLP_CHECK
#endif

#ifdef ACEXT_WLP_CHECK
	/// ACEXT WLP CHECK_REFINE_USING_LEMMAS
//	#define ACEXT_WLP_REFINE_USING_LEMMAS
#endif

#ifdef SIMULATION_CHECK_SELF_LOOPS
//	#define LEARN_EVERYTHING_FROM_SELF_LOOPS
	#define LIMIT_SIMULATION_ITERATIONS
	#ifdef LIMIT_SIMULATION_ITERATIONS
		#define INIT_SELF_LOOP_ALLOWANCE 5000
	#endif
#endif


#ifdef ASSERT_DIFFERENT_CONSTANTS
	/// Below mode not needed, leave it commented
//	#define ASSERT_DIFFERENT_LEMMA_CONSTANTS
#endif
/// END

//#define RESET_CONTEXT_AFTER_FP								// Reset solver context after forward propagation
#define RESET_FRAME_SOLVERS_AFTER_FP						// Reset all frame solvers after forward propagation

//#define NEW_SOLVER_FOR_AB_MUS									// Use new solvers for MUS extraction used in abstract domain

#define REFRESH_FRAME_SOLVERS_QUERY										// Reset a frame solver after a threshold

#define REFRESH_FRAMES_QUERY_THRESHOLD	300					// Maximum continuous queries allowed for a frame before resetting

//#define INDUCT_INV_PRINT_ONLY					// Option to skip concrete BV check for inductive invariant at the end and simply print the query only

#if 1

#define TEMP_DEBUG_LEVEL 	/* 0  [PRE]   pre-processing */					        	"0"\
							            /* 1  [CTI]   CTI-check */  						          "0"\
                          /* 2  [BP]    backward-propagation */  		        "0"\
                          /* 3  [FP]    forward-propagation */  			    	"0"\
                          /* 4  [DPR]   datapath-refinement */  			    	"0"\
                          /* 5  [TB-D]  trace-back_CTI */  					        "0"\
                          /* 6  [TB-BP] trace-back_backward_propagation*/  	"0"\
                          /* 7  [CC]    containment_check */  				      "0"\
                          /* 8  [RES]   result */								            "1"\
                          /* 9  [EVAL]  eval_formula&term */  		      		"0"\
                          /* 10 [CONF]  config */  							            "0"\
                          /* 11 [SOLV]  solver */  							            "0"\
                          /* 12 [WN]    word-leve_netlist */  			      	"0"\
                          /* 13 [Aman]  aman-essential-printing */  		  	"0"\
                          /* 14 [Sim]   simulation-refinement */  		    	"3"\
                          /* 15 		    clean print */			  			        "0"\
                          /* 16 [SMT]   smt-lib */				  		          	"0"\
                          /* 17 [MUS]   mus-extraction */			  		      	"0"\
                          /* 18 [TSIM]  ternary-simulation */               "0"\
                          /* 19 [ITP]   interpolation */			  		      	"0"\
													/* 20 [BMC]   bounded-model-checking */           "1"

//#define TEMP_DEBUG_LEVEL 	/* 0  [PRE]   pre-processing */					        	"0"\
//							            /* 1  [CTI]   CTI-check */  						          "4"\
//                          /* 2  [BP]    backward-propagation */  		        "4"\
//                          /* 3  [FP]    forward-propagation */  			    	"4"\
//                          /* 4  [DPR]   datapath-refinement */  			    	"4"\
//                          /* 5  [TB-D]  trace-back_CTI */  					        "4"\
//                          /* 6  [TB-BP] trace-back_backward_propagation*/  	"4"\
//                          /* 7  [CC]    containment_check */  				      "4"\
//                          /* 8  [RES]   result */								            "4"\
//                          /* 9  [EVAL]  eval_formula&term */  		      		"0"\
//                          /* 10 [CONF]  config */  							            "0"\
//                          /* 11 [SOLV]  solver */  							            "0"\
//                          /* 12 [WN]    word-leve_netlist */  			      	"0"\
//                          /* 13 [Aman]  aman-essential-printing */  		  	"4"\
//                          /* 14 [Sim]   simulation-refinement */  		    	"4"\
//                          /* 15 		    clean print */			  			        "4"\
//                          /* 16 [SMT]   smt-lib */				  		          	"0"\
//                          /* 17 [MUS]   mus-extraction */			  		      	"4"\
//                          /* 18 [TSIM]  ternary-simulation */               "4"

//#define EXP

//#define TEMP_DEBUG_NEW_CUBE_DERIV_DEFLD

//#define TEMP_DEBUG_LEVEL "1111111111"
//#define TEMP_DEBUG_LEVEL "3333333333"
#else
//#define TEMP_DEBUG_LEVEL "666666666"
//#define TEMP_DEBUG_LEVEL "3333333333"
//#define TEMP_DEBUG_LEVEL "1111111111"
#define TEMP_DEBUG_LEVEL "0000000000"
// FCA:		functional_consistency_analysis
// DEFLD:	derive_euf_func_list_debug
// CIST:	check_invalid_state_term
// LFL:		lookup_func_list
// TB:		trace_back
// #define TEMP_DEBUG_NEW_CUBE_DERIV
// #define TEMP_DEBUG_NEW_CUBE_DERIV_VIOL_FL
	//#define TEMP_DEBUG_NEW_CUBE_DERIV_TB
// #define TEMP_DEBUG_NEW_CUBE_DERIV_FCA_INSERT
// #define TEMP_DEBUG_NEW_CUBE_DERIV_DEFLD
// #define TEMP_DEBUG_NEW_CUBE_DERIV_CIST
// #define TEMP_DEBUG_NEW_CUBE_DERIV_LFL
#endif

	#define ADD_CEXT(_sig, _val)	m_cext[1].push_back(OpInst::create(OpInst::Eq, _sig, _val));m_cext2[1].insert(_sig);


#ifdef _DEBUG_MODE_
	#define DEBUG_CEXT_VALIDATION
	#define DEBUG_REF_ADV_GEN if(0)cout
	//#define DEBUG_REF_ADV_GEN cout
//	#define AVR_DUMP_DOT
// 	#ifndef PATCH_FOR_BIT_LEVEL_AVR
// 		#define AVR_GCUBE_ADD_ALL_PARTITION_INFO
// 		// AVR_CUBE_ADD_STATE_VAL_PARTITION_INFO improves performance a lot
// 		#define AVR_CUBE_ADD_STATE_VAL_PARTITION_INFO
// 	#endif
	#define AVR_CUBE_ADD_STATE_VAL_PARTITION_INFO


	#define AVR_CUBE_SORT
	#define AVR_DUMP_ACCUM_REFF
	#define AVR_DUMP_FRAMES_TO_FILES
	#define AVR_DUMP_DIFF_FRAMES_TO_FILES
	//#define AVR_DUMP_DP_FRAME
	//#define AVR_DP_REFINEMENT_ON_ALL_CEXT_SEGMENTS
//	#define AVR_REFINE_REDUCE_ITnotP
	//	mode : 1 normal collecting violations
	//	mode : 2 avr trace back
	//	mode : 3 avr collect coi
	//#define DEBUG_EVAL_FORMULA_TERM (mode == 1)

	#define AVR_ADD_NEXT_REF
	//#define AVR_PARTIAL_BIT_BLAST
	#define DETAILED_STAT_DUMP
	//	check // TEMP TEMP and delete it
	//#define INSERT_USER_LEMMAS
	//#define INSERT_ZERO_LEMMAS
	//#define AVR_TERMINATION_FIX
	//#define ADD_REG_RESET_DURING_TB

	#define AVR_ADD_INITS_ENABLE
	#define ADD_INITS_TO_GCUBE_TB_CUBE_ENABLE
	#define AVR_CUBE_CONTAIN_INITS_TBCUBE_TRUE

	#if 1
		//#define USE_TRACE_BACK_ALONE
		#define AVR_PME_SOLVER_ENABLE
	#else
		#define USE_TRACE_BACK_ALONE
		//#define AVR_PME_SOLVER_ENABLE
	#endif

	//#define DUMP_CEX_VAL
	//#define AVR_GIDX
	//#define AVR_PPC_SOLVER_ENABLE
	#define AVR_BLOCK_ADD_ONE_ENABLE

	#define CHECK_TERMINAL_CONDITION_DURING_CONTAINMENT_CHECK
	#define USE_MUSES_IN_BLOCK
	#define AVR_INCREMENTAL_DP_REFINEMENT
	//#define DEBUG_AVR_GET_ABST_VIOLS
	//#define CAMS_ONE_MUS	//not using for now
	//#define AVR_SKIP_PROP_IN_VIOL // WE SHOULD NOT USE THIS WITH IC3
	//#define AVR_BLOCK_SAT_ME
	//#define AVR_GIDX

	#define AVR_GENERALIZE_REF
	//#define AVR_CONC_SOLVER_FOR_REACHABILITY
	//#define AVR_CONC_SOLVER_FOR_PROP
	//#define AVR_USE_VE_MODEL
	//#define AVR_ADD_CNF_NEXT
	// You should comment out the function, info in utils.cpp
	// to remove CAMU-related logs
	//#define USE_VE_MODEL
	//#define DEBUG_CEX_VAL
	//#define AVR_TRACE_DEBUG
#else
	#define DEBUG_REF_ADV_GEN if(0)cout
	//#define DEBUG_REF_ADV_GEN cout
	#define AVR_DUMP_DOT
// 	#ifndef PATCH_FOR_BIT_LEVEL_AVR
// 		#define AVR_GCUBE_ADD_ALL_PARTITION_INFO
// 		#define AVR_CUBE_ADD_STATE_VAL_PARTITION_INFO
// 	#endif
//	#define AVR_CUBE_SORT
	//#define AVR_DUMP_ACCUM_REFF
	//#define AVR_DUMP_FRAMES_TO_FILES
	//#define AVR_DUMP_DIFF_FRAMES_TO_FILES
	//#define AVR_DUMP_DP_FRAME

//	#define AVR_DP_REFINEMENT_ON_ALL_CEXT_SEGMENTS

	//#define AVR_REFINE_REDUCE_ITnotP
	//	mode : 1 normal collecting violations
	//	mode : 2 avr trace back
	//	mode : 3 avr collect coi
	//#define DEBUG_EVAL_FORMULA_TERM (mode == 2)

	#define AVR_ADD_NEXT_REF
	//#define AVR_PARTIAL_BIT_BLAST
#ifndef ARM_RELEASE
//	#define DETAILED_STAT_DUMP
#endif
	//	check // TEMP TEMP and delete it
	//#define INSERT_USER_LEMMAS
	//#define INSERT_ZERO_LEMMAS
	//#define AVR_TERMINATION_FIX
	//#define ADD_REG_RESET_DURING_TB

	/// Aman
	#define AVR_ADD_INITS_ENABLE

	#define ADD_INITS_TO_GCUBE_TB_CUBE_ENABLE
	#define AVR_CUBE_CONTAIN_INITS_TBCUBE_TRUE

	#if 1
		//#define USE_TRACE_BACK_ALONE
//		#define AVR_PME_SOLVER_ENABLE

		/// Aman
		#ifndef REACH_ADD_PATH_CONSTRAINTS
		#else
			#ifdef LIMIT_WLP_USING_FCLEVEL
			#endif
			#ifdef LIMIT_WLP_NO_EXTRA_FC
			#endif
		#endif
		/// END
	#else
		#define USE_TRACE_BACK_ALONE
		//#define AVR_PME_SOLVER_ENABLE
	#endif

	//#define DUMP_CEX_VAL
	//#define AVR_GIDX
	//#define AVR_PPC_SOLVER_ENABLE
	#define AVR_BLOCK_ADD_ONE_ENABLE
	#define CHECK_TERMINAL_CONDITION_DURING_CONTAINMENT_CHECK
	#define USE_MUSES_IN_BLOCK
	#define AVR_INCREMENTAL_DP_REFINEMENT
	//#define DEBUG_AVR_GET_ABST_VIOLS
	//#define CAMS_ONE_MUS	//not using for now
	//#define AVR_SKIP_PROP_IN_VIOL // WE SHOULD NOT USE THIS WITH IC3
	//#define AVR_BLOCK_SAT_ME
	//#define AVR_GIDX

//	#define AVR_GENERALIZE_REF
	//#define AVR_CONC_SOLVER_FOR_REACHABILITY
	//#define AVR_CONC_SOLVER_FOR_PROP
	//#define AVR_USE_VE_MODEL
	//#define AVR_ADD_CNF_NEXT
	// You should comment out the function, info in utils.cpp
	// to remove CAMU-related logs
	//#define USE_VE_MODEL
	//#define DEBUG_CEX_VAL
	//#define AVR_TRACE_DEBUG
#endif

#ifdef AVR_PME_SOLVER_ENABLE
	#ifdef AVR_PPC_SOLVER_ENABLE
		#define AVR_PME_SOLVER_BA_IDX 3
		#define AVR_PPC_SOLVER_BA_IDX 4
		#define AVR_REACH_SOLVER_BA_IDX_BASE 5
	#else
		#define AVR_PME_SOLVER_BA_IDX 3
		#define AVR_REACH_SOLVER_BA_IDX_BASE 4
	#endif
#else
	#ifdef AVR_PPC_SOLVER_ENABLE
		#define AVR_PPC_SOLVER_BA_IDX 3
		#define AVR_REACH_SOLVER_BA_IDX_BASE 4
	#else
		#define AVR_REACH_SOLVER_BA_IDX_BASE 3
	#endif
#endif

// cout by Aman
#define REACH_COUT_A(expr)	{cout << expr;}

//	}
//	#define REACH_COUT_A(expr)	cout << expr;

typedef map<string, SigInst*> StrToSExpM;
typedef map<string, Inst*> StrToExpM;
typedef map<string, string> StrToStr;
typedef map<string, unsigned> StrToInt;
typedef pair<Inst*, Inst*> InstsPair;
typedef set<string> StringS;
typedef vector<StringS> StringSV;
typedef struct QueueType {
	int frame;
	unsigned prio;
	Inst *cube;
} QueueType;

// Macros for traceback modes
#define AB_REACH 	 0
#define AB_REACH_TOP 1
#define AB_REACH_INIT 3
#define AB_CC_ACEXT  2

class BR_QUERY {
public:
	int frameIdx;
	InstToInstM Trel;
	InstS dest;
};


class ABSTRACT_CUBE {

public:
	Inst* cube;
	Inst* next;
	int frame;
	const InstL* relevantWires;

	const InstL* relevantWiresNext;

//	InstL cubeConstraints;
//	InstL nextConstraints;

//	Inst* cube_wo_input;

	ABSTRACT_CUBE()
	{
		cube = NULL;
		next = NULL;
		frame = -1;

//		relevantWires.clear();

//		cube_wo_input = NULL;
//		cubeConstraints.clear();
//		nextConstraints.clear();
	}
};


class MIN_TERM_ABSTRACT {

public:
	SOLUTION s;
  InstL all_predicates;
  map< pair< int, SORT>, InstL > all_terms;

	MIN_TERM_ABSTRACT() {
		clear();
	}
	void clear() {
		s.clear();
		all_predicates.clear();
		all_terms.clear();
	};
};

class MIN_TERMS_ABSTRACT_DETAILED {

public:
	SOLUTION s;
	string feasible;
	Inst* allConditions;
	int id;
  unsigned trueId;

  void clear()
  {
    id = -1;
    trueId = 0;
    s.clear();
    feasible = "?";
  };

	MIN_TERMS_ABSTRACT_DETAILED()
	{
		clear();
	}
};

/// END

class PQElement{
public:
	int		prio;
	int		frame;
	int		refs;

	ABSTRACT_REACH_VIOL abViol;
	// cubes_partition contains partition information (or cex value) of the terms in the cube
	// The partition information is obtained during the trace-back cube derivation
	PQElement*	pNext;
	PQElement*	pLink;

	PQElement(int prio, int frame, ABSTRACT_REACH_VIOL abViol, PQElement* pNext) :
	prio(prio), frame(frame), abViol(abViol), pNext(pNext){
		refs  = 1;
		pLink  = NULL;
	}
};

class PriorityQueue{
public:	
	PriorityQueue() : to_remove(NULL), head(NULL), queue_size(0) {}
	void PQ_ref(PQElement* pq_elem);
	void PQ_deref(PQElement* pq_elem);
	PQElement* PQ_push(int prio, int frame, ABSTRACT_REACH_VIOL abViol, PQElement* pNext);
	void PQ_pop();
	void PQ_clear();
	void PQ_print(string loc);
	int PQ_size(){return queue_size;}
	PQElement* PQ_head();
	bool PQ_empty();

private:
//	set<PQElement*> debug_queue;
	PQElement* to_remove;
	PQElement* head;
	int	queue_size;
};

// Uses Bit Vectors to represent variables and BV theory to operate on them
class BV_Mapper: public Solver::TheoryMapper {
	virtual Solver::TheoryMapper::OpType fetch_op(Inst*) {
		return Solver::TheoryMapper::BV_OP;
	}
	virtual Solver::TheoryMapper::VarType fetch_var(Inst*) {
		return Solver::TheoryMapper::BV_VAR;
	}
	virtual LogicType fetch_logic(void) {
		return QF_BV;
	}
	virtual string get_theory_name(void) {
		return "QF_BV";
	}
};

// Uses integer to represent variables and EUF theory to operate on them
// Uses Boolean type for nodes with size=1
class EUF_Mapper: public Solver::TheoryMapper {
	virtual Solver::TheoryMapper::OpType fetch_op(Inst* e) {
		if (e)
		{
			if (e->ab_interpret.is_concrete())
				return Solver::TheoryMapper::BV_OP;
		}
		return Solver::TheoryMapper::EUF_OP;
	}
	virtual Solver::TheoryMapper::VarType fetch_var(Inst*e) {
		if (e)
		{
			if (e->ab_interpret.output_concrete())
//				return (e->get_size() == 1) ? Solver::TheoryMapper::BOOL_VAR : Solver::TheoryMapper::BV_VAR;
				return Solver::TheoryMapper::BV_VAR;
		}
		return (e->get_size() == 1) ? Solver::TheoryMapper::BOOL_VAR : Solver::TheoryMapper::EUF_VAR;
	}
	virtual LogicType fetch_logic(void) {
		return QF_UF;
	}
	virtual string get_theory_name(void) {
		return "QF_UF";
	}
};

// Uses BVs to represent wide variables and UFBV theory to operate on them
// Uses Boolean type for nodes with size=1
class UFBV_Mapper: public Solver::TheoryMapper {
	virtual Solver::TheoryMapper::OpType fetch_op(Inst* e) {
		if (e) {
			e = e->get_port();

			if (Config::g_uf_mult_only) {
				if (e->get_type() == Op) {
					OpInst* op = OpInst::as(e);
					if (op->get_op() == OpInst::Mult)
						return Solver::TheoryMapper::EUF_OP;
				}
				return Solver::TheoryMapper::BV_OP;
			}

			if (Config::g_ab_interpret_excc >= LEVEL_EXCC_ALL) {
				if (e->get_type() == Ex)
					return Solver::TheoryMapper::BV_OP;
				else if (e->get_type() == Op) {
					OpInst* op = OpInst::as(e);
					if (op->get_op() == OpInst::Concat)
						return Solver::TheoryMapper::BV_OP;
				}
			}
			if (Config::g_ab_interpret_limit == 0)
				return Solver::TheoryMapper::BV_OP;
			else if (e->ab_interpret.is_concrete())
				return Solver::TheoryMapper::BV_OP;
		}
		return Solver::TheoryMapper::EUF_OP;
	}
	virtual Solver::TheoryMapper::VarType fetch_var(Inst*e) {
		if (Config::g_uf_mult_only)
			return Solver::TheoryMapper::BV_VAR;
		else if (Config::g_ab_interpret_excc >= LEVEL_EXCC_ALL)
			return Solver::TheoryMapper::BV_VAR;
		else {
			if (Config::g_ab_interpret_limit == 0)
				return Solver::TheoryMapper::BV_VAR;
			else if (e->ab_interpret.output_concrete())
				return Solver::TheoryMapper::BV_VAR;
		}
		return (e->get_size() == 1) ? Solver::TheoryMapper::BOOL_VAR : Solver::TheoryMapper::EUF_VAR;
	}
	virtual LogicType fetch_logic(void) {
		return QF_UFBV;
	}
	virtual string get_theory_name(void) {
		return "QF_UFBV";
	}
};

/// Aman
class LOCATION
{
public:
	Inst* location;
	InstL conditions;

	LOCATION() {
		conditions.clear();
	}
};

class LOOP
{
public:
	Inst* start;
	Inst* end;
	deque < Inst* > loop;
	int size;
	LOOP* parent;
	list <LOOP*> children;
	int id;
	int level;

	LOOP() {
		size = 0;
		parent = NULL;
		children.clear();
		id = 0;
		level = 0;
	}
};

class LoopInfo{
public:

	int loopSize;
	SigInst* locStart;
	SigInst* locEnd;

	LoopInfo(){
//		frameStart = -1;
		loopSize   = 0;
		locStart   = NULL;
		locEnd     = NULL;
	}
};

class SIMULATION_POSITION
{
public:

	/// Contains map of present state register assignments (only of registers of size > 1)
	InstToMpzRefM s;

	/// Contains map of present state register assignments (only of registers of size > 1)
	InstToInstM val;

	/// Set of constants relevant
	InstS consts;

	/// Set of present state registers relevant
	InstS sigs;

	/// Contains map of present inputs to their symbolic constants
	InstToInstM inp2Const;

	/// Contains constant conditions during simulation
	InstS cConditions;

	/// Contains post conditions during simulation
	InstL postConditions;

	///	sIdx: index in ACEXT of corresponding simulation state
	int sIdx;

	///	src: index in ACEXT of parent simulation state
	int src;

	///	dest: index in ACEXT of successor simulation state
	int dest;

//	int selfLoopCount;

	void clear()
	{
		sIdx = -1;
		src  = -1;
		dest = -1;
		val.clear();
		inp2Const.clear();
		sigs.clear();
		consts.clear();
		cConditions.clear();
//		selfLoopCount = -1;
		postConditions.clear();
	}

	SIMULATION_POSITION()
	{
		sIdx = -1;
		src  = -1;
		dest = -1;
		val.clear();
		inp2Const.clear();
		sigs.clear();
		consts.clear();
		cConditions.clear();
//		selfLoopCount = -1;
		postConditions.clear();
	}

};

class SIMULATION_STATE
{
public:
	///	s: concrete solution state in simulation
	InstToMpzM s;

	///	Ls: concrete location in simulation
	Inst* Ls;

	///	sIdx: index in ACEXT of corresponding simulation state
	int sIdx;

	///	LoopS: pointer to loop (NULL if in top) to which simulation state belong to
	LOOP* LoopS;

	void clear()
	{
		LoopS = NULL;
		Ls = NULL;
		sIdx = -1;
		s.clear();
	}

	SIMULATION_STATE()
	{
		LoopS = NULL;
		Ls = NULL;
		sIdx = -1;
	}

};

class SIMULATION_CONFLICT
{
public:
	int src;
	int dest;
	InstL conditions;
	InstL assignments;

	void clear()
	{
		src = -1;
		dest = -1;
		conditions.clear();
		assignments.clear();
	}
	SIMULATION_CONFLICT()
	{
		src = -1;
		dest = -1;
		conditions.clear();
		assignments.clear();
	}

};
/// END

// centralize the algorithm in 3 modules:

#define BAD_CUBE_INDEX -2

class Reach{
public:	// TODO cleanup
	static int num_scalls_sat_ct;
	static int num_scalls_unsat_ct;

	static int num_scalls_sat_mus_sim;
	static int num_scalls_unsat_mus_sim;
	static int num_scalls_sat_muses_dpr;
	static int num_scalls_unsat_muses_dpr;
	static int num_scalls_sat_muses_reach;
	static int num_scalls_unsat_muses_reach;

	static int num_scalls_sat_core_muses_reach;
	static int num_scalls_unsat_core_muses_reach;
	static int num_scalls_sat_min_muses_reach;
	static int num_scalls_unsat_min_muses_reach;

	static int num_scalls_sat_correctness;
	static int num_scalls_unsat_correctness;

	static int sz_hard_core_muses_reach;
	static int sz_soft_core_muses_reach;
	static int sz_out_core_muses_reach;
	static int sz_hard_min_muses_reach;
	static int sz_soft_min_muses_reach;
	static int sz_out_min_muses_reach;
	static int num_muses_reach;

	static int num_path_constraints_taken;
	static int num_path_constraints;

	static int num_sim_iterations;

	static int num_local_eq;
	static int num_local_eq_sig;
	static int num_local_eq_num;
	static int num_local_eq_uf;

	static int refine_flush_count;
	static long long refine_flush_len_acext;
	static long long refine_flush_level;
	static long long refine_flush_frames;
	static long long refine_flush_clauses;

	static map<int, int> num_excc_prop;
  static map<int, int> num_excc_all;

#ifdef SIMULATION_CHECK_SELF_LOOPS
	static int sim_self_loop_allowance;
#endif

	//Reach(){ euf_solver = 0;	}
	Reach(Config *config):_config(config), _euf_solver(NULL), _last_allocated_solver(NULL)
	{
		_refine_exit_frame = -1;

		_concrete_mapper = &_bv_mapper;

		if (Config::g_ab_interpret)
			_abstract_mapper = &_ufbv_mapper;
		else
			_abstract_mapper = &_uf_mapper;
	}

	int _refine_exit_frame;
	
	~Reach();

#ifdef STRUCTURAL_PROJECTION
	STRUCTURE_ANALYSIS sa;
#endif

//	void finalize();



	// from ReachControl
	bool done();
	bool retrieve_abst_cex();
	bool abst_cex_is_top();
	bool localize_bug();

	// objects
	Solver* abst_solver();
	Solver* new_conc_solver(bool is_inc, unsigned ba_idx, int type = conc);
	void del_conc_solver();
	Solver* conc_solver();
	
	// MEGA Steps
	void init_solv();
	void exit_solv();
	void reset_solv();
	void init_flow();
  void delete_solvers();
	void load_model();
	void debug();

	//TODO move to *util*.cpp


	//TODO move to wn.cpp
	void new_print(ostream& out, Inst* e, bool init_visit = false);
	void new_print(ostream& out, InstL &vel, bool init_visit = false);
	void collect_parents(Inst* ve_top, bool init_visit = false);
	Inst* update_chs(Inst *ve_top, InstToInstM& bb_map, bool init_visit = false);

	unsigned dump_dot(int mode, ostream& fout, Inst* top, int depth, bool allowFade, bool init_visit);
	Inst *find_node(Inst *top, unsigned id, bool init_visit = false);
	void draw_graph(int mode, Inst* top, string fname, int depth, bool allowFade = false);
	void draw_graph(string fname, string sname, int depth);
	void draw_graph(int mode, Inst* top1, Inst* top2, string fname, int depth, bool allowFade = false);

	void write_wn();
	void read_wn();


	//TODO move to vwn or some ealier stages
	int write_blif_file();
	void print_module_as_blif(std::ostream&out, Trans*top);
	void print_as_blif(std::ostream&out, Inst*e);
	void gather_rhs(StrToSExpM *sem, Inst *ve); 


	//TODO REMOVE
	void partial_bit_blast(Inst **ve_prop, Inst **ve_nsf, Inst *ve_in);
	void partial_bit_blast(InstL &in_regs);
	//long long Timevaldiff(struct timeval *starttime, struct timeval *finishtime);

	void check_correctness();
	void check_correct_lemmas();
	void check_correct_invariant(InstL& invariant, bool concrete);
	void minimize_inductive_invariant(InstL& invariant, bool concrete, bool fastmode);

	bool cube_contain_inits(Inst *cube);
	bool restrict_cube(Inst* full_cube, Inst* &gen_cube);

	int add_inits_to_gcube(Inst *cube, Inst *&gcube, bool tb_cube);

	bool check_if_global(Inst *ve_gcube);
	bool check_using_ufbv(InstL& cube);
  void check_excc(ABSTRACT_REACH_VIOL& abViol, InstS& implications);
	bool check_blocked(int g_idx, CLAUSE &gcube);
	bool check_blocked_using_solver(int g_idx, InstL& conjunct_cube, InstL& conjunct_cone, int count);
	int containment_check(int g_idx, CLAUSE &gcube, int count);

	void forward_frame_clause(int g_idx, int blockIdx, CLAUSE &gcube);

	bool update_inc_solvers(int idx, Inst *ve);
	void dp_refinement_cleanup();
	void collect_inputs(Inst *top, InstS &s_inputs, bool init_visit = true);
	void collect_consts(Inst *top, InstS &s_consts, bool init_visit = true);
	void print_cex();
	void print_design_smt2();
	void print_design_btor2();

	/// Added by Aman
	Inst* try_intermediate_form(Inst* e);
	Inst* try_wired_form(Inst* e);

	void project_abstract_uf(int pmode, InstL& viol, map< string, map< mpz_class, InstL > >& relevantUFs);

	void add_predicate_constraints(Solver* solver, InstL& predConstraints, InstS& wireSet);
	void add_fapps_constraints(InstL& viol, InstL& inputC, InstType type = Sig);

	void print_backward_coi_matrix();
	void print_backward_coi_list();

	void print_all_abstract_min_term(InstL conjunct_top, Solver* solver);

	void print_concrete_min_term(string comment = "");
	void collect_func_stat(Inst* top, int& numConst, int& numCF, int& numUF, int& numMux, int& numCc, int& numEx, map< string, int >& ufType, map< string, int >& ccType, map< string, int >& exType, InstS& constants, InstS& regs, InstS& inps, bool init_visit = false);

	void collect_all_abstract_min_terms(Solver* solver, map< int, MIN_TERMS_ABSTRACT_DETAILED >& allMinTerms, Inst* full_formula, bool concreteOnly = false);
	char check_abstract_transition(InstL& conjunctTmp, bool concreteOnly = false);

	/// Obsolete
//	void expand_next_from_abstract_minterm(MIN_TERM_ABSTRACT& min_term);

//	void print_all_min_term(SolverAPI* solver, int* count, Inst* full_formula, bool abstract = true);
	int check_query (InstL& conjunct_query, string comment="", int forceRes = -1, bool abstract = true);

	/// Aman
	/// Cube expansion using pme solver (MUS extraction)
	int expand_via_pme (InstL& viol);

//	InstS _temp_viol;

	void fetch_failure_condition(Inst* next, InstL conjunct_c, bool resExitAb, InstL conjunct_T, InstLL& failConditions);
	bool simulation_check(deque< ABSTRACT_CUBE >& rcext, ABSTRACT_CUBE& _badCube);
	bool convert_to_lemmas(InstL& failureCondition, InstL& newLemmas, SIMULATION_POSITION& sCurr, deque< ABSTRACT_CUBE >& rcext);
  bool add_predicate(Inst* tve, InstL& newRef, InstS& cubeSet, InstS& predSetN, InstL& predList, InstToSetM& constMap, InstToInstM& valMap);
  bool process_predicate_info(Inst* top);
	bool simulation_check_old(deque< ABSTRACT_CUBE >& rcext);
  Inst* sanitize_predicate(Inst* tve);

	bool is_next_wire(Inst *top);

	bool find_input(Inst *top);
//	bool find_next(Inst *top);
	bool find_pre(Inst *top);
	bool find_reg(Inst *top);
//	bool find_sig(Inst *top);
//	bool find_constant(Inst *top);
	bool find_has_limited_sigs(Inst *top, InstS& inputs);
	bool find_limited_sigs(Inst *top, InstS& inputs);
	bool find_limited_sigs(Inst *top, InstToInstM& inputs);
	bool find_from_minset(Inst *top, InstS& relSig, InstS& relConst, set< string >& relUFtype);
	bool find_from_minset2(Solver* solver, Inst *top, InstS& relSig, InstS& relConst, set< string >& relUFtype);

  void print_solution(ostream& out, SOLUTION& s, string comment = "");
	void print_solution(SOLUTION& s, string comment = "", int loc = 15, int level = 2);
	bool add_constraints_using_numbers(InstL& cubes);
	void uniquify_list(InstL& l);
	void uniquify_solution(SOLUTION& s);
	bool simplify_solution(SOLUTION& s, InstToListM& opMap);
	void simplify_solution2();
	bool resimplify_solution(SOLUTION& s, InstToListM& opMap);
	bool resimplify_solution(SOLUTION& s, InstToListM& opMap, InstToInstM& subMap, InstToInstM& subMapR);
	void model_project(SOLUTION& s, SOLUTION& out, string mode, bool allowInp, bool quiet = false);
	void model_abstract(SOLUTION& s, SOLUTION& pre, SOLUTION& inp, SOLUTION& next, SOLUTION& mixed, bool quiet = false);
	void model_abstract2(SOLUTION& s, SOLUTION& pre, SOLUTION& inp, SOLUTION& next, SOLUTION& mixed, bool quiet = false);
  void model_abstract(SOLUTION& s, SOLUTION& pre, SOLUTION& inp, SOLUTION& next, SOLUTION& mixed, InstToInstM& subMapR, bool quiet = false);
	bool model_generalize(SOLUTION& s, InstS& relSig, InstS& relConst, set< string >& relUFtype);
	bool model_generalize2(Solver* solver, InstL& conjunct_q, MIN_TERM_ABSTRACT& m, InstS& relSig, InstS& relConst, set< string >& relUFtype, int mode);
  void model_convert(SOLUTION& s, SOLUTION& out, InstToInstM& subMap, string comment="", bool quiet = false);
	void add_wires_from_solution(SOLUTION& s, InstL& wires);
	void add_wires_from_list(InstL& l, InstL& wires);
	void add_from_solution(Solver* solver, SOLUTION& s, InstL& target, InstL& output);
	void add_from_solution(Solver* solver, SOLUTION& s, InstL& target, InstL& output, InstToInstM& subMap);
	void add_from_solution(Solver* solver, SOLUTION& s, InstL& target, string comment="");
	void add_from_solution(Solver* solver, SOLUTION& s, InstL& target, InstToInstM& subMap, string comment="");
	void add_pred_from_solution(SOLUTION& s, InstL& target, string comment="");
	void add_required_pred_from_solution(SOLUTION& s, InstL& target, int level, string comment="");
	void add_pred_from_solution(SOLUTION& s, InstL& target, InstL& wires, string comment="");

	void add_modify_solution(Solver* solver, SOLUTION& s, InstL& target, InstL& output);
	void add_modify_solution(Solver* solver, SOLUTION& s, InstL& target, string comment="");

	void add_wires(Inst* top, InstL& wires);

	void merge_lists(InstL& target, InstL& side);
	void interpret_distinct_constant(InstL& target);

	bool find_limited_constants(Inst *top, InstS& constants);

	Inst* replace_with_constant(Inst *top, InstToInstM& sigMap, int pIdx);
  Inst* replace_constant_with_value(Inst *top);
  Inst* replace_constant_with_parent(Inst *top, InstToInstM& valMap, bool init_visit=false);
	Inst* replace_from_map(Inst *top, InstToInstM& opMap);

	Inst* replace_constant_with_all_parent(Inst *top, int& idx, list< pair< Inst*, pair< int, Inst* > > >& l, InstToInstM& valMap, bool init_visit=false);

	Inst* substitute_from_map(Inst *top, const InstToInstM* pre, const InstToInstM* next);

	bool add_lazy_assumes(InstToBoolM& dp_lemmas);

	/// Add refinement to _negated_refs and assert to solvers
	bool add_refinement(Inst *tve, string comment="", bool simplificationAllowed=true);

	bool add_single_refinement(Inst *tve);

	/// Add all wires in the back cone of top
	void add_all_wires(Inst *top, InstL& wireList, bool init_visit=false);

	/// Add more wires in the back cone of top
	void add_more_wires(Inst *top, InstL& wireList, bool init_visit=false);

	/// Add gate consistency constraint
	void add_gate_consistency(Inst* tve, InstL& viol, bool init_visit = false);

	/// Checks if an expression is a gate consistency constraints
	bool is_gate_consistency(Inst *top);

	/// Generalize failure condition to derive a lemma
	Inst* make_lemmas(InstL& failCondition);

	/// Reduces ref by unit propagation
	pair< Inst*, Inst* > reduce_ref(Inst *top);
	/// Reduces ref by removing gate consistency constraints
	Inst* reduce_ref_gate(Inst *top);
	/// Reduces ref by trivial equality propagation among wires
	Inst* reduce_ref_wires(Inst *top);
	/// Reduces ref by evaluation
	Inst* reduce_ref_eval(Inst *top);
	/// Reduces ref by evaluation
	bool reduce_ref_eval_sim(InstL& conjunct_top, InstL& conjunct_ref);


//	/// Slice the next state relation into relevant portions only
//	Inst* slice_transition(ABSTRACT_CUBE& cube);

	/// Simplifies expression by using partial interpretation of Ex/Cc
	Inst* simplify_expr(Inst *top);
	Inst* simplify_expr_all(Inst *top);

  Inst* simplify_excc(Inst *top, map< int, map< mpz_class, Inst* > >& numMap, InstToInstM& nextMap);
  Inst* replace_with_num_excc(Inst *top, map< int, map< mpz_class, Inst* > >& numMap, InstToInstM& nextMap);

	/// Converts expression to it's signal equivalent
	Inst* signal_expr(Inst *top);

	/// Eliminate don't cares and simplifies expression by using solver dont cares
	Inst* eliminate_dont_cares(Inst *top, ABSTRACT_CUBE& abCube, int& numOptions, bool init_visit = false);

	int compute_comb_distances(Inst* e);
	void compute_number_uf(Inst* top, vector < int >& ufInfo, bool init_visit = false);

	void collect_constants(Inst *top, InstS& s, bool init_visit = false);
	void collect_const(Inst *top, InstS& s, bool init_visit = false);
	void collect_sig(Inst *top, InstS& s, bool init_visit = false);
	void collect_wire(Inst *top, InstS& s, bool init_visit = false);
	void collect_Assignments(Inst *top, Inst* sigNext, bool init_flag = false);
//	void collect_Eq(Inst *top, int nextAllowed = 1, bool init_visit = false);
//	void collect_simulation_Eq(Inst *top, InstS& eqList, bool init_visit = false);

	void collect_OR(Inst *top, bool init_visit = false);
	void collect_Ternary(Inst *top, bool init_visit = false);
	/// End

	void dump_hm_sizes();
	void global_init();
	void setup_signal(int signum);
	void print_node(ostream& fout, Inst *e);

	Inst *rename_inputs(Inst *e, bool init_visit = false);
	Inst *rename_inputs_2(Inst *e, bool init_visit = false);

	Inst *all_next2pre_ec(Inst *e, bool init_visit = false);

	void all_pre2next(InstL& viol);

	Inst* replace_inputs_with_val(Inst *e, bool init_visit = false);

	bool node_count(Inst *e, bool init_visit = false);
	int get_depth(string str);

	Inst *find_original_node(Inst *top, Inst *target_node, bool init_visit);
	void substitute_nodes(Inst *top, Inst *ve_old, Inst *ve_new, bool init_visit);
	void collect_common_nodes(Inst *ve_top, map<int, Inst*> &m_nodes, int depth, bool init_visit);

	Inst* add_missing_wires(Inst* top);
	/// Aman
	Inst* apply_simulation_constants (Inst *e, InstToSetM& m_constMap, bool init_visit = false);
	Inst* apply_simulation_constants2 (Inst *e, InstToSetM& m_constMap, bool init_visit = false);
	/// END

	Inst *propagate_const(Inst *e, InstToInstM& m_gref);

	Inst *apply_const_with_wires(Inst *e, InstToInstM& m_gref, InstS& useSet);

	Inst *apply_const(Inst *e, InstToInstM& m_gref, InstS& useSet);
	Inst *apply_const_gcube(Inst *e);
	Inst *frame_down(Inst *e);
	
	void get_func_applications(map<string, InstL>& func_list, Inst *top, bool init_visit = false);

	bool derive_euf_func_list(map<string, InstL>& func_list, Inst *top, bool init_visit);
	bool derive_euf_func_list_2(Inst *top, bool init_visit=false);

#ifdef ABSTRACTION_COURSE
	int compute_uf_distances(Inst *top, unsigned currDistance, InstToIntM& ufDistance, bool init_visit=false);
	void add_white_func(Inst *top);
	void add_black_func(Inst *top);
	bool convert_to_white(Inst *top, bool init_visit=false);
	bool convert_to_important(Inst *top);
#endif

	bool exist_wide_mult(Inst *top, bool init_visit);
	int check_invalid_state_term(Inst *top);

	void trace_back(Solver*solver, Inst *full_formula, InstL& assumptions, Inst* e_v, Inst* e_p, int mode = AB_REACH);
	Inst* compare_and_simplify(Inst* v);

	void expand_avr1_style(InstL& viol);
	void functional_consistency_analysis(InstS &result, map<string, InstL>& func_list, Inst *top);
	Inst* lookup_func_list(list<InstsPair>& pairs_equiv_chs, list<InstsPair>& pairs_neq_chs,
							 map<string, InstL>& func_list, OpInst* top);

	// below three functions are for the mixed cube that solves the nondeterministic (never-ending) behavior
	void derive_partition(Inst* ve_gcube_next, InstToMpzM* cube_partition, InstL& conjunct_partition);
	void collect_terms(Inst* top, map<int, InstS> &m_terms, bool init_visit = false);

	void collect_nsfs(Inst *top, bool init_visit = false);
	void collect_wide_regs(Inst *top, map<int, InstS> &m_regs, bool init_visit = false);
	void collect_regs2(Inst *top, set<string> &s_reg_names, bool init_visit = false);
	bool generalize_ref(InstL& c_ref);

	Inst* propagate_internal_nodes(Inst* ref);

	/// Aman
	bool generalize_ref_with_wires(InstL& c_ref);

	/// Aman
	void map_bit_select_const(Inst* lhs, Inst* rhs, InstToSetM& m_constMap, InstToInstM& m_constBitMap);
	bool generalize_simulation_predicates(InstL& tc_ref, InstToSetM& m_constMap, bool& learn);
	/// END

	bool generalize_gcube(Inst *&gcube);
	void add_zero_lemmas(Inst *top, bool init_visit = false);

	Inst *next2pre(Inst *e, bool init_visit = false);
	Inst *pre2next(Inst *e, bool init_visit = false);
	void collect_cubes(Inst *e, bool init_visit = false);
  void collect_all_cubes(Inst *e, bool init_visit = false);
	void collect_nsfs(Inst *top, InstL &vel_nsfs, bool init_visit = false);
	void refine(InstL& hardConstraints, ABSTRACT_CUBE& abCube, Inst *top_wo_ref, bool ab);
	void get_conc_viols(Inst *top);

	void generalize_unsat_query(BR_QUERY& q, InstLL& muses);
	void generalize_unsat_query(BR_QUERY& q, InstLL& muses, Solver* coreSolver, Solver* minSolver);
	int ccext_block();
	int verify();
	void reset_frame_solvers();
	void reset_frame_solver(int frameIdx);
	void reset_cti_solver();
	void set_cti_solver();
	void set_frame_solvers();
	void set_frame_solver(int frameIdx);
	void add_frame_solver();

//	void refine_flush();

	void dump_execution_time(int result);

	bool exist_str(Inst *top, string pattern, bool init_visit = false);


	// Auxiliary Functions
	void load(Trans& trans, string fname, string ftype, bool dump_modeling = false);

  void retrieve_cex_val(Inst*, Solver*, bool abstract, bool init_visit, bool evalSimple = true);
  void retrieve_ab_sol(Solver*, bool init_visit);
  void retrieve_ab_sol(Solver* solver, Inst* e, InstS& relSig, InstS& relConst, set< string >& relUFtype);

	void evaluate_cex_val(Inst* e, Solver*);
	// groups (a=a) and !(a=b) in a single group! since they will never participate in the refinement, and it's good for the MUS algorithm to have them as one entity
	void clean_viol(InstL&);
	// deletes repetition
	void uniqify_viol(InstL&);

	void experimental_viol(Inst*e, unsigned type, bool coi, bool init_visit = false);

	/// Aman
//	void expand_from_minterm(int mode);

	int find_value (Inst* tve, Inst* lhs, Inst* rhs);
	bool is_redundant (Inst* tve);

	void evaluate_refine_relation(int mode, Inst*e, InstL& viol, bool init_visit = false);
	void evaluate_refine_term(int mode, Inst*e, InstL& viol);

	void evaluate_abstract_relation(int mode, Inst*e, EVAL& s);
	void evaluate_abstract_term(int mode, Inst*e, EVAL& s);

	void evaluate_substitute_relation(int mode, Inst*e, ABSTRACT_REACH_VIOL& bins, InstToInstM& nextMap, InstS& relevantSet, bool init_visit = false);
	void evaluate_substitute_term(int mode, Inst*e, ABSTRACT_REACH_VIOL& bins, InstToInstM& nextMap, InstS& relevantSet);

	void COI_prune_relation(Inst*e, EVAL& s, int region);
	void COI_prune_term(Inst*e, EVAL& s, int region);
	void COI_generalize(Inst*e, EVAL& s);
  void COI_generalize_sim(Inst*e, SIMULATION_POSITION& pre, SIMULATION_POSITION& next);

	void evaluate_path_relation(int mode, Inst*e, ABSTRACT_REACH_VIOL& bins, InstToInstM& nextMap, bool init_visit = false);
	void evaluate_path_term(int mode, Inst*e, ABSTRACT_REACH_VIOL& bins, InstToInstM& nextMap);

	void evaluate_abstract_destination(int mode, Inst*e, InstL& bin_pre, InstToInstM& nextMap, bool init_visit = false);
	void evaluate_abstract_destination_term(int mode, Inst*e, InstL& bin_pre, InstToInstM& nextMap);

	void evaluate_simulation_relation(int mode, Inst*e, SIMULATION_POSITION& pre, SIMULATION_POSITION& next, bool& stuck, bool init_visit = false);
	void evaluate_simulation_term(int mode, Inst*e, SIMULATION_POSITION& pre, SIMULATION_POSITION& next, bool& stuck);

	Inst* evaluate_generalize_relation(Inst*e, InstL& viol, bool init_visit = false);
	void evaluate_generalize_term(Inst*e, InstL& viol);

	void evaluate_relation(int mode, Inst*e);
	void evaluate_term(int mode, Inst*e);

	Inst* reduce_relation(Inst*e);
	Inst* reduce_relation_sim(Inst*e, InstToInstM& eqMap);

	bool add_local_eq(Inst* lhs, Inst* rhs);
	bool allowed_relation(Inst* lhs, Inst* rhs, OpInst::OpType opt);

  void print_frames(string comment="");
  void print_summary(string comment="");
  bool propagateBlockedCubes();
  void print_config();
  bool sort_present(SORT sort, SortType target);
  bool collect_system_orig();
  void reduce_system();
  void preprocess_system();
  void collect_system();
  void collect_cones();
  void collect_inputs();
  void set_init_dontcare();
  void print_config2();
  void print_system_stats();
  void collect_struct_info();
  void set_property();
  void draw_system();
  void draw_all_simple(Inst *top, int& count, string comment="", bool init_visit=false);
  void count_all_simple(Inst *top, int depth, bool isProp, bool init_visit);
  void draw_simple(Inst* e, string comment="");
  void check_all_excc(Inst *top, bool init_visit=false);
  void check_excc(Inst* lhs, Inst* rhs);
  void print_frame_states_transitions(bool concreteS = false, bool concreteT = false);
  void print_states_transitions(string filename, Inst* invariant = NULL, bool concreteS = false, bool concreteT = false);
  void print_states_transitions(string filename, Inst* src, Inst* dest, bool concreteS = false, bool concreteT = false);
  void print_states_transitions(string filename, InstL& src, InstL& dest, bool concreteS = false, bool concreteT = false);
  void print_states_transitions(string filename, InstL& src, Inst* dest, bool concreteS = false, bool concreteT = false);

  void print_frame_summary(int k);
  int print_sorted_list(ofstream& out, InstL& l, bool print_msz = false);

  int solveRelative(int frame, InstL& cube, int queryType, bool getModel, bool checkType);
  int solveRelative(int frame, Inst* cube, int queryType, bool getModel, bool checkType) {
    InstL c;  c.push_back(cube);
    return solveRelative(frame, c, queryType, getModel, checkType);
  }
  bool solveCube(InstL& cubeSub, InstL& cube, string comment="");
  bool solvePartition(ABSTRACT_REACH_VIOL& abViol, string comment="");
  bool solveBadDest();
  void refineCube(ABSTRACT_CUBE cube, int idx);

  void add_frame();
  unsigned get_memlimit() {	return _global_memory_limit;	}

	inline int get_bval(Solver* solver, Inst* e) {
		int val = e->get_bval();
		if (val != INVALID_SVAL)
			return val;
		else {
			if (Inst::st_ba_idx < e->sval.size()) {
				SOLVER_VALUE& sVal = e->sval[Inst::st_ba_idx];
				if (sVal.key == Inst::st_retrieve_key)
					return e->get_bval();
			}
			solver->get_assignment(e, val);
	//		bool res = solver->get_assignment(e, val);
	//		if (!res)
	//			cout << *e << endl;
	//		assert(res);
			return e->get_bval();
		}
	}
	inline mpz_class* get_ival(Solver* solver, Inst* e) {
		mpz_class* val = e->get_ival();
		if (val != INVALID_SMPZ)
			return val;
		else {
			if (Inst::st_ba_idx < e->sval.size()) {
				SOLVER_VALUE& sVal = e->sval[Inst::st_ba_idx];
				if (sVal.key == Inst::st_retrieve_key)
					return e->get_ival();
			}
			solver->get_assignment(e, val);
//			bool res = solver->get_assignment(e, val);
//			if (!res)
//				cout << *e << endl;
//			assert(res);
			return e->get_ival();
		}
	}

	void bmc_init ();
	int bmc_run (int kmax);
	void kind_init ();
	int kind_run (int kmax);
	Inst* unroll_to(Inst* top, int u, int v, bool add_to_cex = true);

	Config *_config;

private:
	int controlling(OpInst::OpType op_type) { return ((op_type==OpInst::LogAnd)?0:1); }

	EUF_Mapper  _uf_mapper;
	BV_Mapper   _bv_mapper;
	UFBV_Mapper _ufbv_mapper;

	Solver::TheoryMapper* _abstract_mapper;
	Solver* _euf_solver;

	Solver* _last_allocated_solver;
	Solver::TheoryMapper* _concrete_mapper;

	InstToInstM _m_reg_init;

	InstL _l_negated_ff_inits;// if init = !q1 && !q2 && (r1 == 0) && (r2 == 0), 
							// s_negated_qs is {q1, q2} // used in add_inits_to_gcube
	InstS _s_negated_ff_inits;

	InstToInstM _init_values;
	
	InstToInstM _m_corr_regs;
	InstToInstM _init_dont_care;

	// partition information of a cube, used to pass it to ccext_block()
	InstToMpzM* _cube_partition;

  InstPairS _s_local_eq;       // set of local == instances involving local UFs

	/// Added by Aman
  InstS _s_signals;               // set of learnt signals
  InstS _s_constants;               // set of learnt constants
  InstS _s_uf;                      // set of learnt uf instances
  set< string > _s_uf_types;                      // set of learnt uf types
  InstS _s_conditions_pre; 							// set of learnt predicates (present state)
//	InstS _s_conditions_next; 							// set of learnt predicates (next state)
	InstToListM _m_assignments; 			// map of assignments possible to next state variables in the design
	MIN_TERM_ABSTRACT _min_term;
	InstToMpzM _min_term_c;
	ostringstream _temp_stream;
	InstL _collected_OR;
	list< pair< Inst*, Inst* > > _collected_Ternary;

	ABSTRACT_REACH_VIOL _bad_cube;
	/// END
	
	//temporary variables
	InstL _collected_cubes;
	InstS _collected_nsfs;
	InstToInstM _m_gref; // used in a ref generalization routine
	InstS _s_coi; // set of registers in the design, used to filter out inputs later
	InstS _s_dpl;	// dp lemmas of zeros
	InstS _pre_cubes;
	InstS _cur_cubes;

	//formulas
	Inst *_ve_init;
  Inst *_ve_initNeg;
	Inst *_ve_model;
	Inst *_ve_model_nsf;
	Inst *_ve_prop_eq_1;
	Inst *_ve_prop_eq_0;
	Inst *_ve_prop_next_eq_0;
	Inst *_ve_prop_next_eq_1;
	Inst *_ve_model_next;
	InstL _conjunct_init;
	InstL _conjunct_nsf;

	Inst *_ve_model_nextT;

	Inst* _ve_assume_orig;
	InstS _assumptions;
	Inst* _ve_assume;
	InstToBoolM _all_assumptions;
	InstL _assume_wires;
	InstS _assume_regNext;
	InstToBoolM _assume_T;

	InstL _assume_Twires;

	InstL _init_preds;

	unordered_set< Inst* > _neg_init;

	/// Aman
	vector < long long int > constantValues;
	Inst* LoneHot;
	Inst* LoneHot_next;

	int _max_funcLevel;
#ifdef LIMIT_WLP_USING_FCLEVEL
	int _allowed_funcLevel;
#endif
	/// END

//#define ADD_PSEUDO_CONSTANT
//#ifdef ADD_PSEUDO_CONSTANT
//	Inst *_ve_pseudoK;
//	Inst *_ve_pseudoK2;
//#endif

	//config
	bool _derive_eq_corr_regs;
	bool _derive_eq_init_enabled;
	bool _derive_eq_coi_enabled;
	int _derive_eq_ordering_mode;
	int _global_timeout;
	unsigned _global_memory_limit;
	int _prop_timeout;
	int _reach_timeout;

	//containment check 
	int _set_containment_cnt;
	int _redundant_cube_cnt;
	int _pme_fail_cnt;
	int _pme_succ_cnt;

	//solvers
//	int _num_reach_solvers; // determine how many reach solvers become incremental in each frame
						   // For example, if reach_solvers_inc_thres = 1,
						   // then the reach solver of (frame_idx -1) (i.e. only one) becomes incremental
//	z3_API *_refine_bv_solver;
//	z3_API *_pme_solver; // the solver for the maximum expansion
//	z3_API *_ppc_solver; // the solver for the maximum expansion

	Solver* _cti_solver; // the solver that checks property
	
	int numResetContext;
	int numAssume;
	int numAssumeSig;
	int numAssumeReg;
	int numAssumeInit;
	int numAssumeLemmas;


	class FRAME_SOLVER {
	public:
		Solver* solver1;
		Solver* solver_main;					// Always Z3

		static int numResetFrames;
#ifdef REFRESH_FRAME_SOLVERS_QUERY
		static int maxQ;
		int numQ;
#endif

		FRAME_SOLVER() {
		  solver1 = NULL;
		  solver_main = NULL;
#ifdef REFRESH_FRAME_SOLVERS_QUERY
			numQ = 0;
#endif
		}
		void reset() {
			if (solver_main) {
				delete static_cast<SOLVER_CORE*>(solver_main);
				solver_main = NULL;
				numResetFrames++;
			}
#ifdef FRAME_SOLVER_MULTI
			if (solver1) {
				delete static_cast<SOLVER_REACH*>(solver1);
				solver1 = NULL;
			}
#endif
#ifdef REFRESH_FRAME_SOLVERS_QUERY
			numQ = 0;
#endif
		}

	private:
	};
	vector<FRAME_SOLVER> _reach_solvers; // TODO use vector instead

	//important variables
	// cubes to be blocked at each frame
	// they are accumulating. i.e. cubes @ frame 1 = cubes[1] + cubes[0]
	vector<vector<CLAUSE>> _cubes;
	InstS pool_viol;		// TODO debugging purpose, remove it!!!
	// R0, R1, ... Rn,
	// they are not accumulating. i.e. clauses @ frame 3 = negated_cubes[3]
	inline void negated_cubes(int frameIdx, InstL& output) {
		if (frameIdx == 0) {
			for (InstL::iterator cit = _conjunct_init.begin(); cit != _conjunct_init.end(); cit++)
				output.push_back(*cit);
		}
		else {
			for (int i = frameIdx; i < _cubes.size(); i++) {
				vector<CLAUSE>& c = _cubes[i];
				for (int j = 0; j < c.size(); j++)
					output.push_back(c[j].clause);
			}
		}
	}

	InstL _negated_refs;
	PriorityQueue _queue;
	PriorityQueue _tb_queue;

	/// Aman
	deque< ABSTRACT_CUBE > _rcext_orig;
	vector< int > _cext_idx;

//	PriorityQueue _tb_queue2;
	int _frame_idx;
	int _loop_idx;
	
	//hash to improve the performance // need to be removed at some point
	map<string, Inst *> _msv_all_next2pre_vars;
	map<string, Inst *> _msv_all_pre2next_vars;
	map<InstsPair, bool> _containment_hash;	//slow

	//stats
	int _max_depth;

	int _numTbCalls;
	int _maxSzAbCube;
	int _maxSzCcCube;
	long long _sizeAbCube;
	long long _sizeCcCube;

	long long _numSvAbCube;
	long long _tsbSvAbCube;
	int _maxNumSvAbCube;
	int _maxTsbSvAbCube;

	long long _szT1;
	long long _szT2;
	long long _szT3;
	long long _szT4;

	long long _selT1;
	long long _selT2;
	long long _selT3;
	long long _selT4;

	int _nT1;
	int _nT2;
	int _nT3;
	int _nT4;

	long long _sizeCoiAbCube;
	long long _sizeCoiCcCube;
	long long _sizePredAbCube;
	long long _sizePredCcCube;
	long long _sizefProjAbCube;
	long long _sizefProjCcCube;
	long long _sizeProjAbCube;
	long long _sizeProjCcCube;
	long long _sizeSubsAbCube;

  long long _cube_ab_SigEqSig;
  long long _cube_ab_SigEqNum;
  long long _cube_ab_SigEqOther;
  long long _cube_ab_NumEqOther;
  long long _cube_ab_OtherEqOther;
  long long _cube_ab_SigNeqSig;
  long long _cube_ab_SigNeqNum;
  long long _cube_ab_SigNeqOther;
  long long _cube_ab_NumNeqOther;
  long long _cube_ab_OtherNeqOther;
  long long _cube_ab_SigBool;
  long long _cube_ab_Up;
  long long _cube_ab_Other;

  long long _sizeCoiNumEqAbCube;
  long long _sizeCoiNumNeqAbCube;
  long long _sizeCoiSigEqAbCube;
  long long _sizeCoiSigNeqAbCube;
  long long _sizeCoiOtherAbCube;

	long long _sizefProjNumEqAbCube;
	long long _sizefProjNumNeqAbCube;
	long long _sizefProjSigEqAbCube;
	long long _sizefProjSigNeqAbCube;

	long long _sizeProjNumEqAbCube;
	long long _sizeProjNumNeqAbCube;
	long long _sizeProjSigEqAbCube;
	long long _sizeProjSigNeqAbCube;

	long long _sizefProjNumEqCcCube;
	long long _sizefProjNumNeqCcCube;
	long long _sizefProjSigEqCcCube;
	long long _sizefProjSigNeqCcCube;

	long long _sizeProjNumEqCcCube;
	long long _sizeProjNumNeqCcCube;
	long long _sizeProjSigEqCcCube;
	long long _sizeProjSigNeqCcCube;

	int _numFrameRes;
	int _maxFrameRes;
	long long _sumFrameRes;

	long long _selCoiAbCube;
	long long _selPredAbCube;
	long long _selfProjAbCube;
	long long _selProjAbCube;
	long long _selSubsAbCube;


  long long _cube_ab_SigEqSig_sel;
  long long _cube_ab_SigEqNum_sel;
  long long _cube_ab_SigEqOther_sel;
  long long _cube_ab_NumEqOther_sel;
  long long _cube_ab_OtherEqOther_sel;
  long long _cube_ab_SigNeqSig_sel;
  long long _cube_ab_SigNeqNum_sel;
  long long _cube_ab_SigNeqOther_sel;
  long long _cube_ab_NumNeqOther_sel;
  long long _cube_ab_OtherNeqOther_sel;
  long long _cube_ab_SigBool_sel;
  long long _cube_ab_Up_sel;
  long long _cube_ab_Other_sel;

  long long _selCoiNumEqAbCube;
  long long _selCoiNumNeqAbCube;
  long long _selCoiSigEqAbCube;
  long long _selCoiSigNeqAbCube;
  long long _selCoiOtherAbCube;

	long long _selfProjNumEqAbCube;
	long long _selfProjNumNeqAbCube;
	long long _selfProjSigEqAbCube;
	long long _selfProjSigNeqAbCube;

	long long _selProjNumEqAbCube;
	long long _selProjNumNeqAbCube;
	long long _selProjSigEqAbCube;
	long long _selProjSigNeqAbCube;

	long long _relevantT;
	long long _queryT;

	long long _tb_eval_time;
	long long _tb_pred_time;
	long long _tb_fproj_time;
	long long _tb_proj_time;
	long long _tb_subs_time;
	long long _tb_cube_time;

	long long _tb_ct_initial_time;
	long long _tb_ct_isblocked_time;
	long long _tb_ct_containment_time;
	long long _tb_ct_forwardfast_time;

	long long _tb_setcontain_time;
	long long _tb_updateincsolver_time;

	long long _tb_reach_time;
	long long _tb_val_time;
	long long _tb_UNSAT_camus_time;
	long long _tb_ct_time;
	long long _tb_total_time;

	long long _tb_reach_mus_core;
	long long _tb_reach_mus_min;

	long long _tb_tmp_time;

//	long long _bp_reach_time;
//	long long _bp_SAT_camus_time;
//	long long _bp_UNSAT_camus_time;
//	long long _bp_gidx_time;
//	long long _bp_ct_time;

	long long _pre_time;
	long long _cti_time;
	long long _pme_time;
//	long long _bp_time;
	long long _cleanup_time;
	
	long long _cti_val_time;

	long long _cti_i_time;
	long long _pme_i_time;
	long long _solver_set_time;

	long long _sim_time;	//simulation time

	long long _cc_extra_tb_time;	//extra correctness_check time in tb
	long long _cc_extra_fp_time;	//extra correctness_check time in fp

	long long _cc_time;	//final correctness_check time
	long long _fp_time;
	long long _tb_time;
	long long _dpr_time;

	long long _cc_inv_time; // final correctness check for invariant time

	long long _draw_time;

	int _converged_frame;
	int _numStrongInvariant;
	int _numWeakInvariant;
	int _numImplications;
	int _szInvariant;

	int _nBlocks; // the number of times blockState was called
	int _nBlocksS;
	int _nBlocksU;
	int _nObligs; // the number of proof obligations derived
	int _nObligsS;
	int _nObligsU;
	int _nCubes; // the number of cubes derived
	int _nLiterals; // the number of literals of the cubes derived
	//		int nFrames;	// frames explored
	long long _pme_clauses_before;
	long long _pme_literals_before;
	long long _pme_clauses_after;
	long long _pme_literals_after;

	long long _coi_literals_before;
	long long _coi_literals_after;

	long long _mus_before;
	long long _mus_lit;
	long long _mus_cls;
	long long _mus_cnt;

	int _node_cnt;
	int _bool_node_cnt;
	int _int_node_cnt;
	int _int_op_cnt;	// concat, ex, non-boolean operators
	int _bool_op_cnt;
//	map<OpInst::OpType, int> op_stats;	// <int_op_type, count>
	map<string, int> _op_stats;	// <int_op_type, count>
	InstToSetM _m_pars;
	
	list<int> _nFramesL;
	list<int> _nLegnthsCEXTL;
	list<int> _nDPLemmasL;
	
	int _accum_dp_lemmas;
	int _num_dp_refs_zero_lemmas;

	int _refine_idx; // # of refine() calls
	int _num_dp_refine; // # of iterations of Datapath Refinement
	int _refine_seq_idx;
	struct timeval _start_time;

	
	// from the old version of state
	Trans _model;
	Inst* _prop;
	// refinements!
	InstL _refs;
	InstL _new_refs;
	unsigned _prop_cycle;
	// the violation for feasibility checking
	ABSTRACT_REACH_VIOL _abViol;

//	/// Aman
//	Inst* _next_state;
//	InstL _input_viol;
//	InstL _path_viol;

//	InstL _viol_original;	//just for debugging
//	InstL _viol_partition;
	// used for the experiment.
	InstL _vars;
	StringS _varss;

	bool _sat_res;
	bool _feas_sat_res;
	unsigned _iter;
	bool _finished;
	map<string, InstL> _func_list;

	/// Aman
	int _trace_depth;

	/// TODO: not needed anymore
	int _simeval_depth;

	// Ternary simulation object
  TERNARY_SIM tsim;

  // Counterexample object
  CEX cext;

  // BMC object
  BMC bm;
};

void SIGXCPU_handler(int signum);
void solver_interrupt_handler(int signum);
bool compare_inst(Inst *first, Inst *second);

//Inst *z3_check_v_important(Inst *top);

};

#endif


