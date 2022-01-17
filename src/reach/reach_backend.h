/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


/*
 * reach_backend.h
 *
 *  Created on: Jun 26, 2017
 *      Author: rock
 */

#ifndef AVERROES_FLOW_BACKEND_H_
#define AVERROES_FLOW_BACKEND_H_

/// Solver Backend (Shared constructs)

#include <unistd.h>
#include "avr_word_netlist.h"

/// Configurations
/// Note: Only one of the below flag should be enabled

#define BACKEND_Y2			// Yices 2 for all queries
// #define BACKEND_HYBRID	// hybrid config
// #define BACKEND_BT		// Boolector for all queries
// #define BACKEND_Z3		// Z3 for all queries
// #define BACKEND_M5		// MathSAT 5 for all queries

/// Config: BACKEND_Y2
#ifdef BACKEND_Y2
	#define SOLVER_CTI		  y2_API		// Solver for checking SAT_abstract ? [ F[top] ^ P ^ T ^ !P+ ]
	#define SOLVER_REACH	  y2_API		// Solver for checking SAT_abstract ? [ F[k-1] ^ P ^ T ^ C+ ] and for Fast-forward check
	#define SOLVER_CONTAIN	  y2_API		// Solver for checking if frame restriction global
	#define SOLVER_AB		  y2_API		// Solver for all other abstract queries: Basis check, Lemma redundancy check
	#define SOLVER_CORE       y2_API		// Solver for getting unsat core
	#define SOLVER_MUS		  y2_API		// Solver for getting minimal unsat core
	#define SOLVER_BV         y2_API		// Solver for concrete / bit-vector queries
#endif

/// Config: BACKEND_HYBRID
#ifdef BACKEND_HYBRID
	#define SOLVER_CTI		  y2_API
	#define SOLVER_REACH	  y2_API
	#define SOLVER_CONTAIN	  y2_API
	#define SOLVER_AB		  y2_API
    #define SOLVER_CORE       y2_API
	#define SOLVER_MUS		  y2_API
	#define SOLVER_BV         bt_API
#endif

/// Config: BACKEND_BT
#ifdef BACKEND_BT
	#define SOLVER_CTI		  bt_API
	#define SOLVER_REACH	  bt_API
	#define SOLVER_CONTAIN	  bt_API
	#define SOLVER_AB		  bt_API
    #define SOLVER_CORE       bt_API
	#define SOLVER_MUS		  bt_API
    #define SOLVER_BV         bt_API
#endif

/// Config: BACKEND_M5
#ifdef BACKEND_M5
	#define SOLVER_CTI		  m5_API
	#define SOLVER_REACH	  m5_API
	#define SOLVER_CONTAIN	  m5_API
	#define SOLVER_AB		  m5_API
    #define SOLVER_CORE       m5_API
	#define SOLVER_MUS		  m5_API
    #define SOLVER_BV         m5_API
#endif

/// Config: BACKEND_Z3
#ifdef BACKEND_Z3
	#define SOLVER_CTI		z3_API
	#define SOLVER_REACH	z3_API
	#define SOLVER_CONTAIN	z3_API
	#define SOLVER_AB		z3_API
    #define SOLVER_CORE     z3_API
	#define SOLVER_MUS		z3_API
	#define SOLVER_BV		z3_API
#endif

#define MICRO_ALARM

	/// Query Timeouts
#ifndef MICRO_ALARM
	#define AB_QUERY_TIMEOUT 100			// in seconds
	#define BV_QUERY_TIMEOUT 500			// in seconds
#else
	#define AB_QUERY_TIMEOUT 10000000000			// in microseconds
	#define BV_QUERY_TIMEOUT 10000000000			// in microseconds
#endif

//#define RANDOM_SHUFFLE_CORE


#define REFRESH_FRAME_SOLVERS										// Reset a frame solver after a threshold
#define REFRESH_FRAMES_THRESHOLD		20

#define QUERY_PATH "/home/rock/ws/cpp/avr/smt_queries/"

//#define SMTCOMP
#ifdef SMTCOMP
  #define FLATTEN_QUERY
#endif

//#define DUMP_LONGEST_QUERY
#define FLATTEN_QUERY
#define SET_NAMES

//#define TRACE_SOLVER

/// Macros for a query to be SAT, UNSAT, T.O.
#define AVR_QSAT  1
#define AVR_QUSAT 0
#define AVR_QTO  -1

#define ONESHOT_SAT    	1
#define INC_SAT			2
#define MUS_SAT 		3
#define ONESHOT_UNSAT 	4
#define INC_UNSAT 		5
#define MUS_UNSAT 		6
#define TIME_TO 		7
#define ERROR     8
#define NO_ERROR     9

#define TIME_S(start_time)\
			getrusage( RUSAGE_SELF, &usage );\
			timeradd(&usage.ru_utime, &usage.ru_stime, &start_time);

/// dump accumulated (elapsed) runtime
#define TIME_E(start_time, end_time, result)\
			getrusage( RUSAGE_SELF, &usage );\
			timeradd(&usage.ru_utime, &usage.ru_stime, &end_time);\
			time_diff = Timevaldiff(&start_time, &end_time);\
			result += time_diff;

extern string _benchmark;

typedef std::string SMTBA;
typedef unsigned MarkBA;
typedef std::list<SMTBA> SMTBAL;
typedef std::list<MarkBA> MarkBAL;

struct ASSERT_LIST
{
	InstL assumptions;
	InstLL assertions;

	ASSERT_LIST()
	{

	}
	void clear(void)
	{
		assumptions.clear();
		assertions.clear();
	}
};

typedef enum {
	pre_to_next,
	next_to_pre,
	no_induct
} UnsatType;

enum {
  regular  = 0,
  cti      = 1,
  br       = 2,
  fp       = 3,
  mus_core = 4,
  mus_min  = 5,
  conc     = 6,
  mdl    = 7,
  prt    = 8,
};

static string qtype2str(int queryType) {
	switch(queryType) {
	case regular:
		return "reg";
	case cti:
		return "cti";
	case br:
		return "br-";
	case fp:
		return "fp-";
	case mus_core:
		return "mco";
	case mus_min:
		return "mmi";
	case conc:
		return "con";
	case mdl:
		return "mdl";
	case prt:
		return "prt";
	}
	return "???";
}

typedef enum {
		SMT_Z3, SMT_Yices2, SMT_MathSAT5, SMT_Boolector, SMT_MiniSAT
	} SolverType;

	//class TIME_BREAK {
//public:
//  unsigned int n;
//  unsigned int s;
//
//  long long time_sat;
//  long long time_unsat;
//
//  long long time_max_sat;
//  long long time_max_unsat;
//
//  TIME_BREAK() {
//    n = 0;
//    s = 0;
//    time_sat = 0;
//    time_unsat = 0;
//  }
//
//  capture_time(long long& t, unsigned m, bool sat) {
//    n++;
//    s += m;
//    switch
//    if (t > time_max)
//  }
//};

struct SOLVER_STAT {
		map< string, pair< long long, int> > s;
		int count;

		SOLVER_STAT() {
			count = 0;
		}

		inline void update(string& key, int value) {
			map< string, pair< long long, int> >::iterator mit = s.find(key);
			if (mit == s.end()) {
				s[key] = make_pair(value, value);
			}
			else {
				pair< long long, int >& p = (*mit).second;
				p.first += value;
				p.second = max(p.second, value);
			}
		}

		void print(ofstream& out, string prefix) {
			out << prefix << "count" << ":\t" << count << "\n";
			for (auto& v: s) {
				out << prefix << "avg-" << v.first << ":\t" << ((count != 0) ? ((double) v.second.first / count) : 0) << "\n";
			}
			for (auto& v: s) {
				out << prefix << "max-" << v.first << ":\t" << v.second.second << "\n";
			}
		}
};

class Solver {
public:
	static int numRefresh;
	int countRefresh;

	static unordered_map<string, Inst*> m_nameToInst;

	static map< string, mpz_class > solv_values;

	static long long incremental_count;

	unsigned m_ba_idx;

	static int num_scalls_sat;
	static int num_scalls_unsat;
	static int num_scalls_timeout;

	static int num_scalls_sat_fp;
	static int num_scalls_unsat_fp;
	static int num_scalls_sat_fp_non_accum;
	static int num_scalls_unsat_fp_non_accum;
	static int num_scalls_contained_fp_non_accum;

	static int num_ab_sat_oneshot;
	static int num_ab_unsat_oneshot;
	static int num_ab_sat_inc;
	static int num_ab_unsat_inc;
	static int num_ab_sat_mus;
	static int num_ab_unsat_mus;
	static int num_ab_timeout;

	static int num_bv_sat_oneshot;
	static int num_bv_unsat_oneshot;
	static int num_bv_sat_inc;
	static int num_bv_unsat_inc;
	static int num_bv_sat_mus;
	static int num_bv_unsat_mus;
	static int num_bv_timeout;

	static int num_ab_muses_calls;
	static int num_bv_muses_calls;
	static unsigned long long total_sz_ab_muses_input;
	static unsigned long long total_sz_bv_muses_input;
	static int max_sz_ab_muses_input;
	static int max_sz_bv_muses_input;

	static int total_itr_ab_muses_input;
	static int total_itr_bv_muses_input;

	static int num_ab_mus_core;
	static int num_bv_mus_core;
	static unsigned long long total_sz_ab_core;
	static unsigned long long total_sz_bv_core;
	static int max_sz_ab_core;
	static int max_sz_bv_core;

	static int num_ab_query;
	static int num_bv_query;
	static unsigned long long total_sz_ab_query;
	static unsigned long long total_sz_bv_query;
	static int max_sz_ab_query;
	static int max_sz_bv_query;

	static long long time_ab_sat_oneshot;
	static long long time_ab_unsat_oneshot;
	static long long time_ab_sat_inc;
	static long long time_ab_unsat_inc;
	static long long time_ab_sat_mus;
	static long long time_ab_unsat_mus;
	static long long time_ab_timeout;

	static long long time_bv_sat_oneshot;
	static long long time_bv_unsat_oneshot;
	static long long time_bv_sat_inc;
	static long long time_bv_unsat_inc;
	static long long time_bv_sat_mus;
	static long long time_bv_unsat_mus;
	static long long time_bv_timeout;

	static long long time_max_ab_query;
	static long long time_max_bv_query;
	static long long time_max_ab_mus_query;
	static long long time_max_bv_mus_query;

	static long long time_ccext;
	static long long time_tmp;

	static bool s_check_timed_out;

	static long long time_sat_core_muses_reach;
	static long long time_unsat_core_muses_reach;
  static long long time_sat_core2_muses_reach;
  static long long time_unsat_core2_muses_reach;
	static long long time_sat_min_muses_reach;
	static long long time_unsat_min_muses_reach;

	static long long time_max_sat_core_muses_reach;
	static long long time_max_unsat_core_muses_reach;
  static long long time_max_sat_core2_muses_reach;
  static long long time_max_unsat_core2_muses_reach;
	static long long time_max_sat_min_muses_reach;
	static long long time_max_unsat_min_muses_reach;

  static long long core1_size;

  static int num_scalls_sat_core2_muses_reach;
  static int num_scalls_unsat_core2_muses_reach;

  static map < string, SOLVER_STAT > g_solver_stats;

//	static TIME_BREAK time_min_muses_reach1;
//  static TIME_BREAK time_min_muses_reach2;
//  static TIME_BREAK time_min_muses_reach3;
//  static TIME_BREAK time_min_muses_reach4;
//  static TIME_BREAK time_min_muses_reach5;

	// Global counter for solver_id used in reusing constraints
	static unsigned st_solver_id;

	static void init_solver_id() {
		st_solver_id++;
	}
	void set_solver_id() {
		m_solver_id = st_solver_id;
	}
	unsigned get_solver_id() {
		return m_solver_id;
	}

	// converts a value into a string
	static std::string val_to_str(unsigned long long val, unsigned sz, bool reversed = true);
	// converts a string into a value
	static unsigned long long str_to_val(std::string s, bool reversed = true);
	// converts an array of (boolean) values into a string
	static std::string arr_to_str(int* val, unsigned sz);

  virtual void collect_solver_stats() = 0;

	virtual void debug() = 0;

	virtual SolverType fetch_solv_name(void) = 0;

	class TheoryMapper {
	public:
		typedef enum {
			BV_OP, EUF_OP, BV_EUF_OP, CLU_OP
		} OpType;
		typedef enum {
			BV_VAR, EUF_VAR, BOOL_VAR
		} VarType;
		typedef enum {
			QF_UF, QF_BV, QF_UFBV
		} LogicType;
		virtual OpType fetch_op(Inst* = NULL) = 0;
		virtual VarType fetch_var(Inst*) = 0;
		virtual LogicType fetch_logic(void) = 0;
		virtual string get_theory_name(void) = 0;
		virtual ~TheoryMapper() {
		}
	};

	// C'tor. Needs to know the theory mapper
	Solver(TheoryMapper* m, unsigned ba_idx, int type) :
		m_mapper(m), m_uf_apps(0), m_logic(""), m_ba_idx(ba_idx) {
		assert(m);
		num_of_terms = 0;
		num_of_bools = 0;
		m_query_sz = 0;
	  allow_all = false;
	  countRefresh = 0;
	  uType = no_induct;
		m_numpush = 0;
		m_numpop = 0;

		push_assert();

		init_solver_id();
		set_solver_id();

		if (m_mapper->fetch_logic() == TheoryMapper::QF_UF || m_mapper->fetch_logic() == TheoryMapper::QF_UFBV)
			m_abstract = true;
		else
			m_abstract = false;

#ifdef FLATTEN_QUERY
		allow_flatten = true;
#else
		if (m_abstract)
			allow_flatten = false;
		else
			allow_flatten = true;
#endif

		m_allow_ex_cc = m_abstract;
		if (Config::g_ab_interpret_excc <= LEVEL_EXCC_NONE)
			m_allow_ex_cc = false;

		set_vIdx();
		set_cIdx();

		queryType = type;

		switch(queryType) {
		case cti:
		case br:
		case mdl:
			need_model = true;
			break;
		default:
			need_model = false;
		}

		if (m_abstract)
			disable_flatten();
		enable_fallback();
		if (queryType == prt)
			disable_flatten();
		enable_cache_hard();
//		disable_cache_hard();
	}

	virtual void set_logic(std::string l) {
		m_logic = l;
	}
	void set_command(std::string cmd) {
		m_cmd = cmd;
	}
	void set_vIdx(void) {
		switch(m_mapper->fetch_logic())
		{
		case TheoryMapper::QF_UF:   vIdx = UF_V; return;
		case TheoryMapper::QF_BV:   vIdx = BV_V; return;
		case TheoryMapper::QF_UFBV: vIdx = UFBV_V; return;
		default: assert(0);
		}
	}
	void set_cIdx(void) {
		switch(m_mapper->fetch_logic())
		{
		case TheoryMapper::QF_UF:   cIdx = (m_allow_ex_cc ? UF_C : UF_C_WO_EX_CC); return;
		case TheoryMapper::QF_BV:   cIdx = BV_C; return;
		case TheoryMapper::QF_UFBV: cIdx = UFBV_C; return;
		default: assert(0);
		}
	}
	int get_vIdx(void) {	return vIdx;	}
	int get_cIdx(void) {	return cIdx;	}

#ifdef TEST_CONNECT_BV
  int  get_connectIdx(void) { return CONNECT_V;  }
#endif

/// Virtual functions
	// Check SAT of the given expression
	virtual bool check_sat(Inst* e, long timeout_value, bool getModel) = 0;

	virtual int forward_propagation(long timeout_value, int frame_idx, InstL& forwarded,
			vector<vector<CLAUSE>>& cubes, void *inst) = 0;

	virtual int get_muses(long timeout_value, InstL& vel_1, InstL& vel_2, InstLL& muses, int& numSat, int& numUnsat, Solver* core_solver) = 0;
	virtual int get_muses_2(long timeout_value, InstL& vel, InstLL& muses, int& numSat, int& numUnsat, Solver* core_solver) = 0;
	virtual void minimize_core(long timeout_value, InstL& vel, InstLL& muses, int& numSat, int& numUnsat, bool recordTime = false) = 0;
  virtual int find_unsat_core(long timeout_value, InstL& hardQ, InstL& vel, InstL& mus, int& numSat, int& numUnsat) = 0;

	/// Should be only called when input core is UNSAT
	virtual int get_unsat_core(long timeout_value, InstL& vel, InstL& core, int& numSat, int& numUnsat) = 0;

	virtual bool s_assert(Inst* e) = 0;
	virtual bool s_assert(InstL& vel) = 0;
	virtual bool s_assert_retractable(InstL vel) = 0;
	virtual bool s_assert_retractable(Inst* tve) = 0;
	virtual bool s_retract_all_assertions() = 0;
	virtual bool s_retract_assertions() = 0;

	virtual int s_check(long timeout_value, bool getModel = true) = 0;
	virtual int s_check_assume(long timeout_value, bool getModel = true) = 0;

	virtual bool get_relation(Inst* lhs, Inst* rhs, bool expected) = 0;

	// Get the assignment. Returns false if it's not available!
//	virtual bool get_assignment(Inst*, long long&) = 0;
	virtual bool get_assignment(Inst*, int& val) = 0;
	virtual bool get_assignment(Inst*, mpz_class* val) = 0;

	/// Dump query in SMT2 format
	/// time_diff is time taken by AVR (in seconds)
	virtual void print_smt2(string fname="", string header="") = 0;
	virtual void print_constraints(int loc = 15, int level = 0) = 0;
	virtual bool s_another_solution(void) = 0;

#ifdef ASSERT_DISTINCT_NUMBERS
	virtual void assert_distinct_constants(void) = 0;
#endif

	virtual ~Solver() {
	}

	void init_inst2yices()	{	Inst::init_visit();	}

	unsigned num_of_terms;
	unsigned num_of_bools;

	typedef std::list<unsigned> Ints;
	// type of a function: true/false for predicate/function (or boolean/term); the second argument is a list of sizes.
	// If there are no elements, then it's a bool/term. If there are a number of elements of size 0, then
	// that's the number of arguments to a UF/UP. If they are (all) non zero, these are the BV sizes.
	typedef std::pair<bool, Ints> VarType;
	typedef std::map<std::string, VarType> VarDefs;
	VarDefs get_var_defs() {
		return m_var_defs;
	}
	unsigned get_uf_apps() {
		return m_uf_apps;
	}

	void stop_ex_cc_interpret() {
		m_allow_ex_cc = false;
		set_cIdx();
	}

	void assert_all_wire_constraints(void)
	{
		allow_all = true;
	}
  bool allow_all_wires(void)
  {
    return allow_all;
  }

	/// Print asserted instances in m_assertList
	void print_asserts(string comment = "", int loc = 15, int level = 0);
	void add_assert(Inst* e);
	void add_assume(Inst* e);
	void add_assume_front(Inst* e);
	void push_assert(void);
	void pop_assert(void);
	void clear_assume(void);
	void pop_assume(void);
	void copy_asserts(ASSERT_LIST& in);

  void print_query(long long time_diff, int mode, string suffix);

  void enable_fallback(void) {
    allow_fallback = true;
  }
  void disable_fallback(void) {
    allow_fallback = false;
  }

  void enable_induct_pn() {
    uType = pre_to_next;
  }
  void enable_induct_np() {
    uType = next_to_pre;
  }
  void disable_induct() {
    uType = no_induct;
  }

  void enable_flatten() {
    allow_flatten = true;
  }
  void disable_flatten() {
    allow_flatten = false;
  }

	ASSERT_LIST m_asserts;
  int queryType;
  int queryTypeStore;

#ifdef TRACE_SOLVER
	virtual void process_trace(ofstream& f) = 0;
  void print_trace(string suffix = "", bool iscore = false);

	list< string > m_trace;
#endif

  bool need_model;

  void enable_cache_hard() {
  	m_cache_hard = true;
  }
  void disable_cache_hard() {
  	m_cache_hard = false;
  }

  bool m_cache_hard;
	bool m_allow_ex_cc;

protected:

	bool m_abstract;

	int m_numpush;
	int m_numpop;

	/// Variable to decide whether automatically assert all internal wire constaints as well or not
	bool allow_all;

	bool allow_flatten;			// flatten expressions or not

	unsigned m_query_sz;

	/// Aman
	//	Below constructs added to enable reusing of constraints among different solver calls
	//
	// solver_id uniquely allotted with every SolverAPI constructor call
	// This is attached to stored constraints within object instances and matched before reusing
	unsigned m_solver_id;

  bool allow_fallback;

	TheoryMapper* m_mapper;

	UnsatType uType;

  void copy_induct(UnsatType u) {
    uType = u;
  }

  void copy_attributes(Solver* s) {
    uType = s->uType;
    allow_all = s->allow_all;
    allow_fallback = s->allow_fallback;
  }


	std::string clean_str(std::string);
	void add_func(std::string var, std::string op, bool interpreted, bool predicate, SMTBAL& ch, Ints& sz);
	void add_bvop(std::string var, std::string op, bool convert, SMTBAL&ch, unsigned sz);
	void add_var(std::string var, bool predicate, unsigned bv_size = 0);
	void add_const(std::string var, unsigned long long val, unsigned sz);

	void update_query_sz(void);
	void collect_stats_mus(unsigned sz);
	void collect_stats_muses(unsigned sz);
	void collect_stats_query(long long time_diff, int mode);
	void update_query_time(double time_diff, int mode);

	typedef std::list<std::string> LetDefs;
	LetDefs m_smt_defs;
	VarDefs m_var_defs;
	unsigned m_uf_apps;
	typedef std::set<std::string> SS;
	SS m_consts;
	std::string m_logic;
	std::string m_cmd;

private:
	int vIdx;
	int cIdx;
};

typedef enum {
	sat, unsat, timeout
} SatRes;

#endif /* AVERROES_FLOW_BACKEND_H_ */
