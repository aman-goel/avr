/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


#ifndef AVERROES_FLOW_Z3_H__
#define AVERROES_FLOW_Z3_H__

/// Z3 Backend
#include "reach_backend.h"

#ifdef _Z3

namespace _z3 {

//#define Z3_INTERPOLATION

#define Z3_MUS_M1			// MUS extraction with alternate way to assert assertions

//#define TEST_Z3

//#ifndef PERFORMANCE
//	#define SIMPLIFY_Z3_CONSTRAINTS
//#endif

//#define DISABLE_Z3_CORE

/// Z3 solver2_timeout (in millisec) parameter value
#define Z3_SOLVER2_TIMEOUT 1

#define SORT_PREFIX "utt"

typedef std::map<std::string, z3_expr_ptr> z3_StringToDecl;
typedef std::map<pair <Inst*, string>, z3_expr_ptr, compare_pair_string> z3_InstToFuncDecl;
typedef std::map<std::string, z3_ftype_ptr> z3_StringToFunctM;
typedef std::map< pair<unsigned, SORT>, z3_type_ptr> z3_IntBvM;
typedef std::map< pair<unsigned, SORT>, z3_type_ptr> z3_IntUtM;
typedef std::map<mpz_class*, z3_expr_ptr> z3_MpzToNum;

class z3_API: public Solver {
public:

	static z3_StringToDecl m_var_decs;
	static z3_InstToFuncDecl m_func_decs;
	static z3_StringToFunctM m_funct;
	static z3_IntBvM m_sz_to_bv;
	static z3_IntUtM m_sz_to_ut;
	static z3_MpzToNum m_num_to_const;

#ifdef ASSERT_DISTINCT_NUMBERS
	static pair < int, z3_expr_vec > m_distinct_constraints;
#endif

	////// Zero and one
	// BV type!
	static z3_expr_ptr m_v0, m_v1;
	// BOOL type!
	static z3_expr_ptr m_b0, m_b1;

	static z3_config  g_config;
	static z3_context g_ctx;
	static z3_param  g_param;

	/// Global set of Z3 expression pointers created
	static list < z3_expr_ptr > g_exps;
	static list < z3_type_ptr > g_typs;
	static list < z3_ftype_ptr > g_ftyps;

	static void add_ptr(z3_expr_ptr& ptr)
	{
//		cout << "adding: " << ptr << "\t" << *ptr << endl;
		g_exps.push_back(ptr);
	}
	static void add_ptr(z3_type_ptr& ptr)
	{
		g_typs.push_back(ptr);
	}
	static void add_ptr(z3_ftype_ptr& ptr)
	{
		g_ftyps.push_back(ptr);
	}

	static void delete_ptrs()
	{
		for (auto& p: g_exps)
			if (p) {
				try {
//					cout << "deleting: " << p << "\t" << *p << endl;
					delete p;
				} catch (z3::exception e) {
				}
			}
		g_exps.clear();
		for (auto& p: g_typs)
			if (p)
				delete p;
		g_typs.clear();
		for (auto& p: g_ftyps)
			if (p)
				delete p;
		g_ftyps.clear();
	}

	static void z3_init();
	static void z3_exit();
	static void z3_interrupt(int signum);

	// Needs to know the index of the back-annotation that this solver is allowed to work with!
	z3_API(TheoryMapper* m, unsigned ba_idx, bool is_inc, int type);
	z3_API(TheoryMapper* m);

	virtual void debug();

  virtual void collect_solver_stats() {	};

	virtual SolverType fetch_solv_name(void);
	virtual bool check_sat(Inst* e, long timeout_value, bool getModel);
	virtual int forward_propagation(long timeout_value, int frame_idx, InstL& forwarded,
			vector<vector<CLAUSE>>& cubes, void *inst);

	virtual int get_muses(long timeout_value, InstL& vel_1, InstL& vel_2, InstLL& muses, int& numSat, int& numUnsat, Solver* core_solver);
	virtual int get_muses_2(long timeout_value, InstL& vel, InstLL& muses, int& numSat, int& numUnsat, Solver* core_solver);
	virtual int get_unsat_core(long timeout_value, InstL& vel, InstL& core, int& numSat, int& numUnsat);
	virtual void minimize_core(long timeout_value, InstL& vel, InstLL& muses, int& numSat, int& numUnsat, bool recordTime = false);
  virtual int find_unsat_core(long timeout_value, InstL& hardQ, InstL& vel, InstL& mus, int& numSat, int& numUnsat);

	virtual bool s_assert(Inst* e);
	virtual bool s_assert(InstL& vel);
	virtual bool s_assert_retractable(InstL vel);
	virtual bool s_assert_retractable(Inst* tve)
	{
		InstL vel;
		vel.push_back(tve);
		return s_assert_retractable(vel);
	}
	virtual bool s_retract_all_assertions();
	virtual bool s_retract_assertions();

	virtual int s_check(long timeout_value, bool getModel = true);
	virtual int s_check_assume(long timeout_value, bool getModel = true);

	virtual bool get_relation(Inst* lhs, Inst* rhs, bool expected);

	virtual bool get_assignment(Inst*, int& val);
	virtual bool get_assignment(Inst*, mpz_class* val);

	void get_value_bv(unsigned sz, z3_expr_ptr decl, string& sval);
	void get_value_int(unsigned sz, z3_expr_ptr decl, string& sval);
	void get_value_utt(unsigned sz, z3_expr_ptr decl, string& sval);
	void get_value(bool abstract, SORT& sort, z3_expr_ptr decl, string& sval);
	void get_value_arr(bool abstract, SORT& sort, z3_expr_ptr decl, string& sval);

	/// Dump query in SMT2 format
	/// time_diff is time taken by AVR (in seconds)
	virtual void print_smt2(string fname="", string header="");
	virtual void print_constraints(int loc = 15, int level = 0);
	virtual bool s_another_solution(void);

#ifdef ASSERT_DISTINCT_NUMBERS
  virtual void assert_distinct_constants(z3_solver& solver);
	void assert_distinct_constants(void) {
	  assert_distinct_constants(m_solver);
	}
#endif

	int check_half(int start, int size, std::unordered_map<string, string>& indVarHash, long timeout_value, z3_solver& ni_solver, vector < pair <Inst*, string> >& instCore, int& numSat, int& numUnsat, bool recordTime);
	int check_linear(std::unordered_map<string, string>& indVarHash, long timeout_value, z3_solver& ni_solver, vector < pair <Inst*, string> >& instCore, int& numSat, int& numUnsat, bool recordTime);
	z3_result find_mus(std::unordered_map<string, string>& indVarHash, long timeout_value, z3_solver& ni_solver, vector < pair <Inst*, string> >& instCore, InstL& mus, int& numSat, int& numUnsat, bool recordTime);

	int get_mus(long utimeout_value, InstL& vel_2, InstL& mus, int& numSat, int& numUnsat, bool recordTime);
	int get_mus_avr(long timeout_value, InstL& vel_2, InstL& mus, int& numSat, int& numUnsat, bool recordTime);

//	int identify_dont_cares(long utimeout_value, InstL& mus, int& numSat, int& numUnsat);

	bool s_check_model(bool allowDontCares=false);
	z3_result shift_to_noninc(long timeout_value, long long time_diff, bool getModel);

	z3_result s_check_mus(z3_solver& solver, long timeout_value, z3_expr_vector& assumptions, bool getModel = true);
	z3_result s_check_inc(z3_solver& solver, long timeout_value, bool getModel = true);
	z3_result s_check_oneshot(long timeout_value, bool getModel = true);

	void s_assert_constraints(z3_solver& solver, bool reset = true, z3_expr_ptr indVar = NULL);
	void s_assert_constraints(bool reset = true, z3_expr_ptr indVar = NULL)
	{
		s_assert_constraints(m_solver, reset, indVar);
	}

	void s_assert_constraint(z3_solver& solver, z3_expr_ptr ye, z3_expr_ptr indVar = NULL);
	void s_assert_constraint(z3_expr_ptr ye, z3_expr_ptr indVar = NULL)
	{
		s_assert_constraint(m_solver, ye, indVar);
	}
	void s_assert_constraints_inc(z3_solver& solver, vector < z3_expr_ptr >& assumptions);

	void s_assert_constraints_mus(z3_solver& solver, z3_expr_ptr indVar);
	void s_assert_constraint_mus(z3_solver& solver, z3_expr_ptr ye);
	void s_assert_constraints_mus(z3_solver& solver, z3_expr_vector& stack);

	void s_push(z3_solver& solver, bool fake = false);
	void s_push(bool fake = false)
	{
		s_push(m_solver, fake);
	}
	void s_pop(z3_solver& solver, bool fake = false);
	void s_pop(bool fake = false)
	{
		s_pop(m_solver, fake);
	}

	void s_change_timeout(unsigned to, z3_solver solver);
	void s_change_timeout(unsigned to)
	{
		s_change_timeout(to, m_solver);
	}

	void s_print_model(void);

	virtual ~z3_API();

	std::string get_z3_name(Inst*e);
	std::string get_z3_temp_name(Inst*e, int count);

	z3_expr_ptr create_z3_number(NumInst* num);

#ifdef Z3_INTERPOLATION
	int get_interpolant(long timeout_value, InstL& velA, InstL& velB, InstL& interpolant, int& numSat, int& numUnsat);
#endif

	z3_context m_ctx;
	z3_param   m_param;
	z3_solver  m_solver;
	z3_model   m_model;

	/// Solver used for current query
	z3_solver  q_solver;

	/// Flag true if solver is incremental
	bool is_i;

	/// Utility functions
	///
	/// Print constraints in m_cList
	void print_constraints(string comment, int loc=15, int level=0)
	{
		AVR_LOG(loc, level, "(" << comment << ")" << endl);
		print_constraints(loc, level);
	}

	z3_expr_vector& get_assumptions()
	{
		return (*m_assumptions);
	}

#ifdef TEST_Z3
	void shift_to_tactic_solver(void)	{	shift_to_tactic_solver(m_solver);	}
	void shift_to_tactic_solver(z3_solver& solver);
#endif

#ifdef TRACE_SOLVER
	virtual void process_trace(ofstream& f) {}
#endif

protected:

	// Timeout to shift to non-incremental solver in Z3 (in microseconds)
	static unsigned int query_timeout_ab;
	static unsigned int query_timeout_bv;
	static unsigned int query_timeout_core_ab;
	static unsigned int query_timeout_core_bv;

	z3_expr_vec m_constraints;

	z3_expr_vector* m_assumptions;
  z3_expr_vector* q_assumptions;

	list< pair<int, z3_expr_vec> > m_cList;

	void set_logic(void);
	void set_logic(z3_solver& zsolver);
	void set_logic_core(z3_solver& zsolver, z3_param param);

	void inst2yices(Inst*e, bool bvAllConstraints=false);
	void inst2z3(Inst*e, bool bvAllConstraints=false);


//	/// Obsolete
//	void getConstraints(Inst*e);
//	void singleInst2yices(solv_solver& solver, Inst*e, int& count, map<string, pair <Inst*, bool> >& indVar2exprFull, solv_expr_vector& assumptions, bool isTop);

	void add_constraint(z3_expr_ptr y, std::string comment = "", Inst*e = 0, bool storeC = true);
	void force(Inst* e);
	z3_expr_ptr force_wo_add(Inst* e);

	z3_type_ptr create_bv_sort(pair< unsigned, SORT > sz);
	z3_type_ptr create_int_sort(pair< unsigned, SORT > sz);

	z3_expr_ptr create_bv_var(std::string name, pair< unsigned, SORT > sz);
	z3_expr_ptr create_int_var(std::string name, pair< unsigned, SORT > sz);
	z3_expr_ptr create_bool_var(std::string name);

	void add_yices_func(z3_expr_ptr& var, std::string op, bool pred, z3_expr_list& ch, Ints& sz, Inst* e);

	void print_timeout_query(string fname, long long time_res);

private:

};

};

#ifndef MICRO_ALARM
#define Z3_SET_TIMEOUT																			\
				s_check_timed_out = false;													\
				assert(0 == alarm(timeout_value));
#else
#define Z3_SET_TIMEOUT																							\
	s_check_timed_out = false;																				\
	{																																	\
		struct itimerval t;																							\
		t.it_interval.tv_usec = 0;																			\
		t.it_interval.tv_sec = 0;																				\
		t.it_value.tv_usec = (__suseconds_t) timeout_value % 1000000;		\
		t.it_value.tv_sec  = (__time_t)      timeout_value / 1000000;		\
		assert (0 == setitimer (ITIMER_REAL, &t, NULL));								\
	}
#endif

#define Z3_CHECK_TIMEOUT																						\
			alarm(0);																											\
			if (s_check_timed_out == true) {															\
				cout << "AVR_Timeout, t:" << timeout_value << endl; 				\
				res = z3::unknown;																					\
			}
#define Z3_CHECK_TIMEOUT_OS																					\
			alarm(0);																											\
			if (s_check_timed_out == true) {															\
		    print_query(time_res, TIME_TO, "to");      									\
				cout << "AVR_Timeout, t:" << timeout_value << endl; 				\
				res = z3::unknown;																					\
			}


#endif

#endif
