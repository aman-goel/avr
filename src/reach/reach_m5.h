/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


/*
 * reach_m5.h
 *
 *  Created on: Feb 11, 2019
 *      Author: rock
 */

#ifndef SRC_REACH_REACH_M5_H_
#define SRC_REACH_REACH_M5_H_


/// MathSAT 5 Backend

#include "reach_backend.h"

#ifdef _M5

// equality predicates and hash functions for msat_termS
inline bool operator==(msat_term a, msat_term b) {
    return msat_term_id(a) == msat_term_id(b);
}
inline bool operator!=(msat_term a, msat_term b) {
    return !(a == b);
}
inline bool operator<(msat_term a, msat_term b) {
    return msat_term_id(a) < msat_term_id(b);
}
namespace std {
template<>
struct hash<::msat_term> {
    size_t operator()(::msat_term t) const { return msat_term_id(t); }
};
}

namespace _m5 {

#define M5_INTERPOLATION

typedef std::map<std::string, m5_expr_ptr> m5_StringToDecl;
typedef std::map<pair<Inst*, string>, m5_expr_ptr, compare_pair_string> m5_InstToFuncDecl;
typedef std::map<std::string, m5_ftype_ptr> m5_StringToFunctM;
typedef std::map< pair<unsigned, SORT>, m5_type_ptr> m5_IntBvM;
typedef std::map< pair<unsigned, SORT>, m5_type_ptr> m5_IntUtM;
typedef std::map<mpz_class*, m5_expr_ptr> m5_MpzToNum;
typedef std::map<Inst*, pair<m5_expr, m5_expr>, compare> m5_InstToExprM;
typedef std::set<msat_term> TermSet;

class m5_API: public Solver {
public:
	static m5_StringToDecl m_var_decs;
	static m5_InstToFuncDecl m_func_decs;
	static m5_StringToFunctM m_funct;
	static m5_IntBvM m_sz_to_bv;
	static m5_IntUtM m_sz_to_ut;
	static m5_MpzToNum m_num_to_const;
#ifdef ASSERT_DISTINCT_NUMBERS
	static pair < int, m5_expr_vec > m_distinct_constraints;
#endif
	static m5_expr_ptr m_v0, m_v1;	    // Zero and one, BV type
	static m5_expr_ptr m_b0, m_b1;	    // zero and one, Bool type

	static m5_config	g_config;
	static m5_context g_ctx;

	static m5_type_ptr g_ufboolt;
	static m5_expr_ptr g_uftrue, g_uffalse;
	static bool g_setufbool;

	m5_config	m_config;
	m5_context m_ctx;

	static void m5_interrupt(int signum);
	static void m5_init();
	static void m5_exit();

	static void m5_set_bool_uf();

	void m5_init_ctx();
	void m5_exit_ctx();

	m5_API(TheoryMapper* m, unsigned ba_idx, bool is_inc, int type);

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

	virtual ~m5_API();

	/// Dump query in SMT2 format
	/// time_diff is time taken by AVR (in seconds)
	virtual void print_smt2(string fname="", string header="");

#ifdef ASSERT_DISTINCT_NUMBERS
	virtual void assert_distinct_constants(void);
#endif

	virtual void print_constraints(int loc = 15, int level = 0);

	virtual bool s_another_solution(void);

	int get_mus(long timeout_value, InstL& vel_2, InstL& mus, int& numSat, int& numUnsat, bool recordTime);
	int get_interpolant(long timeout_value, InstL& velA, InstL& velB, InstL& new_preds, int& numSat, int& numUnsat);
	void get_predicates(msat_term t, TermSet &out, bool minimize = true);
	void extract_predicates(TermSet &in, InstL& out, bool minimize = true);
	string print_name(Inst* e);
	void print_expression(InstL& vel, ofstream& out);
	void print_expression(Inst* tve, ofstream& out) {
		InstL vel;
		vel.push_back(tve);
		print_expression(vel, out);
	}
	Inst* read_expression(ifstream& in);

protected:
	m5_model_ptr m_model;
	m5_expr_vec m_constraints;
	m5_expr_vec m_assumptions;
	list< pair<int, m5_expr_vec> > m_cList;
  m5_expr_vec m_unsatCore;
	m5_InstToExprM m_inst_to_y;
  map<m5_expr, Inst*> m_y_to_inst;

	string get_m5_name(Inst*e);
	string get_m5_temp_name(Inst*e, int count);
	string get_logic_name();
	m5_type create_bv_sort(pair< unsigned, SORT > sz);
	m5_type create_int_sort(pair< unsigned, SORT > sz);

	m5_expr create_bv_var(std::string name, pair< unsigned, SORT > sz);
	m5_expr create_int_var(std::string name, pair< unsigned, SORT > sz);
	m5_expr create_bool_var(std::string name);

	void inst2yices(Inst*e, bool bvAllConstraints=false);

	void add_constraint(m5_expr_ptr y, std::string comment = "", Inst*e = 0, bool storeC = true);
	void force(Inst* e);
	m5_expr force_wo_add(Inst* e);

	void add_yices_func(m5_expr& var, std::string op, bool pred, m5_expr_list& ch, Ints& sz, Inst* e);
	void s_assert_constraints(m5_expr_ptr indVar, bool reset = true);
	void s_assert_constraints(bool reset = true)
	{
		m5_expr_ptr tmp;
		MSAT_MAKE_ERROR_TERM(tmp);
		s_assert_constraints(tmp, reset);
	}
	int s_assert_constraint(m5_expr_ptr ye);

	m5_result s_check_inc(long timeout_value, bool getModel = true);
	m5_result s_check_mus(long timeout_value, m5_expr_vec& assumptions, m5_expr_vec& unsatCore, bool getModel = true);
  int32_t s_push(void);
	int32_t s_pop(void);

	void get_value_bv(unsigned sz, m5_expr_ptr decl, string& sval);
	void get_value_int(unsigned sz, m5_expr_ptr decl, string& sval);
	void get_value_utt(unsigned sz, m5_expr_ptr decl, string& sval);
	void get_value(bool abstract, SORT& sort, m5_expr_ptr decl, string& sval);
	void get_value_arr(bool abstract, SORT& sort, m5_expr_ptr decl, string& sval);

private:
  m5_expr_ptr create_m5_number(NumInst* num);

};

#ifndef MICRO_ALARM
#define M5_SET_TIMEOUT													\
				g_ctx = m_ctx;													\
				s_check_timed_out = false;							\
				assert(0 == alarm(timeout_value));
#else
#define M5_SET_TIMEOUT(context)																			\
	s_check_timed_out = false;																				\
	alarm(0);																													\
	{																																	\
		struct itimerval t;																							\
		t.it_interval.tv_usec = 0;																			\
		t.it_interval.tv_sec = 0;																				\
		t.it_value.tv_usec = (__suseconds_t) timeout_value % 1000000;		\
		t.it_value.tv_sec  = (__time_t)      timeout_value / 1000000;		\
		assert (0 == setitimer (ITIMER_REAL, &t, NULL));								\
	}
#endif

#define M5_CHECK_TIMEOUT																						\
	alarm(0);																													\
	if (s_check_timed_out == true) {																	\
		res = MSAT_UNKNOWN;																				\
	}


#define m5_logvv(expr)	cout << expr;
#define m5_logv(expr)		cout << expr;
#define m5_log(expr)		cout << expr;
#define m5_logw(expr)		cout << "\t(warning: " << expr << ')' << endl;
#define m5_logwv(expr)	cout << "\t(warning: " << expr << ')' << endl;
#define m5_loge(expr)		cout << "\t(error: " << expr << ')' << endl; \
													assert(0);

};

#endif

#endif /* SRC_REACH_REACH_M5_H_ */
