/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


/*
 * reach_bt.h
 *
 *  Created on: Jul 23, 2019
 *      Author: amangoel
 */

#ifndef SRC_REACH_REACH_BT_H_
#define SRC_REACH_REACH_BT_H_

/// Boolector Backend

#include "reach_backend.h"

#ifdef _BT

namespace _bt {

typedef std::map<std::string, bt_expr_ptr> bt_StringToDecl;
typedef std::map<pair<Inst*, string>, bt_expr_ptr, compare_pair_string> bt_InstToFuncDecl;
typedef std::map<std::string, bt_ftype_ptr> bt_StringToFunctM;
typedef std::map< pair<unsigned, SORT>, bt_type_ptr> bt_IntBvM;
typedef std::map< pair<unsigned, SORT>, bt_type_ptr> bt_IntUtM;
typedef std::map<mpz_class*, bt_expr_ptr> bt_MpzToNum;
typedef std::map<Inst*, pair<bt_expr, bt_expr>, compare> bt_InstToExprM;

class bt_API: public Solver {
public:
	static bt_StringToDecl m_var_decs;
	static bt_InstToFuncDecl m_func_decs;
	static bt_StringToFunctM m_funct;
	static bt_IntBvM m_sz_to_bv;
	static bt_IntUtM m_sz_to_ut;
	static bt_MpzToNum m_num_to_const;
#ifdef ASSERT_DISTINCT_NUMBERS
	static pair < int, bt_expr_vec > m_distinct_constraints;
#endif

	static bt_expr_ptr m_b0, m_b1;	    // zero and one, Bool type
	static bt_context g_ctx;
	static FILE* g_fd;

	static void bt_interrupt(int signum);
	static void bt_init();
	static void bt_exit();

	void bt_init_ctx();
	void bt_exit_ctx();

	bt_API(TheoryMapper* m, unsigned ba_idx, bool is_inc, int type);

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

	virtual ~bt_API();

	/// Dump query in SMT2 format
	/// time_diff is time taken by AVR (in seconds)
	virtual void print_smt2(string fname="", string header="");

#ifdef ASSERT_DISTINCT_NUMBERS
	virtual void assert_distinct_constants(void);
#endif

	virtual void print_constraints(int loc = 15, int level = 0);

	virtual bool s_another_solution(void);

	int get_mus(long timeout_value, InstL& vel_2, InstL& mus, int& numSat, int& numUnsat, bool recordTime);

	void print_expression(InstL& vel, FILE* out);
	void print_expression(Inst* tve, FILE* out) {
		InstL vel;
		vel.push_back(tve);
		print_expression(vel, out);
	}

	static list< pair<Inst*, bt_expr_ptr> > g_gateList;

protected:
	list< pair<Inst*, bt_expr_ptr> > m_gateList;

	bt_expr_vec m_constraints;
	bt_expr_vec m_assertions;
	bt_expr_vec m_assertions_retract;
	bt_expr_vec m_assumptions;
	list< pair<int, bt_expr_vec> > m_cList;
  bt_expr_vec m_unsatCore;
	bt_InstToExprM m_inst_to_y;
  map<bt_expr, Inst*> m_y_to_inst;

	string get_bt_name(Inst*e);
	string get_bt_temp_name(Inst*e, int count);
	string get_logic_name();
	bt_type create_bv_sort(pair< unsigned, SORT > sz);
	bt_type create_int_sort(pair< unsigned, SORT > sz);

	bt_expr create_bv_var(std::string name, pair< unsigned, SORT > sz);
	bt_expr create_int_var(std::string name, pair< unsigned, SORT > sz);
	bt_expr create_bool_var(std::string name);

	void inst2yices(Inst*e, bool bvAllConstraints=false);

	void add_constraint(bt_expr_ptr y, std::string comment = "", Inst*e = 0, bool storeC = true);
	void add_force_constraint(bt_expr_ptr y, std::string comment = "", Inst*e = 0);
	void force(Inst* e);
	bt_expr force_wo_add(Inst* e);
	bt_expr_ptr en_implies(bt_expr_ptr ye);

	void add_yices_func(bt_expr& var, std::string op, bool pred, bt_expr_list& ch, Ints& sz, Inst* e);
	void s_assert_constraints(bt_expr_ptr indVar, bool reset = true);
	void s_assert_constraints(bool reset = true)
	{
		bt_expr_ptr tmp = BT_INVALID_EXPR;
		s_assert_constraints(tmp, reset);
	}
	int s_assert_constraint(bt_expr_ptr ye);

	bt_result s_check_mus(long timeout_value, bt_expr_vec& assumptions, bt_expr_vec& unsatCore, bool getModel = true);

	void get_value_bv(unsigned sz, bt_expr_ptr decl, string& sval);
	void get_value_int(unsigned sz, bt_expr_ptr decl, string& sval);
	void get_value_utt(unsigned sz, bt_expr_ptr decl, string& sval);
	void get_value(bool abstract, SORT& sort, bt_expr_ptr decl, string& sval);
	void get_value_arr(bool abstract, SORT& sort, bt_expr_ptr decl, string& sval);

private:
  bt_expr_ptr create_bt_number(NumInst* num);

};

#ifndef MICRO_ALARM
#define BT_SET_TIMEOUT													\
				g_ctx = m_ctx;													\
				s_check_timed_out = false;							\
				assert(0 == alarm(timeout_value));
#else
#define BT_SET_TIMEOUT(context)																			\
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

#define BT_CHECK_TIMEOUT																						\
	alarm(0);																													\
	if (s_check_timed_out == true) {																	\
		res = BOOLECTOR_UNKNOWN;																				\
	}


#define bt_loge(expr)		cout << "\t(error: " << expr << ')' << endl; \
													assert(0);

};

#endif


#endif /* SRC_REACH_REACH_BT_H_ */
