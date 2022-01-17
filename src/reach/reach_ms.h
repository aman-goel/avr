/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


/*
 * reach_ms.h
 *
 *  Created on: Jan 13, 2020
 *      Author: rock
 */

#ifndef SRC_REACH_REACH_MS_H_
#define SRC_REACH_REACH_MS_H_


/// MiniSAT Backend

#include "reach_backend.h"

#ifdef _MS

namespace _ms {

class ms_API: public Solver {
public:
	static void ms_interrupt(int signum);
	static void ms_init();
	static void ms_exit();

	void ms_init_ctx();
	void ms_exit_ctx();

	ms_API(TheoryMapper* m, unsigned ba_idx, bool is_inc, int type);

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

	virtual ~ms_API();

	/// Dump query in SMT2 format
	/// time_diff is time taken by AVR (in seconds)
	virtual void print_smt2(string fname="", string header="");

#ifdef ASSERT_DISTINCT_NUMBERS
	virtual void assert_distinct_constants(void);
#endif

	virtual void print_constraints(int loc = 15, int level = 0);

	virtual bool s_another_solution(void);

protected:

private:

};


#define ms_loge(expr)		cout << "\t(error: " << expr << ')' << endl; \
													assert(0);
#define ms_logw(expr)		cout << "\t(warning: " << expr << ')' << endl;
#define ms_log(expr)		cout << "\t(ms: " << expr << ')' << endl;
#define ms_logv(expr)		//cout << "\t(ms: " << expr << ')' << endl;

};

#endif




#endif /* SRC_REACH_REACH_MS_H_ */
