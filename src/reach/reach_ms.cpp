/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


/*
 * reach_ms.cpp
 *
 *  Created on: Jan 13, 2020
 *      Author: rock
 */

#include "reach_ms.h"

#ifdef _MS

using namespace std;

namespace _ms {

#define MS_TODO			assert(0 && "(ms: todo)");


static inline sat_solver* manNewSolver2(sat_solver * pSat, int k, int fInit) {
    assert( pSat );

    abctime     timeToStop;
    int runId;            // PDR id in this run
    int(*pFuncStop)(int); // callback to terminate

    // start the SAT solver
//    pSat = sat_solver_new();
    sat_solver_setnvars( pSat, 500 );
    sat_solver_set_runtime_limit( pSat, timeToStop );
    sat_solver_set_runid( pSat, runId );
    sat_solver_set_stop_func( pSat, pFuncStop );
    return pSat;
}

sat_solver * createSolver(int k, int seed) {
    sat_solver * pSat;
    // create new solver
//    pSat = sat_solver_new();
    pSat = zsat_solver_new_seed(seed);
    pSat = manNewSolver2( pSat, k, (int)(k == 0) );
    return pSat;
}


void ms_API::debug() {
	MS_TODO
}

SolverType ms_API::fetch_solv_name(void) {
	return SMT_MiniSAT;
}

void ms_API::ms_interrupt(int signum) {
	s_check_timed_out = true;
}

void ms_API::ms_init() {
	ms_log("Initializing MiniSAT");
  sat_solver* s = createSolver( 0, 0);
}

void ms_API::ms_exit() {
	ms_log("Exiting MiniSAT");
}

void ms_API::ms_exit_ctx() {
	MS_TODO
}

void ms_API::ms_init_ctx() {
	MS_TODO
}

ms_API::ms_API(TheoryMapper* m, unsigned ba_idx, bool is_inc, int type) :
			Solver(m, ba_idx, type) {
	assert(m);

	AVR_LOG(11, 1, "Creating new MS instance for BA[" << m_ba_idx << "] with solver_id [" << m_solver_id << "]" << endl);

  MS_TODO
}

ms_API::~ms_API() {
	AVR_LOG(11, 1, "Deleting M5 instance for BA[" << m_ba_idx << "] with solver_id [" << m_solver_id << "]" << endl);
	MS_TODO
}

bool ms_API::check_sat(Inst* e, long timeout_value, bool getModel) {
	MS_TODO
}

int ms_API::forward_propagation(long timeout_value, int frame_idx, InstL& forwarded,
			vector<vector<CLAUSE>>& cubes, void *inst) {
	MS_TODO
}

int ms_API::get_muses(long timeout_value, InstL& vel_1, InstL& vel_2, InstLL& muses, int& numSat, int& numUnsat, Solver* core_solver) {
	MS_TODO
}

int ms_API::get_muses_2(long timeout_value, InstL& vel, InstLL& muses, int& numSat, int& numUnsat, Solver* core_solver) {
	MS_TODO
}

int ms_API::get_unsat_core(long timeout_value, InstL& vel, InstL& core, int& numSat, int& numUnsat) {
	MS_TODO
}

int ms_API::find_unsat_core(long timeout_value, InstL& hardQ, InstL& vel, InstL& mus, int& numSat, int& numUnsat) {
	MS_TODO
}

void ms_API::minimize_core(long timeout_value, InstL& vel, InstLL& muses, int& numSat, int& numUnsat, bool recordTime) {
	MS_TODO
}

bool ms_API::s_assert(Inst* e) {
	MS_TODO
}

bool ms_API::s_assert(InstL& vel) {
	MS_TODO
}

bool ms_API::s_assert_retractable(InstL vel) {
	MS_TODO
}

bool ms_API::s_retract_assertions() {
	MS_TODO
}

bool ms_API::s_retract_all_assertions() {
	MS_TODO
}

int ms_API::s_check(long timeout_value, bool getModel) {
	MS_TODO
}

int ms_API::s_check_assume(long timeout_value, bool getModel) {
	MS_TODO
}

bool ms_API::get_relation(Inst* lhs, Inst* rhs, bool expected) {
	MS_TODO
}

bool ms_API::get_assignment(Inst* e, int& val) {
	MS_TODO
}

bool ms_API::get_assignment(Inst* e, mpz_class* val) {
	MS_TODO
}

void ms_API::print_smt2(string fname, string header) {
	MS_TODO
}

#ifdef ASSERT_DISTINCT_NUMBERS
void ms_API::assert_distinct_constants(void) {
	MS_TODO
}
#endif


void ms_API::print_constraints(int loc, int level) {
	MS_TODO
}

bool ms_API::s_another_solution(void) {
	MS_TODO
}


};

#endif





