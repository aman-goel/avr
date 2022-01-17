/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


#include "reach_y2.h"

#ifdef _Y2

#include <cstdlib>
#include <fstream>
#include <cmath>
#include <csignal>
#include <pthread.h>
#include <functional>

using namespace std;

namespace _y2 {

#ifdef Y2_EXP
y2_statistic y2_API::g_stat_cti;
y2_statistic y2_API::g_stat_br;
y2_statistic y2_API::g_stat_fp;
y2_statistic y2_API::g_stat_core;
y2_statistic y2_API::g_stat_min;
y2_statistic y2_API::g_stat_reg;
#endif

#ifdef Y2_RESET_FALLBACK_ONLY
int y2_API::g_soft_timeout = Y2_RESET_TIMEOUT_FALLBACK;
#else
int y2_API::g_soft_timeout = Y2_ABSTRACT_SOFT_TIMEOUT;
#endif

int y2_API::g_num_reset = 0;

map< int, y2_API* > y2_API::y2_solvers = map< int, y2_API* >();

y2_expr_list y2_API::conds;

y2_IntBvM y2_API::m_sz_to_bv;
y2_IntUtM y2_API::m_sz_to_ut;
y2_StringToFunctM y2_API::m_funct;

y2_StringToDecl y2_API::m_var_decs;
y2_InstToFuncDecl y2_API::m_func_decs;
y2_MpzToNum y2_API::m_num_to_const;

#ifdef ASSERT_DISTINCT_NUMBERS
	pair < int, y2_expr_vec > y2_API::m_distinct_constraints = make_pair(-1, y2_expr_vec());
#endif

y2_context	y2_API::g_ctx = NULL;

y2_expr_ptr y2_API::m_v0 = Y2_INVALID_EXPR;
y2_expr_ptr y2_API::m_v1 = Y2_INVALID_EXPR;

y2_expr_ptr y2_API::m_b0 = Y2_INVALID_EXPR;
y2_expr_ptr y2_API::m_b1 = Y2_INVALID_EXPR;

#ifdef Y2_SCALAR_BUCKETS
vector<unsigned> y2_API::sz_to_card = vector<unsigned>();
#endif

out_of_mem_callback_t y2_API::y2_out_of_memory_callback = NULL;


SolverType y2_API::fetch_solv_name(void)
{
	return SMT_Yices2;
}

void y2_API::y2_unset()
{
//	conds.clear();

	m_sz_to_bv.clear();
	m_sz_to_ut.clear();
	m_funct.clear();

	m_var_decs.clear();
	m_func_decs.clear();
	m_num_to_const.clear();

	m_distinct_constraints.second.clear();
	m_distinct_constraints = make_pair(-1, y2_expr_vec());

	g_ctx = NULL;

	m_v0 = Y2_INVALID_EXPR;
	m_v1 = Y2_INVALID_EXPR;

	m_b0 = Y2_INVALID_EXPR;
	m_b1 = Y2_INVALID_EXPR;
}

void y2_API::y2_set()
{
	Y2_INFO::inc_y2_key();

  yices_set_out_of_mem_callback(y2_API::y2_out_of_memory_callback);

	y2_API::m_v0 = yices_bvconst_zero(1);
	y2_API::m_v1 = yices_bvconst_one(1);

	y2_API::m_b0 = yices_false();
	y2_API::m_b1 = yices_true();

#ifdef Y2_SCALAR_BUCKETS
  sz_to_card.push_back(1);
	sz_to_card.push_back(2);
  sz_to_card.push_back(4);
  sz_to_card.push_back(8);
  sz_to_card.push_back(16);
  sz_to_card.push_back(32);
  sz_to_card.push_back(64);
#endif
}

void y2_API::y2_init()
{
	yices_init();    // Always call this first
	y2_set();

	_resFile << "y2-force-reset-limit:\t" << Y2_MAX_RESET_ALLOWED << endl;
#ifndef MICRO_ALARM
	_resFile << "y2-force-reset-timeout-sec:\t" << Y2_RESET_TIMEOUT << endl;
	_resFile << "y2-ab-soft-reset-timeout-sec:\t" << Y2_ABSTRACT_SOFT_TIMEOUT << endl;
#else
	_resFile << "y2-force-reset-timeout-sec:\t" << Y2_RESET_TIMEOUT / 1000000.0 << endl;
	_resFile << "y2-ab-soft-reset-timeout-sec:\t" << Y2_ABSTRACT_SOFT_TIMEOUT / 1000000.0 << endl;
#endif
}

void y2_API::y2_exit()
{

}

void y2_API::y2_reset()
{
	y2_unset();
	yices_reset();
	y2_set();
	Inst::init_visit();

#ifdef Y2_RESET_FALLBACK_ONLY
	g_soft_timeout = Y2_RESET_TIMEOUT_FALLBACK;
#else
	g_soft_timeout = Y2_ABSTRACT_SOFT_TIMEOUT;
#endif
}


void y2_API::y2_interrupt(int signum)
{
	if(g_ctx != NULL)
	{
		yices_stop_search(g_ctx);
		s_check_timed_out = true;
	}
}

#ifdef Y2_EXP
void y2_API::print_solv_statistic(ofstream& out, y2_statistic& stat, string comment)
{
	out << comment << "q-ab:\t" << stat.num_ab_q << endl;
	out << comment << "q-bv:\t" << stat.num_bv_q << endl;
	out << comment << "q-fail:\t" << stat.num_fail_q << endl;

  out << comment << "s-ab:\t" << stat.num_ab_end << endl;
  out << comment << "s-bv:\t" << stat.num_bv_end << endl;
  out << comment << "s-fail:\t" << stat.num_fail_end << endl;

/// Avg
  // AB
  out << comment << "q-time-ab-avg-boolean_propagation\t" << ((stat.num_ab_q != 0) ? (((double) stat.ab_sum.st.boolean_propagation) / stat.num_ab_q) / 1000.0 : 0) << endl;
  out << comment << "q-time-ab-avg-theory_propagation\t" << ((stat.num_ab_q != 0) ? (((double) stat.ab_sum.st.theory_propagation) / stat.num_ab_q) / 1000.0 : 0) << endl;
  out << comment << "q-time-ab-avg-resolve_conflict\t" << ((stat.num_ab_q != 0) ? (((double) stat.ab_sum.st.resolve_conflict) / stat.num_ab_q) / 1000.0 : 0) << endl;
  out << comment << "q-time-ab-avg-smt_restart\t" << ((stat.num_ab_q != 0) ? (((double) stat.ab_sum.st.smt_restart) / stat.num_ab_q) / 1000.0 : 0) << endl;
  out << comment << "q-time-ab-avg-select_unassigned_literal\t" << ((stat.num_ab_q != 0) ? (((double) stat.ab_sum.st.select_unassigned_literal) / stat.num_ab_q) / 1000.0 : 0) << endl;
  out << comment << "q-time-ab-avg-decide_literal\t" << ((stat.num_ab_q != 0) ? (((double) stat.ab_sum.st.decide_literal) / stat.num_ab_q) / 1000.0 : 0) << endl;
  out << comment << "q-time-ab-avg-add_all_lemmas\t" << ((stat.num_ab_q != 0) ? (((double) stat.ab_sum.st.add_all_lemmas) / stat.num_ab_q) / 1000.0 : 0) << endl;
  out << comment << "q-time-ab-avg-delete_irrelevant_variables\t" << ((stat.num_ab_q != 0) ? (((double) stat.ab_sum.st.delete_irrelevant_variables) / stat.num_ab_q) / 1000.0 : 0) << endl;
  out << comment << "q-time-ab-avg-simplify_clause_database\t" << ((stat.num_ab_q != 0) ? (((double) stat.ab_sum.st.simplify_clause_database) / stat.num_ab_q) / 1000.0 : 0) << endl;
  out << comment << "q-time-ab-avg-reduce_clause_database\t" << ((stat.num_ab_q != 0) ? (((double) stat.ab_sum.st.reduce_clause_database) / stat.num_ab_q) / 1000.0 : 0) << endl;

  out << comment << "q-time-ab-avg-eg-propagate\t" << ((stat.num_ab_q != 0) ? (((double) stat.ab_sum.st.propagate) / stat.num_ab_q) / 1000.0 : 0) << endl;
  out << comment << "q-time-ab-avg-eg-internal_propagation\t" << ((stat.num_ab_q != 0) ? (((double) stat.ab_sum.st.internal_propagation) / stat.num_ab_q) / 1000.0 : 0) << endl;
  out << comment << "q-time-ab-avg-eg-reactivate_dynamic_terms\t" << ((stat.num_ab_q != 0) ? (((double) stat.ab_sum.st.reactivate_dynamic_terms) / stat.num_ab_q) / 1000.0 : 0) << endl;
  out << comment << "q-time-ab-avg-eg-process_equality\t" << ((stat.num_ab_q != 0) ? (((double) stat.ab_sum.st.process_equality) / stat.num_ab_q) / 1000.0 : 0) << endl;
  out << comment << "q-time-ab-avg-eg-inconsistent_edge\t" << ((stat.num_ab_q != 0) ? (((double) stat.ab_sum.st.inconsistent_edge) / stat.num_ab_q) / 1000.0 : 0) << endl;
  out << comment << "q-time-ab-avg-eg-invert_branch\t" << ((stat.num_ab_q != 0) ? (((double) stat.ab_sum.st.invert_branch) / stat.num_ab_q) / 1000.0 : 0) << endl;
  out << comment << "q-time-ab-avg-eg-remove_parents\t" << ((stat.num_ab_q != 0) ? (((double) stat.ab_sum.st.remove_parents) / stat.num_ab_q) / 1000.0 : 0) << endl;
  out << comment << "q-time-ab-avg-eg-assign_new_label\t" << ((stat.num_ab_q != 0) ? (((double) stat.ab_sum.st.assign_new_label) / stat.num_ab_q) / 1000.0 : 0) << endl;
  out << comment << "q-time-ab-avg-eg-collect_eqterms\t" << ((stat.num_ab_q != 0) ? (((double) stat.ab_sum.st.collect_eqterms) / stat.num_ab_q) / 1000.0 : 0) << endl;
  out << comment << "q-time-ab-avg-eg-reprocess_parents\t" << ((stat.num_ab_q != 0) ? (((double) stat.ab_sum.st.reprocess_parents) / stat.num_ab_q) / 1000.0 : 0) << endl;
  out << comment << "q-time-ab-avg-eg-check_false_eq\t" << ((stat.num_ab_q != 0) ? (((double) stat.ab_sum.st.check_false_eq) / stat.num_ab_q) / 1000.0 : 0) << endl;
  out << comment << "q-time-ab-avg-eg-atom_propagation\t" << ((stat.num_ab_q != 0) ? (((double) stat.ab_sum.st.atom_propagation) / stat.num_ab_q) / 1000.0 : 0) << endl;
  out << comment << "q-time-ab-avg-eg-propagate_boolean_equality\t" << ((stat.num_ab_q != 0) ? (((double) stat.ab_sum.st.propagate_boolean_equality) / stat.num_ab_q) / 1000.0 : 0) << endl;

  out << comment << "q-num-ab-avg-eg-nassert_atom\t" << ((stat.num_ab_q != 0) ? (((double) stat.ab_sum.st.nassert_atom) / stat.num_ab_q) : 0) << endl;
  out << comment << "q-num-ab-avg-eg-nprocess_eq\t" << ((stat.num_ab_q != 0) ? (((double) stat.ab_sum.st.nprocess_eq) / stat.num_ab_q) : 0) << endl;
  out << comment << "q-num-ab-avg-eg-nprocess_eq_redundant\t" << ((stat.num_ab_q != 0) ? (((double) stat.ab_sum.st.nprocess_eq_redundant) / stat.num_ab_q) : 0) << endl;

  out << comment << "q-ab-avg-egraph_eq_props:\t" << ((stat.num_ab_q != 0) ? (((double) stat.ab_sum.st.egraph_eq_props) / stat.num_ab_q) : 0) << endl;
  out << comment << "q-ab-avg-egraph_th_props:\t" << ((stat.num_ab_q != 0) ? (((double) stat.ab_sum.st.egraph_th_props) / stat.num_ab_q) : 0) << endl;
  out << comment << "q-ab-avg-egraph_th_conflicts:\t" << ((stat.num_ab_q != 0) ? (((double) stat.ab_sum.st.egraph_th_conflicts) / stat.num_ab_q) : 0) << endl;
  out << comment << "q-ab-avg-egraph_final_checks:\t" << ((stat.num_ab_q != 0) ? (((double) stat.ab_sum.st.egraph_final_checks) / stat.num_ab_q) : 0) << endl;
  out << comment << "q-ab-avg-egraph_interface_eqs:\t" << ((stat.num_ab_q != 0) ? (((double) stat.ab_sum.st.egraph_interface_eqs) / stat.num_ab_q) : 0) << endl;

	out << comment << "q-ab-avg-restarts:\t" << ((stat.num_ab_q != 0) ? (((double) stat.ab_sum.st.restarts) / stat.num_ab_q) : 0) << endl;
	out << comment << "q-ab-avg-simplify_calls:\t" << ((stat.num_ab_q != 0) ? (((double) stat.ab_sum.st.simplify_calls) / stat.num_ab_q) : 0) << endl;
	out << comment << "q-ab-avg-reduce_calls:\t" << ((stat.num_ab_q != 0) ? (((double) stat.ab_sum.st.reduce_calls) / stat.num_ab_q) : 0) << endl;
  out << comment << "q-ab-avg-decisions:\t" << ((stat.num_ab_q != 0) ? (((double) stat.ab_sum.st.decisions) / stat.num_ab_q) : 0) << endl;
  out << comment << "q-ab-avg-random_decisions:\t" << ((stat.num_ab_q != 0) ? (((double) stat.ab_sum.st.random_decisions) / stat.num_ab_q) : 0) << endl;
  out << comment << "q-ab-avg-conflicts:\t" << ((stat.num_ab_q != 0) ? (((double) stat.ab_sum.st.conflicts) / stat.num_ab_q) : 0) << endl;

  out << comment << "s-time-ab-avg-base_bool_propagate:\t" << ((stat.num_ab_end != 0) ? (((double) stat.ab_sum.st.base_bool_propagate) / stat.num_ab_end) / 1000.0 : 0) << endl;
  out << comment << "s-time-ab-avg-base_th_propagate:\t" << ((stat.num_ab_end != 0) ? (((double) stat.ab_sum.st.base_th_propagate) / stat.num_ab_end) / 1000.0 : 0) << endl;
  out << comment << "s-time-ab-avg-flatten_assertion:\t" << ((stat.num_ab_end != 0) ? (((double) stat.ab_sum.st.flatten_assertion) / stat.num_ab_end) / 1000.0 : 0) << endl;
  out << comment << "s-time-ab-avg-preprocess_assertion:\t" << ((stat.num_ab_end != 0) ? (((double) stat.ab_sum.st.preprocess_assertion) / stat.num_ab_end) / 1000.0 : 0) << endl;
  out << comment << "s-time-ab-avg-assert_toplevel_formula:\t" << ((stat.num_ab_end != 0) ? (((double) stat.ab_sum.st.assert_toplevel_formula) / stat.num_ab_end) / 1000.0 : 0) << endl;
  out << comment << "s-time-ab-avg-assert_toplevel_intern:\t" << ((stat.num_ab_end != 0) ? (((double) stat.ab_sum.st.assert_toplevel_intern) / stat.num_ab_end) / 1000.0 : 0) << endl;

  out << comment << "s-num-ab-avg-nassert_rounds:\t" << ((stat.num_ab_end != 0) ? (((double) stat.ab_sum.st.nassert_rounds) / stat.num_ab_end) : 0) << endl;
  out << comment << "s-num-ab-avg-nassert:\t" << ((stat.num_ab_end != 0) ? (((double) stat.ab_sum.st.nassert) / stat.num_ab_end) : 0) << endl;

  out << comment << "s-ab-avg-egraph_app_reductions:\t" << ((stat.num_ab_end != 0) ? (((double) stat.ab_sum.st.egraph_app_reductions) / stat.num_ab_end) : 0) << endl;
  out << comment << "s-ab-avg-egraph_nd_lemmas:\t" << ((stat.num_ab_end != 0) ? (((double) stat.ab_sum.st.egraph_nd_lemmas) / stat.num_ab_end) : 0) << endl;
  out << comment << "s-ab-avg-egraph_aux_eqs:\t" << ((stat.num_ab_end != 0) ? (((double) stat.ab_sum.st.egraph_aux_eqs) / stat.num_ab_end) : 0) << endl;
  out << comment << "s-ab-avg-egraph_boolack_lemmas:\t" << ((stat.num_ab_end != 0) ? (((double) stat.ab_sum.st.egraph_boolack_lemmas) / stat.num_ab_end) : 0) << endl;
  out << comment << "s-ab-avg-egraph_ack_lemmas:\t" << ((stat.num_ab_end != 0) ? (((double) stat.ab_sum.st.egraph_ack_lemmas) / stat.num_ab_end) : 0) << endl;
  out << comment << "s-ab-avg-egraph_terms:\t" << ((stat.num_ab_end != 0) ? (((double) stat.ab_sum.st.egraph_terms) / stat.num_ab_end) : 0) << endl;

  out << comment << "s-ab-avg-remove_calls:\t" << ((stat.num_ab_end != 0) ? (((double) stat.ab_sum.st.remove_calls) / stat.num_ab_end) : 0) << endl;
	out << comment << "s-ab-avg-propagations:\t" << ((stat.num_ab_end != 0) ? (((double) stat.ab_sum.st.propagations) / stat.num_ab_end) : 0) << endl;
	out << comment << "s-ab-avg-th_props:\t" << ((stat.num_ab_end != 0) ? (((double) stat.ab_sum.st.th_props) / stat.num_ab_end) : 0) << endl;
	out << comment << "s-ab-avg-th_prop_lemmas:\t" << ((stat.num_ab_end != 0) ? (((double) stat.ab_sum.st.th_prop_lemmas) / stat.num_ab_end) : 0) << endl;
	out << comment << "s-ab-avg-th_conflicts:\t" << ((stat.num_ab_end != 0) ? (((double) stat.ab_sum.st.th_conflicts) / stat.num_ab_end) : 0) << endl;
	out << comment << "s-ab-avg-th_conflict_lemmas:\t" << ((stat.num_ab_end != 0) ? (((double) stat.ab_sum.st.th_conflict_lemmas) / stat.num_ab_end) : 0) << endl;
	out << comment << "s-ab-avg-prob_literals:\t" << ((stat.num_ab_end != 0) ? (((double) stat.ab_sum.st.prob_literals) / stat.num_ab_end) : 0) << endl;
	out << comment << "s-ab-avg-learned_literals:\t" << ((stat.num_ab_end != 0) ? (((double) stat.ab_sum.st.learned_literals) / stat.num_ab_end) : 0) << endl;
	out << comment << "s-ab-avg-prob_clauses_deleted:\t" << ((stat.num_ab_end != 0) ? (((double) stat.ab_sum.st.prob_clauses_deleted) / stat.num_ab_end) : 0) << endl;
	out << comment << "s-ab-avg-learned_clauses_deleted:\t" << ((stat.num_ab_end != 0) ? (((double) stat.ab_sum.st.learned_clauses_deleted) / stat.num_ab_end) : 0) << endl;
	out << comment << "s-ab-avg-bin_clauses_deleted:\t" << ((stat.num_ab_end != 0) ? (((double) stat.ab_sum.st.bin_clauses_deleted) / stat.num_ab_end) : 0) << endl;
	out << comment << "s-ab-avg-literals_before_simpl:\t" << ((stat.num_ab_end != 0) ? (((double) stat.ab_sum.st.literals_before_simpl) / stat.num_ab_end) : 0) << endl;
	out << comment << "s-ab-avg-subsumed_literals:\t" << ((stat.num_ab_end != 0) ? (((double) stat.ab_sum.st.subsumed_literals) / stat.num_ab_end) : 0) << endl;
	out << comment << "s-ab-avg-boolean_variables:\t" << ((stat.num_ab_end != 0) ? (((double) stat.ab_sum.st.boolean_variables) / stat.num_ab_end) : 0) << endl;
	out << comment << "s-ab-avg-atoms:\t" << ((stat.num_ab_end != 0) ? (((double) stat.ab_sum.st.atoms) / stat.num_ab_end) : 0) << endl;

//  // Pre
//  out << comment << "ab-avg-pre_boolean_variables:\t" << ((stat.num_ab != 0) ? (((double) stat.ab_sum.st.pre_boolean_variables) / stat.num_ab) : 0) << endl;
//  out << comment << "ab-avg-pre_atoms:\t" << ((stat.num_ab != 0) ? (((double) stat.ab_sum.st.pre_atoms) / stat.num_ab) : 0) << endl;
//  out << comment << "ab-avg-pre_egraph_terms:\t" << ((stat.num_ab != 0) ? (((double) stat.ab_sum.st.pre_egraph_terms) / stat.num_ab) : 0) << endl;
//  out << comment << "ab-avg-pre_egraph_app_reductions:\t" << ((stat.num_ab != 0) ? (((double) stat.ab_sum.st.pre_egraph_app_reductions) / stat.num_ab) : 0) << endl;

//	out << comment << "ab-avg-num_init_vars:\t" << ((stat.num_ab != 0) ? (((double) stat.ab_sum.st.num_init_vars) / stat.num_ab) : 0) << endl;
//	out << comment << "ab-avg-num_init_edges:\t" << ((stat.num_ab != 0) ? (((double) stat.ab_sum.st.num_init_edges) / stat.num_ab) : 0) << endl;
//	out << comment << "ab-avg-num_update_axiom1:\t" << ((stat.num_ab != 0) ? (((double) stat.ab_sum.st.num_update_axiom1) / stat.num_ab) : 0) << endl;
//	out << comment << "ab-avg-num_update_axiom2:\t" << ((stat.num_ab != 0) ? (((double) stat.ab_sum.st.num_update_axiom2) / stat.num_ab) : 0) << endl;
//	out << comment << "ab-avg-num_extensionality_axiom:\t" << ((stat.num_ab != 0) ? (((double) stat.ab_sum.st.num_extensionality_axiom) / stat.num_ab) : 0) << endl;
//
//	out << comment << "ab-avg-bv_variables:\t" << ((stat.num_ab != 0) ? (((double) stat.ab_sum.st.bv_variables) / stat.num_ab) : 0) << endl;
//	out << comment << "ab-avg-bv_atoms:\t" << ((stat.num_ab != 0) ? (((double) stat.ab_sum.st.bv_atoms) / stat.num_ab) : 0) << endl;
//	out << comment << "ab-avg-bv_eq_atoms:\t" << ((stat.num_ab != 0) ? (((double) stat.ab_sum.st.bv_eq_atoms) / stat.num_ab) : 0) << endl;
//	out << comment << "ab-avg-bv_dyn_eq_atoms:\t" << ((stat.num_ab != 0) ? (((double) stat.ab_sum.st.bv_dyn_eq_atoms) / stat.num_ab) : 0) << endl;
//	out << comment << "ab-avg-bv_ge_atoms:\t" << ((stat.num_ab != 0) ? (((double) stat.ab_sum.st.bv_ge_atoms) / stat.num_ab) : 0) << endl;
//	out << comment << "ab-avg-bv_sge_atoms:\t" << ((stat.num_ab != 0) ? (((double) stat.ab_sum.st.bv_sge_atoms) / stat.num_ab) : 0) << endl;
//	out << comment << "ab-avg-bv_equiv_lemmas:\t" << ((stat.num_ab != 0) ? (((double) stat.ab_sum.st.bv_equiv_lemmas) / stat.num_ab) : 0) << endl;
//	out << comment << "ab-avg-bv_equiv_conflicts:\t" << ((stat.num_ab != 0) ? (((double) stat.ab_sum.st.bv_equiv_conflicts) / stat.num_ab) : 0) << endl;
//	out << comment << "ab-avg-bv_semi_equiv_lemmas:\t" << ((stat.num_ab != 0) ? (((double) stat.ab_sum.st.bv_semi_equiv_lemmas) / stat.num_ab) : 0) << endl;
//	out << comment << "ab-avg-bv_interface_lemmas:\t" << ((stat.num_ab != 0) ? (((double) stat.ab_sum.st.bv_interface_lemmas) / stat.num_ab) : 0) << endl;


  // BV
	// Pre
//	out << comment << "bv-avg-pre_boolean_variables:\t" << ((stat.num_bv != 0) ? (((double) stat.bv_sum.st.pre_boolean_variables) / stat.num_bv) : 0) << endl;
//	out << comment << "bv-avg-pre_atoms:\t" << ((stat.num_bv != 0) ? (((double) stat.bv_sum.st.pre_atoms) / stat.num_bv) : 0) << endl;
//	out << comment << "bv-avg-pre_egraph_terms:\t" << ((stat.num_bv != 0) ? (((double) stat.bv_sum.st.pre_egraph_terms) / stat.num_bv) : 0) << endl;
//	out << comment << "bv-avg-pre_egraph_app_reductions:\t" << ((stat.num_bv != 0) ? (((double) stat.bv_sum.st.pre_egraph_app_reductions) / stat.num_bv) : 0) << endl;

//	out << comment << "bv-avg-restarts:\t" << ((stat.num_bv != 0) ? (((double) stat.bv_sum.st.restarts) / stat.num_bv) : 0) << endl;
//	out << comment << "bv-avg-simplify_calls:\t" << ((stat.num_bv != 0) ? (((double) stat.bv_sum.st.simplify_calls) / stat.num_bv) : 0) << endl;
//	out << comment << "bv-avg-reduce_calls:\t" << ((stat.num_bv != 0) ? (((double) stat.bv_sum.st.reduce_calls) / stat.num_bv) : 0) << endl;
//	out << comment << "bv-avg-remove_calls:\t" << ((stat.num_bv != 0) ? (((double) stat.bv_sum.st.remove_calls) / stat.num_bv) : 0) << endl;
//	out << comment << "bv-avg-decisions:\t" << ((stat.num_bv != 0) ? (((double) stat.bv_sum.st.decisions) / stat.num_bv) : 0) << endl;
//	out << comment << "bv-avg-random_decisions:\t" << ((stat.num_bv != 0) ? (((double) stat.bv_sum.st.random_decisions) / stat.num_bv) : 0) << endl;
//	out << comment << "bv-avg-propagations:\t" << ((stat.num_bv != 0) ? (((double) stat.bv_sum.st.propagations) / stat.num_bv) : 0) << endl;
//	out << comment << "bv-avg-conflicts:\t" << ((stat.num_bv != 0) ? (((double) stat.bv_sum.st.conflicts) / stat.num_bv) : 0) << endl;
//	out << comment << "bv-avg-th_props:\t" << ((stat.num_bv != 0) ? (((double) stat.bv_sum.st.th_props) / stat.num_bv) : 0) << endl;
//	out << comment << "bv-avg-th_prop_lemmas:\t" << ((stat.num_bv != 0) ? (((double) stat.bv_sum.st.th_prop_lemmas) / stat.num_bv) : 0) << endl;
//	out << comment << "bv-avg-th_conflicts:\t" << ((stat.num_bv != 0) ? (((double) stat.bv_sum.st.th_conflicts) / stat.num_bv) : 0) << endl;
//	out << comment << "bv-avg-th_conflict_lemmas:\t" << ((stat.num_bv != 0) ? (((double) stat.bv_sum.st.th_conflict_lemmas) / stat.num_bv) : 0) << endl;
//	out << comment << "bv-avg-prob_literals:\t" << ((stat.num_bv != 0) ? (((double) stat.bv_sum.st.prob_literals) / stat.num_bv) : 0) << endl;
//	out << comment << "bv-avg-learned_literals:\t" << ((stat.num_bv != 0) ? (((double) stat.bv_sum.st.learned_literals) / stat.num_bv) : 0) << endl;
//	out << comment << "bv-avg-prob_clauses_deleted:\t" << ((stat.num_bv != 0) ? (((double) stat.bv_sum.st.prob_clauses_deleted) / stat.num_bv) : 0) << endl;
//	out << comment << "bv-avg-learned_clauses_deleted:\t" << ((stat.num_bv != 0) ? (((double) stat.bv_sum.st.learned_clauses_deleted) / stat.num_bv) : 0) << endl;
//	out << comment << "bv-avg-bin_clauses_deleted:\t" << ((stat.num_bv != 0) ? (((double) stat.bv_sum.st.bin_clauses_deleted) / stat.num_bv) : 0) << endl;
//	out << comment << "bv-avg-literals_before_simpl:\t" << ((stat.num_bv != 0) ? (((double) stat.bv_sum.st.literals_before_simpl) / stat.num_bv) : 0) << endl;
//	out << comment << "bv-avg-subsumed_literals:\t" << ((stat.num_bv != 0) ? (((double) stat.bv_sum.st.subsumed_literals) / stat.num_bv) : 0) << endl;
//	out << comment << "bv-avg-boolean_variables:\t" << ((stat.num_bv != 0) ? (((double) stat.bv_sum.st.boolean_variables) / stat.num_bv) : 0) << endl;
//	out << comment << "bv-avg-atoms:\t" << ((stat.num_bv != 0) ? (((double) stat.bv_sum.st.atoms) / stat.num_bv) : 0) << endl;
//
//	out << comment << "bv-avg-egraph_app_reductions:\t" << ((stat.num_bv != 0) ? (((double) stat.bv_sum.st.egraph_app_reductions) / stat.num_bv) : 0) << endl;
//	out << comment << "bv-avg-egraph_eq_props:\t" << ((stat.num_bv != 0) ? (((double) stat.bv_sum.st.egraph_eq_props) / stat.num_bv) : 0) << endl;
//	out << comment << "bv-avg-egraph_th_props:\t" << ((stat.num_bv != 0) ? (((double) stat.bv_sum.st.egraph_th_props) / stat.num_bv) : 0) << endl;
//	out << comment << "bv-avg-egraph_th_conflicts:\t" << ((stat.num_bv != 0) ? (((double) stat.bv_sum.st.egraph_th_conflicts) / stat.num_bv) : 0) << endl;
//	out << comment << "bv-avg-egraph_nd_lemmas:\t" << ((stat.num_bv != 0) ? (((double) stat.bv_sum.st.egraph_nd_lemmas) / stat.num_bv) : 0) << endl;
//	out << comment << "bv-avg-egraph_aux_eqs:\t" << ((stat.num_bv != 0) ? (((double) stat.bv_sum.st.egraph_aux_eqs) / stat.num_bv) : 0) << endl;
//	out << comment << "bv-avg-egraph_boolack_lemmas:\t" << ((stat.num_bv != 0) ? (((double) stat.bv_sum.st.egraph_boolack_lemmas) / stat.num_bv) : 0) << endl;
//	out << comment << "bv-avg-egraph_ack_lemmas:\t" << ((stat.num_bv != 0) ? (((double) stat.bv_sum.st.egraph_ack_lemmas) / stat.num_bv) : 0) << endl;
//	out << comment << "bv-avg-egraph_final_checks:\t" << ((stat.num_bv != 0) ? (((double) stat.bv_sum.st.egraph_final_checks) / stat.num_bv) : 0) << endl;
//	out << comment << "bv-avg-egraph_interface_eqs:\t" << ((stat.num_bv != 0) ? (((double) stat.bv_sum.st.egraph_interface_eqs) / stat.num_bv) : 0) << endl;
//	out << comment << "bv-avg-egraph_terms:\t" << ((stat.num_bv != 0) ? (((double) stat.bv_sum.st.egraph_terms) / stat.num_bv) : 0) << endl;
//
//	out << comment << "bv-avg-num_init_vars:\t" << ((stat.num_bv != 0) ? (((double) stat.bv_sum.st.num_init_vars) / stat.num_bv) : 0) << endl;
//	out << comment << "bv-avg-num_init_edges:\t" << ((stat.num_bv != 0) ? (((double) stat.bv_sum.st.num_init_edges) / stat.num_bv) : 0) << endl;
//	out << comment << "bv-avg-num_update_axiom1:\t" << ((stat.num_bv != 0) ? (((double) stat.bv_sum.st.num_update_axiom1) / stat.num_bv) : 0) << endl;
//	out << comment << "bv-avg-num_update_axiom2:\t" << ((stat.num_bv != 0) ? (((double) stat.bv_sum.st.num_update_axiom2) / stat.num_bv) : 0) << endl;
//	out << comment << "bv-avg-num_extensionality_axiom:\t" << ((stat.num_bv != 0) ? (((double) stat.bv_sum.st.num_extensionality_axiom) / stat.num_bv) : 0) << endl;
//
//	out << comment << "bv-avg-bv_variables:\t" << ((stat.num_bv != 0) ? (((double) stat.bv_sum.st.bv_variables) / stat.num_bv) : 0) << endl;
//	out << comment << "bv-avg-bv_atoms:\t" << ((stat.num_bv != 0) ? (((double) stat.bv_sum.st.bv_atoms) / stat.num_bv) : 0) << endl;
//	out << comment << "bv-avg-bv_eq_atoms:\t" << ((stat.num_bv != 0) ? (((double) stat.bv_sum.st.bv_eq_atoms) / stat.num_bv) : 0) << endl;
//	out << comment << "bv-avg-bv_dyn_eq_atoms:\t" << ((stat.num_bv != 0) ? (((double) stat.bv_sum.st.bv_dyn_eq_atoms) / stat.num_bv) : 0) << endl;
//	out << comment << "bv-avg-bv_ge_atoms:\t" << ((stat.num_bv != 0) ? (((double) stat.bv_sum.st.bv_ge_atoms) / stat.num_bv) : 0) << endl;
//	out << comment << "bv-avg-bv_sge_atoms:\t" << ((stat.num_bv != 0) ? (((double) stat.bv_sum.st.bv_sge_atoms) / stat.num_bv) : 0) << endl;
//	out << comment << "bv-avg-bv_equiv_lemmas:\t" << ((stat.num_bv != 0) ? (((double) stat.bv_sum.st.bv_equiv_lemmas) / stat.num_bv) : 0) << endl;
//	out << comment << "bv-avg-bv_equiv_conflicts:\t" << ((stat.num_bv != 0) ? (((double) stat.bv_sum.st.bv_equiv_conflicts) / stat.num_bv) : 0) << endl;
//	out << comment << "bv-avg-bv_semi_equiv_lemmas:\t" << ((stat.num_bv != 0) ? (((double) stat.bv_sum.st.bv_semi_equiv_lemmas) / stat.num_bv) : 0) << endl;
//	out << comment << "bv-avg-bv_interface_lemmas:\t" << ((stat.num_bv != 0) ? (((double) stat.bv_sum.st.bv_interface_lemmas) / stat.num_bv) : 0) << endl;



/// Max
  // AB
	out << comment << "q-time-ab-max-boolean_propagation:\t" << stat.ab_max.st.boolean_propagation / 1000.0 << endl;
	out << comment << "q-time-ab-max-theory_propagation:\t" << stat.ab_max.st.theory_propagation / 1000.0 << endl;
	out << comment << "q-time-ab-max-resolve_conflict:\t" << stat.ab_max.st.resolve_conflict / 1000.0 << endl;
	out << comment << "q-time-ab-max-smt_restart:\t" << stat.ab_max.st.smt_restart / 1000.0 << endl;
	out << comment << "q-time-ab-max-select_unassigned_literal:\t" << stat.ab_max.st.select_unassigned_literal / 1000.0 << endl;
	out << comment << "q-time-ab-max-decide_literal:\t" << stat.ab_max.st.decide_literal / 1000.0 << endl;
	out << comment << "q-time-ab-max-add_all_lemmas:\t" << stat.ab_max.st.add_all_lemmas / 1000.0 << endl;
	out << comment << "q-time-ab-max-delete_irrelevant_variables:\t" << stat.ab_max.st.delete_irrelevant_variables / 1000.0 << endl;
	out << comment << "q-time-ab-max-simplify_clause_database:\t" << stat.ab_max.st.simplify_clause_database / 1000.0 << endl;
	out << comment << "q-time-ab-max-reduce_clause_database:\t" << stat.ab_max.st.reduce_clause_database / 1000.0 << endl;

	out << comment << "q-time-ab-max-eg-propagate:\t" << stat.ab_max.st.propagate / 1000.0 << endl;
	out << comment << "q-time-ab-max-eg-internal_propagation:\t" << stat.ab_max.st.internal_propagation / 1000.0 << endl;
  out << comment << "q-time-ab-max-eg-reactivate_dynamic_terms:\t" << stat.ab_max.st.reactivate_dynamic_terms / 1000.0 << endl;
	out << comment << "q-time-ab-max-eg-process_equality:\t" << stat.ab_max.st.process_equality / 1000.0 << endl;
	out << comment << "q-time-ab-max-eg-inconsistent_edge:\t" << stat.ab_max.st.inconsistent_edge / 1000.0 << endl;
	out << comment << "q-time-ab-max-eg-invert_branch:\t" << stat.ab_max.st.invert_branch / 1000.0 << endl;
	out << comment << "q-time-ab-max-eg-remove_parents:\t" << stat.ab_max.st.remove_parents / 1000.0 << endl;
	out << comment << "q-time-ab-max-eg-assign_new_label:\t" << stat.ab_max.st.assign_new_label / 1000.0 << endl;
	out << comment << "q-time-ab-max-eg-collect_eqterms:\t" << stat.ab_max.st.collect_eqterms / 1000.0 << endl;
	out << comment << "q-time-ab-max-eg-reprocess_parents:\t" << stat.ab_max.st.reprocess_parents / 1000.0 << endl;
	out << comment << "q-time-ab-max-eg-check_false_eq:\t" << stat.ab_max.st.check_false_eq / 1000.0 << endl;
	out << comment << "q-time-ab-max-eg-atom_propagation:\t" << stat.ab_max.st.atom_propagation / 1000.0 << endl;
	out << comment << "q-time-ab-max-eg-propagate_boolean_equality:\t" << stat.ab_max.st.propagate_boolean_equality / 1000.0 << endl;

  out << comment << "q-num-ab-max-eg-nassert_atom:\t" << stat.ab_max.st.nassert_atom << endl;
  out << comment << "q-num-ab-max-eg-nprocess_eq:\t" << stat.ab_max.st.nprocess_eq << endl;
  out << comment << "q-num-ab-max-eg-nprocess_eq_redundant:\t" << stat.ab_max.st.nprocess_eq_redundant << endl;

	out << comment << "q-ab-max-egraph_eq_props:\t" << stat.ab_max.st.egraph_eq_props << endl;
  out << comment << "q-ab-max-egraph_th_props:\t" << stat.ab_max.st.egraph_th_props << endl;
  out << comment << "q-ab-max-egraph_th_conflicts:\t" << stat.ab_max.st.egraph_th_conflicts << endl;
  out << comment << "q-ab-max-egraph_final_checks:\t" << stat.ab_max.st.egraph_final_checks << endl;
  out << comment << "q-ab-max-egraph_interface_eqs:\t" << stat.ab_max.st.egraph_interface_eqs << endl;

	out << comment << "q-ab-max-restarts:\t" << stat.ab_max.st.restarts << endl;
	out << comment << "q-ab-max-simplify_calls:\t" << stat.ab_max.st.simplify_calls << endl;
	out << comment << "q-ab-max-reduce_calls:\t" << stat.ab_max.st.reduce_calls << endl;
  out << comment << "q-ab-max-decisions:\t" << stat.ab_max.st.decisions << endl;
  out << comment << "q-ab-max-random_decisions:\t" << stat.ab_max.st.random_decisions << endl;
  out << comment << "q-ab-max-conflicts:\t" << stat.ab_max.st.conflicts << endl;

  out << comment << "s-time-ab-max-base_bool_propagate:\t" << stat.ab_max.st.base_bool_propagate / 1000.0 << endl;
  out << comment << "s-time-ab-max-base_th_propagate:\t" << stat.ab_max.st.base_th_propagate / 1000.0 << endl;
  out << comment << "s-time-ab-max-flatten_assertion:\t" << stat.ab_max.st.flatten_assertion / 1000.0 << endl;
  out << comment << "s-time-ab-max-preprocess_assertion:\t" << stat.ab_max.st.preprocess_assertion / 1000.0 << endl;
  out << comment << "s-time-ab-max-assert_toplevel_formula:\t" << stat.ab_max.st.assert_toplevel_formula / 1000.0 << endl;
  out << comment << "s-time-ab-max-assert_toplevel_intern:\t" << stat.ab_max.st.assert_toplevel_intern / 1000.0 << endl;

  out << comment << "s-num-ab-max-nassert_rounds:\t" << stat.ab_max.st.nassert_rounds << endl;
  out << comment << "s-num-ab-max-nassert:\t" << stat.ab_max.st.nassert << endl;

  out << comment << "s-ab-max-egraph_app_reductions:\t" << stat.ab_max.st.egraph_app_reductions << endl;
  out << comment << "s-ab-max-egraph_nd_lemmas:\t" << stat.ab_max.st.egraph_nd_lemmas << endl;
  out << comment << "s-ab-max-egraph_aux_eqs:\t" << stat.ab_max.st.egraph_aux_eqs << endl;
  out << comment << "s-ab-max-egraph_boolack_lemmas:\t" << stat.ab_max.st.egraph_boolack_lemmas << endl;
  out << comment << "s-ab-max-egraph_ack_lemmas:\t" << stat.ab_max.st.egraph_ack_lemmas << endl;
  out << comment << "s-ab-max-egraph_terms:\t" << stat.ab_max.st.egraph_terms << endl;

	out << comment << "s-ab-max-remove_calls:\t" << stat.ab_max.st.remove_calls << endl;
	out << comment << "s-ab-max-propagations:\t" << stat.ab_max.st.propagations << endl;
	out << comment << "s-ab-max-th_props:\t" << stat.ab_max.st.th_props << endl;
	out << comment << "s-ab-max-th_prop_lemmas:\t" << stat.ab_max.st.th_prop_lemmas << endl;
	out << comment << "s-ab-max-th_conflicts:\t" << stat.ab_max.st.th_conflicts << endl;
	out << comment << "s-ab-max-th_conflict_lemmas:\t" << stat.ab_max.st.th_conflict_lemmas << endl;
	out << comment << "s-ab-max-prob_literals:\t" << stat.ab_max.st.prob_literals << endl;
	out << comment << "s-ab-max-learned_literals:\t" << stat.ab_max.st.learned_literals << endl;
	out << comment << "s-ab-max-prob_clauses_deleted:\t" << stat.ab_max.st.prob_clauses_deleted << endl;
	out << comment << "s-ab-max-learned_clauses_deleted:\t" << stat.ab_max.st.learned_clauses_deleted << endl;
	out << comment << "s-ab-max-bin_clauses_deleted:\t" << stat.ab_max.st.bin_clauses_deleted << endl;
	out << comment << "s-ab-max-literals_before_simpl:\t" << stat.ab_max.st.literals_before_simpl << endl;
	out << comment << "s-ab-max-subsumed_literals:\t" << stat.ab_max.st.subsumed_literals << endl;
	out << comment << "s-ab-max-boolean_variables:\t" << stat.ab_max.st.boolean_variables << endl;
	out << comment << "s-ab-max-atoms:\t" << stat.ab_max.st.atoms << endl;

//  // Pre
//  out << comment << "ab-max-pre_boolean_variables:\t" << stat.ab_max.st.pre_boolean_variables << endl;
//  out << comment << "ab-max-pre_atoms:\t" << stat.ab_max.st.pre_atoms << endl;
//  out << comment << "ab-max-pre_egraph_terms:\t" << stat.ab_max.st.pre_egraph_terms << endl;
//  out << comment << "ab-max-pre_egraph_app_reductions:\t" << stat.ab_max.st.pre_egraph_app_reductions << endl;

//	out << comment << "ab-max-num_init_vars:\t" << stat.ab_max.st.num_init_vars << endl;
//	out << comment << "ab-max-num_init_edges:\t" << stat.ab_max.st.num_init_edges << endl;
//	out << comment << "ab-max-num_update_axiom1:\t" << stat.ab_max.st.num_update_axiom1 << endl;
//	out << comment << "ab-max-num_update_axiom2:\t" << stat.ab_max.st.num_update_axiom2 << endl;
//	out << comment << "ab-max-num_extensionality_axiom:\t" << stat.ab_max.st.num_extensionality_axiom << endl;
//
//	out << comment << "ab-max-bv_variables:\t" << stat.ab_max.st.bv_variables << endl;
//	out << comment << "ab-max-bv_atoms:\t" << stat.ab_max.st.bv_atoms << endl;
//	out << comment << "ab-max-bv_eq_atoms:\t" << stat.ab_max.st.bv_eq_atoms << endl;
//	out << comment << "ab-max-bv_dyn_eq_atoms:\t" << stat.ab_max.st.bv_dyn_eq_atoms << endl;
//	out << comment << "ab-max-bv_ge_atoms:\t" << stat.ab_max.st.bv_ge_atoms << endl;
//	out << comment << "ab-max-bv_sge_atoms:\t" << stat.ab_max.st.bv_sge_atoms << endl;
//	out << comment << "ab-max-bv_equiv_lemmas:\t" << stat.ab_max.st.bv_equiv_lemmas << endl;
//	out << comment << "ab-max-bv_equiv_conflicts:\t" << stat.ab_max.st.bv_equiv_conflicts << endl;
//	out << comment << "ab-max-bv_semi_equiv_lemmas:\t" << stat.ab_max.st.bv_semi_equiv_lemmas << endl;
//	out << comment << "ab-max-bv_interface_lemmas:\t" << stat.ab_max.st.bv_interface_lemmas << endl;


  // BV
	// Pre
//	out << comment << "bv-max-pre_boolean_variables:\t" << stat.bv_max.st.pre_boolean_variables << endl;
//	out << comment << "bv-max-pre_atoms:\t" << stat.bv_max.st.pre_atoms << endl;
//	out << comment << "bv-max-pre_egraph_terms:\t" << stat.bv_max.st.pre_egraph_terms << endl;
//	out << comment << "bv-max-pre_egraph_app_reductions:\t" << stat.bv_max.st.pre_egraph_app_reductions << endl;

//	out << comment << "bv-max-restarts:\t" << stat.bv_max.st.restarts << endl;
//	out << comment << "bv-max-simplify_calls:\t" << stat.bv_max.st.simplify_calls << endl;
//	out << comment << "bv-max-reduce_calls:\t" << stat.bv_max.st.reduce_calls << endl;
//	out << comment << "bv-max-remove_calls:\t" << stat.bv_max.st.remove_calls << endl;
//	out << comment << "bv-max-decisions:\t" << stat.bv_max.st.decisions << endl;
//	out << comment << "bv-max-random_decisions:\t" << stat.bv_max.st.random_decisions << endl;
//	out << comment << "bv-max-propagations:\t" << stat.bv_max.st.propagations << endl;
//	out << comment << "bv-max-conflicts:\t" << stat.bv_max.st.conflicts << endl;
//	out << comment << "bv-max-th_props:\t" << stat.bv_max.st.th_props << endl;
//	out << comment << "bv-max-th_prop_lemmas:\t" << stat.bv_max.st.th_prop_lemmas << endl;
//	out << comment << "bv-max-th_conflicts:\t" << stat.bv_max.st.th_conflicts << endl;
//	out << comment << "bv-max-th_conflict_lemmas:\t" << stat.bv_max.st.th_conflict_lemmas << endl;
//	out << comment << "bv-max-prob_literals:\t" << stat.bv_max.st.prob_literals << endl;
//	out << comment << "bv-max-learned_literals:\t" << stat.bv_max.st.learned_literals << endl;
//	out << comment << "bv-max-prob_clauses_deleted:\t" << stat.bv_max.st.prob_clauses_deleted << endl;
//	out << comment << "bv-max-learned_clauses_deleted:\t" << stat.bv_max.st.learned_clauses_deleted << endl;
//	out << comment << "bv-max-bin_clauses_deleted:\t" << stat.bv_max.st.bin_clauses_deleted << endl;
//	out << comment << "bv-max-literals_before_simpl:\t" << stat.bv_max.st.literals_before_simpl << endl;
//	out << comment << "bv-max-subsumed_literals:\t" << stat.bv_max.st.subsumed_literals << endl;
//	out << comment << "bv-max-boolean_variables:\t" << stat.bv_max.st.boolean_variables << endl;
//	out << comment << "bv-max-atoms:\t" << stat.bv_max.st.atoms << endl;
//
//	out << comment << "bv-max-egraph_app_reductions:\t" << stat.bv_max.st.egraph_app_reductions << endl;
//	out << comment << "bv-max-egraph_eq_props:\t" << stat.bv_max.st.egraph_eq_props << endl;
//	out << comment << "bv-max-egraph_th_props:\t" << stat.bv_max.st.egraph_th_props << endl;
//	out << comment << "bv-max-egraph_th_conflicts:\t" << stat.bv_max.st.egraph_th_conflicts << endl;
//	out << comment << "bv-max-egraph_nd_lemmas:\t" << stat.bv_max.st.egraph_nd_lemmas << endl;
//	out << comment << "bv-max-egraph_aux_eqs:\t" << stat.bv_max.st.egraph_aux_eqs << endl;
//	out << comment << "bv-max-egraph_boolack_lemmas:\t" << stat.bv_max.st.egraph_boolack_lemmas << endl;
//	out << comment << "bv-max-egraph_ack_lemmas:\t" << stat.bv_max.st.egraph_ack_lemmas << endl;
//	out << comment << "bv-max-egraph_final_checks:\t" << stat.bv_max.st.egraph_final_checks << endl;
//	out << comment << "bv-max-egraph_interface_eqs:\t" << stat.bv_max.st.egraph_interface_eqs << endl;
//	out << comment << "bv-max-egraph_terms:\t" << stat.bv_max.st.egraph_terms << endl;
//
//	out << comment << "bv-max-num_init_vars:\t" << stat.bv_max.st.num_init_vars << endl;
//	out << comment << "bv-max-num_init_edges:\t" << stat.bv_max.st.num_init_edges << endl;
//	out << comment << "bv-max-num_update_axiom1:\t" << stat.bv_max.st.num_update_axiom1 << endl;
//	out << comment << "bv-max-num_update_axiom2:\t" << stat.bv_max.st.num_update_axiom2 << endl;
//	out << comment << "bv-max-num_extensionality_axiom:\t" << stat.bv_max.st.num_extensionality_axiom << endl;
//
//	out << comment << "bv-max-bv_variables:\t" << stat.bv_max.st.bv_variables << endl;
//	out << comment << "bv-max-bv_atoms:\t" << stat.bv_max.st.bv_atoms << endl;
//	out << comment << "bv-max-bv_eq_atoms:\t" << stat.bv_max.st.bv_eq_atoms << endl;
//	out << comment << "bv-max-bv_dyn_eq_atoms:\t" << stat.bv_max.st.bv_dyn_eq_atoms << endl;
//	out << comment << "bv-max-bv_ge_atoms:\t" << stat.bv_max.st.bv_ge_atoms << endl;
//	out << comment << "bv-max-bv_sge_atoms:\t" << stat.bv_max.st.bv_sge_atoms << endl;
//	out << comment << "bv-max-bv_equiv_lemmas:\t" << stat.bv_max.st.bv_equiv_lemmas << endl;
//	out << comment << "bv-max-bv_equiv_conflicts:\t" << stat.bv_max.st.bv_equiv_conflicts << endl;
//	out << comment << "bv-max-bv_semi_equiv_lemmas:\t" << stat.bv_max.st.bv_semi_equiv_lemmas << endl;
//	out << comment << "bv-max-bv_interface_lemmas:\t" << stat.bv_max.st.bv_interface_lemmas << endl;
}
#endif

void y2_API::y2_collect_garbage(bool keep_named) {
	AVR_LOG(11, 0, "before cleaning- #terms: " << yices_num_terms() << "\t#types: " << yices_num_types() << endl);
	yices_garbage_collect(NULL, 0, NULL, 0, keep_named);
	AVR_LOG(11, 0, "after cleaning- #terms: " << yices_num_terms() << "\t#types: " << yices_num_types() << endl);
}


string print_term(y2_expr y)
{
//	return "";

	char* tmp = yices_term_to_string(y, 20000, 1, 0);
	string str(tmp);
	yices_free_string(tmp);
//	str += "_" + to_string(y);
	return str;
}

string print_terms(y2_expr_vec& yV)
{
//	return "";
  ostringstream ostr;
	for (auto& y: yV)
	  ostr << "\t" << print_term(y) << endl;
	return ostr.str();
}

string print_terms(list<y2_expr>& yV)
{
//	return "";
	string s = "";
	for (auto& y: yV)
		s = s + print_term(y) + " ";
	return s;
}

string print_terms(set<y2_expr>& yV)
{
//	return "";
	string s = "";
	for (auto& y: yV)
		s = s + print_term(y) + " ";
	return s;
}

string print_type(y2_type y)
{
//	return "";

	char* tmp = yices_type_to_string(y, 200, 1, 0);
	string str(tmp);
	yices_free_string(tmp);
	return str;
}

string print_smt_term(y2_expr y)
{
//  return "";

//#ifdef FLATTEN_QUERY
#if 1
  char* tmp = yices_term_to_string(y, 200000000, 1, 0);
  string str(tmp);
  yices_free_string(tmp);

//  cout << "original:" << str << endl;
  size_t pos = str.find("/=", 0);
  while(pos != string::npos)
  {
    str.replace(pos, 2, "not (=");
    pos += 6;

    size_t posOpen  = pos;
    int openCount = 1;
    do {
      posOpen = str.find_first_of("()", posOpen);
      assert (posOpen != string::npos);

			if (str[posOpen] == '(')
				openCount++;
			else {
				assert (str[posOpen] == ')');
				openCount--;
			}
    }
    while (openCount > 0);

		str.insert(posOpen, 1, ')');

    pos = str.find("/=",pos+1);
//    assert(0);
  }
#else
  char* tmp = yices_term_to_string(y, 200000, 1, 0);
  string str(tmp);
  yices_free_string(tmp);

////  cout << "original:" << str << endl;
//  size_t pos = str.find("/=", 0);
//  while(pos != string::npos)
//  {
//    str.replace(pos, 2, "not (=");
//    pos += 6;
//
//    pos = str.find_first_of(')', pos);
//    str.insert(pos, 1, ')');
////    int openCount = 1;
////    for (size_t i = pos; i != str.length(); i++)
////    {
////      if (str[i] == '(')
////        openCount++;
////      else if (str[i] == ')')
////      {
////        openCount--;
////        if (openCount == 0)
////        {
////          str.replace(i, 1, "))");
////          break;
////        }
////      }
////    }
//
//    pos = str.find("/=",pos+1);
////    assert(0);
//  }
#endif
//  cout << "changed to:" << str << endl;

	replace(str.begin(), str.end(), '[', '$');
	replace(str.begin(), str.end(), ']', '$');
	replace(str.begin(), str.end(), ':', '_');

  return str;
}

string print_smt_type(y2_type y)
{
//	return "";

	char* tmp = yices_type_to_string(y, 2000, 1, 0);
	string str(tmp);
	yices_free_string(tmp);
	if (str == "bool")
		return "Bool";
	else if (str.length() >= 11 && str.substr(0, 10) == "(bitvector")
	{
		return "(_ BitVec" + str.substr(10);
	}
	return str;
}

void y2_API::debug() {

}

void y2_API::collect_solver_stats() {
#ifdef Y2_STATS
	FILE * tempFile = tmpfile();
	if(tempFile) {
		yices_print_context_statistics(tempFile, g_ctx);

		// rewind() function sets the file pointer at the beginning of the stream.
		rewind(tempFile);

		char line[256];
		string key;
		int value;

		string name = "y2-";
		name += (m_abstract ? "ab-" : "bv-");
		SOLVER_STAT& st = g_solver_stats[name];
		st.count++;

		string name2 = name + qtype2str(queryType) + "-";
		SOLVER_STAT& st2 = g_solver_stats[name2];
		st2.count++;
		while (fgets(line, sizeof(line), tempFile)) {
				/* note that fgets don't strip the terminating \n, checking its
					 presence would allow to handle lines longer that sizeof(line) */
			istringstream ss(line);
			ss >> key >> value;
			st.update(key, value);
			st2.update(key, value);
//			cout << "y2-stats> " << key << "\t" << value << endl;
		}
		fclose(tempFile);
	}
	else {
		AVR_LOG(15, 0, "\t(warning: unable to create temporary stats file)\n");
	}
#endif
}


void y2_API::set_logic(y2_config cfg)
{
#ifdef BIT_LEVEL_AVR
  yices_default_config_for_logic(cfg, "NONE");
#else
	string lname = "QF_";
  if (m_abstract)
	{
		if (m_mapper->fetch_logic() == TheoryMapper::QF_UF)
		{
			if (Inst::en_array)
				lname += "A";
			lname += "UF";
			//		yices_set_config(m_config, "uf-solver", "default");
			//		yices_set_config(m_config, "bv-solver", "none");
		}
		else
		{
			assert (m_mapper->fetch_logic() == TheoryMapper::QF_UFBV);
			if (Inst::en_array)
				lname += "A";
			lname += "UFBV";
			if (Inst::en_integer)
				lname += "LIA";
			if (Inst::en_array && Inst::en_integer)
				lname = "ALL";
		}
	}
	else
	{
		assert (m_mapper->fetch_logic() == TheoryMapper::QF_BV);
		if (Inst::en_array)
			lname += "A";
		lname += "BV";
		if (Inst::en_integer)
			lname += "LIA";
		if (Inst::en_array && Inst::en_integer)
			lname = "ALL";
//		yices_set_config(m_config, "uf-solver", "none");
//		yices_set_config(m_config, "bv-solver", "default");
	}
//	cout << "logic: " << lname << endl;
	yices_default_config_for_logic(cfg, lname.c_str());
#endif
}

y2_API::y2_API(Solver::TheoryMapper* m, unsigned ba_idx, int mode, int type) :
	Solver(m, ba_idx, type) {

	y2_solvers[m_solver_id] = this;
	assert(m);

//	yices_enable_log_file("yices.log");
//	yices_set_verbosity(100);

	AVR_LOG(11, 1, "Creating new Yices instance for BA[" << m_ba_idx << "] with solver_id [" << m_solver_id << "]" << endl);

	m_config = yices_new_config();
	m_param = yices_new_param_record();

	set_logic();

	if (mode == 0)
	{
		yices_set_config(m_config, "mode", "one-shot");
	}
	else if (mode == 1)
	{
		yices_set_config(m_config, "mode", "multi-checks");
	}
	else
	{
#ifdef Y2_INTERACTIVE
		yices_set_config(m_config, "mode", "interactive");
#else
		yices_set_config(m_config, "mode", "push-pop");
#endif
		if (m_abstract)
			enable_fallback();
		else
			disable_fallback();

		is_i = (mode == 2);
		assert(0);
	}

	m_ctx = yices_new_context(m_config);
	g_ctx = m_ctx;
	set_context_parameters();

	yices_default_params_for_context(m_ctx, m_param);
	set_parameters();

//	m_stack.clear();
	m_constraints.clear();
	m_model = NULL;
	m_cList.clear();
#ifdef TRACE_SOLVER
	m_trace.clear();
#endif

	y2_expr_vec tmp;
	m_cList.push_back(make_pair(m_cList.size() + 1, tmp));

#ifdef ASSERT_DISTINCT_NUMBERS
	if (m_abstract)
	{
		assert_distinct_constants();
	}
#endif
}

void y2_API::s_reset_scope() {
	if (g_num_reset > Y2_MAX_RESET_ALLOWED) {
		AVR_LOG(15, 0, "\t(warning: reached maximum limit for Y2 resets)" << endl);
		assert(0);
	}
	AVR_LOG(15, 0, "\t(resetting Y2 scope)" << endl);
	g_num_reset++;
	y2_reset();
}

void y2_API::s_reset_single_solver() {
	s_reset_scope();
	AVR_LOG(15, 0, "\t(resetting single Y2 solver)" << endl);
	s_reset_solver();
}

void y2_API::s_reset_remaining_solvers(int solver_id) {
	AVR_LOG(15, 0, "\t(resetting remaining Y2 solvers)" << endl);
	for (auto& s: y2_solvers) {
		if (s.first != solver_id)
			s.second->s_reset_solver();
	}
}

void y2_API::s_reset_all_solvers() {
	s_reset_scope();
	AVR_LOG(15, 0, "\t(resetting all Y2 solvers)" << endl);
	for (auto& s: y2_solvers)
		s.second->s_reset_solver();
}

void y2_API::s_reset_solver() {
	num_of_terms = 0;
	num_of_bools = 0;
	m_query_sz = 0;

	AVR_LOG(11, 1, "Resetting Yices instance for BA[" << m_ba_idx << "] with solver_id [" << m_solver_id << "]" << endl);

	m_config = yices_new_config();
	m_param = yices_new_param_record();

	set_logic();

#ifdef Y2_CTI_MULTICHECKS
	if (queryType == cti)
	  yices_set_config(m_config, "mode", "multi-checks");
	else
#endif
#ifdef Y2_INTERACTIVE
		yices_set_config(m_config, "mode", "interactive");
#else
		yices_set_config(m_config, "mode", "push-pop");
#endif

	m_ctx = yices_new_context(m_config);
	g_ctx = m_ctx;
	set_context_parameters();

	yices_default_params_for_context(m_ctx, m_param);
	set_parameters();

//	m_stack.clear();
	m_constraints.clear();
	m_model = NULL;
	m_cList.clear();
	m_assumptions.clear();
	m_hard_constraints.clear();
#ifdef TRACE_SOLVER
	m_trace.push_back("(reset)");
#endif

	if (queryType == mus_core) {
//		assert(m_y_to_inst);
		m_y_to_inst.clear();
	}
	if (queryType == mus_min) {
//		assert(m_inst_to_y);
		//	m_inst_to_y.clear();
	}

	y2_expr_vec tmp;
	m_cList.push_back(make_pair(m_cList.size() + 1, tmp));

#ifdef ASSERT_DISTINCT_NUMBERS
	if (m_abstract)
	{
		assert_distinct_constants();
	}
#endif

	int diff = m_numpush - m_numpop;
	ASSERT_LIST in = m_asserts;

	m_numpush = 0;
	m_numpop = 0;
	m_asserts.clear();
	push_assert();

	int i = 1;
	bool skipPush = true;
	for (auto& vel: in.assertions) {
		if (!skipPush)
			s_push();
		skipPush = false;

		// add all asserts
		AVR_LOG(11, 1, "[SID:" << m_solver_id << ", SBA:" << m_ba_idx << "]----------" << endl);
	 	init_inst2yices();
		m_constraints.clear();

		for (auto& e: vel)
		{
			add_assert(e);
			if (queryType == mus_min && (i != 1))
			{
				y2_InstToExprM::iterator mit = m_inst_to_y.find(e);
				if (mit != m_inst_to_y.end()) {
					y2_expr_ptr indVar = (*mit).second.first;
					m_constraints.push_back(indVar);
//					s_assert_constraint(indVar);
					continue;
				}
			}
			inst2yices(e);
			force(e);
		}
		s_assert_constraints();

		if (i == 1)
		{
			if (queryType == mus_min)
			{
				if (!m_inst_to_y.empty()) {
					InstL core;
					for (auto& v: m_inst_to_y)
						core.push_back(v.first);
					s_add_core(core, true);
					skipPush = true;
				}
			}

			if (queryType == mus_core)
			{
				s_add_assumptions(in.assumptions, true);
				skipPush = true;
			}
		}

		i++;
	}

	if (m_numpush != diff)
	{
		cout << "diff : " << diff << endl;
		cout << "#push: " << m_numpush << endl;

		print_asserts("new", 15, 0);
		cout << endl;
		copy_asserts(in);
		print_asserts("old", 15, 0);

	}
//	if (queryType != mus_core && queryType != mus_min)
		assert(m_numpush == diff);
}

y2_API::y2_API(Solver::TheoryMapper* m, unsigned ba_idx, bool is_inc, int type) :
	Solver(m, ba_idx, type), is_i(is_inc) {

	y2_solvers[m_solver_id] = this;
	assert(m);

//	yices_enable_log_file("yices.log");
//	yices_set_verbosity(100);

//	if (m_abstract && queryType != cti)
#ifdef Y2_CTI_MULTICHECKS
	if (queryType == cti)
		disable_fallback();
	else
#endif
		enable_fallback();

	m_numpush = 0;
	m_numpop = 0;

	AVR_LOG(11, 1, "Creating new Yices instance for BA[" << m_ba_idx << "] with solver_id [" << m_solver_id << "]" << endl);

	m_config = yices_new_config();
	m_param = yices_new_param_record();

	set_logic();

#ifdef Y2_CTI_MULTICHECKS
	if (queryType == cti)
	  yices_set_config(m_config, "mode", "multi-checks");
	else
#endif
#ifdef Y2_INTERACTIVE
		yices_set_config(m_config, "mode", "interactive");
#else
		yices_set_config(m_config, "mode", "push-pop");
#endif

	m_ctx = yices_new_context(m_config);
	g_ctx = m_ctx;
	set_context_parameters();

	yices_default_params_for_context(m_ctx, m_param);
	set_parameters();

//	m_stack.clear();
	m_constraints.clear();
	m_model = NULL;
	m_cList.clear();
#ifdef TRACE_SOLVER
	m_trace.clear();
#endif

	y2_expr_vec tmp;
	m_cList.push_back(make_pair(m_cList.size() + 1, tmp));

#ifdef ASSERT_DISTINCT_NUMBERS
	if (m_abstract)
	{
		assert_distinct_constants();
	}
#endif
}

y2_API::~y2_API()
{
#ifdef Y2_EXP
  collect_solv_statistic_end();
#endif

	AVR_LOG(11, 1, "Deleting Yices instance for BA[" << m_ba_idx << "] with solver_id [" << m_solver_id << "]" << endl);
	y2_solvers.erase(m_solver_id);

//	m_stack.clear();
	m_constraints.clear();
	m_cList.clear();

	if (m_ctx)
		yices_free_context(m_ctx);
	if (m_config)
		yices_free_config(m_config);
	if (m_param)
		yices_free_param_record(m_param);
	if (m_model != NULL)
		yices_free_model(m_model);
}

void y2_API::enable_var_elim(y2_context ctx) {
	int res = yices_context_enable_option(ctx, "var-elim");
	assert(res == 0);
}

void y2_API::disable_var_elim(y2_context ctx) {
	int res;
//	if (allow_flatten)
//		res = yices_context_disable_option(ctx, "var-elim");
//	else
		res = yices_context_enable_option(ctx, "var-elim");
	assert(res == 0);
}

void y2_API::enable_keep_ite(y2_context ctx) {
	int res = yices_context_enable_option(ctx, "keep-ite");
	assert(res == 0);
}

void y2_API::disable_keep_ite(y2_context ctx) {
	int res = yices_context_disable_option(ctx, "keep-ite");
	assert(res == 0);
}

void y2_API::set_context_parameters(y2_context ctx) {
  if (need_model)
  	disable_var_elim(ctx);
  else
  	enable_var_elim(ctx);

  enable_keep_ite(ctx);

  int res;
	if (m_mapper->fetch_logic() == TheoryMapper::QF_UF) {
//		res = yices_context_enable_option(ctx, "break-symmetries");
		res = yices_context_disable_option(ctx, "break-symmetries");
		assert(res == 0);
	}

	res = yices_context_enable_option(ctx, "flatten");
//	res = yices_context_disable_option(ctx, "flatten");
	assert(res == 0);
	res = yices_context_disable_option(ctx, "learn-eq");
	assert(res == 0);
	res = yices_context_disable_option(ctx, "assert-ite-bounds");
	assert(res == 0);
}

void y2_API::set_parameters(y2_param prm) {
	int res;
	if (Config::g_random)
	{
		unsigned seed = rand();
		string seedString = to_string(seed);
		res = yices_set_param(prm, "random-seed", seedString.c_str());
		assert(res == 0);
	}

//	if (allow_fallback)
//	{
//		unsigned restart_limit = 10;
//		string parString = to_string(restart_limit);
//		res = yices_set_param(prm, "restart-limit", parString.c_str());
//		assert(res == 0);
//	}

	// decision
//	res = yices_set_param(prm, "var-decay", "0.6");
//	assert(res == 0);
//	res = yices_set_param(prm, "randomness", "0.01");
//	assert(res == 0);

	// branching
//	res = yices_set_param(prm, "branching", "theory");
//	assert(res == 0);

	// theory
//	res = yices_set_param(prm, "cache-tclauses", "true");
//	assert (res == 0);
//	res = yices_set_param(prm, "tclause-size", "100");
//	assert (res == 0);
//
//	res = yices_set_param(prm, "dyn-ack", "true");
//	assert (res == 0);
//	res = yices_set_param(prm, "max-ack", "10000");
//	assert (res == 0);
//	res = yices_set_param(prm, "dyn-ack-threshold", "1");
//	assert (res == 0);
//
//	res = yices_set_param(prm, "dyn-bool-ack", "true");
//	assert (res == 0);
//	res = yices_set_param(prm, "max-bool-ack", "10000");
//	assert (res == 0);
//	res = yices_set_param(prm, "dyn-bool-ack-threshold", "1");
//	assert (res == 0);
//
//	res = yices_set_param(prm, "aux-eq-quota", "100000");
//	assert (res == 0);
//	res = yices_set_param(prm, "aux-eq-ratio", "0.5");
//	assert (res == 0);


	// theory-egraph interfacing
//	res = yices_set_param(prm, "optimistic-final-check", "true");
//	assert (res == 0);
//	res = yices_set_param(prm, "max-interface-eqs", "100000");
//	assert (res == 0);
}


std::string y2_API::get_y2_name(Inst*e)
{
	string prefix = "y$";
	string suffix = "";

	switch(get_vIdx())
	{
	case UFBV_V: suffix = "_ufbv"; break;
	case BV_V:   suffix = "_bv";   break;
	}

	string output = "";

#if 0
	if (e->get_type() == Sig)
	{
		SigInst* sig = SigInst::as(e);
		output = prefix + sig->get_name() + suffix;
	}
	else if (e->get_type() == Wire)
  {
    WireInst* w = WireInst::as(e);
    output = prefix + w->get_name() + suffix;
  }
	else if (e->get_type() == Num)
	{
		NumInst* num = NumInst::as(e);
		ostringstream str;
//		cout << "num: " << *num << endl;
		str << prefix << "n" << *(num->get_mpz()) << "s" << num->get_sort().sort2str() << suffix;
		output = str.str();
	}
  else if (e->get_type() == Op)
  {
    OpInst* op = OpInst::as(e);
    Inst* wire = op->get_wire();
    if (wire)
    {
      WireInst* w = WireInst::as(wire);
      output = prefix + w->get_name() + "_op" + suffix;
    }
    else
    {
      ostringstream str;
      str << prefix << e->get_id() << suffix;
      output = str.str();
    }
  }
	else
	{
		ostringstream str;
		str << prefix << e->get_id() << suffix;
		output = str.str();
	}
	replace(output.begin(), output.end(), '\\', '$');
#else
  {
    ostringstream str;
    str << prefix << e->get_id() << suffix;
    output = str.str();
  }
#endif

//	replace(output.begin(), output.end(), '[', '$');
//	replace(output.begin(), output.end(), ']', '$');
//	replace(output.begin(), output.end(), ':', '_');

	Solver::m_nameToInst[output] = e;
	return output;
}

std::string y2_API::get_y2_temp_name(Inst*e, int count) {
//	return to_string(count);
	return to_string(e->get_id()) + (m_abstract?"":"_bv");
//	return to_string(e->get_id()) + "$" + to_string(count);
}


y2_type y2_API::create_bv_sort(pair< unsigned, SORT > sz) {
	y2_type bv;
	y2_IntBvM::iterator it = m_sz_to_bv.find(sz);
	if (it == m_sz_to_bv.end())
	{
		if (sz.second.type == bvtype) {
			if (sz.first == 1)
				bv = yices_bool_type();
			else {
				assert(sz.first > 1);
				bv = yices_bv_type(sz.first);
			}
		}
		else if (sz.second.type == arraytype) {
			SORT& d = sz.second.args.front();
			SORT& r = sz.second.args.back();
			y2_type_ptr dt = create_bv_sort(make_pair(d.sz, d));
			y2_type_ptr rt = create_bv_sort(make_pair(r.sz, r));
#ifndef Y2_ARRAY_ALLOW_BOOL
			if (yices_type_is_bool(dt))
				dt = yices_bv_type(1);
			if (yices_type_is_bool(rt))
				rt = yices_bv_type(1);
#endif
			bv = yices_function_type1(dt, rt);
		}
		else if (sz.second.type == inttype)
			bv = yices_int_type();
		else {
			AVR_LOG(11, 0, "unsupported sort: " << sz.second.type << endl);
			assert(0);
		}
		m_sz_to_bv.insert(make_pair(sz, bv));
		AVR_LOG(11, 2, "inserting conc var type: " << print_type(bv) << " (sz = " << sz.first << ", " << sz.second << ")" << endl);
	}
	else
		bv = (*it).second;
	return bv;
}

y2_type y2_API::create_int_sort(pair< unsigned, SORT > sz, bool dom_bv, bool ran_bv) {
	y2_type ut;
	y2_IntUtM::iterator it = m_sz_to_ut.find(sz);
	if (it == m_sz_to_ut.end())
	{
		if (sz.second.type == bvtype || sz.second.type == inttype) {
			if (sz.first == 1)
				ut = yices_bool_type();
			else {
#ifdef Y2_SCALAR_BUCKETS
				if (sz < sz_to_card.size())
					ut = yices_new_scalar_type(sz_to_card[sz]);
				else
#endif
				ut = yices_new_uninterpreted_type();
			}
		}
		else if (sz.second.type == arraytype) {
			SORT& d = sz.second.args.front();
			SORT& r = sz.second.args.back();
			y2_type_ptr dt = dom_bv ? create_bv_sort(make_pair(d.sz, d)) : create_int_sort(make_pair(d.sz, d));
			y2_type_ptr rt = ran_bv ? create_bv_sort(make_pair(r.sz, r)) : create_int_sort(make_pair(r.sz, r));
#ifndef Y2_ARRAY_ALLOW_BOOL
			if (yices_type_is_bool(dt))
				dt = yices_bv_type(1);
			if (yices_type_is_bool(rt))
				rt = yices_bv_type(1);
#endif
			ut = yices_function_type1(dt, rt);
		}
		else {
			AVR_LOG(11, 0, "unsupported sort: " << sz.second.type << endl);
			assert(0);
		}

#ifdef SET_NAMES
		string typeName = "utt$";
		if (sz.second.type != bvtype) {
			typeName += sz.second.sort2str();
		}
		else {
			typeName += to_string(sz.first);
		}

		yices_set_type_name(ut, typeName.c_str());
#endif
		m_sz_to_ut.insert(make_pair(sz, ut));
//#ifdef TRACE_SOLVER
//			m_trace.push_back("(declare-sort " + print_type(ut) + " 0)");
//#endif
		AVR_LOG(11, 2, "inserting ut var type: " << print_type(ut) << " (sz = " << sz.first << ", " << sz.second << ")" << endl);
	}
	else
		ut = (*it).second;
	return ut;
}

y2_expr y2_API::create_bv_var(std::string name, pair< unsigned, SORT > sz)
{
	y2_expr d;
	y2_StringToDecl::iterator tit = m_var_decs.find(name);
	if (tit == m_var_decs.end())
	{
		y2_type bv = create_bv_sort(sz);
		d = yices_new_uninterpreted_term(bv);
#ifdef SET_NAMES
		yices_set_term_name(d, name.c_str());
#endif
		m_var_decs[name] = d;
//#ifdef TRACE_SOLVER
//		m_trace.push_back("(declare-fun " + print_smt_term(d) + " () " + print_smt_type(bv) + ")");
//#endif
		AVR_LOG(11, 2, "creating conc var: " << print_term(d) << " (sz = " << sz.first << ", " << sz.second << ")" << endl);
	}
	else
	{
		d = (*tit).second;
	}
	return d;
}

y2_expr y2_API::create_int_var(std::string name, pair< unsigned, SORT > sz, bool dom_bv, bool ran_bv)
{
	y2_expr d;
	y2_StringToDecl::iterator tit = m_var_decs.find(name);
	if (tit == m_var_decs.end())
	{
		y2_type ut = create_int_sort(sz, dom_bv, ran_bv);
		d = yices_new_uninterpreted_term(ut);
#ifdef SET_NAMES
		yices_set_term_name(d, name.c_str());
#endif
		m_var_decs[name] = d;
//#ifdef TRACE_SOLVER
//		m_trace.push_back("(declare-fun " + print_smt_term(d) + " () " + print_smt_type(ut) + ")");
//#endif
		AVR_LOG(11, 2, "creating ut var: " << print_term(d) << " (sz = " << sz.first << ", " << sz.second << ")" << endl);
	}
	else
	{
		d = (*tit).second;
	}
	return d;
}

y2_expr y2_API::create_bool_var(std::string name)
{
	y2_expr d;
	y2_StringToDecl::iterator tit = m_var_decs.find(name);
	if (tit == m_var_decs.end())
	{
		y2_type bt = yices_bool_type();
		d = yices_new_uninterpreted_term(bt);
#ifdef SET_NAMES
		yices_set_term_name(d, name.c_str());
#endif
		m_var_decs[name] = d;
//#ifdef TRACE_SOLVER
//		m_trace.push_back("(declare-fun " + print_smt_term(d) + " () " + print_smt_type(bt) + ")");
//#endif
		AVR_LOG(11, 2, "creating bool var: " << print_term(d) << endl);
	}
	else
	{
    d = (*tit).second;
	}
	return d;
}

void y2_API::print_constraints(int loc, int level)
{
	AVR_LOG(loc, level, "\nConstraints:" << endl);
	for (auto& cit : m_cList)
	{
		int idx = cit.first;
		AVR_LOG(loc, level, "[" << idx << "]" << endl);
		for (auto& y : cit.second)
		{
			string name = print_term(y);
			if (Solver::m_nameToInst.find(name) != Solver::m_nameToInst.end())
			{
				AVR_LOG(loc, level, name << "\t\t(i.e. " << *(Solver::m_nameToInst[name]) << ")" << endl);
			}
			else
			{
//				AVR_LOG(loc, level, print_term(y) << endl);
			}
		}
		AVR_LOG(loc, level, endl);
	}
	AVR_LOG(loc, level, endl);
}

#ifdef Y2_EXP
void y2_API::dump_core(void)
{
  yices_derive_unsat_core(m_ctx);
  y2_dump_context(stdout, m_ctx);
}
#endif

void y2_API::add_yices_func(y2_expr& var, string op, bool pred, y2_expr_list& ch, Ints& sz, Inst* e)
{
	assert(m_mapper->fetch_logic() == TheoryMapper::QF_UF || m_mapper->fetch_logic() == TheoryMapper::QF_UFBV);
	assert(m_abstract);

	y2_expr func;
	pair <Inst*, string> typeKey = make_pair(e, op);
	y2_InstToFuncDecl::iterator tit = m_func_decs.find(typeKey);
	if (tit == m_func_decs.end())
	{
		ostringstream str;
		str << op;
		str << "_" << e->get_size();
		for (Ints::iterator it = sz.begin(), end_it = sz.end(); it != end_it; ++it)
		{
			str << "_" << *it;
		}
		op = str.str();

		y2_expr funct;
		y2_StringToFunctM::iterator it = m_funct.find(op);
		if (it == m_funct.end())
		{
			y2_type target;
			if (var == Y2_INVALID_EXPR) {
				// first, what type of variable should we allocate
				if (m_mapper->fetch_var(e) == TheoryMapper::BV_VAR) {
					target = create_bv_sort(make_pair(e->get_size(), e->get_sort()));
				}
				else if (m_mapper->fetch_var(e) == TheoryMapper::EUF_VAR) {
					target = create_int_sort(make_pair(e->get_size(), e->get_sort()));
				}
				else if (m_mapper->fetch_var(e) == TheoryMapper::BOOL_VAR) {
					target = yices_bool_type();
				}
				else {
					assert(0);
				}
			}
			else {
				target = yices_type_of_term(var);
			}
//			bool extract = op.find("Extract") != string::npos;

			y2_type domain[ch.size()];
			{
				unsigned i = 0;
				for (y2_expr_list::iterator it = ch.begin(), end_it = ch.end(); it != end_it; ++it)
				{
					y2_expr_ptr tmp = *it;
					domain[i] = yices_type_of_term(tmp);
					i++;
				}
			}
			y2_type functt = yices_function_type(ch.size(), domain, target);
			funct = yices_new_uninterpreted_term(functt);
#ifdef SET_NAMES
			yices_set_term_name(funct, op.c_str());
#endif
			m_funct.insert(make_pair(op, funct));
//			cout << op << endl;
//			cout << *e << endl;
			AVR_LOG(11, 3, "inserting function template: " << print_term(funct) << " of type " << print_type(functt) << endl);
		}
		else
			funct = (*it).second;

		InstL::const_iterator cit = e->get_children()->begin();
		y2_expr args[ch.size()];
		unsigned i = 0;
		for (y2_expr_list::iterator it = ch.begin(), end_it = ch.end(); it != end_it; ++it, ++i, ++cit)
		{
			args[i] = *it;
		}
		func = yices_application(funct, ch.size(), args);
		m_func_decs[typeKey] = func;
		if (func == -1)
		{
			cout << *e << endl;
			cout << "present type: " << (it != m_funct.end()) << endl;
			{
				int i = 0;
				for (auto& ch: (*e->get_children())) {
					cout << i++ << ": " << *ch << endl;
					ch->y2_node.print();
				}
			}
			{
				int i = 0;
				for (auto& arg: args)
					cout << i++ << ": " << arg << endl;
			}
			{
				for (int i = ch.size() - 1; i >= 0; i--)
					cout << i << ": " << print_term(args[i]) << endl;
			}
		}
		assert(func != -1);
		AVR_LOG(11, 3, "creating function application: " << print_term(func) << " of type " << print_term(funct) << endl);
	}
	else
	{
		func = (*tit).second;
	}

	if (func == -1)
	{
		cout << *e << endl;
		cout << "present: " << (tit != m_func_decs.end()) << endl;
	}
	assert(func != -1);

	add_gate_constraint(var, func, "func link", e, false, false);

//	// change domain and target from int to BV!
//	if (res_sz > 0)
//	{
//		assert(0);
//		yices_type boolt = yices_bool_type();
//		yices_type intt = utt;
//		yices_type target = pred ? boolt : intt;
//		yices_type domain[ch.size()];
//
//		target = yices_bv_type(res_sz);
//		unsigned i = 0;
//		if (extract)
//		{
//			Ints::iterator it = sz.begin();
//			it++;
//			it++;
//			domain[0] = yices_bv_type(*it);
//		}
//		else
//		{
//			for (Ints::iterator it = sz.begin(), end_it = sz.end(); it != end_it; ++it, i++)
//			{
//				domain[i] = yices_bv_type(*it);
//			}
//		}
//	}
}

#ifdef TEST_CONNECT_BV
y2_expr_ptr y2_API::u2b(int sz, Inst* e_orig) {
  Inst* e = e_orig->get_port();

  y2_expr_ptr in = e->y2_node.solv_var[get_vIdx()];
  y2_expr& out = e->y2_node.solv_var[get_connectIdx()];
  if (e->y2_node.solv_vset[get_connectIdx()])
    return out;

  out = create_bv_var(get_y2_name(e) + "_u2b", sz);
  if (sz == 1) {
    assert (yices_term_is_bool(in));

    if (in == m_b1)
      out = m_v1;
    else if (in == m_b0)
      out = m_v0;
    else
      out = yices_ite(in, m_v1, m_v0);
  }
  else {
    assert (!yices_term_is_bitvector(in));
    string ufName = "U2B_" + to_string(sz);
    AVR_LOG(11, 7, "(converting " << *e << " to bv)" << endl);
    add_conversion_func(out, ufName, in, sz, e);

//    y2_expr_ptr uf2 = create_int_var(get_y2_name(e) + "_conn", sz);
//    ufName = "B2U_" + to_string(sz);
//    AVR_LOG(11, 7, "(converting " << *e << " to ut)" << endl);
//    add_conversion_func(uf2, ufName, out, sz, e);
//    y2_expr_ptr eq = yices_eq(in, uf2);
//    if (eq == Y2_INVALID_EXPR) {
//      cout << print_term(in) << endl;
//      cout << print_term(uf2) << endl;
//    }
//    assert(eq != Y2_INVALID_EXPR);
//    add_constraint(eq, "u2b constraint", e);
  }
  e->y2_node.solv_vset[get_connectIdx()] = true;
  if (e_orig != e) {
    e_orig->y2_node.solv_var[get_connectIdx()] = out;
    e_orig->y2_node.solv_vset[get_connectIdx()] = true;
  }
  assert(out != Y2_INVALID_EXPR);
  return out;
}

y2_expr_ptr y2_API::b2u(int sz, Inst* e_orig) {
  Inst* e = e_orig->get_port();

  y2_expr_ptr in = e->y2_node.solv_var[get_vIdx()];
  y2_expr& out = e->y2_node.solv_var[get_connectIdx()];
  if (e->y2_node.solv_vset[get_connectIdx()])
    return out;

  assert (yices_term_is_bitvector(in));
  if (sz == 1) {
    out = create_bool_var(get_y2_name(e) + "_b2u");
    if (in == m_v1)
      out = m_b1;
    else if (in == m_v0)
      out = m_b0;
    else
      out = yices_eq(in, m_v1);
  }
  else {
    out = create_int_var(get_y2_name(e) + "_b2u", sz);
    string ufName = "B2U_" + to_string(sz);
    AVR_LOG(11, 7, "(converting " << *e << " to ut)" << endl);
    add_conversion_func(out, ufName, in, sz, e);

//    y2_expr_ptr bv2 = create_bv_var(get_y2_name(e) + "_conn", sz);
//    ufName = "U2B_" + to_string(sz);
//    AVR_LOG(11, 7, "(converting " << *e << " to bv)" << endl);
//    add_conversion_func(bv2, ufName, out, sz, e);
//    y2_expr_ptr eq = yices_eq(in, bv2);
//    assert(eq != Y2_INVALID_EXPR);
//    add_constraint(eq, "b2u constraint", e);
  }
  e->y2_node.solv_vset[get_connectIdx()] = true;
  if (e_orig != e) {
    e_orig->y2_node.solv_var[get_connectIdx()] = out;
    e_orig->y2_node.solv_vset[get_connectIdx()] = true;
  }
  assert(out != Y2_INVALID_EXPR);
  return out;
}

void y2_API::add_conversion_func(y2_expr& out, std::string op, y2_expr_ptr ch, int sz, Inst* e) {
  assert(m_abstract);

  y2_expr funct;
  y2_StringToFunctM::iterator it = m_funct.find(op);
  if (it == m_funct.end())
  {
    y2_type target = yices_type_of_term(out);
    y2_type domain[1];
    domain[0] = yices_type_of_term(ch);
    y2_type functt = yices_function_type(1, domain, target);
    funct = yices_new_uninterpreted_term(functt);
    yices_set_term_name(funct, op.c_str());
    m_funct.insert(make_pair(op, funct));
    AVR_LOG(11, 3, "inserting function template: " << print_term(funct) << " of type " << print_type(functt) << endl);
  }
  else
    funct = (*it).second;

  y2_expr args[1];
  args[0] = ch;
  out = yices_application(funct, 1, args);

  if (out == -1)
  {
    cout << *e << endl;
  }
  assert(out != -1);
  AVR_LOG(11, 3, "creating function application: " << print_term(out) << " of type " << print_term(funct) << endl);
}
#endif

bool y2_API::check_sat(Inst* e, long timeout_value, bool getModel)
{
	AVR_LOG(11, 1, "[SID:" << m_solver_id << ", SBA:" << m_ba_idx << "]----------" << endl);

	init_inst2yices();
	inst2yices(e);
	force(e);
	add_assert(e);

//	check_sat_cnt++;

	// add the constraints to YICES
	s_assert_constraints();
//	for (YicesAPIBAV::iterator it = m_constraints.begin(), end_it = m_constraints.end(); it != end_it; ++it)
//	{
//		yices_assert_formula(m_ctx, *it);
//	}

	AVR_LOG(11, 3, "calling YICES" << endl);
  int res;
  if (m_abstract)
    res = s_check(timeout_value, getModel);
  else
    res = s_check(timeout_value, getModel);

  if (res == AVR_QSAT)
    return true;
  else if (res == AVR_QUSAT)
    return false;
  else
    assert(0);
}

void y2_API::add_variable(y2_expr& lhs, Inst*e) {
	if (lhs == Y2_INVALID_EXPR) {
		string name = get_y2_name(e);
		if (m_mapper->fetch_var(e) == TheoryMapper::BOOL_VAR) {
			lhs = create_bool_var(name);
		} else {
			if (m_mapper->fetch_logic() == TheoryMapper::QF_UFBV && e->get_sort_type() == arraytype) {
				if (m_mapper->fetch_op(e) == TheoryMapper::BV_OP) {
					lhs = create_bv_var(name, make_pair(e->get_size(), e->get_sort()));
				}
				else if (m_mapper->fetch_var(e) == TheoryMapper::BV_VAR) {
					lhs = create_int_var(name, make_pair(e->get_size(), e->get_sort()), false, true);
				}
				else if (e->ab_interpret.input_concrete()) {
					lhs = create_int_var(name, make_pair(e->get_size(), e->get_sort()), true, false);
				}
				else {
					lhs = create_int_var(name, make_pair(e->get_size(), e->get_sort()));
				}
			}
			else {
				// first, what type of variable should we allocate
				if (m_mapper->fetch_var(e) == TheoryMapper::BV_VAR) {
					lhs = create_bv_var(name, make_pair(e->get_size(), e->get_sort()));
				}
				else if (m_mapper->fetch_var(e) == TheoryMapper::EUF_VAR) {
					lhs = create_int_var(name, make_pair(e->get_size(), e->get_sort()));
				}
				else {
					assert(0);
				}
			}
		}

	}
}

void y2_API::add_gate_constraint(y2_expr& lhs, y2_expr_ptr rhs, std::string comment, Inst*e, bool asConstraint, bool checkType) {
	assert(rhs != Y2_INVALID_EXPR);

	if (checkType) {
		if (e->get_sort_type() == bvtype) {
			if (e->get_size() == 1) {
	      if (yices_term_is_bitvector(rhs))
	        rhs = yices_eq(rhs, m_v1);
			}
		}
	}

	bool directConnect = !asConstraint && !allow_flatten;
	if (directConnect) {
		if (e->get_size() == 1) {
			switch (e->get_type()) {
			case Op:
			case Ex:
			{
//				if ((e->level % 5) == 4)
					directConnect = false;
			}
			break;
			}
		}
	}

  if (directConnect)
  	lhs = rhs;
  else {
		add_variable(lhs, e);
		assert(lhs != Y2_INVALID_EXPR);

    if (yices_term_is_bool(lhs)) {
      if (yices_term_is_bitvector(rhs))
        rhs = yices_eq(rhs, m_v1);
    }
    else if (yices_term_is_bitvector(lhs)) {
      if (yices_term_is_bool(rhs))
        rhs = yices_ite(rhs, m_v1, m_v0);
    }

    if (yices_type_of_term(lhs) != yices_type_of_term(rhs)) {
    	cout << "inconsistent term types for node " << *e << endl;
    	cout << "lhs: " << print_term(lhs) << " of type " << print_type(yices_type_of_term(lhs)) << endl;
    	cout << "rhs: " << print_term(rhs) << " of type " << print_type(yices_type_of_term(rhs)) << endl;
    	assert(0);
    }
  	add_constraint(yices_eq(lhs, rhs), comment, e, true, false);
  }
//  cout << *e << "\t" << print_term(lhs) << endl;
}

void y2_API::add_constraint(y2_expr_ptr y, string comment, Inst*e, bool storeC, bool forced)
{
	if (y == -1)
	{
		cout << *e << endl;
		cout << e->get_size() << endl;
		cout << m_abstract << endl;
		cout << comment << endl;
		cout << get_vIdx() << endl;
		cout << get_cIdx() << endl;
		yices_print_error(stdout);
		assert(0);
	}

	if (m_cache_hard && !forced) {
		if (m_hard_constraints.find(y) == m_hard_constraints.end()) {
			m_constraints.push_back(y);
			if (m_numpush == 0) {
				m_hard_constraints.insert(y);
				AVR_LOG(11, 4, "     inserting (" << comment << "): " << print_term(y) << endl);
			}
		}
		else {
			AVR_LOG(11, 4, "       present (" << comment << "): " << print_term(y) << endl);
		}
	}
	else
		m_constraints.push_back(y);

	if (e != 0)
	{
		if (storeC)
		{
			unsigned cIdx = get_cIdx();
			e->y2_node.y2_constraints[cIdx].push_back(y);
//			if (m_solver_id == 21)
			AVR_LOG(11, 2, "     storing (" << comment << "): " << print_term(y) << " for " << *e << endl);
		}
		else
		{
//			if (m_solver_id == 21)
			AVR_LOG(11, 3, "     adding constraints (" << comment << "): " << print_term(y) << " for " << *e << endl);
		}
	}
	else
	{
//		if (m_solver_id == 21)
		AVR_LOG(11, 3, "     adding constraints (" << comment << "): " << print_term(y) << endl);
	}
}

void y2_API::force(Inst* e)
{
	if (m_mapper->fetch_var(e) == TheoryMapper::BV_VAR)
	{
		add_constraint(e->y2_node.solv_var(get_vIdx()), "forcing for BV", e, false, true);
	}
	else if (m_mapper->fetch_var(e) == TheoryMapper::BOOL_VAR)
	{
		add_constraint(e->y2_node.solv_var(get_vIdx()), "forcing for BOOL", e, false, true);
	}
	else if (m_mapper->fetch_var(e) == TheoryMapper::EUF_VAR)
	{
		assert(0);
	}
	else
		assert(0);
}

y2_expr y2_API::force_wo_add(Inst* e)
{
	if (m_mapper->fetch_var(e) == TheoryMapper::BV_VAR)
	{
		return e->y2_node.solv_var(get_vIdx());
	}
	else if (m_mapper->fetch_var(e) == TheoryMapper::BOOL_VAR)
	{
		return e->y2_node.solv_var(get_vIdx());
	}
	else if (m_mapper->fetch_var(e) == TheoryMapper::EUF_VAR)
	{
		assert(0);
	}
	else
	{
		assert(0);
	}
}

int y2_API::s_assert_constraint(y2_expr_ptr ye)
{
#ifdef DO_CORRECTNESS_CHECKS
		assert(m_cList.size() >= 1);
#endif
	pair< int, y2_expr_vec>& tmp = m_cList.back();

  AVR_LOG(17, 7, "(assert " << print_term(ye) << " )" << endl);
	int res = yices_assert_formula(m_ctx, ye);

	tmp.second.push_back(ye);
#ifdef TRACE_SOLVER
	m_trace.push_back("(assert " + print_smt_term(ye) + ")");
#endif
	m_query_sz += 1;

	if (res != 0)
		yices_print_error(stdout);

	assert (res == 0);
	return res;
}

void y2_API::s_assert_constraints(y2_expr_ptr indVar, bool reset)
{
//	struct rusage usage;
//	struct timeval start_time, end_time;
//	long long time_diff;
//
//	TIME_S(start_time);

#ifdef DO_CORRECTNESS_CHECKS
	assert(m_cList.size() >= 1);
#endif
	pair< int, y2_expr_vec>& tmp = m_cList.back();

	int sz = m_constraints.size();

	if (sz != 0) {
		int res = 0;
		if (indVar == Y2_INVALID_EXPR)
		{
			for (auto& ye: m_constraints)
			{
				AVR_LOG(11, 8, "(assert " << print_term(ye) << " )" << endl);
			}
			/// Assumed std::vector guarantees continuous memory allocation
			res = yices_assert_formulas(m_ctx, sz, &(m_constraints.front()));
		}
		else
		{
			for (auto& c: m_constraints)
			{
				y2_expr_ptr ye = yices_implies(indVar, c);
				AVR_LOG(11, 8, "(assert " << print_term(ye) << " )" << endl);

				int resTmp = yices_assert_formula(m_ctx, ye);
				if (resTmp != 0)
					res = resTmp;
			}
		}

		if (res != 0)
		{
			yices_print_error(stdout);
			cout << "status: " << yices_context_status(m_ctx) << endl;
			for (auto& t: m_constraints)
			{
				cout << t << endl;
				cout << print_term(t) << "\t" << print_type(yices_type_of_term(t)) << endl;
			}
		}
		assert(res == 0);

		for (auto& c : m_constraints) {
			tmp.second.push_back(c);
#ifdef TRACE_SOLVER
			m_trace.push_back("(assert " + print_smt_term(c) + ")");
#endif
		}

		m_query_sz += sz;

		if (reset)
			m_constraints.clear();
	}
//  TIME_E(start_time, end_time, Solver::time_tmp);
}

int y2_API::forward_propagation(long timeout_value, int frame_idx, InstL& forwarded,
		vector<vector<CLAUSE>>& cubes, void *inst)
{
	//clock_t ref_time = clock();
	int next_frame_idx = frame_idx + 1;
	num_scalls_sat_fp_non_accum = 0;
	num_scalls_unsat_fp_non_accum = 0;
	num_scalls_contained_fp_non_accum = 0;

	long timeout_value_original = timeout_value;

	vector<CLAUSE>::iterator it_c = cubes[frame_idx].begin();
	while (it_c != cubes[frame_idx].end())
	{
		Inst* cube = (*it_c).cube;
		Inst *ve_next_c = Inst::all_pre2next(cube);

		InstL conjunct_query;
		InstS relevantNext;
		Inst::collect_next_reg(ve_next_c, relevantNext, true);
		for (auto& sigNext : relevantNext)
		{
			conjunct_query.push_back(Inst::fetch_trelation(sigNext));
		}

		int res = AVR_QTO;
		res = s_check(AB_QUERY_TIMEOUT, false);
		if (res != AVR_QUSAT) {

#if 0
		m_constraints.clear();
		s_push();

		init_inst2yices();
		for (auto& c: conjunct_query)
		{
			inst2yices(c);
			force(c);
			add_assert(c);
		}
    inst2yices(ve_next_c);
    force(ve_next_c);
    add_assert(ve_next_c);

		s_assert_constraints();
		res = s_check(AB_QUERY_TIMEOUT, false);
		s_pop();
#ifdef DO_CORRECTNESS_CHECKS
		assert(m_numpush == m_numpop);
#endif
#else
		conjunct_query.push_back(ve_next_c);
		s_assert_retractable(conjunct_query);
		res = s_check_assume(AB_QUERY_TIMEOUT, false);
		s_retract_assertions();
#endif
		}

		if (res == AVR_QSAT)
		{
			//SAT i.e. not contained
			num_scalls_sat_fp_non_accum++;
			num_scalls_sat_fp++;
			AVR_LOG(3, 2, "ve_fp: SAT		:"
					<< " i_" << frame_idx
					<< " c_" << num_scalls_contained_fp_non_accum
					<< " s_" << num_scalls_sat_fp_non_accum
					<< " u_" << num_scalls_unsat_fp_non_accum << endl);
//			AVR_LOG(15, 0, "\t\tNot forwarding " << *(*it_c) <<	" from F[" << frame_idx << "] to F[" << next_frame_idx << "]" << endl);
			it_c++;
			continue;
		}
		else
//			assert(res == z3::unsat);
			assert(res == AVR_QUSAT);

		CLAUSE& blockC = (*it_c);

		/// Aman Test
//		int origSz = conjunct_dest.size();
//		InstLL muses;
//		int resMus = get_muses_2(AB_QUERY_TIMEOUT, conjunct_dest, muses, Solver::num_ab_sat_mus, Solver::num_ab_unsat_mus);
//		assert(resMus == 1);
//		assert(!muses.empty());
//		Inst* blockExpand = all_next2pre(inst, OpInst::create(OpInst::LogAnd, muses.front()), true);
//		int newSz = muses.front().size();
//		if (newSz < origSz)
//		{
//			AVR_LOG(15, 0, "\t\t(" << origSz << " -> " << newSz << endl);
//			AVR_LOG(15, 0, "\t\tBlocking " << *blockExpand << " instead of " << *blockC  << endl);
//			blockC = blockExpand;
//		}
		/// END


		num_scalls_unsat_fp++;
		num_scalls_unsat_fp_non_accum++;

		AVR_LOG(3, 2, "ve_fp: UNSAT		:"
				<< " i_" << frame_idx
				<<  " c_" << num_scalls_contained_fp_non_accum
				<< " s_" << num_scalls_sat_fp_non_accum
				<< " u_" << num_scalls_unsat_fp_non_accum << endl);

    vector<CLAUSE>& fd = cubes[next_frame_idx];
    size_t j = 0;
    for (size_t i = 0; i < fd.size(); ++i) {
        if (!blockC.subsumes(fd[i])) {
            fd[j++] = fd[i];
        } else {
            ++CLAUSE::_numSubsumedCube;
        }
    }
    fd.resize(j);

		AVR_LOG(15, 2, "\t\tForwarding " << *blockC.clause <<
				" from F[" << frame_idx << "] to F[" << next_frame_idx << "]" << endl);
		cubes[next_frame_idx].push_back(blockC);
		forwarded.push_back(cube);
		it_c = cubes[frame_idx].erase(it_c);
		timeout_value = timeout_value_original;
	}
	return 1;
}

y2_result y2_API::query_non_inc(long timeout_value, bool getModel)
{
	smt_status_t correct_res = s_check_inc(timeout_value, getModel);

	y2_API* ni_solver = new y2_API(m_mapper, m_ba_idx, static_cast<int>(1), queryType);
  ni_solver->copy_asserts(m_asserts);
	for (auto& l: m_cList)
	{
		for (auto& c: l.second)
			ni_solver->s_assert_constraint(c);
	}
	smt_status_t res = ni_solver->s_check_inc(timeout_value, getModel);

	if (res != correct_res)
	{
		cout << "inc: " << correct_res << endl;
		cout << "ninc: " << res << endl;

//		y2_API* ni_solver2 = new y2_API(m_mapper, 0, static_cast<int>(1));
//		smt_status res2 = STATUS_UNKNOWN;
//		for (auto& l: m_cList)
//		{
//			for (auto& c: l.second)
//			{
//				cout << print_term(c) << endl;
//				ni_solver2->s_assert_constraint(c);
//				res2 = ni_solver2->s_check_inc(timeout_value);
//				if (res2 == STATUS_UNSAT)
//					break;
//			}
//			if (res2 == STATUS_UNSAT)
//				break;
//		}
//		cout << "n2inc: " << res2 << endl;

//		ni_solver->print_constraints();
		string fname = "error/" + _benchmark;
		ni_solver->print_y2(fname);
		assert(0);
	}

	delete ni_solver;
	return res;
}

int y2_API::get_mus(long timeout_value, InstL& vel, InstL& mus, int& numSat, int& numUnsat, bool recordTime)
{
	int qType_orig = queryType;
	queryType = mus_min;

  struct rusage usage;
  struct timeval start_time, end_time;
  long long time_diff;
  long long time_res = 0;

	unsigned sz = vel.size();
	AVR_LOG(17, 2, "\tEntering MUS core extraction from Y2" << endl);
	AVR_LOG(17, 5, "\t[Input]: " << vel << " (sz: " << sz << ")" << endl);
	assert(!vel.empty());

	int res = -1;

	m_constraints.clear();
	y2_InstToExprM& inst_to_y = m_inst_to_y;
	inst_to_y.clear();

	InstL stack;
//	m_stack2.clear();

	int initialPush = false;
	s_push();
	initialPush = true;

	int count = 0;
	InstL queue;
  y2_expr_vec constraints;
	for (InstL::iterator it = vel.begin(); it != vel.end(); it++)
	{
		init_inst2yices();
		inst2yices(*it);
		force(*it);

		string iName = "_q_$" + get_y2_temp_name(*it, count);
    y2_expr_ptr indVar = create_bool_var(iName);

		AVR_LOG(17, 5, "\t\t\t(inst: " << *(*it) << ", indicator: " << print_term(indVar) << ")" << endl);
		if (!m_constraints.empty())
		{
			AVR_LOG(17, 7, "\t\t\t\t(assertions " << print_term(indVar) << " => " << print_terms(m_constraints) << endl);
      for (auto& c: m_constraints)
        constraints.push_back(yices_implies(indVar, c));
      m_constraints.clear();
		}
		queue.push_back(*it);
		inst_to_y[*it] = make_pair(indVar, Y2_INVALID_EXPR);

    count++;
	}
  m_constraints.swap(constraints);

	assert (!m_constraints.empty());

	{
//		for (auto& c: m_constraints)
//			cout << print_term(c) << endl;

		s_assert_constraints();
	}

//	cout << vel_2 << endl;

	for (InstL::iterator sit = queue.begin(); sit != queue.end(); sit++)
	{
		smt_status_t result = yices_context_status(m_ctx);
		if (result == STATUS_UNSAT)
		{
			AVR_LOG(17, 5, "\t\t(breaking before " << print_term(inst_to_y[*sit].first) << ")" << endl);
			break;
		}

		s_push();
//		cout << "(push)" << endl;

		y2_expr_ptr indVar = inst_to_y[*sit].first;
		s_assert_constraint(indVar);
		stack.push_front(*sit);
		add_assert(*sit);
	}

  TIME_S(start_time);
	smt_status_t initial_res = s_check_inc(timeout_value, false);
  TIME_E(start_time, end_time, time_res);
//  clear_assume();
  AVR_LOG(17, 5, "\t\t(initial-check) " << initial_res << endl);

	InstL satBucket;
	if (initial_res == STATUS_UNSAT)
	{
		numUnsat++;
		if (recordTime)
		{
	    time_unsat_min_muses_reach += time_diff;
	    if (time_diff > time_max_unsat_min_muses_reach)
	      time_max_unsat_min_muses_reach = time_diff;
		}

		m_constraints.clear();
		while(!stack.empty())
		{
			s_pop();

			Inst* currInst = stack.front();
			stack.pop_front();
			AVR_LOG(17, 5, "curr: " << *currInst << endl);
//			y2_expr curr = inst_to_y[currInst].first;
//			AVR_LOG(17, 6, "stack: " << print_terms(m_stack2) << endl);

			bool pushed = !mus.empty();

			if (pushed) {
				s_push();
	//			cout << "(mpush)" << endl;
	//			result2 = yices_context_status(m_ctx);
	//			cout << "status_mpush: " << result2 << endl;

	//			for (auto& v: stack) {
	//				add_assert(v);
	//			}
				for (auto& v: mus) {
					pair < y2_expr, y2_expr > p = inst_to_y[v];
					m_constraints.push_back(p.first);
					add_assert(v);
				}
				s_assert_constraints();
			}

//			s_assert_constraints(false);

		  TIME_S(start_time);
			smt_status_t result = s_check_inc(timeout_value, false);
		  TIME_E(start_time, end_time, time_res);
			AVR_LOG(17, 5, "status_check: " << result << endl);

			if (result == STATUS_UNSAT)
			{
				numUnsat++;
				assert(result == STATUS_UNSAT);
		    if (recordTime)
		    {
		      time_unsat_min_muses_reach += time_diff;
		      if (time_diff > time_max_unsat_min_muses_reach)
		        time_max_unsat_min_muses_reach = time_diff;
		    }
			}
			else
			{
				if (result != STATUS_SAT)
				{
					assert(result == STATUS_INTERRUPTED);
					cout << "Timeout while deriving MUS_a" << endl;
					cout << "Core: " << vel << endl;
					assert(0);
				}
				else
					numSat++;

		    if (recordTime)
		    {
	        time_sat_min_muses_reach += time_diff;
	        if (time_diff > time_max_sat_min_muses_reach)
	          time_max_sat_min_muses_reach = time_diff;
		    }

				mus.push_back(currInst);
				currInst->bump_activity();

//				assert(curr != -1);
//				m_constraints.push_back(curr);
				AVR_LOG(17, 5, "adding to mus: " << *currInst << endl);
			}
			if (pushed)
				s_pop();
		}
		m_constraints.clear();

		if (mus.empty())
		{
			cout << "warning: mus.empty()" << endl;
      mus.push_back(vel.front());
//      assert(0);
		}
		res = 1;
	}
	else
	{
//		cout << "SAT" << endl;
//		print_query(0, ERROR, "error2");
//		if (!m_abstract)
//			yices_print_model(stdout, m_model);

		numSat++;
		assert(initial_res == STATUS_SAT);
    if (recordTime)
    {
      time_sat_min_muses_reach += time_diff;
      if (time_diff > time_max_sat_min_muses_reach)
        time_max_sat_min_muses_reach = time_diff;
    }

		while(!stack.empty())
		{
			s_pop();
			stack.pop_front();
		}
		res = 0;			//the given formula is SAT, i.e. there's no MUS
	}

	if (initialPush)
		s_pop();

#ifdef DO_CORRECTNESS_CHECKS
	assert(m_numpush == m_numpop);
#endif

	queryType = qType_orig;
	return res;
}

#if 1
int y2_API::find_unsat_core(long timeout_value, InstL& hardQ, InstL& vel, InstL& mus, int& numSat, int& numUnsat)
{
  m_constraints.clear();
  init_inst2yices();
  if (!hardQ.empty())
    s_assert(OpInst::create(OpInst::LogAnd, hardQ));
  int result = get_unsat_core(timeout_value, vel, mus, numSat, numUnsat);
  return result;
}
#else
int y2_API::find_unsat_core(long timeout_value, InstL& hardQ, InstL& vel, InstLL& muses, int& numSat, int& numUnsat)
{
  InstL core;

  queryType = mus_core;

  struct rusage usage;
  struct timeval start_time, end_time;
  long long time_diff;
  long long time_res;

  assert(m_abstract);

  unsigned sz = vel.size();
  AVR_LOG(17, 5, "\tEntering unsat core extraction from Y2" << endl);
  AVR_LOG(17, 5, "\t[Input]: " << vel << " (sz: " << sz << ")" << endl);
  assert(!vel.empty());

  yices_enable_unsat_core(m_ctx);

  int res = -1;

  m_constraints.clear();
  list<y2_expr> stack;
  map<y2_expr, Inst*> y_to_inst;
  list<y2_expr> coreStack;

  init_inst2yices();
  if (!hardQ.empty())
    s_assert(OpInst::create(OpInst::LogAnd, hardQ));

  int initialPush = false;

  int count = 0;
  list<y2_expr> queue;
  y2_expr_vec constraints;
  for (InstL::iterator it = vel.begin(); it != vel.end(); it++)
  {
    init_inst2yices();
    inst2yices(*it);
    force(*it);

    string iName = "p$" + to_string(count);
    y2_expr_ptr indVar = create_bool_var(iName, false);

    AVR_LOG(17, 5, "\t\t\t(inst: " << *(*it) << ", indicator: " << print_term(indVar) << ")" << endl);
    if (!m_constraints.empty())
    {
      AVR_LOG(17, 7, "\t\t\t\t(assertions " << print_term(indVar) << " => " << print_terms(m_constraints) << endl);
      for (auto& c: m_constraints)
        constraints.push_back(yices_implies(indVar, c));
      m_constraints.clear();
    }

    queue.push_back(indVar);
    y_to_inst[indVar] = (*it);
    count++;
  }
  m_constraints.swap(constraints);

  if (!m_constraints.empty())
  {
    s_push();
    initialPush = true;
    s_assert_constraints();
  }

  s_push();

  for (list<y2_expr>::iterator sit = queue.begin(); sit != queue.end(); sit++)
  {
    smt_status_t result = yices_context_status(m_ctx);
    if (result == STATUS_UNSAT)
    {
      AVR_LOG(17, 5, "\t\t(breaking before " << print_term(*sit) << ")" << endl);
      break;
    }

    y2_expr_ptr indVar = (*sit);
    s_assert_constraint(indVar);
    stack.push_front(indVar);
    add_assume(y_to_inst[indVar]);
  }

  TIME_S(start_time);
  smt_status_t initial_res = s_check_inc(timeout_value, false);
  TIME_E(start_time, end_time, time_res);
  AVR_LOG(17, 5, "\t\t(initial-check) " << initial_res << endl);

  InstL satBucket;
  if (initial_res == STATUS_UNSAT)
  {
    numUnsat++;
    time_unsat_core_muses_reach += time_diff;
    if (time_diff > time_max_unsat_core_muses_reach)
      time_max_unsat_core_muses_reach = time_diff;

    int core_status = yices_derive_unsat_core(m_ctx);
    if (core_status != 0) {
      yices_print_error(stdout);
    }
    assert (core_status == 0);
//    y2_dump_context(m_ctx);

    coreStack = stack;
    bool success = true;
    for (list<y2_expr>::iterator pit = coreStack.begin(); pit != coreStack.end();)
    {
      y2_expr term = *pit;
      int term_val = -1;
      int status = yices_term_in_unsat_core(m_ctx, term, &term_val);
      AVR_LOG(17, 5, "\t" << print_term(term) << " is " << term_val << ", status: " << status << endl);

      if (status == 0)
      {
        if (term_val == 0)
        {
          pit = coreStack.erase(pit);
          continue;
        }
        else if (term_val != 1)
          success = false;
      }
      else
        success = false;
      pit++;
    }
    if (!success)
    {
      AVR_LOG(17, 0, "\t(fast unsat core extraction from Yices 2 failed)" << endl);
    }
    assert (success);

    AVR_LOG(17, 6, "core stack: " << print_terms(coreStack) << endl);
    for (auto& curr: coreStack)
    {
      assert(curr != -1);

      Inst *tve = y_to_inst[curr];
      core.push_back(tve);
      AVR_LOG(17, 5, "adding to mus: " << *tve << endl);
    }
//    y2_dump_context(m_ctx);

    if (core.empty())
    {
//      y2_dump_context(m_ctx);
      cout << "mus.empty()" << endl;
      assert(0);
    }
    muses.push_back(core);
    res = AVR_QUSAT;
  }
  else
  {
    numSat++;
    assert(initial_res == STATUS_SAT);
    time_sat_core_muses_reach += time_diff;
    if (time_diff > time_max_sat_core_muses_reach)
      time_max_sat_core_muses_reach = time_diff;

    res = AVR_QSAT;      //the given formula is SAT, i.e. there's no MUS
  }

  s_pop();
  clear_assume();
  m_constraints.clear();
//  cout << "Core 1: " << core << endl;

#ifdef Y2_EXPENSIVE_CORE_EXTRACTION
  if (res == AVR_QUSAT)
  {
    // Reduced unsat core is stored in core/coreStack
    int n = coreStack.size();
    assert(n > 0);

    core1_size += n;
    if (n > 1)
    {
      AVR_LOG(17, 5, "\tEntering experimental unsat core minimization from Y2" << endl);
      AVR_LOG(17, 5, "\t[Input]: " << print_terms(coreStack) << " (sz: " << n << ")" << endl);

      set <y2_expr> DFinal;
      map <y2_expr, y2_expr_vec > AfFinal;
      set <y2_expr> options;
      for (auto& p: coreStack)
        options.insert(p);

      smt_status_t result;

      TIME_S(start_time);
      result = s_check_inc(timeout_value, false);
      TIME_E(start_time, end_time, time_res);

      set <y2_expr> minCore;
      int itCount = 0;
      while (result == STATUS_SAT) {
        num_scalls_sat_core2_muses_reach++;
        time_sat_core2_muses_reach += time_diff;
        if (time_diff > time_max_sat_core2_muses_reach)
          time_max_sat_core2_muses_reach = time_diff;

        set <y2_expr> Dt, Df, At, Af, X;
        bool notMode = false;
        for (list<y2_expr>::iterator pit = coreStack.begin(); pit != coreStack.end(); pit++)
        {
          y2_expr term = *pit;
          int term_val = -2;
          int status = y2_categorize_core_term(m_ctx, term, &term_val);
//          AVR_LOG(17, 0, "\tmus_min_pre: " << print_term(term) << " is " << term_val << endl);
          assert (status == 0);

          switch(term_val) {
          case 0:
            X.insert(term);
            break;
          case 1:
            Dt.insert(term);
            DFinal = Dt;
            break;
          case 2:
            At.insert(term);
            options.erase(term);
            break;
          case 3:
            Df.insert(term);
            break;
          case 4:
          {
            Af.insert(term);

//            if (AfFinal.find(term) == AfFinal.end())
            {
              status = y2_trace_implication(m_ctx, term);
              assert(status == 0);
              y2_expr_vec tmp;
              for (auto& v: coreStack)
              {
                if (v != term)
                {
                  int term_val = -1;
                  int status = y2_term_in_implication_root(m_ctx, v, &term_val);
                  assert(status == 0);
                  if (term_val == 1)
                    tmp.push_back(v);
                  else
                    assert(term_val == 0);
                }
              }
              AfFinal.insert(make_pair(term, tmp));
            }
            options.erase(term);
          }
            break;
          case -1:
            assert(0);
            break;
          default:
            assert(0);
          }
        }
        if (!AfFinal.empty())
        {
          for (auto& p: Df)
            options.erase(p);
          for (auto& p: X)
            options.erase(p);

//          if (itCount == 0)
//            DFinal.clear();
        }
        AVR_LOG(17, 7, "[" << itCount << "]\tDt: " << print_terms(Dt) << endl);
        AVR_LOG(17, 7, "[" << itCount << "]\tDf: " << print_terms(Df) << endl);
        AVR_LOG(17, 7, "[" << itCount << "]\tAt: " << print_terms(At) << endl);
        AVR_LOG(17, 7, "[" << itCount << "]\tAf: " << print_terms(Af) << endl);
        AVR_LOG(17, 7, "[" << itCount << "]\tX : " << print_terms(X)  << endl);
        AVR_LOG(17, 7, "[" << itCount << "]\top: " << print_terms(options) << endl);

        if (!AfFinal.empty())
//          if (itCount == 0)
            break;

        if (options.empty())
          break;

        int m = options.size() - 1;
        y2_expr Pi[m];
        int i = 0;
        for (auto& term: options)
        {
          if (i == m)
          {
            options.erase(term);
            break;
          }
          Pi[i] = term;
          i++;
        }
        if (m > 0)
        {
          y2_expr sumi = yices_or(m, Pi);
          s_assert_constraint(sumi);
          InstL orList;
          for (i = 0; i < m; i++)
            orList.push_back(y_to_inst[Pi[i]]);
          add_assert(OpInst::create(OpInst::LogOr, orList));
          AVR_LOG(17, 7, "asserting " << print_term(sumi) << endl);
        }
        else
          break;

        TIME_S(start_time);
        result = s_check_inc(timeout_value, false);
        TIME_E(start_time, end_time, time_res);

        itCount++;
        if (itCount > 5)
          break;
      }
      if (result == STATUS_UNSAT)
      {
        num_scalls_unsat_core2_muses_reach++;
        time_unsat_core2_muses_reach += time_diff;
        if (time_diff > time_max_unsat_core2_muses_reach)
          time_max_unsat_core2_muses_reach = time_diff;
      }

      AVR_LOG(17, 6, "[Final]\tD : " << print_terms(DFinal) << endl);
      AVR_LOG(17, 6, "[Final]\top: " << print_terms(options) << endl);
      AVR_LOG(17, 6, "[Final]\tAf: " << endl);
      for (auto& t: AfFinal)
      {
        AVR_LOG(17, 6, "\t\t" << print_term(t.first) << " <- " << print_terms(t.second) << endl);
      }

      list <y2_expr> mus;
      y2_expr selection = Y2_INVALID_EXPR;
      if (!AfFinal.empty())
        selection = AfFinal.begin()->first;
      else if (!DFinal.empty())
        selection = *DFinal.begin();
      else
        assert(0);

      s_assert_constraint(selection);
      add_assert(y_to_inst[selection]);

      mus.push_back(selection);

      map <y2_expr, y2_expr_vec > AfTop;
      while (selection != Y2_INVALID_EXPR)
      {
        AVR_LOG(17, 7, "selecting " << print_term(selection) << endl);
        TIME_S(start_time);
        result = s_check_inc(timeout_value, false);
        TIME_E(start_time, end_time, time_res);
//          cout << " ans: " << result << endl;

        set <y2_expr> Dt, At, X;
        map <y2_expr, y2_expr_vec > Df, Af;
        for (list<y2_expr>::iterator pit = coreStack.begin(); pit != coreStack.end(); pit++)
        {
          y2_expr term = *pit;
          int term_val = -2;
          int status = y2_categorize_core_term(m_ctx, term, &term_val);
          assert (status == 0);
  //          AVR_LOG(17, 0, "\tmus_min_pre: " << print_term(term) << " is " << term_val << endl);

          switch(term_val) {
          case 0:
            X.insert(term);
            AfTop.erase(term);
            break;
          case 1:
            Dt.insert(term);
            break;
          case 2:
            At.insert(term);
            break;
          case 3:
          {
            y2_expr_vec tmp;
            tmp.push_back(selection);
            Df[term] = tmp;
          }
            break;
          case 4:
          {
            status = y2_trace_implication(m_ctx, term);
            assert(status == 0);
            y2_expr_vec tmp;
            for (auto& v: coreStack)
            {
              if (v != term)
              {
                int term_val = -1;
                int status = y2_term_in_implication_root(m_ctx, v, &term_val);
                assert(status == 0);
                if (term_val == 1)
                  tmp.push_back(v);
                else
                  assert(term_val == 0);
              }
            }
            Af[term] = tmp;
            AfTop[term] = tmp;
          }
            break;
          case -1:
            assert(0);
            break;
          default:
            assert(0);
          }
        }

        if (!Af.empty())
        {
//          for (auto& p: X)
//            AfTop.erase(p);
          for (auto& p: Df)
            AfTop.erase(p.first);
        }
        else
        {
          for (auto& p: Df)
            AfTop[p.first] = Df[p.first];
        }

        AVR_LOG(17, 7, "[Select]\tS : " << print_terms(mus)  << endl);
        AVR_LOG(17, 7, "[Select]\tX : " << print_terms(X)  << endl);
        AVR_LOG(17, 7, "[Select]\tAt: " << print_terms(At) << endl);
        AVR_LOG(17, 7, "[Select]\tDt: " << print_terms(Dt) << endl);
        AVR_LOG(17, 7, "[Select]\tFf: " << endl);
        for (auto& t: Df)
        {
          AVR_LOG(17, 7, "\t\t\t" << print_term(t.first) << " <- " << print_terms(t.second) << endl);
        }
        AVR_LOG(17, 7, "[Select]\tAf: " << endl);
        for (auto& t: Af)
        {
          AVR_LOG(17, 7, "\t\t\t" << print_term(t.first) << " <- " << print_terms(t.second) << endl);
        }

        if (result == STATUS_SAT)
        {
          num_scalls_sat_core2_muses_reach++;
          time_sat_core2_muses_reach += time_diff;
          if (time_diff > time_max_sat_core2_muses_reach)
            time_max_sat_core2_muses_reach = time_diff;

          int Afsz = Af.size();
          selection = Y2_INVALID_EXPR;
          if (!Af.empty())
            selection = Af.begin()->first;
          else if (!Df.empty())
            selection = Df.begin()->first;

          s_assert_constraint(selection);
          add_assert(y_to_inst[selection]);
          mus.push_back(selection);
        }
        else
        {
          num_scalls_unsat_core2_muses_reach++;
          time_unsat_core2_muses_reach += time_diff;
          if (time_diff > time_max_unsat_core2_muses_reach)
            time_max_unsat_core2_muses_reach = time_diff;

          y2_expr_vec tmp;
          set < y2_expr > tmpSet;
          for (auto& v: Af[selection])
          {
            if (tmpSet.find(v) == tmpSet.end())
            {
              tmp.push_back(v);
              tmpSet.insert(v);
            }
          }

          for (auto& v: Dt)
          {
            if (v != selection)
            {
              if (tmpSet.find(v) == tmpSet.end())
              {
                tmp.push_back(v);
                tmpSet.insert(v);
              }
            }
          }
          Af[selection] = tmp;
          AfTop[selection] = tmp;

          break;
        }
      }
      AVR_LOG(17, 6, "[Final]\tS : " << print_terms(mus)  << endl);
      AVR_LOG(17, 6, "[Final]\tAf: " << endl);
      for (auto& t: AfTop)
      {
        AVR_LOG(17, 6, "\t\t\t" << print_term(t.first) << " <- " << print_terms(t.second) << endl);
      }

      for (map <y2_expr, y2_expr_vec >::iterator mit1 = AfTop.begin(); mit1 != AfTop.end();)
      {
        y2_expr lhs = (*mit1).first;
        bool used = false;
        for (map <y2_expr, y2_expr_vec >::iterator mit2 = AfTop.begin(); mit2 != AfTop.end(); mit2++)
        {
          if (mit1 != mit2)
          {
            bool add = false;
            for (auto& rhs: (*mit2).second)
            {
              if (rhs == lhs)
              {
                add = true;
                break;
              }

            }
            if (add)
            {
              used = true;
              for (auto& rhs: (*mit1).second)
                (*mit2).second.push_back(rhs);
            }
          }
        }
        if (used)
          mit1 = AfTop.erase(mit1);
        else
          mit1++;
      }

      AVR_LOG(17, 6, "[Flat]\tAf: " << endl);
      for (auto& t: AfTop)
        AVR_LOG(17, 6, "\t\t\t" << print_term(t.first) << " <- " << print_terms(t.second) << endl);

      map <y2_expr, y2_expr_vec >::iterator mit = AfTop.begin();
      y2_expr lhs = (*mit).first;
      set < y2_expr > pSet;
      pSet.insert(lhs);
      assert(mit != AfTop.end());
      for (auto& rhs: (*mit).second)
        pSet.insert(rhs);

      InstL tmpCore;
      for (auto& p: pSet)
        tmpCore.push_back(y_to_inst[p]);
      muses.push_back(tmpCore);

//      core.clear();
//      for (auto& p: mus)
//      {
//        core.push_back(y_to_inst[p]);
//      }
    }
  }
#endif

  if (initialPush)
    s_pop();

#ifdef DO_CORRECTNESS_CHECKS
  assert(m_numpush == m_numpop);
#endif

  yices_disable_unsat_core(m_ctx);

  return res;
}
#endif

int y2_API::get_unsat_core(long timeout_value, InstL& vel, InstL& core, int& numSat, int& numUnsat)
{
#ifdef RANDOM_SHUFFLE_CORE
	if (Config::g_random)
	{
		vector< Inst* > velVec;
		for (auto& v: vel)
			velVec.push_back(v);
		random_shuffle(velVec.begin(), velVec.end());
		vel.clear();
		for (auto& v: velVec)
			vel.push_back(v);
	}
#endif

	int qType_orig = queryType;
  queryType = mus_core;

  struct rusage usage;
  struct timeval start_time, end_time;
  long long time_diff;
  long long time_res = 0;

  unsigned sz = vel.size();
  AVR_LOG(17, 5, "\tEntering unsat core extraction from Y2" << endl);
  AVR_LOG(17, 5, "\t[Input]: " << vel << " (sz: " << sz << ")" << endl);
  assert(!vel.empty());

  int res = -1;
  m_constraints.clear();
  m_assumptions.clear();
  map< y2_expr, Inst* >& y_to_inst = m_y_to_inst;
  m_y_to_inst.clear();
  m_unsatCore.clear();

	s_push();

  int count = 0;
  y2_expr_vec constraints;
  y2_expr_vec constraints2;
  InstL induct_clause;
  for (InstL::iterator it = vel.begin(); it != vel.end(); it++)
  {
    init_inst2yices();
    inst2yices(*it);
    force(*it);
    add_assume(*it);

    string iName = "_p_$" + get_y2_temp_name(*it, count);
    y2_expr_ptr indVar = create_bool_var(iName);
    AVR_LOG(17, 5, "\t\t\t(inst: " << *(*it) << ", indicator: " << print_term(indVar) << ")" << endl);

    if (m_constraints.empty()) {
    	continue;
    }

    assert (!m_constraints.empty());
		AVR_LOG(17, 7, "\t\t\t\t(assertions " << print_term(indVar) << " => " << print_terms(m_constraints) << endl);
		for (auto& c: m_constraints)
			constraints.push_back(yices_implies(indVar, c));
		m_constraints.clear();

    m_assumptions.push_back(indVar);
    y_to_inst[indVar] = (*it);

    if (uType != no_induct) {
    	Inst* ve2;
      if (uType == pre_to_next)
      	ve2 = Inst::all_pre2next(*it);
      else {
      	assert (uType == next_to_pre);
      	ve2 = Inst::all_next2pre(*it);
      }
      inst2yices(ve2);
      y2_expr_ptr c2 = force_wo_add(ve2);
      induct_clause.push_back(OpInst::create(OpInst::LogNot, ve2));

      string iName = "_pi_$" + get_y2_temp_name(*it, count);
      y2_expr_ptr indVar2 = create_bool_var(iName);
      AVR_LOG(17, 5, "\t\t\t(induct inst: " << *ve2 << ", indicator: " << print_term(indVar2) << ")" << endl);

      if (!m_constraints.empty()) {
				AVR_LOG(17, 7, "\t\t\t\t(induct assertions " << print_term(indVar2) << " => " << print_terms(m_constraints) << endl);
				for (auto& c: m_constraints)
					constraints.push_back(yices_implies(indVar, c));
				m_constraints.clear();
      }
			constraints.push_back(yices_eq(indVar2, c2));
      indVar2 = yices_not(indVar2);
			constraints2.push_back(indVar2);
    }

    count++;
  }
  if (uType != no_induct) {
  	assert(!constraints2.empty());
//		AVR_LOG(17, 7, "\t\t\t(induct assertions " << print_terms(constraints2) << endl);

  	Inst* clause = OpInst::create(OpInst::LogOr, induct_clause);
//  	add_assume(clause);

		string iName = "_pi_$" + get_y2_temp_name(clause, count);
    y2_expr_ptr a = create_bool_var(iName);
    AVR_LOG(17, 5, "\t\t\t(induct indicator: " << print_term(a) << ")" << endl);

    constraints2.push_back(yices_not(a));
  	y2_expr_ptr cInd = yices_or(constraints2.size(), &(constraints2[0]));
  	constraints.push_back(cInd);

    m_assumptions.push_back(a);
    y_to_inst[a] = NULL;
  }
  m_constraints.swap(constraints);

  assert (!m_constraints.empty());
	AVR_LOG(17, 7, "\t\t\t\t(assertions " << print_terms(m_constraints) << endl);
	s_assert_constraints();

//  smt_status_t initial_res = s_check_inc(timeout_value, false);
//  AVR_LOG(17, 5, "\t\t(initial-check) " << initial_res << endl);

  TIME_S(start_time);
  smt_status_t query_res = s_check_mus(timeout_value, m_assumptions, m_unsatCore, false);
  TIME_E(start_time, end_time, time_res);
  AVR_LOG(17, 4, "\t\t(query-check) " << query_res << endl);

  if (query_res == STATUS_UNSAT)
  {
    numUnsat++;
    time_unsat_core_muses_reach += time_diff;
    if (time_diff > time_max_unsat_core_muses_reach)
      time_max_unsat_core_muses_reach = time_diff;

    AVR_LOG(17, 4, "unsat core: (sz: " << m_unsatCore.size() << endl);
    for (int i = 0; i < m_unsatCore.size(); i++)
    {
      y2_expr_ptr curr = m_unsatCore[i];
      assert(curr != -1);
      AVR_LOG(17, 5, "\t" << i << ": " << print_term(curr) << endl);

      Inst *tve = y_to_inst[curr];
      if (tve != NULL) {
				core.push_back(tve);
				AVR_LOG(17, 4, "adding to mus: " << *tve << endl);
      }
    }
//    y2_dump_context(m_ctx);

    if (core.empty())
    {
//      y2_dump_context(m_ctx);
      cout << "warning: mus.empty()" << endl;
      core.push_back(vel.front());
//      assert(0);
    }

    AVR_LOG(15, 0, "\t\t(" << (m_abstract?"ab":"cc") << " core: " << m_assumptions.size() << " -> " << core.size() << ")" << endl);
    res = AVR_QUSAT;
  }
  else
  {
    assert(query_res == STATUS_SAT);
    numSat++;
    time_sat_core_muses_reach += time_diff;
    if (time_diff > time_max_sat_core_muses_reach)
      time_max_sat_core_muses_reach = time_diff;
    res = AVR_QSAT;      //the given formula is SAT, i.e. there's no MUS
  }

  m_constraints.clear();
  clear_assume();
	s_pop();
  queryType = qType_orig;
  assert(m_numpush == m_numpop);
  return res;
}

void y2_API::minimize_core(long timeout_value, InstL& vel, InstLL& muses, int& numSat, int& numUnsat, bool recordTime)
{
//  muses.push_back(vel);
//  return 0;

//  if (recordTime)
//  {
//    queryType = mus_min;
//    y2_enable_unsat_core(m_ctx);
//  }

	collect_stats_muses(vel.size());

#ifdef DO_CORRECTNESS_CHECKS
	#ifndef ALLOW_MULTIPLE_LEVELS
		assert(m_numpush == m_numpop);
		assert(m_cList.size() == 1);
	#endif
#endif


//	vel.sort(CompareInstByPriority);
//	for (InstL::iterator lit = vel.begin(); lit != vel.end(); lit++)
//	{
//		cout << "\t" << (*lit)->priority << "\t" << *(*lit) << endl;
//	}

	InstL remainingList = vel;

//  init_inst2yices();
//	for (auto& v: vel)
//	{
//    inst2yices(v);
//	}
//  s_assert_constraints();

	/// Iteration count
	int itCount = 0;
	while(!remainingList.empty())
	{
		InstL mus;
		int res = get_mus(timeout_value, remainingList, mus, numSat, numUnsat, recordTime);

		if (res == 0)
			break;
		else
		{
			assert(res == 1);
			AVR_LOG(17, 4, "\t(mus) " << mus << endl);
			muses.push_back(mus);

			/// M1 (just 1 MUS always)
			/// Early exit after getting a single MUS
			break;

			/// M2 (5 MUSes max (optional), remove parts of previous MUSes that contain numbers)
////			if (muses.size() < 5)
//			{
//				InstS musSet(mus.begin(), mus.end());
//				bool changed = false;
//				for (InstS::iterator it = remainingSet.begin(); it != remainingSet.end();)
//				{
//					if ((*it)->childrenInfo[NUM])
//					{
//						if (musSet.find(*it) != musSet.end())
//						{
//							changed = true;
//							it = remainingSet.erase(it);
//							continue;
//						}
//					}
//					it++;
//				}
//				if (!changed)
//					break;
//			}
////			else
////				break;

			/// M3 (disjoint MUSes always, any number)
//			InstS musSet(mus.begin(), mus.end());
//			for (InstS::iterator it = remainingSet.begin(); it != remainingSet.end();)
//			{
//				if (musSet.find(*it) != musSet.end())
//					it = remainingSet.erase(it);
//				else
//					it++;
//			}
		}
	}

	if (m_abstract)
		Solver::total_itr_ab_muses_input += itCount;
	else
		Solver::total_itr_bv_muses_input += itCount;

//	if (!muses.empty())
//	{
//		AVR_LOG(17, 4, "\t(#muses: " << muses.size() << ", exit)" << endl);
//
//		/// Reverse muses if M2 is used
////		muses.reverse();
//
//		if (m_model != NULL)
//		{
//			yices_free_model(m_model);
//			m_model = NULL;
//		}
//
//		return 1;
//	}
//	else
//	{
//		AVR_LOG(17, 4, "\t(no mus, exit)" << endl);
////		yices_print_model(stdout, m_model);
//		return 0;
//	}
}

int y2_API::get_muses_2(long timeout_value, InstL& vel, InstLL& muses, int& numSat, int& numUnsat, Solver* core_solver)
{
#ifdef DISABLE_UNSAT_CORE_MINIMIZATION
	struct rusage usage;
	struct timeval start_time, end_time;
	long long time_diff;

	TIME_S(start_time);

	InstL core;
	core_solver->get_unsat_core(timeout_value, vel, core, numSat, numUnsat);
	if (!core.empty())
		muses.push_back(core);

	TIME_E(start_time, end_time, time_tmp);
#else
	InstL core;
	int status = core_solver->get_unsat_core(timeout_value, vel, core, numSat, numUnsat);
	if (status == AVR_QSAT)
	{
//	  if (m_abstract)
//	    assert(0);
		return 0;
	}
	else if (status == AVR_QTO)
	{
		cout << "\t\t(z3 core extraction T.O.)" << endl;
	}
	else if (status == AVR_QUSAT)
	{
//		cout << "\t(z3: " << vel.size() << " -> " << core.size() << ")" << endl;

//		muses.push_back(core);
//		return 1;
	}

	vel.sort(Inst::CompareInstByChildInfoTier);
	minimize_core(timeout_value, core, muses, numSat, numUnsat);
	if (muses.empty() && status == AVR_QUSAT)
	{
//		core_solver->print_constraints();
//		print_constraints();

		core_solver->s_assert(core);
		cout << "Z3 says " << core_solver->s_check(0, false) << " for core " << core << endl;

    s_assert(core);
    cout << "Y2 says " << s_check(0, false) << " for core " << core << endl;

		print_query(0, ERROR, "error");

//		int res = minimize_core(timeout_value, vel, muses, numSat, numUnsat);
//		cout << "Y2 says " << res << endl;
		s_print_model();
		assert(0);
	}
#endif

	if (!muses.empty())
	{
		AVR_LOG(17, 4, "\t(#muses: " << muses.size() << ", exit)" << endl);
		if (m_model != NULL)
		{
			yices_free_model(m_model);
			m_model = NULL;
		}
		return 1;
	}
	else
	{
		AVR_LOG(17, 4, "\t(no mus, exit)" << endl);
//		yices_print_model(stdout, m_model);
		return 0;
	}
}


int y2_API::get_muses(long timeout_value, InstL& vel_1, InstL& vel_2, InstLL& muses, int& numSat, int& numUnsat, Solver* core_solver)
{
	AVR_LOG(17, 4, "Entering MUSes extraction " << endl);
	AVR_LOG(17, 4, "(initial assertions)" << vel_1 << endl);
	init_inst2yices();
	m_constraints.clear();

	if (!vel_1.empty())
	{
		Inst *ve_1 = OpInst::create(OpInst::LogAnd, vel_1);
		inst2yices(ve_1);
		force(ve_1);
		add_assert(ve_1);
	}

	AVR_LOG(17, 4, "\t(i.e.)" << print_terms(m_constraints) << endl);
	s_assert_constraints(true);

	int res = get_muses_2(timeout_value, vel_2, muses, numSat, numUnsat, core_solver);
	return res;
}

int32_t y2_API::s_push(void)
{
//  AVR_LOG(17, 5, "(push)" << endl);
  AVR_LOG(17, 5, m_solver_id << "\t(push)\t" << m_numpush << endl);

//#ifdef DO_CORRECTNESS_CHECKS
	assert(m_numpush >= m_numpop);
//#endif

	int32_t res = yices_push(m_ctx);

	if (res == 0)
	{
		m_numpush++;
	}
	else
	{
		cout << yices_error_string() << endl;
		y2_result status = yices_context_status(m_ctx);
    if (status != STATUS_UNSAT) {
      cout << "status: " << status << endl;
    }
		assert(status == STATUS_UNSAT);
		print_asserts();
		assert(0);
	}

#ifdef DO_CORRECTNESS_CHECKS
	assert(m_numpush >= m_numpop);
#endif

	y2_expr_vec tmp;
	m_cList.push_back(make_pair(m_cList.size() + 1, tmp));
#ifdef TRACE_SOLVER
	m_trace.push_back("(push 1)");
#endif
	push_assert();
	return res;
}

int32_t y2_API::s_pop(void)
{
//  AVR_LOG(17, 5, "(pop)" << endl);
  AVR_LOG(17, 5, m_solver_id << "\t(pop)\t" << m_numpop << endl);

//#ifdef DO_CORRECTNESS_CHECKS
	assert(m_numpush >= m_numpop);
//#endif

	int32_t res = yices_pop(m_ctx);
	if (res == 0)
	{
		m_numpop++;
	}
	else
		assert(0);

//	if (m_solver_id == 5)
//		cout << "(" << m_solver_id << ") pop: " << m_numpop << endl;

#ifdef DO_CORRECTNESS_CHECKS
	assert(m_numpush >= m_numpop);
#endif

	m_cList.pop_back();
#ifdef TRACE_SOLVER
	m_trace.push_back("(pop 1)");
#endif
	pop_assert();
	return res;
}

void y2_API::s_print_model(void)
{
	yices_print_model(stdout, m_model);
}

bool y2_API::s_check_model(bool allowDontCares)
{
	assert(m_model != NULL);
	bool pass = true;
#ifdef DO_CORRECTNESS_CHECKS
	vector <y2_expr_ptr> errors;
		for (auto& cit : m_cList)
		{
			for (auto& y : cit.second)
			{
				int ans = yices_formula_true_in_model(m_model, y);
				if (ans == 0)
				{
					int idx = cit.first;
					cout << "\n[" << idx << "]:\t" << print_term(y) << " -> " << ans << endl;
					pass = false;
					errors.push_back(y);
				}
			}
		}
		if (!pass)
		{
			cout << "context status: " << yices_context_status(m_ctx) << endl;
			cout << "context check: " << yices_check_context(m_ctx, m_param) << endl;
			cout << "context check2: " << yices_check_context(m_ctx, NULL) << endl;

			cout << "m_model: " << endl;
			yices_print_model(stdout, m_model);

			for (auto& y: errors)
				s_assert_constraint(y);
			y2_result res = yices_check_context(m_ctx, m_param);
			assert(res == STATUS_SAT);

			yices_free_model(m_model);
			m_model = yices_get_model(m_ctx, true);
			for (auto& y: errors) {
				int ans = yices_formula_true_in_model(m_model, y);
				cout << print_term(y) << " -> " << ans << endl;
			}
//			cout << "\nm_cList: " << endl;
//			for (auto& cit : m_cList)
//			{
//				int idx = cit.first;
//				cout << "[" << idx << "]" << endl;
//				for (auto& y : cit.second)
//					cout << print_term(y) << endl;
//				cout << endl;
//			}
//			cout << endl;
//			cout << "m_model: " << endl;
//			yices_print_model(stdout, m_model);
			cout << "solver id: " << m_solver_id << endl;
		}
#endif
	return pass;
}

void y2_API::print_smt2(string fname, string header)
{
//	fname = _benchmark + "q_" + to_string(Solver::num_ab_query);
	if (fname == "")
    fname = QUERY_PATH + m_mapper->get_theory_name() + "/" + _benchmark + ".smt2";
  else
    fname = QUERY_PATH + m_mapper->get_theory_name() + "/" + fname + ".smt2";
	ofstream f;
	f.open(fname.c_str());

  if (header != "")
    f << header;
  f << ";\n";
  f << "(set-info :status unknown)\n";

  bool ufOnly = (m_mapper->fetch_logic() == TheoryMapper::LogicType::QF_UF);
  bool isCore = (queryType == mus_core) || !m_assumptions.empty();

	for (y2_IntUtM::iterator sit = y2_API::m_sz_to_ut.begin(); sit != y2_API::m_sz_to_ut.end(); sit++)
	{
		y2_type tt = (*sit).second;
		f << "(declare-sort " << print_type(tt) << " 0)" << endl;
	}
	for (y2_StringToFunctM::iterator sit = y2_API::m_funct.begin(); sit != y2_API::m_funct.end(); sit++)
	{
		string fname = (*sit).first;
		y2_type ft = yices_type_of_term((*sit).second);
		if (ufOnly)
			 if (yices_type_is_bitvector(ft) == 1)
				 continue;

		f << "(declare-fun " << fname << " (";
		int32_t numChild = yices_type_num_children(ft);
		assert(numChild >= 1);
		for (int i = 0; i < numChild-1; i++)
		{
			y2_type dt = yices_type_child(ft, i);
			f << print_smt_type(dt) << " ";
		}
		f << ") ";
		y2_type dt = yices_type_child(ft, numChild-1);
		f << print_smt_type(dt);
		f << ")" << endl;
	}
	for (y2_StringToDecl::iterator sit = y2_API::m_var_decs.begin(); sit != y2_API::m_var_decs.end(); sit++)
	{
		string vname = (*sit).first;
		y2_expr v = (*sit).second;
		y2_type vt = yices_type_of_term(v);
		if (ufOnly)
			 if (yices_type_is_bitvector(vt) == 1)
				 continue;
		f << "(declare-fun " << print_smt_term(v) << " () " << print_smt_type(vt) << ")" << endl;
	}

	for (list< pair<int, y2_expr_vec> >::iterator lit = m_cList.begin(); lit != m_cList.end();)
	{
		for (y2_expr_vec::iterator vit = (*lit).second.begin(); vit != (*lit).second.end(); vit++)
		{
			string termS = print_smt_term(*vit);
			f << "(assert " << termS << ")" << endl;
		}

   lit++;
   if (lit != m_cList.end())
    f << "(push 1)" << endl;
	}

	if (isCore)
	{
		for (int i = 0; i < m_assumptions.size(); i++)
		{
			string termS = print_smt_term(m_assumptions[i]);
			f << "(assert (! " << termS << " :named i$" << to_string(i) << "))\n";
		}
	}

	f << "(check-sat)" << endl;
	if (isCore)
		f << "(get-unsat-core)" << endl;

	f.close();
}

#ifdef TRACE_SOLVER
void y2_API::process_trace(ofstream& f) {
  bool ufOnly = (m_mapper->fetch_logic() == TheoryMapper::LogicType::QF_UF);

	for (y2_IntUtM::iterator sit = y2_API::m_sz_to_ut.begin(); sit != y2_API::m_sz_to_ut.end(); sit++)
	{
		y2_type tt = (*sit).second;
		f << "(declare-sort " << print_type(tt) << " 0)" << endl;
	}
	for (y2_StringToFunctM::iterator sit = y2_API::m_funct.begin(); sit != y2_API::m_funct.end(); sit++)
	{
		string fname = (*sit).first;
		y2_type ft = yices_type_of_term((*sit).second);
		if (ufOnly)
			 if (yices_type_is_bitvector(ft) == 1)
				 continue;

		f << "(declare-fun " << fname << " (";
		int32_t numChild = yices_type_num_children(ft);
		assert(numChild >= 1);
		for (int i = 0; i < numChild-1; i++)
		{
			y2_type dt = yices_type_child(ft, i);
			f << print_smt_type(dt) << " ";
		}
		f << ") ";
		y2_type dt = yices_type_child(ft, numChild-1);
		f << print_smt_type(dt);
		f << ")" << endl;
	}
	for (y2_StringToDecl::iterator sit = y2_API::m_var_decs.begin(); sit != y2_API::m_var_decs.end(); sit++)
	{
		string vname = (*sit).first;
		y2_expr v = (*sit).second;
		y2_type vt = yices_type_of_term(v);
		if (ufOnly)
			 if (yices_type_is_bitvector(vt) == 1)
				 continue;
		f << "(declare-fun " << print_smt_term(v) << " () " << print_smt_type(vt) << ")" << endl;
	}
}
#endif

void y2_API::print_y2(string fname, double time_res)
{
	/// TODO
	if (fname == "")
		fname = "../smt_queries/" + to_string(Config::g_ab_interpret_limit) + "/" + _benchmark + ".ys";
	else
		fname = "../smt_queries/" + to_string(Config::g_ab_interpret_limit) + "/" + fname + ".ys";
	ofstream f;
	f.open(fname.c_str());
	if (time_res != -1)
		f << ";(avr-time: " << time_res << " milli sec)" << endl;


	for (y2_IntUtM::iterator sit = y2_API::m_sz_to_ut.begin(); sit != y2_API::m_sz_to_ut.end(); sit++)
	{
		y2_type tt = (*sit).second;
		f << "(define-type " << print_type(tt) << ")" << endl;
	}
	for (y2_StringToFunctM::iterator sit = y2_API::m_funct.begin(); sit != y2_API::m_funct.end(); sit++)
	{
		string fname = (*sit).first;
		y2_type ft = yices_type_of_term((*sit).second);
		f << "(define " << fname << "::(-> ";
		int32_t numChild = yices_type_num_children(ft);
		assert(numChild >= 1);
		for (int i = 0; i < numChild; i++)
		{
			y2_type dt = yices_type_child(ft, i);
			f << print_type(dt) << " ";
		}
		f << "))" << endl;
	}
	for (y2_StringToDecl::iterator sit = y2_API::m_var_decs.begin(); sit != y2_API::m_var_decs.end(); sit++)
	{
		string vname = (*sit).first;
		y2_expr v = (*sit).second;
		y2_type vt = yices_type_of_term(v);
		f << "(define " << print_term(v) << "::" << print_type(vt) << ")" << endl;
	}

	for (list< pair<int, y2_expr_vec> >::iterator lit = m_cList.begin(); lit != m_cList.end(); lit++)
	{
		for (y2_expr_vec::iterator vit = (*lit).second.begin(); vit != (*lit).second.end(); vit++)
		{
			string termS = print_term(*vit);
			f << "(assert " << termS << ")" << endl;
		}

		if (lit != m_cList.end())
			f << "(push)" << endl;
	}
	f << "(check)" << endl;

	f.close();
}

bool y2_API::s_assert(Inst* e)
{
//	struct rusage usage;
//	struct timeval start_time, end_time;
//	long long time_diff;
//	TIME_S(start_time);

	AVR_LOG(11, 1, "[SID:" << m_solver_id << ", SBA:" << m_ba_idx << "]----------" << endl);
 	init_inst2yices();
	m_constraints.clear();
	inst2yices(e);
	force(e);
	add_assert(e);

//	TIME_E(start_time, end_time, Solver::time_tmp);

	s_assert_constraints();
//	// add the constraints to YICES
//	for (YicesAPIBAV::iterator it = m_constraints.begin(), end_it = m_constraints.end(); it != end_it; ++it)
//	{
//		yices_assert_formula(m_ctx, *it);
//	}

	return true;
}

bool y2_API::s_assert(InstL& vel)
{
//	struct rusage usage;
//	struct timeval start_time, end_time;
//	long long time_diff;
//	TIME_S(start_time);


	AVR_LOG(11, 1, "[SID:" << m_solver_id << ", SBA:" << m_ba_idx << "]----------" << endl);
 	init_inst2yices();
	m_constraints.clear();

	for (auto& e: vel)
	{
		inst2yices(e);
		force(e);
		add_assert(e);
	}

//	TIME_E(start_time, end_time, Solver::time_tmp);

	s_assert_constraints();

	return true;
}

bool y2_API::s_assert(InstLL& l)
{
//	struct rusage usage;
//	struct timeval start_time, end_time;
//	long long time_diff;
//	TIME_S(start_time);


	AVR_LOG(11, 1, "[SID:" << m_solver_id << ", SBA:" << m_ba_idx << "]----------" << endl);
 	init_inst2yices();
	m_constraints.clear();

	for (auto& vel: l)
	{
		for (auto& e: vel)
		{
			inst2yices(e);
			force(e);
			add_assert(e);
		}
	}

//	TIME_E(start_time, end_time, Solver::time_tmp);

	s_assert_constraints();

	return true;
}

bool y2_API::s_assert_retractable(InstL vel)
{
	init_inst2yices();
	m_constraints.clear();

//	if (!m_inc_allowed)
	s_push();

#ifndef Y2_USE_RETRACTABLE_ASSUMPTIONS
	for (InstL::iterator it = vel.begin(); it != vel.end(); it++)
	{
		inst2yices(*it);
	}
//	s_assert_constraints();

	for (InstL::iterator it = vel.begin(); it != vel.end(); it++)
	{
		y2_expr ye = force_wo_add(*it);
		m_constraints.push_back(ye);
		add_assert(*it);
	}
	s_assert_constraints();
#else
	m_assumptions.clear();
	m_unsatCore.clear();

	queryTypeStore = queryType;
  queryType = mus_core;

	Inst* tve = OpInst::create(OpInst::LogAnd, vel);

	inst2yices(tve);
	s_assert_constraints();

	y2_expr_ptr ye = force_wo_add(tve);
	m_assumptions.push_back(ye);
	add_assume(tve);

//	string iName = "_a_$" + get_y2_temp_name(tve, 0);
//	y2_expr_ptr indVar = create_bool_var(iName);
//	AVR_LOG(17, 5, "\t\t\t(inst: " << *tve << ", indicator: " << print_term(indVar) << ")" << endl);
//
//	assert (!m_constraints.empty());
//	AVR_LOG(17, 7, "\t\t\t\t(assertions " << print_term(indVar) << " => " << print_terms(m_constraints) << endl);
//	s_assert_constraints(indVar);
//	m_assumptions.push_back(indVar);
//	AVR_LOG(17, 7, "\t\t\t\t(assertions " << print_terms(m_constraints) << endl);
#endif

	return true;
}

bool y2_API::s_retract_assertions()
{
#ifdef Y2_USE_RETRACTABLE_ASSUMPTIONS
	m_assumptions.clear();
	m_unsatCore.clear();
	clear_assume();
  queryType = queryTypeStore;
#endif

	s_pop();
	assert(m_numpush == m_numpop);
	return true;
}

bool y2_API::s_retract_all_assertions()
{
	assert(0);

//	for(int i = 0; i < m_stack.size(); i++)
//	{
//		s_pop();
//	}
//	m_stack.clear();

	while (m_numpush != m_numpop)
		s_pop();

	assert(m_numpush == m_numpop);
	return true;
}

void y2_API::s_add_core(InstL& core, bool push) {
	// can happen in check_correctness
	if (core.empty()) {
		if (push)
			s_push();
		return;
	}

	m_constraints.clear();
	if (push)
		s_push();
	else
		disable_cache_hard();

	int count = 0;
  y2_expr_vec constraints;
	for (InstL::iterator it = core.begin(); it != core.end(); it++)
	{
		init_inst2yices();
		inst2yices(*it);
		force(*it);

		string iName = "_q_$" + get_y2_temp_name(*it, count);
    y2_expr_ptr indVar = create_bool_var(iName);

		AVR_LOG(17, 5, "\t\t\t(inst: " << *(*it) << ", indicator: " << print_term(indVar) << ")" << endl);
		if (!m_constraints.empty())
		{
			AVR_LOG(17, 7, "\t\t\t\t(assertions " << print_term(indVar) << " => " << print_terms(m_constraints) << endl);
      for (auto& c: m_constraints)
        constraints.push_back(yices_implies(indVar, c));
      m_constraints.clear();
		}
		m_inst_to_y[*it] = make_pair(indVar, Y2_INVALID_EXPR);

    count++;
	}
  m_constraints.swap(constraints);

	assert (!m_constraints.empty());
	{
		s_assert_constraints();
	}
}

void y2_API::s_add_assumptions(InstL& assumptions, bool push) {
	// can happen in check_correctness
	if (assumptions.empty()) {
		if (push)
			s_push();
		return;
	}

	m_constraints.clear();
	if (push)
		s_push();
	else
		disable_cache_hard();

	int count = 0;
	y2_expr_vec constraints;
	y2_expr_vec constraints2;
  InstL induct_clause;
	for (InstL::iterator it = assumptions.begin(); it != assumptions.end(); it++)
	{
		init_inst2yices();
		inst2yices(*it);
		force(*it);
		add_assume(*it);

		string iName = "_p_$" + get_y2_temp_name(*it, count);
		y2_expr_ptr indVar = create_bool_var(iName);

		AVR_LOG(17, 5, "\t\t\t(inst: " << *(*it) << ", indicator: " << print_term(indVar) << ")" << endl);
		if (!m_constraints.empty())
		{
			AVR_LOG(17, 7, "\t\t\t\t(assertions " << print_term(indVar) << " => " << print_terms(m_constraints) << endl);
			for (auto& c: m_constraints)
				constraints.push_back(yices_implies(indVar, c));
			m_constraints.clear();
		}

		m_assumptions.push_back(indVar);
    m_y_to_inst[indVar] = (*it);

    if (uType != no_induct) {
    	Inst* ve2;
      if (uType == pre_to_next)
      	ve2 = Inst::all_pre2next(*it);
      else {
      	assert (uType == next_to_pre);
      	ve2 = Inst::all_next2pre(*it);
      }
      inst2yices(ve2);
      y2_expr_ptr c2 = force_wo_add(ve2);
      induct_clause.push_back(OpInst::create(OpInst::LogNot, ve2));

      string iName = "_pi_$" + get_y2_temp_name(*it, count);
      y2_expr_ptr indVar2 = create_bool_var(iName);
      AVR_LOG(17, 5, "\t\t\t(induct inst: " << *ve2 << ", indicator: " << print_term(indVar2) << ")" << endl);

      if (!m_constraints.empty()) {
				AVR_LOG(17, 7, "\t\t\t\t(induct assertions " << print_term(indVar2) << " => " << print_terms(m_constraints) << endl);
				for (auto& c: m_constraints)
					constraints.push_back(yices_implies(indVar, c));
				m_constraints.clear();
      }
			constraints.push_back(yices_eq(indVar2, c2));
      indVar2 = yices_not(indVar2);
			constraints2.push_back(indVar2);
    }

		count++;
	}
  if (uType != no_induct) {
  	assert(!constraints2.empty());
		AVR_LOG(17, 7, "\t\t\t\t(induct assertions " << print_terms(constraints2) << endl);

		Inst* clause = OpInst::create(OpInst::LogOr, induct_clause);
//  	add_assume(clause);

		string iName = "_pi_$" + get_y2_temp_name(clause, count);
    y2_expr_ptr a = create_bool_var(iName);
    AVR_LOG(17, 5, "\t\t\t(induct indicator: " << print_term(a) << ")" << endl);

    constraints2.push_back(yices_not(a));
  	y2_expr_ptr cInd = yices_or(constraints2.size(), &(constraints2[0]));
  	constraints.push_back(cInd);

    m_assumptions.push_back(a);
    m_y_to_inst[a] = NULL;
  }
	m_constraints.swap(constraints);

	assert (!m_constraints.empty());
	AVR_LOG(17, 7, "\t\t\t\t(assertions " << print_terms(m_constraints) << endl);
	s_assert_constraints();
}

//void y2_API::swap_model(y2_model& mdl) {
//	mdl = m_model;
//	m_model = NULL;
//}

int y2_API::s_check(long timeout_value, bool getModel)
{
	long timeout_value_orig = timeout_value;
  if (allow_fallback) {
#ifdef Y2_FORCE_NONINC
		y2_result newRes = shift_to_noninc(timeout_value, 0, getModel);
		if (newRes == STATUS_SAT)
			return AVR_QSAT;
		else if (newRes == STATUS_UNSAT)
			return AVR_QUSAT;
		else
			assert(0);
#endif

    timeout_value = g_soft_timeout;
  }

  increase_cond_activity();

	update_query_sz();
	struct rusage usage;
	struct timeval start_time, end_time;
	long long time_diff;
	long long time_res = 0;

//	collect_solv_presearch_statistic();
#ifdef TRACE_SOLVER
	m_trace.push_back("(check-sat)");
#endif

	Y2_SET_TIMEOUT(m_ctx);
	TIME_S(start_time);
	y2_result res = yices_check_context(m_ctx, m_param);
	Y2_CHECK_TIMEOUT;

//	string comment = "regular ";
//	comment += m_abstract ? "ab" : "bv";
//	comment += ": ans- " + to_string(res);
//	print_asserts(comment);

	TIME_E(start_time, end_time, time_res);
  Solver::time_tmp += time_res;
#ifdef Y2_EXP
  collect_solv_statistic_query();
#endif

	if (res == STATUS_SAT)
	{
#ifdef DUMP_CONTEXT_SAT
    if (m_abstract)
      y2_dump_context(m_ctx);
#endif
		if (m_numpush == 0)
			collect_stats_query(time_res, ONESHOT_SAT);
		else
			collect_stats_query(time_res, INC_SAT);

		if (getModel)
		{
			if (m_model != NULL)
				yices_free_model(m_model);
			m_model = yices_get_model(m_ctx, true);

			bool mres = s_check_model();
			if (!mres)
			{
		    print_query(time_res, ERROR, "error_model");
			}
			assert(mres);
		}
//		yices_print_model(stdout, m_model);

//		term_vector_t vecV;
//		yices_model_collect_defined_terms(m_model, &vecV);
//		cout << "vecVsz: " << vecV.size << endl;
//		for (unsigned i = 0; i < vecV.size; i++)
//			cout << print_term(vecV.data[i]) << endl;
//		assert(0);
		return AVR_QSAT;
	}
	else if (res == STATUS_UNSAT)
	{
#ifdef DUMP_CONTEXT_UNSAT
    if (m_abstract)
      y2_dump_context(m_ctx);
#endif

		if (m_numpush == 0)
			collect_stats_query(time_res, ONESHOT_UNSAT);
		else
			collect_stats_query(time_res, INC_UNSAT);
		return AVR_QUSAT;
	}
	else
	{
    assert(res != STATUS_ERROR);

    collect_stats_query(time_res, TIME_TO);

//		AVR_LOG(15, 0, "Y2 Query Soft TIMEOUT (" << timeout_value << ")" << endl);
//    print_query(time_res, TIME_TO, "to");
//    Solver::query_timed_out = true;
//		assert(0);

    y2_result newRes = shift_to_noninc(timeout_value_orig, time_res, getModel);
    if (newRes == STATUS_SAT)
      return AVR_QSAT;
    else if (newRes == STATUS_UNSAT)
      return AVR_QUSAT;
    else
      assert(0);
	}
}

int y2_API::s_check_assume(long timeout_value, bool getModel)
{
#ifdef Y2_USE_RETRACTABLE_ASSUMPTIONS
	y2_result res_y = s_check_mus(timeout_value, m_assumptions, m_unsatCore, getModel);

	int res = AVR_QTO;
	switch (res_y) {
	case STATUS_SAT:
		res = AVR_QSAT;
		break;
	case STATUS_UNSAT:
		res = AVR_QUSAT;
		break;
	default:
		res = AVR_QTO;
	}
#else
	int res = s_check(timeout_value, getModel);
#endif
  return res;
}

y2_result y2_API::s_check_inc(long timeout_value, bool getModel)
{
	long timeout_value_orig = timeout_value;
  if (allow_fallback) {
#ifdef Y2_FORCE_NONINC
  	return shift_to_noninc(timeout_value, 0, getModel);
#endif

    timeout_value = g_soft_timeout;
  }

  increase_cond_activity();

  update_query_sz();
  struct rusage usage;
  struct timeval start_time, end_time;
  long long time_diff;
  long long time_res = 0;

//  collect_solv_presearch_statistic();
#ifdef TRACE_SOLVER
	m_trace.push_back("(check-sat)");
#endif

  Y2_SET_TIMEOUT(m_ctx);
  TIME_S(start_time);
  y2_result res = yices_check_context(m_ctx, m_param);
  Y2_CHECK_TIMEOUT;

//  string comment = "inc ";
//  comment += m_abstract ? "ab" : "bv";
//  comment += ": ans- " + to_string(res);
//  print_asserts(comment);

  TIME_E(start_time, end_time, time_res);
  Solver::time_tmp += time_res;
#ifdef Y2_EXP
  collect_solv_statistic_query();
#endif

  if (res == STATUS_SAT)
  {
#ifdef DUMP_CONTEXT_SAT
    if (m_abstract)
      y2_dump_context(m_ctx);
#endif

    if (m_numpush == 0)
      collect_stats_query(time_res, ONESHOT_SAT);
    else
      collect_stats_query(time_res, INC_SAT);

    if (getModel)
    {
      if (m_model != NULL)
        yices_free_model(m_model);
      m_model = yices_get_model(m_ctx, true);

      bool mres = s_check_model();
      if (!mres)
      {
        print_query(time_res, ERROR, "error");
      }
      assert(mres);
    }
  }
  else if (res == STATUS_UNSAT)
  {
#ifdef DUMP_CONTEXT_UNSAT
    if (m_abstract)
      y2_dump_context(m_ctx);
#endif

    if (m_numpush == 0)
      collect_stats_query(time_res, ONESHOT_UNSAT);
    else
      collect_stats_query(time_res, INC_UNSAT);
  }
  else
  {
    assert(res != STATUS_ERROR);

    collect_stats_query(time_res, TIME_TO);

//    AVR_LOG(15, 0, "Y2 Query Soft TIMEOUT (" << timeout_value << ")" << endl);
//    print_query(time_res, TIME_TO, "to");
//    Solver::query_timed_out = true;
//    assert(0);

    y2_result newRes = shift_to_noninc(timeout_value_orig, time_res, getModel);
    if (newRes != STATUS_SAT && newRes != STATUS_UNSAT)
      assert(0);
    res = newRes;
  }
  return res;
}

y2_result y2_API::s_check_oneshot_reset2(long timeout_value, bool getModel, bool keepIte)
{
	struct rusage usage;
	struct timeval start_time, end_time;
	long long time_diff;

	long long time_assert = 0;
	long long time_solve = 0;

	bool singleFirst = false;
	if (!getModel)
		singleFirst = true;

	TIME_S(start_time);
	if (singleFirst)
		s_reset_single_solver();
	else
		s_reset_all_solvers();
	TIME_E(start_time, end_time, time_assert);

	TIME_S(start_time);
	y2_result res2 = s_check_oneshot(timeout_value, getModel, true, keepIte, false);
	TIME_E(start_time, end_time, time_solve);
	AVR_LOG(17, 0, "\t(result (after reset): " << ((res2 == STATUS_SAT) ? "sat" : (res2 == STATUS_UNSAT) ? "unsat" : "??")
			<< ", time: " << (time_assert + time_solve) << " usec (" << time_assert << " + " << time_solve << ")" << endl);

	if (singleFirst)
		s_reset_remaining_solvers(m_solver_id);

//	assert(0);
	return res2;
}

y2_result y2_API::s_check_oneshot_reset(long timeout_value, bool getModel)
{
	struct rusage usage;
	struct timeval start_time, end_time;
	long long time_diff;

	y2_result res2;
	bool useKeepIte = true;

	{
		s_reset_scope();

		{
			long long time_assert = 0;
			long long time_solve = 0;

			y2_API tmpSolver(m_mapper, m_ba_idx, static_cast<int>(0), queryType);
			tmpSolver.copy_attributes(this);

	//		y2_solvers.erase(tmpSolver.m_solver_id);

	//		y2_API tmpSolver(m_mapper, m_ba_idx, is_i, queryType);
			if (getModel)
				tmpSolver.enable_model();
			else
				tmpSolver.disable_model();

			TIME_S(start_time);
			tmpSolver.s_assert(m_asserts.assertions);
			TIME_E(start_time, end_time, time_assert);

			TIME_S(start_time);
			res2 = tmpSolver.s_check_oneshot(Y2_RESET_TIMEOUT_TRIAL, false, false, true, false);
			TIME_E(start_time, end_time, time_solve);
			if (res2 == STATUS_SAT || res2 == STATUS_UNSAT)
				useKeepIte = true;

			AVR_LOG(17, 0, "\t(result (model " << (getModel ? "required" : "not required") << "): " << ((res2 == STATUS_SAT) ? "sat" : (res2 == STATUS_UNSAT) ? "unsat" : "??")
					<< ", time: " << (time_assert + time_solve) << " usec (" << time_assert << " + " << time_solve << ")" << endl);
		}
  }

  if (res2 != STATUS_SAT && res2 != STATUS_UNSAT) {
  	s_reset_scope();

    {
  		long long time_assert = 0;
  		long long time_solve = 0;

  		y2_API tmpSolver(m_mapper, m_ba_idx, static_cast<int>(0), queryType);
			tmpSolver.copy_attributes(this);

  //		y2_solvers.erase(tmpSolver.m_solver_id);

  //		y2_API tmpSolver(m_mapper, m_ba_idx, is_i, queryType);
  		if (getModel)
  			tmpSolver.enable_model();
  		else
  			tmpSolver.disable_model();
			tmpSolver.disable_keep_ite();

  		TIME_S(start_time);
  		tmpSolver.s_assert(m_asserts.assertions);
  		TIME_E(start_time, end_time, time_assert);

  		TIME_S(start_time);
  		res2 = tmpSolver.s_check_oneshot(Y2_RESET_TIMEOUT_TRIAL, false, false, false, false);
  		TIME_E(start_time, end_time, time_solve);
		if (res2 == STATUS_SAT || res2 == STATUS_UNSAT)
			useKeepIte = false;

  		AVR_LOG(17, 0, "\t(result (model " << (getModel ? "required" : "not required") << "): " << ((res2 == STATUS_SAT) ? "sat" : (res2 == STATUS_UNSAT) ? "unsat" : "??")
  				<< ", time: " << (time_assert + time_solve) << " usec (" << time_assert << " + " << time_solve << ")" << endl);
    }
  }

  // Phase 2
  if (res2 != STATUS_SAT && res2 != STATUS_UNSAT) {
		s_reset_scope();

		{
			long long time_assert = 0;
			long long time_solve = 0;

			y2_API tmpSolver(m_mapper, m_ba_idx, static_cast<int>(0), queryType);
			tmpSolver.copy_attributes(this);

	//		y2_solvers.erase(tmpSolver.m_solver_id);

	//		y2_API tmpSolver(m_mapper, m_ba_idx, is_i, queryType);
			if (getModel)
				tmpSolver.enable_model();
			else
				tmpSolver.disable_model();

			TIME_S(start_time);
			tmpSolver.s_assert(m_asserts.assertions);
			TIME_E(start_time, end_time, time_assert);

			TIME_S(start_time);
			res2 = tmpSolver.s_check_oneshot(timeout_value, false, false, true, false);
			TIME_E(start_time, end_time, time_solve);
			if (res2 == STATUS_SAT || res2 == STATUS_UNSAT)
				useKeepIte = true;

			AVR_LOG(17, 0, "\t(result (model " << (getModel ? "required" : "not required") << "): " << ((res2 == STATUS_SAT) ? "sat" : (res2 == STATUS_UNSAT) ? "unsat" : "??")
					<< ", time: " << (time_assert + time_solve) << " usec (" << time_assert << " + " << time_solve << ")" << endl);
		}
  }

  if (res2 != STATUS_SAT && res2 != STATUS_UNSAT) {
  	s_reset_scope();

    {
  		long long time_assert = 0;
  		long long time_solve = 0;

  		y2_API tmpSolver(m_mapper, m_ba_idx, static_cast<int>(0), queryType);
			tmpSolver.copy_attributes(this);

  //		y2_solvers.erase(tmpSolver.m_solver_id);

  //		y2_API tmpSolver(m_mapper, m_ba_idx, is_i, queryType);
  		if (getModel)
  			tmpSolver.enable_model();
  		else
  			tmpSolver.disable_model();
			tmpSolver.disable_keep_ite();

  		TIME_S(start_time);
  		tmpSolver.s_assert(m_asserts.assertions);
  		TIME_E(start_time, end_time, time_assert);

  		TIME_S(start_time);
  		res2 = tmpSolver.s_check_oneshot(timeout_value, false, false, false, false);
  		TIME_E(start_time, end_time, time_solve);
		if (res2 == STATUS_SAT || res2 == STATUS_UNSAT)
			useKeepIte = false;

  		AVR_LOG(17, 0, "\t(result (model " << (getModel ? "required" : "not required") << "): " << ((res2 == STATUS_SAT) ? "sat" : (res2 == STATUS_UNSAT) ? "unsat" : "??")
  				<< ", time: " << (time_assert + time_solve) << " usec (" << time_assert << " + " << time_solve << ")" << endl);
    }
  }

  if (res2 != STATUS_SAT && res2 != STATUS_UNSAT) {

    {
			long long time_assert = 0;
			long long time_solve = 0;

			y2_reset();
			y2_API tmpSolver(m_mapper, m_ba_idx, is_i, queryType);
			tmpSolver.copy_attributes(this);

			tmpSolver.disable_model();
			TIME_S(start_time);
			for (auto& assertions: m_asserts.assertions)
				for (auto& v: assertions)
					tmpSolver.s_assert(v);
			TIME_E(start_time, end_time, time_assert);

			TIME_S(start_time);
			y2_result res2 = tmpSolver.s_check_oneshot(0, false, false, true, false);
			TIME_E(start_time, end_time, time_solve);
			AVR_LOG(17, 0, "\t(result --var-elim --keep-ite: " << ((res2 == STATUS_SAT) ? "sat" : (res2 == STATUS_UNSAT) ? "unsat" : "??")
					<< ", time: " << (time_assert + time_solve) << " usec (" << time_assert << " + " << time_solve << ")" << endl);
    }

    {
			long long time_assert = 0;
			long long time_solve = 0;

			y2_reset();
			y2_API tmpSolver(m_mapper, m_ba_idx, is_i, queryType);
			tmpSolver.copy_attributes(this);

			tmpSolver.enable_model();
			TIME_S(start_time);
			for (auto& assertions: m_asserts.assertions)
				for (auto& v: assertions)
					tmpSolver.s_assert(v);
			TIME_E(start_time, end_time, time_assert);

			TIME_S(start_time);
			y2_result res2 = tmpSolver.s_check_oneshot(0, true, false, false, false);
			TIME_E(start_time, end_time, time_solve);
			AVR_LOG(17, 0, "\t(result:" << ((res2 == STATUS_SAT) ? "sat" : (res2 == STATUS_UNSAT) ? "unsat" : "??")
					<< ", time: " << (time_assert + time_solve) << " usec (" << time_assert << " + " << time_solve << ")" << endl);
    }

		Inst::g_result = f_to_query;
		assert(0);
  }

	s_reset_scope();

  int solver_id = m_solver_id;
  s_reset_solver();

  if (getModel) {
  	if (res2 == STATUS_SAT)
  		s_check_oneshot(timeout_value, getModel, false, useKeepIte, false);
  }

	s_reset_remaining_solvers(solver_id);


//	assert(0);
	return res2;
}

y2_result y2_API::s_check_oneshot(long timeout_value, bool getModel, bool tryVarElim, bool keepIte, bool enReset)
{
#ifdef Y2_DISABLE_TRY_VAR_ELIM
	tryVarElim = false;
#endif

#ifdef Y2_CUSTOM
	enReset = false;
#endif
	long timeout_value_orig = timeout_value;
	if (enReset)
		timeout_value = Y2_RESET_TIMEOUT;

	struct rusage usage;
	struct timeval start_time, end_time;
	long long time_diff;
	long long time_res = 0;

  y2_config cfg = yices_new_config();
  set_logic(cfg);
  yices_set_config(cfg, "mode", "one-shot");

  y2_context ctx = yices_new_context(cfg);
  set_context_parameters(ctx);
  if (!tryVarElim && getModel)
  	disable_var_elim(ctx);
  else
  	enable_var_elim(ctx);
  if (!keepIte)
  	disable_keep_ite(ctx);

  y2_param prm = yices_new_param_record();
  yices_default_params_for_context(ctx, prm);
  set_parameters(prm);

  y2_expr_vec assertions;
  for (auto& v: m_cList)
    for (auto& c: v.second)
      assertions.push_back(c);
  yices_assert_formulas(ctx, assertions.size(), &(assertions.front()));

//  for (auto& v: m_cList)
//    yices_assert_formulas(ctx, v.second.size(), &(v.second.front()));

//  for (auto& v: m_cList)
//		for (auto& c: v.second)
//			yices_assert_formula(ctx, c);

  update_query_sz();

#ifdef TRACE_SOLVER
	m_trace.push_back("(check-sat)");
#endif

	Y2_SET_TIMEOUT(ctx);
	TIME_S(start_time);
	y2_result res = yices_check_context(ctx, prm);
	Y2_CHECK_TIMEOUT;

	TIME_E(start_time, end_time, time_res);
  Solver::time_tmp += time_res;
//	collect_solv_statistic_query();

	if (res == STATUS_SAT)
	{
    collect_stats_query(time_res, ONESHOT_SAT);

		if (getModel)
		{
			if (tryVarElim)
			{
				res = s_check_oneshot(timeout_value_orig, getModel, false, keepIte, enReset);
			}
			else
			{
				if (m_model != NULL)
					yices_free_model(m_model);
				m_model = yices_get_model(ctx, true);

				bool mres = s_check_model();
				if (!mres)
				{
			    print_query(time_res, ERROR, "error");
				}
				assert(mres);
			}
		}
	}
	else if (res == STATUS_UNSAT)
	{
    collect_stats_query(time_res, ONESHOT_UNSAT);
	}
	else
	{
    assert(res != STATUS_ERROR);

    collect_stats_query(time_res, TIME_TO);
//    print_query(time_res, TIME_TO, "error");
    AVR_LOG(15, 0, "Y2 oneshot Query TIMEOUT (" << timeout_value << ")" <<
    		", query type: " << queryType <<
    		", getModel: " << getModel <<
    		", tryVarElim: " << tryVarElim <<
    		", keepIte: " << keepIte <<
    		", enReset: " << enReset <<
				endl);

#ifdef Y2_EXP
    y2_show_statistics(stdout, ctx);
    y2_stat qStat;
    yices_get_statistics(ctx, &qStat.st);
    qStat.print_stat(cout, "Query stats:");
#endif

  	if (enReset) {
			if (prm)
				yices_free_param_record(prm);
			if (ctx)
				yices_free_context(ctx);
			if (cfg)
				yices_free_config(cfg);

  		return s_check_oneshot_reset(timeout_value_orig, getModel);
  	}

//  	if (keepIte)
//  		return s_check_oneshot_reset(timeout_value_orig, getModel, false, false);

	}

//  collect_solv_statistic_end();

	if (prm)
		yices_free_param_record(prm);
	if (ctx)
		yices_free_context(ctx);
	if (cfg)
		yices_free_config(cfg);

#ifndef Y2_FORCE_NONINC
  AVR_LOG(17, 0, "\t(non-inc result: " << ((!tryVarElim && getModel)?"":"--var-elim ") << (keepIte?"--keep-ite ":"") << ((res == STATUS_SAT) ? "sat" : (res == STATUS_UNSAT) ? "unsat" : "??") << ", t: " << time_res << " usec)" << endl);
#endif
  if ((!tryVarElim && getModel) && (res == STATUS_SAT))
  	assert(m_model != NULL);
	return res;
}

y2_result y2_API::shift_to_noninc(long timeout_value, long long time_res, bool getModel)
{
	if (!m_abstract && !allow_fallback) {
	  cout << "\n\t(query timeout reached, " << (m_abstract?"ab":"bv")
	      << ", depth: " << m_cList.size() << ", t:" << time_res << " usec)" << endl;
		print_query(time_res, TIME_TO, "to");
		Inst::g_result = f_to_query;
    assert(0);
	}

#ifndef Y2_FORCE_NONINC
	cout << "\n\t(fallback to non-inc solver, " << (m_abstract?"ab":"bv")
      << ", depth: " << m_cList.size() << ", t:" << time_res << " usec)" << endl;
//  print_query(time_res, TIME_TO, "to");
  Inst::numContextCalls++;
  countRefresh++;
#endif

  if (!allow_fallback)
  {
//    print_query(time_res, TIME_TO, "error");
		AVR_LOG(15, 0, "Y2 non-falling Query TIMEOUT (" << timeout_value << "), query type: " << queryType << ", getModel: " << getModel << endl);

#ifdef Y2_EXP
    y2_show_statistics(stdout, m_ctx);
    y2_stat qStat;
    yices_get_statistics(m_ctx, &qStat.st);
    qStat.print_stat(cout, "Query stats:");
#endif

  	return s_check_oneshot_reset(timeout_value, getModel);
  }

#ifdef Y2_RESET_FALLBACK_ONLY
	return s_check_oneshot_reset(timeout_value, getModel);
#else
#ifdef Y2_SOFT_TIMEOUT_INC
	int numReset = g_num_reset;
  struct rusage usage;
  struct timeval start_time, end_time;
  long long time_diff;
  long long time_solve = 0;
  TIME_S(start_time);
#endif
	y2_result res = s_check_oneshot(timeout_value, getModel, false, true, true);
#ifdef Y2_SOFT_TIMEOUT_INC
  TIME_E(start_time, end_time, time_solve);
	if (g_num_reset == numReset) {
		// Scope was not reset
		if (time_solve > time_res) {
			g_soft_timeout += Y2_SOFT_TIMEOUT_INC_VALUE;
		}
		else if (time_solve < (time_res / 2)) {
			g_soft_timeout -= Y2_SOFT_TIMEOUT_INC_VALUE;
		}
	}
#endif
	return res;
#endif
}

y2_result y2_API::shift_to_noninc(long timeout_value, y2_expr_vec& assumptions, y2_expr_vec& unsatCore, long long time_res, bool getModel)
{
	if (!m_abstract && !allow_fallback) {
		cout << "\n\t(query timeout reached, " << (m_abstract?"ab":"bv")
	      << ", depth: " << m_cList.size() << ", t:" << time_res << " usec)" << endl;
		print_query(time_res, TIME_TO, "to");
		Inst::g_result = f_to_query;
    assert(0);
	}

#ifndef Y2_FORCE_NONINC
	cout << "\n\t(fallback to non-inc solver (core), " << (m_abstract?"ab":"bv")
      << ", depth: " << m_cList.size() << ", t:" << time_res << " usec)" << endl;
//  print_query(time_res, TIME_TO, "to");
  Inst::numContextCalls++;
  countRefresh++;
#endif
  assert(allow_fallback);
#ifdef Y2_RESET_FALLBACK_ONLY
  return s_check_oneshot_mus_reset(timeout_value, assumptions, unsatCore, getModel);
#else
#ifdef Y2_SOFT_TIMEOUT_INC
	int numReset = g_num_reset;
  struct rusage usage;
  struct timeval start_time, end_time;
  long long time_diff;
  long long time_solve = 0;
  TIME_S(start_time);
#endif
  y2_result res = s_check_oneshot_mus(timeout_value, assumptions, unsatCore, getModel, false, true, true);
#ifdef Y2_SOFT_TIMEOUT_INC
  TIME_E(start_time, end_time, time_solve);
	if (g_num_reset == numReset) {
		// Scope was not reset
		if (time_solve > time_res) {
			g_soft_timeout += Y2_SOFT_TIMEOUT_INC_VALUE;
		}
		else if (time_solve < (time_res / 2)) {
			g_soft_timeout -= Y2_SOFT_TIMEOUT_INC_VALUE;
		}
	}
#endif
	return res;
#endif
}

y2_result y2_API::s_check_mus(long timeout_value, y2_expr_vec& assumptions, y2_expr_vec& unsatCore, bool getModel)
{
	long timeout_value_orig = timeout_value;
  if (allow_fallback) {
#ifdef Y2_FORCE_NONINC
  	return shift_to_noninc(timeout_value, assumptions, unsatCore, 0, getModel);
#endif

    timeout_value = g_soft_timeout;
  }

  increase_cond_activity();

  update_query_sz();
  struct rusage usage;
  struct timeval start_time, end_time;
  long long time_diff;
  long long time_res = 0;

//  collect_solv_presearch_statistic();
  Y2_SET_TIMEOUT(m_ctx);
  TIME_S(start_time);

  y2_expr_vector core_vector;
  yices_init_term_vector(&core_vector);

#ifdef TRACE_SOLVER
	for (int i = 0; i < assumptions.size(); i++)
	{
		string termS = print_smt_term(assumptions[i]);
		m_trace.push_back("(assert (! " + termS + " :named i$" + to_string(i) + "))");
	}
	m_trace.push_back("(check-sat)");
#endif

#ifdef Y2_CUSTOM
	y2_result res = yices_check_assumptions(m_ctx, m_param, assumptions.size(), &(assumptions.front()), &core_vector);
#else
	y2_result res = yices_check_context_with_assumptions(m_ctx, m_param, assumptions.size(), &(assumptions.front()));
#endif
  Y2_CHECK_TIMEOUT;

//  string comment = "inc ";
//  comment += m_abstract ? "ab" : "bv";
//  comment += ": ans- " + to_string(res);
//  print_asserts(comment);

  TIME_E(start_time, end_time, time_res);
  Solver::time_tmp += time_res;
#ifdef Y2_EXP
  collect_solv_statistic_query();
#endif

  if (res == STATUS_SAT)
  {
#ifdef DUMP_CONTEXT_SAT
    if (m_abstract)
      y2_dump_context(m_ctx);
#endif

    collect_stats_query(time_res, MUS_SAT);

		if (getModel)
		{
			if (m_model != NULL)
				yices_free_model(m_model);
			m_model = yices_get_model(m_ctx, true);

			bool mres = s_check_model();
			if (!mres)
			{
		    print_query(time_res, ERROR, "error");
			}
			assert(mres);
		}
	}
	else if (res == STATUS_UNSAT)
	{
    collect_stats_query(time_res, MUS_UNSAT);
#ifdef TRACE_SOLVER
    m_trace.push_back("(get-unsat-core)");
#endif
#ifndef Y2_CUSTOM
		int status = yices_get_unsat_core(m_ctx, &core_vector);
		assert(status == 0);
#endif

		unsatCore.clear();
		for (int i = 0; i < core_vector.size; i++)
			unsatCore.push_back(core_vector.data[i]);

#ifdef DUMP_CONTEXT_UNSAT
    if (m_abstract)
      y2_dump_context(m_ctx);
#endif
	}
	else
	{
	  assert(res != STATUS_ERROR);

    collect_stats_query(time_res, TIME_TO);

//    AVR_LOG(15, 0, "Y2 Query Soft TIMEOUT (" << timeout_value << ")" << endl);
//    print_query(time_res, TIME_TO, "to");
//    Solver::query_timed_out = true;
//    assert(0);

    y2_result newRes = shift_to_noninc(timeout_value_orig, assumptions, unsatCore, time_res, getModel);
    if (newRes != STATUS_SAT && newRes != STATUS_UNSAT)
      assert(0);
    res = newRes;
	}
  yices_delete_term_vector(&core_vector);
	return res;
}

y2_result y2_API::s_check_oneshot_mus_reset2(long timeout_value, y2_expr_vec& assumptions, y2_expr_vec& unsatCore, bool getModel, bool keepIte)
{
	struct rusage usage;
	struct timeval start_time, end_time;
	long long time_diff;

	long long time_assert = 0;
	long long time_solve = 0;

	bool singleFirst = false;
	if (!getModel)
		singleFirst = true;

	TIME_S(start_time);
	if (singleFirst)
		s_reset_single_solver();
	else
		s_reset_all_solvers();
	TIME_E(start_time, end_time, time_assert);

	TIME_S(start_time);
	s_reset_all_solvers();
	TIME_E(start_time, end_time, time_assert);

	TIME_S(start_time);
	y2_result res2 = s_check_oneshot_mus(timeout_value, assumptions, unsatCore, getModel, true, keepIte, false);
	TIME_E(start_time, end_time, time_solve);
	AVR_LOG(17, 0, "\t(result (after reset): " << ((res2 == STATUS_SAT) ? "sat" : (res2 == STATUS_UNSAT) ? "unsat" : "??")
			<< ", time: " << (time_assert + time_solve) << " usec (" << time_assert << " + " << time_solve << ")" << endl);

	if (singleFirst)
		s_reset_remaining_solvers(m_solver_id);

//	assert(0);
	return res2;
}

y2_result y2_API::s_check_oneshot_mus_reset(long timeout_value, y2_expr_vec& assumptions, y2_expr_vec& unsatCore, bool getModel)
{
	struct rusage usage;
	struct timeval start_time, end_time;
	long long time_diff;

	y2_result res2;
	bool useKeepIte = true;

	{
		s_reset_scope();

		{
			long long time_assert = 0;
			long long time_solve = 0;

			y2_API tmpSolver(m_mapper, m_ba_idx, static_cast<int>(1), queryType);
			tmpSolver.copy_attributes(this);

	//		y2_solvers.erase(tmpSolver.m_solver_id);
	//		y2_API tmpSolver(m_mapper, m_ba_idx, is_i, queryType);
			if (getModel)
				tmpSolver.enable_model();
			else
				tmpSolver.disable_model();
			tmpSolver.copy_induct(uType);

			TIME_S(start_time);
			tmpSolver.s_assert(m_asserts.assertions);
	//		for (auto& assertions: m_asserts.assertions)
	//			for (auto& v: assertions)
	//				tmpSolver.s_assert(v);
			tmpSolver.s_add_assumptions(m_asserts.assumptions, false);
			TIME_E(start_time, end_time, time_assert);

			TIME_S(start_time);
			res2 = tmpSolver.s_check_oneshot_mus(Y2_RESET_TIMEOUT_TRIAL, tmpSolver.get_assumptions(), unsatCore, false, false, true, false);
			TIME_E(start_time, end_time, time_solve);
			if (res2 == STATUS_SAT || res2 == STATUS_UNSAT)
				useKeepIte = true;

			AVR_LOG(17, 0, "\t(result (model " << (getModel ? "required" : "not required") << "): " << ((res2 == STATUS_SAT) ? "sat" : (res2 == STATUS_UNSAT) ? "unsat" : "??")
					<< ", time: " << (time_assert + time_solve) << " usec (" << time_assert << " + " << time_solve << ")" << endl);
		}
	}

  if (res2 != STATUS_SAT && res2 != STATUS_UNSAT) {
  	s_reset_scope();

    {
  		long long time_assert = 0;
  		long long time_solve = 0;

  		y2_API tmpSolver(m_mapper, m_ba_idx, static_cast<int>(1), queryType);
			tmpSolver.copy_attributes(this);

  //		y2_solvers.erase(tmpSolver.m_solver_id);
  //		y2_API tmpSolver(m_mapper, m_ba_idx, is_i, queryType);
  		if (getModel)
  			tmpSolver.enable_model();
  		else
  			tmpSolver.disable_model();
			tmpSolver.disable_keep_ite();
			tmpSolver.copy_induct(uType);

  		TIME_S(start_time);
  		tmpSolver.s_assert(m_asserts.assertions);
  //		for (auto& assertions: m_asserts.assertions)
  //			for (auto& v: assertions)
  //				tmpSolver.s_assert(v);
  		tmpSolver.s_add_assumptions(m_asserts.assumptions, false);
  		TIME_E(start_time, end_time, time_assert);

  		TIME_S(start_time);
  		res2 = tmpSolver.s_check_oneshot_mus(Y2_RESET_TIMEOUT_TRIAL, tmpSolver.get_assumptions(), unsatCore, false, false, false, false);
  		TIME_E(start_time, end_time, time_solve);
		if (res2 == STATUS_SAT || res2 == STATUS_UNSAT)
			useKeepIte = false;

  		AVR_LOG(17, 0, "\t(result (model " << (getModel ? "required" : "not required") << "): " << ((res2 == STATUS_SAT) ? "sat" : (res2 == STATUS_UNSAT) ? "unsat" : "??")
  				<< ", time: " << (time_assert + time_solve) << " usec (" << time_assert << " + " << time_solve << ")" << endl);
    }
  }


  if (res2 != STATUS_SAT && res2 != STATUS_UNSAT) {
		s_reset_scope();

		{
			long long time_assert = 0;
			long long time_solve = 0;

			y2_API tmpSolver(m_mapper, m_ba_idx, static_cast<int>(1), queryType);
			tmpSolver.copy_attributes(this);

	//		y2_solvers.erase(tmpSolver.m_solver_id);
	//		y2_API tmpSolver(m_mapper, m_ba_idx, is_i, queryType);
			if (getModel)
				tmpSolver.enable_model();
			else
				tmpSolver.disable_model();
			tmpSolver.copy_induct(uType);

			TIME_S(start_time);
			tmpSolver.s_assert(m_asserts.assertions);
	//		for (auto& assertions: m_asserts.assertions)
	//			for (auto& v: assertions)
	//				tmpSolver.s_assert(v);
			tmpSolver.s_add_assumptions(m_asserts.assumptions, false);
			TIME_E(start_time, end_time, time_assert);

			TIME_S(start_time);
			res2 = tmpSolver.s_check_oneshot_mus(timeout_value, tmpSolver.get_assumptions(), unsatCore, false, false, true, false);
			TIME_E(start_time, end_time, time_solve);
			if (res2 == STATUS_SAT || res2 == STATUS_UNSAT)
				useKeepIte = true;

			AVR_LOG(17, 0, "\t(result (model " << (getModel ? "required" : "not required") << "): " << ((res2 == STATUS_SAT) ? "sat" : (res2 == STATUS_UNSAT) ? "unsat" : "??")
					<< ", time: " << (time_assert + time_solve) << " usec (" << time_assert << " + " << time_solve << ")" << endl);
		}
	}

  if (res2 != STATUS_SAT && res2 != STATUS_UNSAT) {
  	s_reset_scope();

    {
  		long long time_assert = 0;
  		long long time_solve = 0;

  		y2_API tmpSolver(m_mapper, m_ba_idx, static_cast<int>(1), queryType);
			tmpSolver.copy_attributes(this);

  //		y2_solvers.erase(tmpSolver.m_solver_id);
  //		y2_API tmpSolver(m_mapper, m_ba_idx, is_i, queryType);
  		if (getModel)
  			tmpSolver.enable_model();
  		else
  			tmpSolver.disable_model();
			tmpSolver.disable_keep_ite();
			tmpSolver.copy_induct(uType);

  		TIME_S(start_time);
  		tmpSolver.s_assert(m_asserts.assertions);
  //		for (auto& assertions: m_asserts.assertions)
  //			for (auto& v: assertions)
  //				tmpSolver.s_assert(v);
  		tmpSolver.s_add_assumptions(m_asserts.assumptions, false);
  		TIME_E(start_time, end_time, time_assert);

  		TIME_S(start_time);
  		res2 = tmpSolver.s_check_oneshot_mus(timeout_value, tmpSolver.get_assumptions(), unsatCore, false, false, false, false);
  		TIME_E(start_time, end_time, time_solve);
		if (res2 == STATUS_SAT || res2 == STATUS_UNSAT)
			useKeepIte = true;

  		AVR_LOG(17, 0, "\t(result (model " << (getModel ? "required" : "not required") << "): " << ((res2 == STATUS_SAT) ? "sat" : (res2 == STATUS_UNSAT) ? "unsat" : "??")
  				<< ", time: " << (time_assert + time_solve) << " usec (" << time_assert << " + " << time_solve << ")" << endl);
    }
  }

  if (res2 != STATUS_SAT && res2 != STATUS_UNSAT) {
    {
			long long time_assert = 0;
			long long time_solve = 0;

			y2_reset();
			y2_API tmpSolver(m_mapper, m_ba_idx, is_i, queryType);
			tmpSolver.copy_attributes(this);

			tmpSolver.disable_model();
			TIME_S(start_time);
			for (auto& assertions: m_asserts.assertions)
				for (auto& v: assertions)
					tmpSolver.s_assert(v);
			for (auto& v: m_asserts.assumptions)
				tmpSolver.s_assert(v);
			TIME_E(start_time, end_time, time_assert);

			TIME_S(start_time);
			y2_result res2 = tmpSolver.s_check_oneshot(0, false, false, true, false);
			TIME_E(start_time, end_time, time_solve);
			AVR_LOG(17, 0, "\t(result --var-elim --keep-ite: " << ((res2 == STATUS_SAT) ? "sat" : (res2 == STATUS_UNSAT) ? "unsat" : "??")
					<< ", time: " << (time_assert + time_solve) << " usec (" << time_assert << " + " << time_solve << ")" << endl);
    }

    {
			long long time_assert = 0;
			long long time_solve = 0;

			y2_reset();
			y2_API tmpSolver(m_mapper, m_ba_idx, is_i, queryType);
			tmpSolver.copy_attributes(this);

			tmpSolver.enable_model();
			TIME_S(start_time);
			for (auto& assertions: m_asserts.assertions)
				for (auto& v: assertions)
					tmpSolver.s_assert(v);
			for (auto& v: m_asserts.assumptions)
				tmpSolver.s_assert(v);
			TIME_E(start_time, end_time, time_assert);

			TIME_S(start_time);
			y2_result res2 = tmpSolver.s_check_oneshot(0, true, false, false, false);
			TIME_E(start_time, end_time, time_solve);
			AVR_LOG(17, 0, "\t(result: " << ((res2 == STATUS_SAT) ? "sat" : (res2 == STATUS_UNSAT) ? "unsat" : "??")
					<< ", time: " << (time_assert + time_solve) << " usec (" << time_assert << " + " << time_solve << ")" << endl);
    }

		Inst::g_result = f_to_query;
    assert(0);
  }

	s_reset_scope();

  int solver_id = m_solver_id;
  s_reset_solver();

  if (getModel) {
  	if (res2 == STATUS_SAT)
  		s_check_oneshot_mus(timeout_value, get_assumptions(), unsatCore, getModel, false, useKeepIte, false);
  }

	s_reset_remaining_solvers(solver_id);

//	assert(0);
	return res2;
}

y2_result y2_API::s_check_oneshot_mus(long timeout_value, y2_expr_vec& assumptions, y2_expr_vec& unsatCore, bool getModel, bool tryVarElim, bool keepIte, bool enReset)
{
#ifdef Y2_DISABLE_TRY_VAR_ELIM
	tryVarElim = false;
#endif

#ifdef Y2_CUSTOM
	enReset = false;
#endif
	long timeout_value_orig = timeout_value;
	if (enReset)
		timeout_value = Y2_RESET_TIMEOUT;

  y2_config cfg = yices_new_config();
  set_logic(cfg);
  yices_set_config(cfg, "mode", "one-shot");

  y2_context ctx = yices_new_context(cfg);
  set_context_parameters(ctx);
  if (!tryVarElim && getModel)
  	disable_var_elim(ctx);
  else
  	enable_var_elim(ctx);
  if (!keepIte)
  	disable_keep_ite(ctx);

  y2_param prm = yices_new_param_record();
  yices_default_params_for_context(ctx, prm);
  set_parameters(prm);

  y2_expr_vec assertions;
  for (auto& v: m_cList)
    for (auto& c: v.second)
      assertions.push_back(c);
  yices_assert_formulas(ctx, assertions.size(), &(assertions.front()));

//  for (auto& v: m_cList)
//    yices_assert_formulas(ctx, v.second.size(), &(v.second.front()));

//  for (auto& v: m_cList)
//		for (auto& c: v.second)
//			yices_assert_formula(ctx, c);

  update_query_sz();
	struct rusage usage;
	struct timeval start_time, end_time;
	long long time_diff;
	long long time_res = 0;

	Y2_SET_TIMEOUT(ctx);
	TIME_S(start_time);

  y2_expr_vector core_vector;
  yices_init_term_vector(&core_vector);

#ifdef TRACE_SOLVER
	for (int i = 0; i < assumptions.size(); i++)
	{
		string termS = print_smt_term(assumptions[i]);
		m_trace.push_back("(assert (! " + termS + " :named i$" + to_string(i) + "))");
	}
	m_trace.push_back("(check-sat)");
#endif

#ifdef Y2_CUSTOM
	y2_result res = yices_check_assumptions(ctx, prm, assumptions.size(), &(assumptions.front()), &core_vector);
#else
	y2_result res = yices_check_context_with_assumptions(ctx, prm, assumptions.size(), &(assumptions.front()));
#endif
	Y2_CHECK_TIMEOUT;

	TIME_E(start_time, end_time, time_res);
  Solver::time_tmp += time_res;
//	collect_solv_statistic_query();

	if (res == STATUS_SAT)
	{
    collect_stats_query(time_res, MUS_SAT);

		if (getModel)
		{
			if (tryVarElim)
			{
				res = s_check_oneshot_mus(timeout_value_orig, assumptions, unsatCore, getModel, false, keepIte, enReset);
			}
			else
			{
				if (m_model != NULL)
					yices_free_model(m_model);
				m_model = yices_get_model(ctx, true);

				bool mres = s_check_model();
				if (!mres)
				{
			    print_query(time_res, ERROR, "error");
				}
				assert(mres);
			}
		}
	}
	else if (res == STATUS_UNSAT)
	{
    collect_stats_query(time_res, MUS_UNSAT);
#ifdef TRACE_SOLVER
    m_trace.push_back("(get-unsat-core)");
#endif
#ifndef Y2_CUSTOM
		int status = yices_get_unsat_core(ctx, &core_vector);
		assert(status == 0);
#endif

		unsatCore.clear();
		for (int i = 0; i < core_vector.size; i++)
			unsatCore.push_back(core_vector.data[i]);
	}
	else
	{
    if (res == STATUS_ERROR) {
    	yices_print_error(stdout);
    }
    assert(res != STATUS_ERROR);

    collect_stats_query(time_res, TIME_TO);

//    print_query(time_res, TIME_TO, "error");
    AVR_LOG(15, 0, "Y2 mus Query TIMEOUT (" << timeout_value << ")" <<
    		", query type: " << queryType <<
    		", getModel: " << getModel <<
    		", tryVarElim: " << tryVarElim <<
    		", keepIte: " << keepIte <<
    		", enReset: " << enReset <<
				endl);
    AVR_LOG(15, 0, "result: " << res << endl);

#ifdef Y2_EXP
    y2_show_statistics(stdout, ctx);
    y2_stat qStat;
    yices_get_statistics(ctx, &qStat.st);
    qStat.print_stat(cout, "Query stats:");
#endif

  	if (enReset) {
  		if (prm)
  			yices_free_param_record(prm);
  		if (ctx)
  			yices_free_context(ctx);
  		if (cfg)
  			yices_free_config(cfg);
  		yices_delete_term_vector(&core_vector);

  		return s_check_oneshot_mus_reset(timeout_value_orig, m_assumptions, m_unsatCore, getModel);
  	}

//  	if (keepIte)
//  		return s_check_oneshot_mus_reset(timeout_value_orig, m_assumptions, m_unsatCore, getModel, false, false);

	}

//  collect_solv_statistic_end();

	if (prm)
		yices_free_param_record(prm);
	if (ctx)
		yices_free_context(ctx);
	if (cfg)
		yices_free_config(cfg);
	yices_delete_term_vector(&core_vector);
#ifndef Y2_FORCE_NONINC
  AVR_LOG(17, 0, "\t(non-inc result: " << ((!tryVarElim && getModel)?"":"--var-elim ") << (keepIte?"--keep-ite ":"") << ((res == STATUS_SAT) ? "sat" : (res == STATUS_UNSAT) ? "unsat" : "??")
  		<< ", t: " << time_res << " usec, core: " << assumptions.size() << " -> " << unsatCore.size() << ")" << endl);
#endif
  if ((!tryVarElim && getModel) && (res == STATUS_SAT))
  	assert(m_model != NULL);
	return res;
}

Solver* y2_API::copy_solver(void)
{
	y2_API* ni_solver = new y2_API(m_mapper, AVR_EXTRA_IDX, true, queryType);
	ni_solver->copy_asserts(m_asserts);
	for (auto& l: m_cList)
	{
		for (auto& c: l.second)
			ni_solver->s_assert_constraint(c);
	}
	return ni_solver;
}

bool y2_API::s_another_solution(void)
{
	int res = yices_assert_blocking_clause(m_ctx);
	if (res != 0)
		yices_print_error(stdout);
	assert(res == 0);

	int result = s_check(AB_QUERY_TIMEOUT);
	assert (result != AVR_QTO);
	bool ret = (result == AVR_QUSAT) ? false : true;
	return ret;
}

bool y2_API::get_relation(Inst* lhs, Inst* rhs, bool expected)
{
#ifdef Y2_EXP
	assert(m_model != NULL);
	assert(m_abstract);

	assert(lhs->sval.size() > m_ba_idx);
	assert(rhs->sval.size() > m_ba_idx);

	y2_expr decl_l = lhs->y2_node.solv_var(get_vIdx());
	y2_expr decl_r = rhs->y2_node.solv_var(get_vIdx());
	assert(decl_l != Y2_INVALID_EXPR);
	assert(decl_r != Y2_INVALID_EXPR);

	int val;
	int result = yices_get_eterm_relation(m_ctx, m_model, decl_l, decl_r, &val);
	assert (result == 0);

	bool isAssigned = (val != -1);
//  cout << "\t[" << *lhs << " == " << *rhs << "] -> " << (isAssigned ? to_string(val) : "x") << " (expected: " << expected << ")" << endl;

	if (isAssigned)
	{
	  assert(expected == (val == 1));
//    cout << "\t[" << *lhs << " == " << *rhs << "] -> " << (isAssigned ? to_string(val) : "x") << " (expected: " << expected << ")" << endl;
	}
	else
	{
//	  cout << "\t[" << *lhs << " == " << *rhs << "] -> " << (isAssigned ? to_string(val) : "x") << " (expected: " << expected << ")" << endl;
	}
	return isAssigned;
#else
	return true;
#endif
}

bool y2_API::get_assignment(Inst* e, int& val)
{
	assert(e->get_sort_type() == bvtype);
	assert(m_model != NULL);

	y2_expr decl = e->y2_node.solv_var(get_vIdx());
	if (decl == Y2_INVALID_EXPR) {
//		cout << *e << endl;
		e->set_bval(INVALID_SVAL);
		return false;
	}
	assert(decl != Y2_INVALID_EXPR);

	assert(e->get_size() == 1);

	y2_val value;
  int status = yices_get_value(m_model, decl, &value);
	if (status == -1) {
		AVR_LOG(11, 3, *e << " is don't care" << endl);
		e->set_bval(INVALID_SVAL);
		return false;
	}

	val = INVALID_SVAL;
	bool done = false;

	// array interpretation for ==, !=
	if (Inst::en_array) {
		Inst* e_new = e->get_port();
		OpInst* op = OpInst::as(e_new);
		if (op) {
			if (op->get_op() == OpInst::Eq || op->get_op() == OpInst::NotEq) {
				Inst* lhs = e_new->get_children()->front();
				Inst* rhs = e_new->get_children()->back();

				if (lhs->get_sort_type() == arraytype) {
					assert(lhs->get_sort() == rhs->get_sort());
					bool eq = false;

					mpz_class* valL = lhs->get_ival();
					mpz_class* valR = rhs->get_ival();

					if (valL == INVALID_SMPZ || valR == INVALID_SMPZ) {
//						val = INVALID_SVAL;
//						done = true;
//						assert(0);
					}
					else {
						eq = (*valL == *valR);
						if (op->get_op() == OpInst::NotEq)
							eq = !eq;
						val = eq;
						done = true;
					}
				}
			}
		}
	}

	int val2 = val;

//	if (!done)
	{
		if (m_mapper->fetch_var(e) == TheoryMapper::BV_VAR)
		{
			int result = yices_get_bool_value(m_model, decl, &val);
			if (result == -1)
			{
				cout << *e << "\t" << e->get_sort().sort2str() << "\t" << print_term(decl) << endl;
				cout << yices_error_string() << endl;
				assert(0);
			}
			assert(result == 0);
		}
		else
		{
			assert (m_mapper->fetch_var(e) == TheoryMapper::BOOL_VAR);
			int result = yices_get_bool_value(m_model, decl, &val);
			if (result == -1)
			{
				assert(0);
			}
			assert(result == 0);
		}
	}

	if (done) {
		if (val2 != val) {
			cout << "got conflicting assignment for " << *e << endl;
			cout << "yices says " << val << endl;
			cout << "children says " << val2 << endl;
			cout << "decl: " << print_term(decl) << endl;

//			print_query(0, ERROR, "y2err");
//			s_print_model();
			assert(0);
		}
	}

	if (val == 1)
	{
		e->set_bval(1);
	}
	else
	{
		assert(val == 0);
		e->set_bval(0);
	}

	AVR_LOG(11, 3, "[VALB] " << *e << "\t" << print_term(decl) << " (" << print_type(yices_type_of_term(decl)) << ") \t" << val << endl);

#ifdef DO_CORRECTNESS_CHECKS
	Inst* tve = e;
	OpInst* op = OpInst::as(e);
	if (op && (op->get_op() == OpInst::Eq || op->get_op() == OpInst::NotEq))
	{
		Inst* lhs = tve->get_children()->front();
		Inst* rhs = tve->get_children()->back();

		bool eq;
		if (lhs->get_size() == 1)
		{
			int val_l = lhs->get_bval();
			int val_r = rhs->get_bval();
			if (val_l == INVALID_SVAL)
				return true;
			if (val_r == INVALID_SVAL)
				return true;
			eq = (val_l == val_r);
		}
		else
		{
			mpz_class* val_l = lhs->get_ival();
			mpz_class* val_r = rhs->get_ival();
			if (val_l == INVALID_SMPZ)
				return true;
			if (val_r == INVALID_SMPZ)
				return true;
			eq = (*val_l == *val_r);
		}

		bool errorFlag = false;

		if ((op->get_op() == OpInst::Eq && val == 1) ||
				(op->get_op() == OpInst::NotEq && val == 0))
		{
			if (!eq)
				errorFlag = true;
		}
		else
		{
			if (eq)
				errorFlag = true;
		}

		if (errorFlag)
		{
			cout << "Error in ==/!=: " << *tve << endl;
			cout << "expr  : " << *tve << " " << " (aka " << print_term(decl) << ") " << e->get_bval() << endl;
			cout << "expr  : " << *tve << " " << " (aka " << print_term(decl) << ") " << val << endl;

			y2_expr_ptr decl_l = lhs->y2_node.solv_var(get_vIdx());
			y2_expr_ptr decl_r = rhs->y2_node.solv_var(get_vIdx());

			if (lhs->get_size() == 1) {
				cout << "lhs  : " << *lhs << " " << " (aka " << print_term(decl_l) << ") " << lhs->get_bval() << endl;
				cout << "rhs  : " << *rhs << " " << " (aka " << print_term(decl_r) << ") " << rhs->get_bval() << endl;
			}
			else {
				cout << "lhs  : " << *lhs << " " << " (aka " << print_term(decl_l) << ") " << *lhs->get_ival() << endl;
				cout << "rhs  : " << *rhs << " " << " (aka " << print_term(decl_r) << ") " << *rhs->get_ival() << endl;
			}

			cout << "formula val: " << yices_formula_true_in_model(m_model, decl) << endl;

			y2_val val_l, val_r;
			yices_get_value(m_model, decl_l, &val_l);
			yices_get_value(m_model, decl_r, &val_r);

			cout << "val lhs  : " << val_l.node_id << endl;
			cout << "val rhs  : " << val_r.node_id << endl;

			assert(0);
		}
	}
	else
	{
		if (op && op->get_op() == OpInst::LogNot)
		{
			tve = e->get_children()->front();
			assert(tve->get_size() == 1);

			y2_expr decl_t = tve->y2_node.solv_var(get_vIdx());
			assert(decl_t != Y2_INVALID_EXPR);

			int val_t = tve->get_bval();
			if (val_t == INVALID_SVAL)
				return true;

			if (val_t == e->get_bval())
			{
				cout << endl << "Error in (not) in SID: " << m_solver_id << " BA: " << m_ba_idx << endl;
				cout << "expr  : " << *e << " " << " (aka " << print_term(decl) << ") " << val << endl;
				cout << "!expr : " << *tve << " " << " (aka " << print_term(decl_t) << ") " << val_t << endl;
				assert(0);
			}
		}
	}
#endif
	return true;
}

void y2_API::get_value_bv(unsigned sz, y2_expr& decl, string& sval) {
	assert(sz > 0);
	int val;
	if (sz == 1 && !yices_get_bool_value(m_model, decl, &val)) {
		sval = val_to_str(val, sz, false);
	}
	else {
		int bv[sz];
		int result = yices_get_bv_value(m_model, decl, bv);
		assert(result == 0);
		sval = arr_to_str(bv, sz);
	}
	assert(sval.size() == sz);
}
void y2_API::get_value_bv(unsigned sz, y2_val* decl, string& sval) {
	assert(sz > 0);
	int val;
	if (sz == 1 && !yices_val_get_bool(m_model, decl, &val)) {
		sval = val_to_str(val, sz, false);
	}
	else {
		int bv[sz];
		int result = yices_val_get_bv(m_model, decl, bv);
		assert(result == 0);
		sval = arr_to_str(bv, sz);
	}
	assert(sval.size() == sz);
}

void y2_API::get_value_int(unsigned sz, y2_expr& decl, string& sval) {
	assert(sz == INT_SZ);
	long val;
	int result = yices_get_int64_value(m_model, decl, &val);
	assert(result == 0);
	sval = to_string(val);
}
void y2_API::get_value_int(unsigned sz, y2_val* decl, string& sval) {
	assert(sz == INT_SZ);
	long val;
	int result = yices_val_get_int64(m_model, decl, &val);
	assert(result == 0);
	sval = to_string(val);
}

void y2_API::get_value_utt(unsigned sz, y2_expr& decl, string& sval) {
	int result;
	if (sz == 1) {
		int val;
		int result = yices_get_bool_value(m_model, decl, &val);
		assert(result == 0);
		sval = val_to_str(val, sz, false);
	}
	else {
		int32_t valTmp = 1;
		result = yices_get_scalar_value(m_model, decl, &valTmp);
		assert(result == 0);
		sval = "u" + val_to_str(valTmp, 0, false);
	}
}
void y2_API::get_value_utt(unsigned sz, y2_val* decl, string& sval) {
	int result;
	if (sz == 1) {
		int val;
		int result = yices_val_get_bool(m_model, decl, &val);
		assert(result == 0);
		sval = val_to_str(val, sz, false);
	}
	else {
		int32_t valTmp = 1;
		y2_type tmpt;
		if (decl->node_tag == YVAL_BV) {
			int bv[sz];
			int result = yices_val_get_bv(m_model, decl, bv);
			assert(result == 0);
			sval = "u" + arr_to_str(bv, sz);
		} else {
			result = yices_val_get_scalar(m_model, decl, &valTmp, &tmpt);
			assert(result == 0);
			sval = "u" + val_to_str(valTmp, 0, false);
		}
	}
}

void y2_API::get_value(bool abstract, SORT& sort, y2_val& decl, string& sval) {
	if (decl.node_tag != YVAL_UNKNOWN) {
		switch(sort.type) {
		case bvtype:
			if (abstract)
				get_value_utt(sort.sz, &decl, sval);
			else
				get_value_bv(sort.sz, &decl, sval);
			break;
		case inttype:
			if (abstract)
				get_value_utt(sort.sz, &decl, sval);
			else
				get_value_int(sort.sz, &decl, sval);
			break;
		case arraytype:
			get_value_arr(abstract, sort, &decl, sval);
			break;
		default:
			assert(0);
		}
	}
	else if (abstract) {
		sval = "u";
	}
	else {
		sval = "?";
//		assert(0);
	}
}

void y2_API::get_value_arr(bool abstract, SORT& sort, y2_val* decl, string& sval) {
	assert(sort.type == arraytype);
	assert(sort.args.size() == 2);

	y2_val def;
  y2_val_vector m;
  yices_init_yval_vector(&m);

  int result = yices_val_expand_function(m_model, decl, &def, &m);
  assert(result == 0);

  SORT& d = sort.args.front();
  SORT& r = sort.args.back();

	string defstr;
	get_value(abstract, r, def, defstr);

	map < string, string > vMap;
	y2_val value;
	for (int i = 0; i < m.size; i++) {
		y2_val address;
    result = yices_val_expand_mapping(m_model, &m.data[i], &address, &value);
		assert(result == 0);

		string addrstr;
		get_value(abstract, d, address, addrstr);

		string valstr;
		get_value(abstract, r, value, valstr);

		vMap[addrstr] = valstr;
	}
  yices_delete_yval_vector(&m);

//	cout << sort.sort2str() << "\tdef: " << defstr << endl;
//  for (auto& v: vMap)
//    cout << v.first << " -> " << v.second << endl;

  //  if (false && !abstract && d.type == bvtype) {
	if (!abstract && d.type == bvtype && r.type == bvtype) {
    sval = "";
    for (int i = pow(2, d.sz) - 1; i >= 0; i--) {
    	map < string, string >::iterator mit = vMap.find(val_to_str(i, d.sz, false));
    	if (mit != vMap.end())
    		sval += (*mit).second;
    	else
    		sval += defstr;
    }
  }
  else {
    sval = "a" + defstr + "b";
		for (auto& v: vMap)
			sval += v.first + "c" + v.second + "d";
  }
}

bool y2_API::get_assignment(Inst* e, mpz_class* val)
{
  assert(m_model != NULL);
  assert(e->get_size() != 1);

  y2_expr decl = e->y2_node.solv_var(get_vIdx());
	if (decl == Y2_INVALID_EXPR) {
//		cout << *e << endl;
		e->set_ival(INVALID_SMPZ);
		return false;
	}
  assert(decl != Y2_INVALID_EXPR);

	y2_val value;
  int status = yices_get_value(m_model, decl, &value);
	if (status == -1) {
		AVR_LOG(11, 3, *e << " is don't care" << endl);
		e->set_ival(INVALID_SMPZ);
		return false;
	}

  string sval;
  int base = 2;
  if (m_mapper->fetch_var(e) == TheoryMapper::BV_VAR)
  {
		if (e->get_sort_type() == bvtype) {
			get_value_bv(e->get_size(), decl, sval);
		}
		else if (e->get_sort_type() == inttype) {
			base = 10;
			get_value_int(e->get_size(), decl, sval);
		}
		else if (e->get_sort_type() == arraytype) {
			y2_val value;
	    int result = yices_get_value(m_model, decl, &value);
	    assert(result == 0);
	    SORT sort = e->get_sort();
	    if (m_mapper->fetch_op(e) == TheoryMapper::BV_OP) {
				// get concrete value
				get_value_arr(false, sort, &value, sval);
	    } else {
				// get abstract value
				get_value_arr(true, sort, &value, sval);
	    }

//	    cout << *e << " bv has value: " << sval << endl;
//	    assert(0);
		}
		else {
			assert(0);
		}
	}
  else
  {
    assert (m_mapper->fetch_var(e) == TheoryMapper::EUF_VAR);
		if (e->get_sort_type() == bvtype || e->get_sort_type() == inttype) {
			get_value_utt(e->get_size(), decl, sval);
		}
		else if (e->get_sort_type() == arraytype) {
			y2_val value;
	    int result = yices_get_value(m_model, decl, &value);
	    assert(result == 0);
	    SORT sort = e->get_sort();
	    // get abstract value
	    get_value_arr(true, sort, &value, sval);

//	    cout << *e << " ab has value: " << sval << endl;
//	    assert(0);
		}
		else {
			assert(0);
		}
  }

  auto mit = solv_values.find(sval);
  mpz_class* pval = INVALID_SMPZ;
  if (mit != solv_values.end())
    pval = &(*mit).second;

//  cout << *e << " gets " << sval << endl;
  if (pval == INVALID_SMPZ)
  {
    mpz_class zval;
    if (m_mapper->fetch_var(e) == TheoryMapper::BV_VAR)
    {
//  		zval = mpz_class(sval, base);
    	bool isNum = (sval[0] == '-' || isdigit(sval[0]));
    	if (isNum) {
				for (int i = 1; i < sval.length(); i++) {
					if (!isdigit(sval[i])) {
						isNum = false;
						break;
					}
				}
    	}
    	if (isNum) {
    		zval = mpz_class(sval, base);
    	}
    	else {
				int dval = solv_values.size() + 2;
				dval *= -1;
				zval = mpz_class(dval);
//				assert(0);
    	}
    }
    else
    {
      int dval = solv_values.size() + 2;
			dval *= -1;
      zval = mpz_class(dval);
    }
    solv_values[sval] = zval;
    AVR_LOG(11, 1, "inserting ut value: " << sval << " with key " << zval << endl);

    mit = solv_values.find(sval);
    assert (mit != solv_values.end());
    pval = &(*mit).second;
  }

  e->set_ival(pval);
  val = pval;

  AVR_LOG(11, 3, "[VALE] " << *e << "\t" << print_term(decl) << " (" << print_type(yices_type_of_term(decl)) << ") \t" << *pval << "\t" << sval << endl);

  return true;
}

#ifdef ASSERT_DISTINCT_NUMBERS
void y2_API::assert_distinct_constants(void)
{
#ifdef Y2_CREATE_UCONSTANTS
  return;
#endif

//#ifndef TEST_CONNECT_BV
  if (m_mapper->fetch_logic() == TheoryMapper::QF_BV)
		return;
  if (Config::g_ab_interpret) {
  	if ((Config::g_ab_interpret_excc >= LEVEL_EXCC_ALL) || (Config::g_ab_interpret_limit == 0))
  		return;
  }
//#endif

	m_constraints.clear();
	int idx = y2_API::m_distinct_constraints.first;
	if (idx != -1)
	{
		y2_expr_vec& dV = y2_API::m_distinct_constraints.second;
		for (auto& dis : dV)
		{
			add_constraint(dis, "forcing distinct constant: ", 0, true, false);
//			cout << "SID: " << m_solver_id << "\t" << print_term(dis) << endl;
		}
	}
	else
	{
		y2_expr_vec dV;
		for (auto& i : NumInst::m_sz_to_constants)
		{
			pair<unsigned, SORT> sz = i.first;
			InstS& consts = i.second;
			unsigned numConsts = consts.size();
			if (numConsts > 1)
			{
				Inst* top = (*consts.begin());
				if (m_mapper->fetch_var(top) == TheoryMapper::BV_VAR)
					continue;
				y2_expr_vec yV;
				for (auto& e : consts)
				{
					e->y2_node.set_key();
					y2_expr& y = e->y2_node.y2_var[get_vIdx()];
					if (y == Y2_INVALID_EXPR)
					{
						string name = get_y2_name(e);
						y = create_int_var(name, sz);
						e->y2_node.y2_vset[get_vIdx()] = true;
					}
					yV.push_back(y);
				}
				unsigned vSz = yV.size();
				if (vSz > 1)
				{
					y2_expr dis = yices_distinct(vSz, &(yV.front()));
					assert (dis != Y2_INVALID_EXPR);

					dV.push_back(dis);
					add_constraint(dis, "forcing distinct constant: ", 0, true, false);
//					cout << "SID: " << m_solver_id << "\t" << print_term(dis) << endl;
				}
			}
		}
		m_distinct_constraints = make_pair(1, dV);
	}
	if (!m_constraints.empty())
	{
		s_assert_constraints();
	}
}
#endif

#ifdef Y2_EXP
void y2_API::collect_solv_statistic_query()
{
  y2_stat tmpStat;
  bool rstat = yices_get_statistics(m_ctx, &tmpStat.st);
  assert(rstat);
  switch (queryType)
  {
  case cti:
    g_stat_cti.collect_query_stats(tmpStat, m_abstract);  break;
  case br:
    g_stat_br.collect_query_stats(tmpStat, m_abstract);  break;
  case fp:
    g_stat_fp.collect_query_stats(tmpStat, m_abstract);  break;
  case mus_core:
    g_stat_core.collect_query_stats(tmpStat, m_abstract);  break;
  case mus_min:
    g_stat_min.collect_query_stats(tmpStat, m_abstract);  break;
  case regular:
    g_stat_reg.collect_query_stats(tmpStat, m_abstract);  break;
  }
}
#endif

#ifdef Y2_EXP
void y2_API::collect_solv_statistic_end()
{
  y2_stat tmpStat;
  bool rstat = yices_get_statistics(m_ctx, &tmpStat.st);
  assert(rstat);
  switch (queryType)
  {
  case cti:
    g_stat_cti.collect_end_stats(tmpStat, m_abstract);  break;
  case br:
    g_stat_br.collect_end_stats(tmpStat, m_abstract);  break;
  case fp:
    g_stat_fp.collect_end_stats(tmpStat, m_abstract);  break;
  case mus_core:
    g_stat_core.collect_end_stats(tmpStat, m_abstract);  break;
  case mus_min:
    g_stat_min.collect_end_stats(tmpStat, m_abstract);  break;
  case regular:
    g_stat_reg.collect_end_stats(tmpStat, m_abstract);  break;
  }
}
#endif

y2_expr_ptr y2_API::create_y2_number(NumInst* num) {
	if (num->get_sort_type() == bvtype) {
		int sz = num->get_size();

		if (sz == 1) {
			if (num->get_num() == 1)
				return m_b1;
			else {
				assert (num->get_num() == 0);
				return m_b0;
			}
		}

		int bv_val[sz];
		string str_num = num->get_mpz()->get_str(2);

		if(str_num[0] == '-'){
			//cout << "str_num: " << str_num << endl;
			int i = 0;
			int j = str_num.length() - 1;
			for(; i < int(str_num.length() - 1); ++i, --j){
				bv_val[i] = (str_num[j] == '0') ? 1 : 0;
			}
			for(; i < sz; ++i){
				bv_val[i] = 1;
			}

			// plus one
			for(i=0; i < sz; ++i){
				if(bv_val[i] == 1){
					bv_val[i] = 0;
				}else{
					bv_val[i] = 1;
					break;
				}
			}
			y2_expr_ptr c = yices_bvconst_from_array(sz, bv_val);
			return c;
		}else{
			int i = 0;
			int j = str_num.length() - 1;
			for(; i < int(str_num.length()); ++i, --j){
				bv_val[i] = (int)str_num[j] - (int)'0';
			}
			for(; i < sz; ++i){
				bv_val[i] = 0;
			}
			y2_expr_ptr c = yices_bvconst_from_array(sz, bv_val);
			return c;
		}
	}
	else if (num->get_sort_type() == inttype) {
		y2_expr_ptr c = yices_int64(num->get_num());
		return c;
	}
	else {
		cout << *num << endl;
		assert(0);
	}
}

void y2_API::inst2yices(Inst*e, bool bvAllConstraints)
{
//  	cout<< endl << "--en--> " << *e << endl;
	assert(e != 0);
	assert(m_mapper);
//	cout << "m_ba_idx: " << m_ba_idx << "  e->yvar_sz: " << e->yvar.size() << endl;

	if (e->get_visit())
	{
//	  	cout<< endl << "--gex--> " << *e << "\t" << print_term(e->yvar[m_ba_idx]) << endl;

		assert (e->y2_node.get_y2_key() == Y2_INFO::st_y2_key);
		return;
	}
	e->set_visit();

	// do the children first.
	y2_expr_list y_ch;
	const InstL* ch = e->get_children();
	Ints s_sz;

	unsigned yIdx = get_vIdx();
	unsigned cIdx = get_cIdx();

	bool reuseAllowed = true;

	/// Disable recursion inside an internal wire in case of concrete query
	if (!m_abstract && !bvAllConstraints)
	{
		WireInst* w = WireInst::as(e);
		if (w)
		{
			Inst* port = w->get_port();
			assert (port);

#ifndef SUBSTITUTE
			reuseAllowed = false;
			if (!allow_all)
			{
//				if (w->get_name().length() > 5 && w->get_name().substr(w->get_name().length() - 5) == "$next")
//				{
//					ch = 0;
//				}
//				else
				{
					if (w->is_connected(WireInst::get_connect_key()))
					{

					}
					else
					{
						ch = 0;
//						cout << "(ignoring wire: " << *w << ")" << endl;
					}
				}
			}
#endif

//			WireInst* w = WireInst::as(e);
//			if (w)
//			{
//				if (w->is_connected(WireInst::get_connect_key()))
//				{
//					ch = 0;
//					reuseAllowed = false;
//
//					Inst* rhs = w->get_connection();
//					inst2yices(rhs);
//					y_ch.push_back(rhs->y_var[yIdx]);
//					s_sz.push_back(rhs->get_size());
//					assert(y_ch.back());
//				}
//			}
		}
	}

//	if (ch)
//	{
//		for (auto& v: *ch)
//		{
//			inst2yices(v);
//			y_ch.push_back(v->y2_node.solv_var(yIdx));
//			s_sz.push_back(v->get_size());
//			assert(y_ch.back());
//			assert(v->y2_node.solv_vset(yIdx));
//		}
//	}

	// first, collect data
	if (m_mapper->fetch_var(e) == TheoryMapper::BV_VAR)
	{
//		assert(!m_abstract);
	}
	else if (m_mapper->fetch_var(e) == TheoryMapper::EUF_VAR)
	{
		num_of_terms++;
		assert(m_abstract);
	}
	else if (m_mapper->fetch_var(e) == TheoryMapper::BOOL_VAR)
	{
		num_of_bools++;
		assert(m_abstract);
	}
	else
	{
		assert(0);
	}

	e->y2_node.set_key();
	y2_expr& yvar = e->y2_node.y2_var[yIdx];

	if (!(e->y2_node.solv_vset(yIdx)))
	{
		e->y2_node.y2_vset[yIdx] = true;
	}

	if (ch)
	{
		for (auto& v: *ch)
		{
			inst2yices(v);
			y_ch.push_back(v->y2_node.solv_var(yIdx));
			s_sz.push_back(v->get_size());
			assert(y_ch.back());
			assert(v->y2_node.solv_vset(yIdx));
		}
	}

#ifdef INTERPRET_EX_CC
	if (m_allow_ex_cc)
	{
		if (Config::g_uf_mult_only || (m_mapper->fetch_op(e) == TheoryMapper::EUF_OP) ||
				(m_mapper->fetch_op(e->t_simple) == TheoryMapper::EUF_OP)) {
			Inst* simplified = e->t_simple;
			if (OpInst::as(e) && e != simplified)
			{
				Inst* simplified = e->t_simple;
				if (e != simplified)
					inst2yices(simplified);
			}
		}
	}

//#ifdef INTERPRET_UF_EXCC
//	{
//		OpInst* op = OpInst::as(e);
//		if (op && op->get_op() == OpInst::Concat) {
//			if (e->get_size() != 1) {
//
//				const InstL* ch = op->get_children();
//				assert(ch);
//				unsigned s_loc = 0, e_loc = 0;
////      cout << "Asserting for " << *e << endl;
//				for (InstL::const_iterator cit = ch->begin(); cit != ch->end(); ++cit)
//				{
//					Inst *tve = *cit;
//					unsigned size = tve->get_size();
//					s_loc = e_loc;
//					e_loc += size;
//					unsigned ns = s_loc;
//					unsigned ne = size - 1 + s_loc;
//
//					{
//						Inst* Ki = ExInst::create(e, ne, ns);
//						Inst* eqInst = OpInst::create(OpInst::Eq, tve, Ki);
//						inst2yices(eqInst);
//						force(eqInst);
//					}
//
//					int c = 0;
//					for (int i = ns; i<= ne; i++, c++) {
//						Inst* lhs = ExInst::create(e, i, i);
//						Inst* rhs = ExInst::create(tve, c, c);
//						Inst* eqInst = OpInst::create(OpInst::Eq, lhs, rhs);
//						inst2yices(eqInst);
//						force(eqInst);
//					}
//
////       cout << "\t" << *eqInst << endl;
//				}
//			}
//		}
//	}
//#endif

#endif

	if (reuseAllowed && e->y2_node.solv_vset(yIdx))
	{
#ifdef ABSTRACTION_COURSE
		if (m_ab_course)
		{
			if (Inst::check_if_uf_black(e) == 1)
			{
//				cout << "\t(treating as input: " << *e << ")" << endl;
//				assert(0);
				return;
			}
		}
#endif

		if (e->y2_node.solv_cset(cIdx))
		{
			/// Constraints already set, use stored constraints.
	//		cout << "reusing stored constraints " << *e << " nC: " << e->y_constraints[yIdx].size() << endl;

			for (auto& c : e->y2_node.solv_constraints(cIdx))
			{
				add_constraint(c, "reusing stored constraints", e, false, false);
			}
			return;
		}
	}

#ifdef ABSTRACTION_COURSE
	if (m_ab_course)
	{
		if (Inst::check_if_uf_black(e) == 1)
		{
//			cout << "\t(treating as input: " << *e << ")" << endl;
//			assert(0);
			return;
		}
	}
#endif

	e->y2_node.y2_cset[cIdx] = true;

//	cout << " e: " << *e << " of type " << e->get_sort().sort2str() << endl;
	//	assert(name == print_term(yvar));

	// now link this node with the children's yices expressions

#ifdef TEST_CONNECT_BV
  AVR_LOG(11, 8, "(processing " << *e << ")" << endl);
	if (e->get_type() == Op || e->get_type() == Ex) {
    if (m_mapper->fetch_op(e) == TheoryMapper::BV_OP) {

      if (ch)
      {
        Ints::iterator sit = s_sz.begin();
        y2_expr_list::iterator cit = y_ch.begin();
        y2_expr_list new_y_ch;
        bool need_new = false;
        int count = 0;
        for (InstL::const_iterator lit = ch->begin(); lit != ch->end(); ) {
          y2_expr_ptr child = (*cit);
          if (!yices_term_is_bitvector(*cit)) {
            cout << "term is " << print_term(*cit) << endl;
            child = u2b(*sit, *lit);
            need_new = true;
          }
          new_y_ch.push_back(child);
          lit++;
          cit++;
          sit++;
          count++;
        }
        if (need_new)
          y_ch.swap(new_y_ch);
      }
    }
    else {
      assert (m_mapper->fetch_op(e) == TheoryMapper::EUF_OP);

      if (ch)
      {
        Ints::iterator sit = s_sz.begin();
        y2_expr_list::iterator cit = y_ch.begin();
        y2_expr_list new_y_ch;
        bool need_new = false;
        int count = 0;
        for (InstL::const_iterator lit = ch->begin(); lit != ch->end(); ) {
          y2_expr_ptr child = (*cit);
          if (yices_term_is_bitvector(*cit)) {
            child = b2u(*sit, *lit);
            need_new = true;
          }
          new_y_ch.push_back(child);
          lit++;
          cit++;
          sit++;
          count++;
        }
        if (need_new)
          y_ch.swap(new_y_ch);
      }
    }
	}
#endif

	switch (e->get_type())
	{
	case Num: {
		NumInst* num = NumInst::as(e);
		assert(num != 0);

		if (m_mapper->fetch_var(e) == TheoryMapper::BV_VAR) {
      y2_expr_ptr c = create_y2_number(num);
			add_gate_constraint(yvar, c, "constant link", e, false, false);

      // required to remain in QF_LIA
      if (e->get_sort_type() == inttype)
      	yvar = c;
		}
		else if (m_mapper->fetch_var(e) == TheoryMapper::BOOL_VAR) {
			yvar = ((*(num->get_mpz()) == 0) ? m_b0 : m_b1);

//			add_constraint(yices_eq((*(num->get_mpz()) == 0) ? m_b0 : m_b1, yvar), "num to boolean conversion", e);
		}
		else {
		add_variable(yvar, e);
#ifdef Y2_CREATE_UCONSTANTS
		  y2_expr_ptr c = create_const_var(num->get_mpz(), num->get_size());
      add_constraint(yices_eq(yvar, c), "num constraint", e);
#endif

#ifdef TEST_CONNECT_BV
      y2_expr_ptr c = create_y2_number(num);
      add_constraint(yices_eq(yvar, c), "b2u num constraint", e);

      y2_expr_ptr uf = b2u(num->get_size(), e);

////      y2_expr_ptr uf2 = create_int_var(get_y2_name(e) + "_b2u", num->get_size());
//      y2_expr_ptr uf2;
//      string ufName = "B2U_" + to_string(num->get_size());
//      AVR_LOG(11, 7, "(converting " << *e << " to ut)" << endl);
//      add_conversion_func(uf2, ufName, bv, num->get_size(), e);
//      add_constraint(yices_eq(uf, uf2), "uf num constraint", e);


#endif
		}
	}
		break;
	case Sig: {
		add_variable(yvar, e);
		// nothing!
	}
		break;
	case Wire: {
		if (m_mapper->fetch_op(e) == TheoryMapper::BV_OP) {
      if (y_ch.size() == 0) {
    		add_variable(yvar, e);
      }
      else {
        assert(y_ch.size() == 1);
        y2_expr_ptr res = y_ch.front();

  			add_gate_constraint(yvar, res, "port connection", e, !m_abstract, false);
      }
		}
		else if (m_mapper->fetch_op(e) == TheoryMapper::EUF_OP || m_mapper->fetch_op(e) == TheoryMapper::CLU_OP) {
      assert(y_ch.size() == 1);
      y2_expr_ptr res = y_ch.front();

			add_gate_constraint(yvar, res, "port connection", e, false, false);
		}
		else {
			assert(0);
		}
	}
		break;
	case Const: {
		add_variable(yvar, e);
		// nothing!
	}
		break;
	case Op: {
		OpInst* op = OpInst::as(e);
		assert(op != 0);
		y2_expr res = 0;
		string opstr = "";
		bool interpreted = false;

		y2_expr_list::iterator it = y_ch.begin(), it2 = y_ch.begin(), end_it = y_ch.end();
		it2++;

		OpInst::OpType o = op->get_op();

		if (o == OpInst::BitWiseXor && op->get_size() == 1 && (m_mapper->fetch_op(e) != TheoryMapper::BV_OP)) {
			o = OpInst::LogXor;
		}
		if (o == OpInst::BitWiseXNor && op->get_size() == 1 && (m_mapper->fetch_op(e) != TheoryMapper::BV_OP)) {
			o = OpInst::LogXNor;
		}

		switch (o) {
		case OpInst::Extract:
		case OpInst::Unknown:
		case OpInst::Future:
			cout << *op << endl;
			assert(0);
			break;

			// "control" operators!
		case OpInst::LogNot:
		case OpInst::LogNand:
		case OpInst::LogNor:
		case OpInst::LogAnd:
		case OpInst::LogXor:
		case OpInst::LogXNor:
		case OpInst::LogOr:
		case OpInst::Eq:
		case OpInst::NotEq:
		case OpInst::ArrayConst:
		case OpInst::ArraySelect:
		case OpInst::ArrayStore:
		case OpInst::Gr:
		case OpInst::SGr:
		case OpInst::Le:
		case OpInst::SLe:
		case OpInst::GrEq:
		case OpInst::SGrEq:
		case OpInst::LeEq:
		case OpInst::SLeEq:
		case OpInst::IntLe:
		case OpInst::IntLeEq:
		case OpInst::IntGr:
		case OpInst::IntGrEq:
		{
			y2_expr log = 0;
			switch (o) {

			case OpInst::LogNot: {
				if (m_mapper->fetch_var(e) == TheoryMapper::BV_VAR) {
					log = yices_not(*it);
				} else if (m_mapper->fetch_var(e) == TheoryMapper::BOOL_VAR) {
					log = yices_not(*it);
				} else {
					assert(0);
				}
				assert(log != Y2_INVALID_EXPR);
				interpreted = true;
			}
				break;
			case OpInst::LogNand:
			case OpInst::LogNor:
			case OpInst::LogAnd:
			case OpInst::LogOr: {
				y2_expr arguments[y_ch.size()];
				for (unsigned j = 0; j < y_ch.size(); j++, ++it) {
					arguments[j] = *it;
				}

				if (m_mapper->fetch_var(e) == TheoryMapper::BV_VAR) {
					log = ((o == OpInst::LogAnd) || (o == OpInst::LogNand)) ? yices_and(y_ch.size(), arguments) : yices_or(y_ch.size(), arguments);
					if((o == OpInst::LogNor) || (o == OpInst::LogNand)){
						log = yices_not(log);
					}
				} else if (m_mapper->fetch_var(e) == TheoryMapper::BOOL_VAR) {
					log = ((o == OpInst::LogAnd) || (o == OpInst::LogNand)) ? yices_and(y_ch.size(), arguments) : yices_or(y_ch.size(), arguments);
					if((o == OpInst::LogNor) || (o == OpInst::LogNand)){
						log = yices_not(log);
					}
				} else {
					assert(0);
				}
				interpreted = true;
			}
				break;
			case OpInst::LogXNor:
			case OpInst::LogXor: {
				y2_expr arguments[y_ch.size()];
				for (unsigned j = 0; j < y_ch.size(); j++, ++it) {
					arguments[j] = *it;
				}

				if (m_mapper->fetch_var(e) == TheoryMapper::BV_VAR) {
					log = yices_xor(y_ch.size(), arguments);
					if(o == OpInst::LogXNor){
						log = yices_not(log);
					}
				} else if (m_mapper->fetch_var(e) == TheoryMapper::BOOL_VAR) {
					log = yices_xor(y_ch.size(), arguments);
					if(o == OpInst::LogXNor){
						log = yices_not(log);
					}
				} else {
					assert(0);
				}
				interpreted = true;
			}
				break;
			case OpInst::Eq:{
				assert(y_ch.size() == 2);
				if (m_mapper->fetch_var(e) == TheoryMapper::BV_VAR) {
					log = yices_eq(*it, *it2);
				} else if (m_mapper->fetch_var(e) == TheoryMapper::BOOL_VAR) {
					log = yices_eq(*it, *it2);

					assert(log);

//#ifdef INTERPRET_EX_CC
//          if (m_allow_ex_cc)
//          {
//            OpInst* op_t = OpInst::as(e);
//            assert(op_t);
//
//            Inst* simplified = op_t->t_simple;
//            if (e != simplified)
//            {
//              y2_expr_ptr a = simplified->y2_node.solv_var(get_vIdx());
//              add_constraint(yices_eq(log, a), "partial interpretation of == with Ex/Cc", e);
////              cout << "Asserting " << *e << " == " << *simplified << endl;
//            }
//          }
//#endif
				} else {
					assert(0);
				}
				interpreted = true;
			}
				break;
			case OpInst::NotEq: {
				assert(y_ch.size() == 2);
				if (m_mapper->fetch_var(e) == TheoryMapper::BV_VAR) {
					log = yices_neq(*it, *it2);
				} else if (m_mapper->fetch_var(e) == TheoryMapper::BOOL_VAR) {
					log = yices_neq(*it, *it2);

//#ifdef INTERPRET_EX_CC
//          if (m_allow_ex_cc)
//          {
//            OpInst* op_t = OpInst::as(e);
//            assert(op_t);
//
//            Inst* simplified = op_t->t_simple;
//            if (e != simplified)
//            {
//              y2_expr_ptr a = simplified->y2_node.solv_var(get_vIdx());
//              add_constraint(yices_eq(log, a), "partial interpretation of != with Ex/Cc", e);
////              cout << "Asserting " << *e << " == " << *simplified << endl;
//            }
//          }
//#endif
				} else {
					assert(0);
				}
				interpreted = true;
			}
				break;
			case OpInst::ArrayConst: {
				if (m_mapper->fetch_op(e) == TheoryMapper::BV_OP) {
					y2_type functt = create_bv_sort(make_pair(e->get_size(), e->get_sort()));
					y2_expr funct = yices_new_uninterpreted_term(functt);
					log = funct;
//					cout << "constarray: " << print_term(log) << " of type " << print_type(yices_type_of_term(log)) << endl;

					SORT* d = e->get_sort_domain();
					SORT* r = e->get_sort_range();
					assert(d->type == bvtype);
					assert(r->type == bvtype);
					int width = d->sz;
					int size = r->sz;

					Inst* init_val = e->get_children()->back();
					assert(init_val->get_type() == Num);
					string value = NumInst::as(init_val)->get_mpz()->get_str(2);
					while (value.length() < e->get_size())
						value = "0" + value;
					int maxaddress = pow(2, width) - 1;
					for (int i = 0; i <= maxaddress; i++) {
						string v = value.substr(i*size, size);
						Inst* address = NumInst::create(maxaddress - i, width, SORT());
						Inst* data = NumInst::create(v, size, 2, SORT());
						y2_expr_ptr a = create_y2_number(NumInst::as(address));
						y2_expr_ptr b = create_y2_number(NumInst::as(data));
#ifndef Y2_ARRAY_ALLOW_BOOL
						if (yices_term_is_bool(a))
							a = yices_ite(a, m_v1, m_v0);
						if (yices_term_is_bool(b))
							b = yices_ite(b, m_v1, m_v0);
#endif
						log = yices_update1(log, a, b);
					}
//					cout << "updatearray: " << print_term(log) << endl;
				} else if (m_mapper->fetch_op(e) == TheoryMapper::EUF_OP) {
					SORT* d = e->get_sort_domain();
					SORT* r = e->get_sort_range();
					assert(d->type == bvtype);
					assert(r->type == bvtype);
					int width = d->sz;
					int size = r->sz;

					y2_type functt;
					if (m_mapper->fetch_logic() == TheoryMapper::QF_UFBV && m_mapper->fetch_var(e) == TheoryMapper::BV_VAR) {
						// operation is EUF but output is BV, i.e. input is EUF type, output is BV type
						functt = create_int_sort(make_pair(e->get_size(), e->get_sort()), false, true);
					}
					else if (m_mapper->fetch_logic() == TheoryMapper::QF_UFBV && e->ab_interpret.input_concrete()) {
						functt = create_int_sort(make_pair(e->get_size(), e->get_sort()), true, false);
					}
					else {
						functt = create_int_sort(make_pair(e->get_size(), e->get_sort()));
					}

					y2_expr funct = yices_new_uninterpreted_term(functt);
					log = funct;
//					cout << "constarray: " << print_term(log) << " of type " << print_type(yices_type_of_term(log)) << endl;

//					int width = e->get_sort_width();
//					Inst* init_val = e->get_children()->back();
//					assert(init_val->get_type() == Num);
//					string value = NumInst::as(init_val)->get_mpz()->get_str(2);
//					while (value.length() < e->get_size())
//						value = "0" + value;
//					int size = e->get_sort_size();
//					int maxaddress = pow(2, width) - 1;
//					for (int i = 0; i <= maxaddress; i++) {
//						string v = value.substr(i*size, size);
//						Inst* address = NumInst::create(maxaddress - i, width);
//						Inst* data = NumInst::create(v, size, 2);
//						inst2yices(address);
//						inst2yices(data);
//						y2_expr_ptr a = address->y2_node.solv_var(yIdx);
//						y2_expr_ptr b = data->y2_node.solv_var(yIdx);
//						log = yices_update1(log, a, b);
//					}
				} else {
					assert(0);
				}
				assert(log);
				interpreted = true;
			}
				break;
			case OpInst::ArraySelect: {
				y2_expr a = *it;
				y2_expr b = *it2;
#ifndef Y2_ARRAY_ALLOW_BOOL
				if (yices_term_is_bool(b))
					b = yices_ite(b, m_v1, m_v0);
#endif
				log = yices_application1(a, b);
				if (log == Y2_INVALID_EXPR) {
					cout << "e: " << *e << endl;
					cout << "a: " << print_term(a) << " of type " << print_type(yices_type_of_term(a)) << endl;
					cout << "b: " << print_term(b) << " of type " << print_type(yices_type_of_term(b)) << endl;

					yices_print_error(stdout);
					assert(0);
				}
//				cout << "selectarray: " << print_term(log) << " of type " << print_type(yices_type_of_term(log)) << endl;
				assert(log);
				assert(log != Y2_INVALID_EXPR);
				interpreted = true;
			}
				break;
			case OpInst::ArrayStore: {
				y2_expr a = *it;
				y2_expr b = *it2;
				it2++;
				y2_expr c = *it2;
#ifndef Y2_ARRAY_ALLOW_BOOL
				if (yices_term_is_bool(b))
					b = yices_ite(b, m_v1, m_v0);
				if (yices_term_is_bool(c))
					c = yices_ite(c, m_v1, m_v0);
#endif
				log = yices_update1(a, b, c);
//				cout << "storearray: " << print_term(log) << " of type " << print_type(yices_type_of_term(log)) << endl;
				assert(log);
				interpreted = true;
			}
				break;
			case OpInst::Gr:
			case OpInst::SGr:
			case OpInst::Le:
			case OpInst::SLe:
			case OpInst::GrEq:
			case OpInst::SGrEq:
			case OpInst::LeEq:
			case OpInst::SLeEq:
			case OpInst::IntLe:
			case OpInst::IntLeEq:
			case OpInst::IntGr:
			case OpInst::IntGrEq:
			{
				if (m_mapper->fetch_op(e) == TheoryMapper::EUF_OP) {
					switch (o) {
					case OpInst::Gr:
						opstr = "Gr";
						break;
					case OpInst::SGr:
						opstr = "SGr";
						break;
					case OpInst::Le:
						opstr = "Le";
						break;
					case OpInst::SLe:
						opstr = "SLe";
						break;
					case OpInst::GrEq:
						opstr = "GrEq";
						break;
					case OpInst::SGrEq:
						opstr = "SGrEq";
						break;
					case OpInst::LeEq:
						opstr = "LeEq";
						break;
					case OpInst::SLeEq:
						opstr = "SLeEq";
						break;
					case OpInst::IntLe:
						opstr = "IntLe";
						break;
					case OpInst::IntLeEq:
						opstr = "IntLeEq";
						break;
					case OpInst::IntGr:
						opstr = "IntGr";
						break;
					case OpInst::IntGrEq:
						opstr = "IntGrEq";
						break;
					default:
						assert(0);
					}
				} else if (m_mapper->fetch_op(e) == TheoryMapper::CLU_OP) {
					assert(0);
				} else if (m_mapper->fetch_op(e) == TheoryMapper::BV_OP) {

					y2_expr_ptr y1 = *it;
					y2_expr_ptr y2 = *it2;
					Inst* c1 = e->get_children()->front();
					Inst* c2 = e->get_children()->back();
					int c1Sz = c1->get_size();
					int c2Sz = c2->get_size();

					if (yices_term_is_bool(y1))
						y1 = yices_ite(y1, m_v1, m_v0);
					if (yices_term_is_bool(y2))
						y2 = yices_ite(y2, m_v1, m_v0);

					if (c1Sz < c2Sz)
						y1 = yices_zero_extend(y1, (c2Sz - c1Sz));
					if (c2Sz < c1Sz)
						y2 = yices_zero_extend(y2, (c1Sz - c2Sz));

					switch (o) {
					case OpInst::Gr:
						log = yices_bvgt_atom(y1, y2);
						break;
					case OpInst::SGr:
						log = yices_bvsgt_atom(y1, y2);
						break;
					case OpInst::Le:
						log = yices_bvlt_atom(y1, y2);
						break;
					case OpInst::SLe:
						log = yices_bvslt_atom(y1, y2);
						break;
					case OpInst::GrEq:
						log = yices_bvge_atom(y1, y2);
						break;
					case OpInst::SGrEq:
						log = yices_bvsge_atom(y1, y2);
						break;
					case OpInst::LeEq:
						log = yices_bvle_atom(y1, y2);
						break;
					case OpInst::SLeEq:
						log = yices_bvsle_atom(y1, y2);
						break;
					case OpInst::IntLe:
						log = yices_arith_lt_atom(y1, y2);
						break;
					case OpInst::IntLeEq:
						log = yices_arith_leq_atom(y1, y2);
						break;
					case OpInst::IntGr:
						log = yices_arith_gt_atom(y1, y2);
						break;
					case OpInst::IntGrEq:
						log = yices_arith_geq_atom(y1, y2);
						break;
					default:
						assert(0);
					}
					interpreted = true;
				}
			}
				break;
			default:
				assert(0);
			}
			if (opstr != "") {
//				add_yices_func(yvar, opstr, e->get_size() == 1, y_ch, s_sz, e, (m_mapper->fetch_var(e) == TheoryMapper::BV_VAR) ? e->get_size() : 0);
			} else if (m_mapper->fetch_var(e) == TheoryMapper::BV_VAR) {
				res = log;
			} else if (interpreted) {
				res = log;
			} else
				assert(0);
		}
			break;
		case OpInst::Concat: {
			if (m_mapper->fetch_op(e) == TheoryMapper::BV_OP) {
//				assert(m_mapper->fetch_var(e) == TheoryMapper::BV_VAR);
				if (y_ch.size() == 1) {
					res = *it;
				} else {
					y2_expr arguments[y_ch.size()];
					for (int j = (y_ch.size() - 1); j >= 0; j--, ++it) {
						if (yices_term_is_bitvector(*it))
							arguments[j] = *it;
						else
						{
	            assert (yices_term_is_bool(*it));
              arguments[j] = yices_ite(*it, m_v1, m_v0);
						}
					}
					res = yices_bvconcat(y_ch.size(), arguments);
				}
			}
			else
			{
				opstr = "Concat";
			}
		}
			break;

			// "datapath" operators
		case OpInst::Minus:
		case OpInst::Add:
		case OpInst::AddC:
		case OpInst::Sub:
		case OpInst::Mult:
		case OpInst::Div:
		case OpInst::SDiv:
		case OpInst::Rem:
		case OpInst::SRem:
		case OpInst::SMod:
		case OpInst::BitWiseNot:
		case OpInst::BitWiseAnd:
		case OpInst::BitWiseNand:
		case OpInst::BitWiseOr:
		case OpInst::BitWiseNor:
		case OpInst::BitWiseXor:
		case OpInst::BitWiseXNor:
		case OpInst::ReductionAnd:
		case OpInst::ReductionOr:
		case OpInst::ReductionXor:
		case OpInst::ReductionXNor:
		case OpInst::ReductionNand:
		case OpInst::ReductionNor:
		case OpInst::RotateL:
		case OpInst::RotateR:
		case OpInst::ShiftL:
		case OpInst::ShiftR:
		case OpInst::AShiftR:
		case OpInst::AShiftL:
		case OpInst::Sext:
		case OpInst::Zext:
		case OpInst::VShiftL:
		case OpInst::VShiftR:
		case OpInst::VAShiftL:
		case OpInst::VAShiftR:
		case OpInst::VRotateL:
		case OpInst::VRotateR:
		case OpInst::VEx:
		case OpInst::IntAdd:
		case OpInst::IntSub:
		case OpInst::IntMult:
		case OpInst::IntDiv:
		case OpInst::IntMod:
		case OpInst::IntFloor:
		case OpInst::IntMinus:
		{
			if (m_mapper->fetch_op(e) == TheoryMapper::BV_OP) {
				assert(m_mapper->fetch_var(e) == TheoryMapper::BV_VAR);

				y2_expr_ptr a = (*it);
				if (yices_term_is_bool(a))
					a = yices_ite(a, m_v1, m_v0);
				Inst* c1 = e->get_children()->front();
				int outSz = e->get_size();
				int c1Sz = c1->get_size();
				if (c1Sz < outSz)
					a = yices_zero_extend(a, (outSz - c1Sz));

				switch (o) {
				case OpInst::Minus: {
					assert(y_ch.size() == 1);
					res = yices_bvneg(a);
				}
					break;
				case OpInst::BitWiseNot: {
					assert(y_ch.size() == 1);
					res = yices_bvnot(a);
				}
					break;
				case OpInst::IntFloor: {
					assert(y_ch.size() == 1);
					res = yices_floor(a);
				}
					break;
				case OpInst::IntMinus: {
					assert(y_ch.size() == 1);
					res = yices_neg(a);
				}
					break;

				case OpInst::Add:
				case OpInst::Sub:
				case OpInst::Mult:
				case OpInst::Div:
				case OpInst::SDiv:
				case OpInst::Rem:
				case OpInst::SRem:
				case OpInst::SMod:
				case OpInst::BitWiseAnd:
				case OpInst::BitWiseNand:
				case OpInst::BitWiseOr:
				case OpInst::BitWiseNor:
				case OpInst::BitWiseXor:
				case OpInst::BitWiseXNor:
				case OpInst::ShiftL:
				case OpInst::ShiftR:
				case OpInst::AShiftR:
				case OpInst::Sext:
				case OpInst::Zext:
				case OpInst::IntAdd:
				case OpInst::IntSub:
				case OpInst::IntMult:
				case OpInst::IntDiv:
				case OpInst::IntMod:
				{
					y2_expr_ptr b = (*it2);
					if (yices_term_is_bool(b))
						b = yices_ite(b, m_v1, m_v0);

					int outSz = e->get_size();
					int maxSz = outSz;
					if (e->get_sort_type() == bvtype) {
						Inst* c2 = e->get_children()->back();
						int c2Sz = c2->get_size();
						if (maxSz < c1Sz)
							maxSz = c1Sz;
						if (maxSz < c2Sz)
							maxSz = c2Sz;

						if (outSz < maxSz)
						{
							a = yices_zero_extend(a, (maxSz - outSz));
						}
						if (c2Sz < maxSz)
						{
							b = yices_zero_extend(b, (maxSz - c2Sz));
						}
					}

					switch (o) {
					case OpInst::Add:{
						assert(y_ch.size() == 2);
						res = yices_bvadd(a, b);
					}break;
					case OpInst::Sub: {
						assert(y_ch.size() == 2);
						res = yices_bvsub(a, b);
					}
						break;
					case OpInst::Mult:{
						assert(y_ch.size() == 2);
						res = yices_bvmul(a, b);
					}
						break;
					case OpInst::Div:{
						assert(y_ch.size() == 2);
						res = yices_bvdiv(a, b);
					}
						break;
					case OpInst::SDiv:{
						assert(y_ch.size() == 2);
						res = yices_bvsdiv(a, b);
					}
						break;
					case OpInst::Rem:{
						assert(y_ch.size() == 2);
						res = yices_bvrem(a, b);
					}
						break;
					case OpInst::SRem:{
						assert(y_ch.size() == 2);
						res = yices_bvsrem(a, b);
					}
						break;
					case OpInst::SMod:{
						assert(y_ch.size() == 2);
						res = yices_bvsmod(a, b);
					}
						break;
					case OpInst::BitWiseAnd: {
						assert(y_ch.size() == 2);
						res = yices_bvand2(a, b);
					}
						break;
					case OpInst::BitWiseNand: {
						assert(y_ch.size() == 2);
						res = yices_bvnand(a, b);
					}
						break;
					case OpInst::BitWiseOr: {
						assert(y_ch.size() == 2);
						res = yices_bvor2(a, b);
					}
						break;
					case OpInst::BitWiseNor: {
						assert(y_ch.size() == 2);
						res = yices_bvnor(a, b);
					}
						break;
					case OpInst::BitWiseXor: {
						assert(y_ch.size() == 2);
						res = yices_bvxor2(a, b);
					}
						break;
					case OpInst::BitWiseXNor: {
						assert(y_ch.size() == 2);
						res = yices_bvxnor(a, b);
					}
						break;
					case OpInst::ShiftL:
					case OpInst::ShiftR: {
						assert(y_ch.size() == 2);
						InstL::const_iterator ve_it = ch->begin(), ve_it2 = ch->begin();
						ve_it2++;
						NumInst* num = NumInst::as(*ve_it2);
						if (num != 0)
						{
							if (o == OpInst::ShiftL)
							{
								res = yices_shift_left0(a, num->get_mpz()->get_si());
							} else {
								res = yices_shift_right0(a, num->get_mpz()->get_si());
							}
						}
						else
						{
							if (o == OpInst::ShiftR)
								res = yices_bvlshr(a, b);
							else if (o == OpInst::ShiftL)
								res = yices_bvshl(a, b);
							else
								assert(0);
						}
						assert(res != -1);
					}
						break;
					case OpInst::AShiftR: {
						assert(y_ch.size() == 2);
						InstL::const_iterator ve_it = ch->begin(), ve_it2 = ch->begin();
						ve_it2++;
						NumInst* num = NumInst::as(*ve_it2);
						if (num != 0)
						{
							res = yices_ashift_right(a, num->get_mpz()->get_si());
							assert(res != -1);
						}
						else
						{
							res = yices_bvashr(a, b);
						}
						assert(res != -1);
					}
						break;
					case OpInst::Sext:
					case OpInst::Zext: {
						y2_expr_ptr a2 = (*it);
						if (yices_term_is_bool(a2))
							a2 = yices_ite(a2, m_v1, m_v0);
						assert(y_ch.size() == 2);
						InstL::const_iterator ve_it = ch->begin();
						int amount = e->get_size() - (*ve_it)->get_size();
						assert(amount >= 0);
						{
							if (o == OpInst::Sext)
							{
								res = yices_sign_extend(a2, amount);
							} else {
								res = yices_zero_extend(a2, amount);
							}
						}
						assert(res != -1);
					}
						break;
					case OpInst::IntAdd: {
						assert(y_ch.size() == 2);
						res = yices_add(a, b);
					}
						break;
					case OpInst::IntSub: {
						assert(y_ch.size() == 2);
						res = yices_sub(a, b);
					}
						break;
					case OpInst::IntMult: {
						assert(y_ch.size() == 2);
						res = yices_mul(a, b);
					}
						break;
					case OpInst::IntDiv: {
						assert(y_ch.size() == 2);
						res = yices_idiv(a, b);
					}
						break;
					case OpInst::IntMod: {
						assert(y_ch.size() == 2);
						res = yices_imod(a, b);
					}
						break;
					default:
						assert(0);
					}
					if (e->get_sort_type() == bvtype) {
						if (outSz < maxSz)
							res = yices_bvextract(res, 0, (outSz - 1));
					}
				}
					break;

				case OpInst::AddC:
				case OpInst::AShiftL:
					assert(0); // for now.

				case OpInst::ReductionAnd:
				case OpInst::ReductionNand: {
					assert(y_ch.size() == 1);
					res = yices_redand(a);
					if (o == OpInst::ReductionNand)		res = yices_bvnot(res);
				}
					break;
				case OpInst::ReductionOr:
				case OpInst::ReductionNor: {
					assert(y_ch.size() == 1);
					res = yices_redor(a);
					if (o == OpInst::ReductionNor)		res = yices_bvnot(res);
				}
					break;
				case OpInst::ReductionXor:
				case OpInst::ReductionXNor: {
					assert(y_ch.size() == 1);
					unsigned sz = (*(ch->begin()))->get_size();
					assert(sz > 1);

					y2_expr bit = yices_bvextract(a, 0, 0);
					y2_expr bit2 = yices_bvextract(a, 1, 1);
					bit = yices_bvxor2(bit, bit2);
					for (unsigned i = 2; i < sz; i++)
					{
						bit = yices_bvxor2(bit, yices_bvextract(a, i, i));
					}
					if (o == OpInst::ReductionXNor)		bit = yices_bvnot(bit);
					res = bit;
				}
					break;
				case OpInst::VRotateR:{
					const InstL* ch = e->get_children();
					InstL::const_iterator ve_it = ch->begin();
					Inst *ve_val = *ve_it;
					++ve_it;
					int amt_size = (*ve_it)->get_size();
					int rotate_amount = (1 << amt_size) - 1;
					int out_size = e->get_size();

					bool simp_to_zero = false;
					if(ve_val == NumInst::create(0, ve_val->get_size(), SORT())){
						simp_to_zero = true;
					}else if((ve_val->get_type() == Op) && (OpInst::as(ve_val)->get_op() == OpInst::Concat)){
						const InstL* chs = ve_val->get_children();

						if(chs && !chs->empty()){
							for(InstL::const_iterator cit = chs->begin(); cit != chs->end(); ++cit){
								Inst *tve = *cit;
								if(tve != NumInst::create(0, tve->get_size(), SORT())){	// TODO check type and value
									simp_to_zero = false;
									break;
								}
								simp_to_zero = true;
							}
						}
					}
					if(simp_to_zero == true){
						//cout << "(simp_to_zero == true): e: " << *e << endl;
						res = yices_bvconst_uint32(out_size, 0);
					}else{
						//cout << "(simp_to_zero == false): e: " << *e << endl;
	//					int rotate_amount = 31;
						y2_expr els = yices_bvconcat2(yices_bvextract(*it, 0, rotate_amount-1), yices_bvextract(*it, rotate_amount, out_size-1));	//right	31
						rotate_amount--;
						y2_expr thn = yices_bvconcat2(yices_bvextract(*it, 0, rotate_amount-1), yices_bvextract(*it, rotate_amount, out_size-1));	//right	30

						y2_expr num = yices_bvconst_uint32(amt_size, rotate_amount);
						y2_expr cond = yices_eq(*it2, num);
						res = yices_ite(cond, thn, els);	// (sel == 30) ? rotate_30 : rotate_31

						for(; rotate_amount > 0; --rotate_amount){
							thn = yices_bvconcat2(yices_bvextract(*it, 0, rotate_amount-1), yices_bvextract(*it, rotate_amount, out_size-1));
							num = yices_bvconst_uint32(amt_size, rotate_amount);
							cond = yices_eq(*it2, num);
							res = yices_ite(cond, thn, res);
						}
						num = yices_bvconst_uint32(amt_size, 0);
						cond = yices_eq(*it2, num);
						res = yices_ite(cond, *it, res);
						#ifdef YICES_BV_INPUT_DUMP_DERIVED
							cout << this <<": ";
							cout << "(derived ";
							yices_pp_expr(res);
							cout << endl;
						#endif
					}
					break;
					//yices_mk_bv_concat(m_ctx, yices_mk_bv_extract(m_ctx, out_size-1-rotate_amount, 0, *it), yices_mk_bv_extract(m_ctx, out_size-1, out_size-rotate_amount, *it))	//left
				}
				case OpInst::VRotateL:{
					const InstL* ch = e->get_children();
					InstL::const_iterator ve_it = ch->begin();
					Inst *ve_val = *ve_it;
					++ve_it;
					int amt_size = (*ve_it)->get_size();
					int rotate_amount = (1 << amt_size) - 1;
					int out_size = e->get_size();

					bool simp_to_zero = false;
					if(ve_val == NumInst::create(0, ve_val->get_size(), SORT())){
						simp_to_zero = true;
					}else if((ve_val->get_type() == Op) && (OpInst::as(ve_val)->get_op() == OpInst::Concat)){
						const InstL* chs = ve_val->get_children();

						if(chs && !chs->empty()){
							for(InstL::const_iterator cit = chs->begin(); cit != chs->end(); ++cit){
								Inst *tve = *cit;
								if(tve != NumInst::create(0, tve->get_size(), SORT())){	// TODO check type and value
									simp_to_zero = false;
									break;
								}
								simp_to_zero = true;
							}
						}
					}
					if(simp_to_zero == true){
						//cout << "(simp_to_zero == true): e: " << *e << endl;
						res = yices_bvconst_uint32(out_size, 0);
					}else{
						//cout << "(simp_to_zero == false): e: " << *e << endl;
						//int rotate_amount = 31;

						y2_expr els = yices_bvconcat2(yices_bvextract(*it, 0, out_size-rotate_amount-1), yices_bvextract(*it, out_size-rotate_amount, out_size-1));	//right	31
						rotate_amount--;
						y2_expr thn = yices_bvconcat2(yices_bvextract(*it, 0, out_size-rotate_amount-1), yices_bvextract(*it, out_size-rotate_amount, out_size-1));	//right	30

						y2_expr num = yices_bvconst_uint32(amt_size, rotate_amount);
						y2_expr cond = yices_eq(*it2, num);
						res = yices_ite(cond, thn, els);	// (sel == 30) ? rotate_30 : rotate_31

						for(; rotate_amount > 0; --rotate_amount){
							thn = yices_bvconcat2(yices_bvextract(*it, 0, out_size-rotate_amount-1), yices_bvextract(*it, out_size-rotate_amount, out_size-1));
							num = yices_bvconst_uint32(amt_size, rotate_amount);
							cond = yices_eq(*it2, num);
							res = yices_ite(cond, thn, res);
						}
						num = yices_bvconst_uint32(amt_size, 0);
						cond = yices_eq(*it2, num);
						res = yices_ite(cond, *it, res);
						#ifdef YICES_BV_INPUT_DUMP_DERIVED
							cout << this <<": ";
							cout << "(derived ";
							yices_pp_expr(res);
							cout << endl;
						#endif
					}
					break;
				}
				case OpInst::VShiftL:	//TODO
				case OpInst::VShiftR:
				case OpInst::VAShiftL:
				case OpInst::VAShiftR:
				case OpInst::VEx:{
					const InstL* ch = e->get_children();
					InstL::const_iterator ve_it = ch->begin();
					int ex_offset = (*ve_it)->get_size()-1;
					++ve_it;
					int idx_size = (*ve_it)->get_size();

// 					cout << "ex_offset: " << ex_offset << endl;
// 					cout << "idx_size: " << idx_size << endl;

					y2_expr els = yices_bvextract(*it, ex_offset, ex_offset);
					ex_offset--;
					y2_expr thn = yices_bvextract(*it, ex_offset, ex_offset);

					y2_expr num = yices_bvconst_uint32(idx_size, ex_offset);
					y2_expr cond = yices_eq(*it2, num);
					res = yices_ite(cond, thn, els);	// (sel == 30) ? rotate_30 : rotate_31

					for(; ex_offset >= 0; --ex_offset){
						thn = yices_bvextract(*it, ex_offset, ex_offset);
						num = yices_bvconst_uint32(idx_size, ex_offset);
						cond = yices_eq(*it2, num);
						res = yices_ite(cond, thn, res);
					}
					#ifdef YICES_BV_INPUT_DUMP_DERIVED
						cout << this <<": ";
						cout << "(derived ";
						yices_pp_expr(res);
						cout << endl;
					#endif
					break;
				}
				default:
					assert(0);
				}
			} else if (m_mapper->fetch_op(e) == TheoryMapper::EUF_OP || m_mapper->fetch_op(e) == TheoryMapper::CLU_OP) {
				switch (o) {
				case OpInst::VShiftL:	//TODO
					opstr = "VShiftL";
					break;
				case OpInst::VShiftR:
					opstr = "VShiftR";
					break;
				case OpInst::VAShiftL:
					opstr = "VAShiftL";
					break;
				case OpInst::VAShiftR:
					opstr = "VAShiftR";
					break;
				case OpInst::VRotateL:
					opstr = "VRotateL";
					break;
				case OpInst::VRotateR:
					opstr = "VRotateR";
					break;
				case OpInst::VEx:
					opstr = "VEx";
					break;
				case OpInst::Minus:
					opstr = "Minus";
					break;
				case OpInst::AddC:
					opstr = "AddC";
					break;
				case OpInst::Add:
					if (m_mapper->fetch_op(e) == TheoryMapper::EUF_OP) {
#ifdef USE_INTERPRETED_ADD_SUB
						yices_expr args[2];
						args[0] = *it;
						args[1] = *it2;
						res = yices_mk_sum(m_ctx, args, 2);
						interpreted = true;
#elif defined USE_INTERPRETED_ADD_SUB_CONST
						const InstL* ch = e->get_children();
						InstL::const_iterator it = ch->begin();
						InstL::const_iterator it2 = ch->begin();
						it2++;
						if(((*it)->get_type() == Num) != ((*it)->get_type() == Num)) {
							// TODO check if we can use interpreted add or sub for the case of (num OP num)
							yices_expr args[2];
							args[0] = *it;
							args[1] = *it2;
							res = yices_mk_sum(m_ctx, args, 2);
							interpreted = true;
						} else {
							opstr = "Add";
						}
#else
						opstr = "Add";
#endif
					} else if (m_mapper->fetch_op(e) == TheoryMapper::CLU_OP) {
						//TODO
// 						if (config->get_arg(UBADD_ARG) == "1") {
// 							yices_expr arguments[2];
// 							arguments[0] = *it;
// 							arguments[1] = *it2;
// 							res = yices_mk_sum(m_ctx, arguments, 2);
// 							interpreted = true;
// 						} else {
// 							InstL::const_iterator cit = ch->begin(), cit2;
// 							cit2 = cit;
// 							cit2++;
// 							if ((*cit2)->get_type() == Num) {
// 								NumInst* num = NumInst::as(*cit2);
// 								assert(num != 0);
// 								yices_expr arguments[2];
// 								arguments[0] = *it;
// 								arguments[1] = yices_mk_num(m_ctx, num->get_mpz());
// 								res = yices_mk_sum(m_ctx, arguments, 2);
// 								interpreted = true;
// 							} else if ((*cit)->get_type() == Num) {
// 								NumInst* num = NumInst::as(*cit);
// 								assert(num != 0);
// 								yices_expr arguments[2];
// 								arguments[1] = *it;
// 								arguments[0] = yices_mk_num(m_ctx, num->get_mpz());
// 								res = yices_mk_sum(m_ctx, arguments, 2);
// 								interpreted = true;
// 							} else
// 								opstr = "Add";
// 						}
					} else
						assert(0);
					break;
				case OpInst::Sub:
					if (m_mapper->fetch_op(e) == TheoryMapper::EUF_OP) {
#ifdef USE_INTERPRETED_ADD_SUB
						yices_expr args[2];
						args[0] = *it;
						args[1] = *it2;
						res = yices_mk_sub(m_ctx, args, 2);
						interpreted = true;
#elif defined USE_INTERPRETED_ADD_SUB_CONST
						const InstL* ch = e->get_children();
						InstL::const_iterator it = ch->begin();
						InstL::const_iterator it2 = ch->begin();
						it2++;
						if(((*it)->get_type() == Num) != ((*it)->get_type() == Num)) {
							// TODO check if we can use interpreted add or sub for the case of (num OP num)
							yices_expr args[2];
							args[0] = *it;
							args[1] = *it2;
							res = yices_mk_sub(m_ctx, args, 2);
							interpreted = true;
						} else {
							opstr = "Sub";
						}
#else
						opstr = "Sub";
#endif
					} else if (m_mapper->fetch_op(e) == TheoryMapper::CLU_OP)
					{
						assert(0);
//						InstL::const_iterator cit2 = ch->begin();
//						cit2++;
//						if ((*cit2)->get_type() == Num) {
//							NumInst* num = NumInst::as(*cit2);
//							assert(num != 0);
//							yices_expr arguments[2];
//							arguments[0] = *it;
//							arguments[1] = yices_mk_num(m_ctx, num->get_mpz()->get_si());
//							res = yices_mk_sub(m_ctx, arguments, 2);
//							interpreted = true;
//						} else
//							opstr = "Sub";
					} else
						assert(0);
					break;
				case OpInst::Mult:
					opstr = "Mult";
					break;
				case OpInst::Div:
					opstr = "Div";
					break;
				case OpInst::SDiv:
					opstr = "SDiv";
					break;
				case OpInst::Rem:
					opstr = "Rem";
					break;
				case OpInst::SRem:
					opstr = "SRem";
					break;
				case OpInst::SMod:
					opstr = "SMod";
					break;
				case OpInst::BitWiseAnd:
					opstr = "BitWiseAnd";
					break;
				case OpInst::BitWiseOr:
					opstr = "BitWiseOr";
					break;
				case OpInst::BitWiseNot:
					opstr = "BitWiseNot";
					break;
				case OpInst::BitWiseXor:
					opstr = "BitWiseXor";
					break;
				case OpInst::BitWiseXNor:
					opstr = "BitWiseXNor";
					break;
				case OpInst::BitWiseNor:
					opstr = "BitWiseNor";
					break;
				case OpInst::BitWiseNand:
					opstr = "BitWiseNand";
					break;
				case OpInst::ReductionAnd:
					opstr = "ReductionAnd";
					break;
				case OpInst::ReductionOr:
					opstr = "ReductionOr";
					break;
				case OpInst::ReductionXor:
					opstr = "ReductionXor";
					break;
				case OpInst::ReductionXNor:
					opstr = "ReductionXNor";
					break;
				case OpInst::ReductionNand:
					opstr = "ReductionNand";
					break;
				case OpInst::ReductionNor:
					opstr = "ReductionNor";
					break;
				case OpInst::RotateL:
					opstr = "RotateL";
					break;
				case OpInst::RotateR:
					opstr = "RotateR";
					break;
				case OpInst::ShiftL:
					opstr = "ShiftL";
					break;
				case OpInst::ShiftR:
					opstr = "ShiftR";
					break;
				case OpInst::AShiftR:
					opstr = "AShiftR";
					break;
				case OpInst::AShiftL:
					opstr = "AShiftL";
					break;
				case OpInst::Sext:
					opstr = "Sext";
					break;
				case OpInst::Zext:
					opstr = "Zext";
					break;
//				case OpInst::ArrayConst:
//					opstr = "ArrayConst";
//					break;
//				case OpInst::ArraySelect:
//					opstr = "ArraySelect";
//					break;
//				case OpInst::ArrayStore:
//					opstr = "ArrayStore";
//					break;
				case OpInst::IntAdd:
					opstr = "IntAdd";
					break;
				case OpInst::IntSub:
					opstr = "IntSub";
					break;
				case OpInst::IntMult:
					opstr = "IntMult";
					break;
				case OpInst::IntDiv:
					opstr = "IntDiv";
					break;
				case OpInst::IntMod:
					opstr = "IntMod";
					break;
				case OpInst::IntFloor:
					opstr = "IntFloor";
					break;
				case OpInst::IntMinus:
					opstr = "IntMinus";
					break;
				default:
					assert(0);
				}
			}
		}
			break;
		case OpInst::Ternary: {
//		  for (auto& c: y_ch) {
//		    cout << print_term(c) << endl;
//		  }
//		  cout << y_ch.size() << endl;

		  assert(y_ch.size() == 3);
			y2_expr_list::iterator it3 = it2;
			it3++;
			y2_expr_ptr cond = (*it);
			y2_expr_ptr y1 = (*it2);
			y2_expr_ptr y2 = (*it3);

			if (yices_term_is_bitvector(cond))
			  cond = yices_eq(cond, m_v1);

      res = yices_ite(cond, y1, y2);
//      conds.push_back(cond);

			interpreted = true;

//			cout << *e << " " << print_term(y1) << " of type " << print_type(yices_type_of_term(y1)) << endl;
//			cout << *e << " " << print_term(y2) << " of type " << print_type(yices_type_of_term(y2)) << endl;
//			cout << *e << " " << print_term(cond) << " of type " << print_type(yices_type_of_term(cond)) << endl;
//			cout << *e << " " << print_term(yvar) << " of type " << print_type(yices_type_of_term(yvar)) << endl;

			assert(res);

//#ifdef INTERPRET_EX_CC
//			if (m_allow_ex_cc)
//			{
//				OpInst* op_t = OpInst::as(e);
//				assert(op_t);
//				assert(op_t->get_op() == OpInst::Ternary);
//
//				Inst* simplified = op_t->t_simple;
//				if (e != simplified)
//				{
//					y2_expr_ptr a = simplified->y2_node.solv_var(get_vIdx());
//					add_constraint(yices_eq(res, a), "partial interpretation of ternary with Ex/Cc", e);
////						cout << "Asserting " << *e << " == " << *simplified << endl;
//				}
//			}
//#endif
		}
			break;
		default:
			AVR_COUT << o << endl;
			assert(0);
		}
		if (m_mapper->fetch_op(e) == TheoryMapper::BV_OP) {
			assert(res);
			add_gate_constraint(yvar, res, "result of a bv op", e, false, true);
		}
		else if (m_mapper->fetch_op(e) == TheoryMapper::EUF_OP || m_mapper->fetch_op(e) == TheoryMapper::CLU_OP) {
			if (interpreted) {
				assert(res);
				add_gate_constraint(yvar, res, "interpreted operator constraint for EUF", e, false, true);
			}
			else {
				if (opstr == "") {
					cout << OpInst::op2str(o) << endl;
					assert(0);
				}
				add_yices_func(yvar, opstr, e->get_size() == 1, y_ch, s_sz, e);

//#ifdef INTERPRET_EX_CC
//				if (m_allow_ex_cc)
//				{
//					OpInst* op_cc = OpInst::as(e);
//					assert(op_cc);
////					if (op_cc->get_op() == OpInst::Concat)
//					{
//						Inst* simplified = op_cc->t_simple;
//						if (e != simplified)
//						{
//							add_constraint(yices_eq(yvar, simplified->y2_node.solv_var(get_vIdx())), "partial interpretation of Cc", e);
////							cout << "Asserting " << *e << " == " << *simplified << endl;
//						}
//
//						/// Test
////						const InstL* ch = op_cc->get_children();
////						if (ch)
////						{
////							unsigned s_loc = 0, e_loc = 0;
////							for (InstL::const_iterator cit = ch->begin(); cit != ch->end(); ++cit)
////							{
////								Inst *tve = *cit;
////								unsigned size = tve->get_size();
////								s_loc = e_loc;
////								e_loc += size;
////								Inst* ex_tve = ExInst::create(op_cc, (e_loc - 1), s_loc);
////								assert(tve->get_size() == ex_tve->get_size());
////								cout << "Asserting " << *ex_tve << " == " << *tve << endl;
////								inst2yices(ex_tve);
////								add_constraint(yices_eq(tve->y_var[ABSTRACT], ex_tve->y_var[ABSTRACT]), "partial interpretation of Cc", e);
////							}
////						}
//					}
//				}
//#endif
			}
		} else {
			assert(0);
		}
	}
		break;
	case Ex: {
		ExInst* ex = ExInst::as(e);
		assert(ex != 0);
		if (m_mapper->fetch_op(e) == TheoryMapper::BV_OP) {

			y2_expr_ptr res = yices_bvextract(y_ch.front(), ex->get_lo(), ex->get_hi());
      assert(res);

			add_gate_constraint(yvar, res, "result of a bv EX", e, false, true);

		} else if (m_mapper->fetch_op(e) == TheoryMapper::EUF_OP || m_mapper->fetch_op(e) == TheoryMapper::CLU_OP) {
			assert(y_ch.size() == 1);
			s_sz.clear();
			s_sz.push_back(ex->get_hi());
			s_sz.push_back(ex->get_lo());
			s_sz.push_back((*(ch->begin()))->get_size());
			add_yices_func(yvar, "Extract", e->get_size() == 1, y_ch, s_sz, e);

//#ifdef INTERPRET_EX_CC
//			if (m_allow_ex_cc)
//			{
//				ExInst* ex = ExInst::as(e);
//				Inst* simplified = ex->t_simple;
//				if (e != simplified)
//				{
//					add_constraint(yices_eq(yvar, simplified->y2_node.solv_var(get_vIdx())), "partial interpretation of Ex", e);
//	//				cout << "Asserting " << *e << " == " << *simplified << endl;
//				}
//			}
//#endif
		} else
			assert(0);
	}
		break;
	case UF: {
		UFInst* uf = UFInst::as(e);
		assert(uf != 0);
		assert(ch != 0);
		assert(ch->size() > 0);
		//    unsigned ch_sz = (*(ch->begin()))->get_size();

		//    cout<<"uf->get_name = "<<uf->get_name()<<endl;
		//    cout<<"clean: "<<clean_str(uf->get_name())<<endl;

		add_yices_func(yvar, clean_str(uf->get_name()), e->get_size() == 1, y_ch, s_sz, e);

		/*    if(m_mapper->fetch_op(e)==TheoryMapper::BV_OP){
		 yices_type domains[ch->size()];
		 for(unsigned i = 0 ; i < ch->size(); i++)
		 domains[i] = yices_mk_bitvector_type(m_ctx,ch_sz);
		 yices_type domain = yices_mk_bitvector_type(m_ctx,uf->get_size());
		 yices_type funct = yices_mk_function_type(m_ctx,domains,ch->size(),domain);
		 yices_expr func = create_func(uf->get_name(),funct);
		 link_func(yvar,func,y_ch);
		 } else if(m_mapper->fetch_op(e)==TheoryMapper::EUF_OP ||
		 m_mapper->fetch_op(e)==TheoryMapper::CLU_OP){
		 s_sz.clear();
		 add_yices_func(yvar,clean_str(uf->get_name()),e->get_size()==1,y_ch,s_sz,e,(m_mapper->fetch_var(e)==TheoryMapper::BV_VAR)?e->get_size():0);
		 } else assert(0);*/
	}
		break;
	case Mem:
	default:
		AVR_COUT << e->get_type() << endl;
		assert(0);
	}

#ifdef INTERPRET_EX_CC
	if (m_allow_ex_cc)
	{
		if (Config::g_uf_mult_only || (m_mapper->fetch_op(e) == TheoryMapper::EUF_OP) ||
				(m_mapper->fetch_op(e->t_simple) == TheoryMapper::EUF_OP)) {
			Inst* simplified = e->t_simple;
			if (e != simplified)
			{
	#ifdef INTERPRET_UF_NUM
				{
					NumInst* num = NumInst::as(e);
					if (num) {
						if (e->get_size() != 1) {

							OpInst* opS = OpInst::as(simplified);
							assert(opS);
							assert(opS->get_op() == OpInst::Concat);

							y2_expr_vec tmp_constraints;
							swap(tmp_constraints, m_constraints);

							inst2yices(simplified);
							for (int i = 0; i < num->get_size(); i++) {
								Inst* ex = ExInst::create(num, i, i);
								inst2yices(ex);
							}

							swap(tmp_constraints, m_constraints);
							for (auto& c: tmp_constraints)
								add_constraint(c, "(partial interpretation)", e);
						}
					}
				}
	#endif

	#ifdef INTERPRET_UF_SIG
				{
					SigInst* sig = SigInst::as(e);
					if (sig) {
						if (e->get_size() != 1) {

							OpInst* opS = OpInst::as(simplified);
							assert(opS);
							assert(opS->get_op() == OpInst::Concat);

							y2_expr_vec tmp_constraints;
							swap(tmp_constraints, m_constraints);

							inst2yices(simplified);
	//						for (int i = 0; i < sig->get_size(); i++) {
	//							Inst* ex = ExInst::create(sig, i, i);
	//							inst2yices(ex);
	//						}

							swap(tmp_constraints, m_constraints);
							for (auto& c: tmp_constraints)
								add_constraint(c, "(partial interpretation)", e);
						}
					}
				}
	#endif

				{
					y2_expr_ptr a = simplified->y2_node.solv_var(get_vIdx());
					add_gate_constraint(yvar, a, "(partial interpretation)", e, true, false);
				}
			}
		}
	}
#endif

	if (yvar == Y2_INVALID_EXPR) {
		cout << *e << endl;
	}
	assert(yvar != Y2_INVALID_EXPR);

//	cout << "[I2Y]\t" << *e << " --> " << print_term(yvar) << endl;
}

void y2_API::increase_cond_activity() {
//  for (auto& cond: conds) {
//    double act1 = -1;
//    y2_get_activity(m_ctx, cond, &act1);
//    y2_increase_activity(m_ctx, cond);
//    double act2 = -1;
//    y2_get_activity(m_ctx, cond, &act2);
////    cout << print_term(cond) << " : " << act1 << " -> " << act2 << endl;
////    assert(0);
//  }
}



};

#endif
