/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


/*
 * reach_y2.h
 *
 *  Created on: Jan 23, 2018
 *      Author: rock
 */

#ifndef SRC_REACH_REACH_Y2_H_
#define SRC_REACH_REACH_Y2_H_


/// Yices 2 Backend

#include "reach_backend.h"

#ifdef _Y2

namespace _y2 {

//#define Y2_USE_RETRACTABLE_ASSUMPTIONS

//#define Y2_STATS

#define Y2_MAX_RESET_ALLOWED	1000

#ifndef MICRO_ALARM
	#define Y2_ABSTRACT_SOFT_TIMEOUT  1    // 1 seconds
	#define Y2_RESET_TIMEOUT				  10   // 10 seconds
#else
	#define Y2_ABSTRACT_SOFT_TIMEOUT       3000000		//  1     seconds
	#define Y2_RESET_TIMEOUT_FALLBACK   	10000000		// 10     seconds
	#define Y2_RESET_TIMEOUT				      50000000    // 40     seconds
	#define Y2_RESET_TIMEOUT_TRIAL	      50000000    // 40     seconds

	#define Y2_SOFT_TIMEOUT_INC_VALUE        15000    //  0.01  seconds
#endif

#define Y2_INTERACTIVE
// #define Y2_CTI_MULTICHECKS

#define Y2_ARRAY_ALLOW_BOOL

//#define Y2_DISABLE_TRY_VAR_ELIM
//#define Y2_RESET_FALLBACK_ONLY
#define Y2_SOFT_TIMEOUT_INC

//#define Y2_FORCE_NONINC               // force non-incremetal queries wherever possible

#define Y2_MUS_M1			// MUS extraction with alternate way to assert assertions
//#define Y2_EXPENSIVE_CORE_EXTRACTION
//#define Y2_SCALAR_BUCKETS
//#define Y2_CREATE_UCONSTANTS

//#define DUMP_CONTEXT_SAT
//#define DUMP_CONTEXT_UNSAT

typedef std::map<std::string, y2_expr_ptr> y2_StringToDecl;
typedef std::map<pair<Inst*, string>, y2_expr_ptr, compare_pair_string> y2_InstToFuncDecl;
typedef std::map<std::string, y2_ftype_ptr> y2_StringToFunctM;
typedef std::map< pair<unsigned, SORT>, y2_type_ptr> y2_IntBvM;
typedef std::map< pair<unsigned, SORT>, y2_type_ptr> y2_IntUtM;
typedef std::map<mpz_class*, y2_expr_ptr> y2_MpzToNum;
typedef std::map<Inst*, pair<y2_expr, y2_expr>, compare> y2_InstToExprM;

typedef void (*out_of_mem_callback_t)(void);

#ifdef Y2_EXP
class y2_statistic {
public:
	y2_stat ab_sum;
	y2_stat bv_sum;

	y2_stat ab_max;
	y2_stat bv_max;

  unsigned num_ab_end;
  unsigned num_bv_end;
  unsigned num_fail_end;

	unsigned num_ab_q;
	unsigned num_bv_q;
	unsigned num_fail_q;

	y2_statistic() {
    num_ab_end = 0;
    num_bv_end = 0;
    num_fail_end = 0;

		num_ab_q = 0;
		num_bv_q = 0;
		num_fail_q = 0;

		ab_sum.clear();
		bv_sum.clear();
		ab_max.clear();
		bv_max.clear();
	}

	void collect_query_stats(y2_stat& in, bool abstract) {

		y2_stat& csum = ab_sum;
		y2_stat& cmax = ab_max;
		if (abstract)
		{
			num_ab_q++;
			csum = ab_sum;
			cmax = ab_max;
		}
		else
		{
			num_bv_q++;
			csum = bv_sum;
			cmax = bv_max;
		}

  // Sum
    // Time stats
		csum.st.boolean_propagation += in.st.boolean_propagation;
		csum.st.theory_propagation += in.st.theory_propagation;
		csum.st.resolve_conflict += in.st.resolve_conflict;
		csum.st.smt_restart += in.st.smt_restart;
		csum.st.select_unassigned_literal += in.st.select_unassigned_literal;
		csum.st.decide_literal += in.st.decide_literal;
		csum.st.add_all_lemmas += in.st.add_all_lemmas;
		csum.st.delete_irrelevant_variables += in.st.delete_irrelevant_variables;
		csum.st.simplify_clause_database += in.st.simplify_clause_database;
		csum.st.reduce_clause_database += in.st.reduce_clause_database;

    csum.st.nassert_atom += in.st.nassert_atom;

    // Time (egraph propagation)
		csum.st.propagate += in.st.propagate;
		csum.st.internal_propagation += in.st.internal_propagation;
    csum.st.reactivate_dynamic_terms += in.st.reactivate_dynamic_terms;
		csum.st.process_equality += in.st.process_equality;
		csum.st.inconsistent_edge += in.st.inconsistent_edge;
		csum.st.invert_branch += in.st.invert_branch;
		csum.st.remove_parents += in.st.remove_parents;
		csum.st.assign_new_label += in.st.assign_new_label;
		csum.st.collect_eqterms += in.st.collect_eqterms;
		csum.st.reprocess_parents += in.st.reprocess_parents;
		csum.st.check_false_eq += in.st.check_false_eq;
		csum.st.atom_propagation += in.st.atom_propagation;
		csum.st.propagate_boolean_equality += in.st.propagate_boolean_equality;

    csum.st.nprocess_eq += in.st.nprocess_eq;
    csum.st.nprocess_eq_redundant += in.st.nprocess_eq_redundant;

    csum.st.egraph_eq_props += in.st.egraph_eq_props;
    csum.st.egraph_th_props += in.st.egraph_th_props;
    csum.st.egraph_th_conflicts += in.st.egraph_th_conflicts;
    csum.st.egraph_final_checks += in.st.egraph_final_checks;
    csum.st.egraph_interface_eqs += in.st.egraph_interface_eqs;

    csum.st.restarts += in.st.restarts;
    csum.st.simplify_calls += in.st.simplify_calls;
    csum.st.reduce_calls += in.st.reduce_calls;
    csum.st.decisions += in.st.decisions;
    csum.st.random_decisions += in.st.random_decisions;
    csum.st.conflicts += in.st.conflicts;

  // Max
    // Time stats
    cmax.st.boolean_propagation = max(cmax.st.boolean_propagation, in.st.boolean_propagation);
    cmax.st.theory_propagation = max(cmax.st.theory_propagation, in.st.theory_propagation);
    cmax.st.resolve_conflict = max(cmax.st.resolve_conflict, in.st.resolve_conflict);
    cmax.st.smt_restart = max(cmax.st.smt_restart, in.st.smt_restart);
    cmax.st.select_unassigned_literal = max(cmax.st.select_unassigned_literal, in.st.select_unassigned_literal);
    cmax.st.decide_literal = max(cmax.st.decide_literal, in.st.decide_literal);
    cmax.st.add_all_lemmas = max(cmax.st.add_all_lemmas, in.st.add_all_lemmas);
    cmax.st.delete_irrelevant_variables = max(cmax.st.delete_irrelevant_variables, in.st.delete_irrelevant_variables);
    cmax.st.simplify_clause_database = max(cmax.st.simplify_clause_database, in.st.simplify_clause_database);
    cmax.st.reduce_clause_database = max(cmax.st.reduce_clause_database, in.st.reduce_clause_database);

    cmax.st.nassert_atom = max(cmax.st.nassert_atom, in.st.nassert_atom);

    // Time (egraph propagation)
    cmax.st.propagate = max(cmax.st.propagate, in.st.propagate);
    cmax.st.internal_propagation = max(cmax.st.internal_propagation, in.st.internal_propagation);
    cmax.st.reactivate_dynamic_terms = max(cmax.st.reactivate_dynamic_terms, in.st.reactivate_dynamic_terms);
    cmax.st.process_equality = max(cmax.st.process_equality, in.st.process_equality);
    cmax.st.inconsistent_edge = max(cmax.st.inconsistent_edge, in.st.inconsistent_edge);
    cmax.st.invert_branch = max(cmax.st.invert_branch, in.st.invert_branch);
    cmax.st.remove_parents = max(cmax.st.remove_parents, in.st.remove_parents);
    cmax.st.assign_new_label = max(cmax.st.assign_new_label, in.st.assign_new_label);
    cmax.st.collect_eqterms = max(cmax.st.collect_eqterms, in.st.collect_eqterms);
    cmax.st.reprocess_parents = max(cmax.st.reprocess_parents, in.st.reprocess_parents);
    cmax.st.check_false_eq = max(cmax.st.check_false_eq, in.st.check_false_eq);
    cmax.st.atom_propagation = max(cmax.st.atom_propagation, in.st.atom_propagation);
    cmax.st.propagate_boolean_equality = max(cmax.st.propagate_boolean_equality, in.st.propagate_boolean_equality);

    cmax.st.nprocess_eq = max(cmax.st.nprocess_eq, in.st.nprocess_eq);
    cmax.st.nprocess_eq_redundant = max(cmax.st.nprocess_eq_redundant, in.st.nprocess_eq_redundant);

    cmax.st.egraph_eq_props = max(cmax.st.egraph_eq_props, in.st.egraph_eq_props);
    cmax.st.egraph_th_props = max(cmax.st.egraph_th_props, in.st.egraph_th_props);
    cmax.st.egraph_th_conflicts = max(cmax.st.egraph_th_conflicts, in.st.egraph_th_conflicts);
    cmax.st.egraph_final_checks = max(cmax.st.egraph_final_checks, in.st.egraph_final_checks);
    cmax.st.egraph_interface_eqs = max(cmax.st.egraph_interface_eqs, in.st.egraph_interface_eqs);

    cmax.st.restarts = max(cmax.st.restarts, in.st.restarts);
    cmax.st.simplify_calls = max(cmax.st.simplify_calls, in.st.simplify_calls);
    cmax.st.reduce_calls = max(cmax.st.reduce_calls, in.st.reduce_calls);
    cmax.st.decisions = max(cmax.st.decisions, in.st.decisions);
    cmax.st.random_decisions = max(cmax.st.random_decisions, in.st.random_decisions);
    cmax.st.conflicts = max(cmax.st.conflicts, in.st.conflicts);

	}

  void collect_end_stats(y2_stat& in, bool abstract) {

    y2_stat& csum = ab_sum;
    y2_stat& cmax = ab_max;
    if (abstract)
    {
      num_ab_end++;
      csum = ab_sum;
      cmax = ab_max;
    }
    else
    {
      num_bv_end++;
      csum = bv_sum;
      cmax = bv_max;
    }

    // Sum

    csum.st.base_bool_propagate += in.st.base_bool_propagate;
    csum.st.base_th_propagate += in.st.base_th_propagate;
    csum.st.flatten_assertion += in.st.flatten_assertion;
    csum.st.preprocess_assertion += in.st.preprocess_assertion;
    csum.st.assert_toplevel_formula += in.st.assert_toplevel_formula;
    csum.st.assert_toplevel_intern += in.st.assert_toplevel_intern;
    csum.st.nassert_rounds += in.st.nassert_rounds;
    csum.st.nassert += in.st.nassert;

    csum.st.egraph_app_reductions += in.st.egraph_app_reductions;
    csum.st.egraph_nd_lemmas += in.st.egraph_nd_lemmas;
    csum.st.egraph_aux_eqs += in.st.egraph_aux_eqs;
    csum.st.egraph_boolack_lemmas += in.st.egraph_boolack_lemmas;
    csum.st.egraph_ack_lemmas += in.st.egraph_ack_lemmas;
    csum.st.egraph_terms += in.st.egraph_terms;

		csum.st.remove_calls += in.st.remove_calls;
		csum.st.propagations += in.st.propagations;
		csum.st.th_props += in.st.th_props;
		csum.st.th_prop_lemmas += in.st.th_prop_lemmas;
		csum.st.th_conflicts += in.st.th_conflicts;
		csum.st.th_conflict_lemmas += in.st.th_conflict_lemmas;
		csum.st.prob_literals += in.st.prob_literals;
		csum.st.learned_literals += in.st.learned_literals;
    csum.st.literals_before_simpl += in.st.literals_before_simpl;
    csum.st.subsumed_literals += in.st.subsumed_literals;
		csum.st.prob_clauses_deleted += in.st.prob_clauses_deleted;
		csum.st.learned_clauses_deleted += in.st.learned_clauses_deleted;
		csum.st.bin_clauses_deleted += in.st.bin_clauses_deleted;
		csum.st.boolean_variables += in.st.boolean_variables;
		csum.st.atoms += in.st.atoms;

    // Max

		cmax.st.base_bool_propagate = max(cmax.st.base_bool_propagate, in.st.base_bool_propagate);
		cmax.st.base_th_propagate = max(cmax.st.base_th_propagate, in.st.base_th_propagate);
		cmax.st.flatten_assertion = max(cmax.st.flatten_assertion, in.st.flatten_assertion);
		cmax.st.preprocess_assertion = max(cmax.st.preprocess_assertion, in.st.preprocess_assertion);
		cmax.st.assert_toplevel_formula = max(cmax.st.assert_toplevel_formula, in.st.assert_toplevel_formula);
		cmax.st.assert_toplevel_intern = max(cmax.st.assert_toplevel_intern, in.st.assert_toplevel_intern);
    cmax.st.nassert_rounds = max(cmax.st.nassert_rounds, in.st.nassert_rounds);
		cmax.st.nassert = max(cmax.st.nassert, in.st.nassert);

    cmax.st.egraph_app_reductions = max(cmax.st.egraph_app_reductions, in.st.egraph_app_reductions);
    cmax.st.egraph_nd_lemmas = max(cmax.st.egraph_nd_lemmas, in.st.egraph_nd_lemmas);
    cmax.st.egraph_aux_eqs = max(cmax.st.egraph_aux_eqs, in.st.egraph_aux_eqs);
    cmax.st.egraph_boolack_lemmas = max(cmax.st.egraph_boolack_lemmas, in.st.egraph_boolack_lemmas);
    cmax.st.egraph_ack_lemmas = max(cmax.st.egraph_ack_lemmas, in.st.egraph_ack_lemmas);
    cmax.st.egraph_terms = max(cmax.st.egraph_terms, in.st.egraph_terms);

    cmax.st.remove_calls = max(cmax.st.remove_calls, in.st.remove_calls);
    cmax.st.propagations = max(cmax.st.propagations, in.st.propagations);
    cmax.st.th_props = max(cmax.st.th_props, in.st.th_props);
    cmax.st.th_prop_lemmas = max(cmax.st.th_prop_lemmas, in.st.th_prop_lemmas);
    cmax.st.th_conflicts = max(cmax.st.th_conflicts, in.st.th_conflicts);
    cmax.st.th_conflict_lemmas = max(cmax.st.th_conflict_lemmas, in.st.th_conflict_lemmas);
    cmax.st.prob_literals = max(cmax.st.prob_literals, in.st.prob_literals);
    cmax.st.learned_literals = max(cmax.st.learned_literals, in.st.learned_literals);
    cmax.st.literals_before_simpl = max(cmax.st.literals_before_simpl, in.st.literals_before_simpl);
    cmax.st.subsumed_literals = max(cmax.st.subsumed_literals, in.st.subsumed_literals);
    cmax.st.prob_clauses_deleted = max(cmax.st.prob_clauses_deleted, in.st.prob_clauses_deleted);
    cmax.st.learned_clauses_deleted = max(cmax.st.learned_clauses_deleted, in.st.learned_clauses_deleted);
    cmax.st.bin_clauses_deleted = max(cmax.st.bin_clauses_deleted, in.st.bin_clauses_deleted);
    cmax.st.boolean_variables = max(cmax.st.boolean_variables, in.st.boolean_variables);
    cmax.st.atoms = max(cmax.st.atoms, in.st.atoms);

  }

  void merge_stats(y2_statistic& in) {

    ab_sum.add_stat(in.ab_sum);
    bv_sum.add_stat(in.bv_sum);

    ab_max.max_stat(in.ab_max);
    bv_max.max_stat(in.bv_max);

    num_ab_end += in.num_ab_end;
    num_bv_end += in.num_bv_end;
    num_fail_end += in.num_fail_end;

    num_ab_q += in.num_ab_q;
    num_bv_q += in.num_bv_q;
    num_fail_q += in.num_fail_q;

  }

//		csum.st.num_init_vars += in.st.num_init_vars;
//		csum.st.num_init_edges += in.st.num_init_edges;
//		csum.st.num_update_axiom1 += in.st.num_update_axiom1;
//		csum.st.num_update_axiom2 += in.st.num_update_axiom2;
//		csum.st.num_extensionality_axiom += in.st.num_extensionality_axiom;
//
//		csum.st.bv_variables += in.st.bv_variables;
//		csum.st.bv_atoms += in.st.bv_atoms;
//		csum.st.bv_eq_atoms += in.st.bv_eq_atoms;
//		csum.st.bv_dyn_eq_atoms += in.st.bv_dyn_eq_atoms;
//		csum.st.bv_ge_atoms += in.st.bv_ge_atoms;
//		csum.st.bv_sge_atoms += in.st.bv_sge_atoms;
//		csum.st.bv_equiv_lemmas += in.st.bv_equiv_lemmas;
//		csum.st.bv_equiv_conflicts += in.st.bv_equiv_conflicts;
//		csum.st.bv_semi_equiv_lemmas += in.st.bv_semi_equiv_lemmas;
//		csum.st.bv_interface_lemmas += in.st.bv_interface_lemmas;


//		cmax.st.num_init_vars = max(cmax.st.num_init_vars, in.st.num_init_vars);
//		cmax.st.num_init_edges = max(cmax.st.num_init_edges, in.st.num_init_edges);
//		cmax.st.num_update_axiom1 = max(cmax.st.num_update_axiom1, in.st.num_update_axiom1);
//		cmax.st.num_update_axiom2 = max(cmax.st.num_update_axiom2, in.st.num_update_axiom2);
//		cmax.st.num_extensionality_axiom = max(cmax.st.num_extensionality_axiom, in.st.num_extensionality_axiom);
//
//		cmax.st.bv_variables = max(cmax.st.bv_variables, in.st.bv_variables);
//		cmax.st.bv_atoms = max(cmax.st.bv_atoms, in.st.bv_atoms);
//		cmax.st.bv_eq_atoms = max(cmax.st.bv_eq_atoms, in.st.bv_eq_atoms);
//		cmax.st.bv_dyn_eq_atoms = max(cmax.st.bv_dyn_eq_atoms, in.st.bv_dyn_eq_atoms);
//		cmax.st.bv_ge_atoms = max(cmax.st.bv_ge_atoms, in.st.bv_ge_atoms);
//		cmax.st.bv_sge_atoms = max(cmax.st.bv_sge_atoms, in.st.bv_sge_atoms);
//		cmax.st.bv_equiv_lemmas = max(cmax.st.bv_equiv_lemmas, in.st.bv_equiv_lemmas);
//		cmax.st.bv_equiv_conflicts = max(cmax.st.bv_equiv_conflicts, in.st.bv_equiv_conflicts);
//		cmax.st.bv_semi_equiv_lemmas = max(cmax.st.bv_semi_equiv_lemmas, in.st.bv_semi_equiv_lemmas);
//		cmax.st.bv_interface_lemmas = max(cmax.st.bv_interface_lemmas, in.st.bv_interface_lemmas);

	void fail_query(void) {
		num_fail_q++;
		assert(0);
	}
  void fail_end(void) {
    num_fail_end++;
    assert(0);
  }
};
#endif

class y2_API: public Solver {
public:

	static int g_soft_timeout;
	static int g_num_reset;

	static map< int, y2_API* > y2_solvers;

  static out_of_mem_callback_t y2_out_of_memory_callback;

  static y2_expr_list conds;

#ifdef Y2_EXP
	static y2_statistic g_stat_reg;
  static y2_statistic g_stat_cti;
  static y2_statistic g_stat_br;
  static y2_statistic g_stat_fp;
  static y2_statistic g_stat_core;
  static y2_statistic g_stat_min;
#endif

	static y2_StringToDecl m_var_decs;
	static y2_InstToFuncDecl m_func_decs;
	static y2_StringToFunctM m_funct;
	static y2_IntBvM m_sz_to_bv;
	static y2_IntUtM m_sz_to_ut;
	static y2_MpzToNum m_num_to_const;

#ifdef ASSERT_DISTINCT_NUMBERS
	static pair < int, y2_expr_vec > m_distinct_constraints;
#endif

#ifdef Y2_SCALAR_BUCKETS
  static vector<unsigned> sz_to_card;
#endif

	////// Zero and one
	// BV type!
	static y2_expr_ptr m_v0, m_v1;
	// BOOL type!
	static y2_expr_ptr m_b0, m_b1;

	static y2_context	g_ctx;

	y2_config	m_config;
	y2_context	m_ctx;
	y2_param	m_param;
	y2_model	m_model;

	static void y2_init();
	static void y2_exit();
	static void y2_reset();
	static void y2_set();
	static void y2_unset();

	static void y2_interrupt(int signum);
#ifdef Y2_EXP
	static void print_solv_statistic(ofstream& out, y2_statistic& stat, string comment="");
#endif

	static void y2_collect_garbage(bool keep_named = true);

	// Needs to know the index of the back-annotation that this solver is allowed to work with!
	y2_API(TheoryMapper* m, unsigned ba_idx, bool is_inc, int type);
	y2_API(TheoryMapper* m, unsigned ba_idx, int mode, int type);
	y2_API(TheoryMapper* m);

	virtual void debug();

  virtual void collect_solver_stats();

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

	void enable_model() {
		disable_var_elim(m_ctx);
	}
	void disable_model() {
		enable_var_elim(m_ctx);
	}

	virtual ~y2_API();

	void get_value_bv(unsigned sz, y2_expr& decl, string& sval);
	void get_value_int(unsigned sz, y2_expr& decl, string& sval);
	void get_value_utt(unsigned sz, y2_expr& decl, string& sval);

	void get_value_bv(unsigned sz, y2_val* decl, string& sval);
	void get_value_int(unsigned sz, y2_val* decl, string& sval);
	void get_value_utt(unsigned sz, y2_val* decl, string& sval);
	void get_value_arr(bool abstract, SORT& sort, y2_val* decl, string& sval);
	void get_value(bool abstract, SORT& sort, y2_val& decl, string& sval);


	std::string get_y2_name(Inst*e);
	std::string get_y2_temp_name(Inst*e, int count);

	/// Dump query in SMT2 format
	/// time_diff is time taken by AVR (in seconds)
	virtual void print_smt2(string fname="", string header="");

#ifdef ASSERT_DISTINCT_NUMBERS
	virtual void assert_distinct_constants(void);
#endif

	virtual void print_constraints(int loc = 15, int level = 0);

	Solver* copy_solver(void);
	virtual bool s_another_solution(void);

  void dump_core(void);
  int32_t s_push(void);

  void s_print_model(void);

	/// Flag true if solver is incremental
	bool is_i;

#ifdef TRACE_SOLVER
	virtual void process_trace(ofstream& f);
#endif

protected:

	y2_expr_vec m_constraints;
	y2_expr_vec m_assumptions;
  y2_expr_vec m_unsatCore;

//	list< list< y2_expr_ptr > > m_stack;

//	y2_expr_vec m_assumptions;

	list< pair<int, y2_expr_vec> > m_cList;

	y2_InstToExprM m_inst_to_y;
  map<y2_expr, Inst*> m_y_to_inst;
  set<y2_expr> m_hard_constraints;

  void enable_var_elim(y2_context ctx);
  void disable_var_elim(y2_context ctx);
  void enable_keep_ite(y2_context ctx);
  void disable_keep_ite(y2_context ctx);
  void disable_keep_ite(void) {
  	disable_keep_ite(m_ctx);
  }

  void set_context_parameters(y2_context ctx);
  void set_context_parameters(void) {
  	set_context_parameters(m_ctx);
  }

  void set_parameters(y2_param prm);
  void set_parameters() {
  	set_parameters(m_param);
  }

	void set_logic(y2_config cfg);
  void set_logic(void) {
    set_logic(m_config);
  }

  y2_type create_bv_sort(pair< unsigned, SORT > sz);
  y2_type create_int_sort(pair< unsigned, SORT > sz, bool dom_bv=false, bool ran_bv=false);

	y2_expr create_bv_var(std::string name, pair< unsigned, SORT > sz);
	y2_expr create_int_var(std::string name, pair< unsigned, SORT > sz, bool dom_bv=false, bool ran_bv=false);
	y2_expr create_bool_var(std::string name);

	void add_yices_func(y2_expr& var, std::string op, bool pred, y2_expr_list& ch, Ints& sz, Inst* e);

	void inst2yices(Inst*e, bool bvAllConstraints=false);

	void add_variable(y2_expr& lhs, Inst*e);
	void add_gate_constraint(y2_expr& lhs, y2_expr_ptr rhs, std::string comment, Inst*e, bool asConstraint, bool checkType);
	void add_constraint(y2_expr_ptr y, std::string comment, Inst*e, bool storeC, bool forced);
	void force(Inst* e);
	y2_expr force_wo_add(Inst* e);

	void s_assert_constraints(y2_expr_ptr indVar, bool reset = true);
	void s_assert_constraints(bool reset = true)
	{
		s_assert_constraints(Y2_INVALID_EXPR, reset);
	}
	int s_assert_constraint(y2_expr_ptr ye);

	int32_t s_pop(void);
	void print_y2(string fname="", double time_diff=-1);

	bool s_check_model(bool allowDontCares=false);
//	void swap_model(y2_model& mdl);

	int get_mus(long timeout_value, InstL& vel_2, InstL& mus, int& numSat, int& numUnsat, bool recordTime);

	y2_result shift_to_noninc(long timeout_value, long long time_res, bool getModel);
	y2_result shift_to_noninc(long timeout_value, y2_expr_vec& assumptions, y2_expr_vec& unsatCore, long long time_res, bool getModel);

  y2_result s_check_oneshot(long timeout_value, bool getModel, bool tryVarElim, bool keepIte, bool enReset);
  y2_result s_check_oneshot_reset(long timeout_value, bool getModel);
  y2_result s_check_oneshot_reset2(long timeout_value, bool getModel, bool keepIte);

	y2_result s_check_inc(long timeout_value, bool getModel = true);

  y2_result s_check_mus(long timeout_value, y2_expr_vec& assumptions, y2_expr_vec& unsatCore, bool getModel = true);
  y2_result s_check_oneshot_mus(long timeout_value, y2_expr_vec& assumptions, y2_expr_vec& unsatCore, bool getModel, bool tryVarElim, bool keepIte, bool enReset);
  y2_result s_check_oneshot_mus_reset(long timeout_value, y2_expr_vec& assumptions, y2_expr_vec& unsatCore, bool getModel);
  y2_result s_check_oneshot_mus_reset2(long timeout_value, y2_expr_vec& assumptions, y2_expr_vec& unsatCore, bool getModel, bool keepIte);

  void s_add_core(InstL& core, bool push);

  void s_add_assumptions(InstL& assumptions, bool push);
  y2_expr_vec& get_assumptions() {
  	return m_assumptions;
  }
	bool s_assert(InstLL& vel);

	y2_result query_non_inc(long timeout_value, bool getModel = true);

#ifdef Y2_EXP
	void collect_solv_statistic_query();
  void collect_solv_statistic_end();
#endif

private:
  void s_reset_single_solver();
  void s_reset_remaining_solvers(int solver_id);
  void s_reset_all_solvers();
  void s_reset_scope();

	void s_reset_solver();

  y2_expr_ptr create_y2_number(NumInst* num);
  void increase_cond_activity();

#ifdef TEST_CONNECT_BV
  y2_expr_ptr u2b(int sz, Inst* e);
  y2_expr_ptr b2u(int sz, Inst* e);
  void add_conversion_func(y2_expr& out, std::string op, y2_expr_ptr ch, int sz, Inst* e);
#endif
};

#ifndef MICRO_ALARM
#define Y2_SET_TIMEOUT													\
				g_ctx = m_ctx;													\
				s_check_timed_out = false;							\
				assert(0 == alarm(timeout_value));
#else
#define Y2_SET_TIMEOUT(context)																			\
	g_ctx = context;																									\
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

#define Y2_CHECK_TIMEOUT																						\
	alarm(0);																													\
	if (s_check_timed_out == true) {																	\
		res = STATUS_INTERRUPTED;																				\
	}

};

#endif

#endif /* SRC_REACH_REACH_Y2_H_ */
