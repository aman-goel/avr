/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


/*
 * avr_backend.h
 *
 *  Created on: Jan 23, 2018
 *      Author: amangoel
 */

#ifndef SRC_REACH_AVR_BACKEND_H_
#define SRC_REACH_AVR_BACKEND_H_

#include "avr_def.h"

/// Backends -- enabled through compile time flags
//#define _Z3									// Z3 backend
//#define _Y2									// Yices 2 backend
//#define _M5									// MathSAT 5 backend
//#define _BT									// Boolector backend
//#define _MS									// MiniSAT backend

//#define Y2_CUSTOM
#ifdef Y2_CUSTOM
//	#define Y2_EXP							// Use custom experimental repository for Yices 2
#endif

#ifdef _Z3
	#include "z3++.h"
	using namespace z3;
#endif

#ifdef _Y2
	extern "C"
	{
#ifdef Y2_CUSTOM
	#include "/home/rock/ws/version/github/aman_goel/tmp/yices2/src/include/yices.h"
#else
//	#include "/home/rock/ws/version/github/yices2/src/include/yices.h"
	#include "yices.h"
//	#include "/home/rock/ws/version/github/aman_goel/yices2/src/include/yices.h"
#endif
//	#include "yices.h"
	}
#endif

#ifdef _M5
	#include "mathsat.h"
#endif

#ifdef _BT
	extern "C"
	{
	#include "boolector.h"
	}
#endif

#ifdef _MS
	extern "C"
	{
	#include "../sat/minisat/satSolver.h"
	}
#endif


#ifdef _Z3
	typedef z3::config*     z3_config;
	typedef z3::context*    z3_context;
	typedef z3::params*     z3_param;
	typedef z3::solver*     z3_solver;
	typedef z3::model*      z3_model;
	typedef z3::sort        z3_type;
	typedef z3::expr        z3_expr;
	typedef z3::expr_vector z3_expr_vector;
	typedef z3::func_decl   z3_ftype;
	typedef z3::stats   	z3_stats;
	typedef z3::func_interp z3_func_interp;

	typedef check_result	z3_result;
	typedef z3_type*		z3_type_ptr;
	typedef z3_expr*		z3_expr_ptr;
	typedef z3_ftype*		z3_ftype_ptr;

	typedef std::vector<z3_expr_ptr>	z3_expr_vec;
	typedef std::list<z3_expr_ptr>		z3_expr_list;

	#define Z3_INVALID_EXPR NULL
#endif

#ifdef _Y2
	typedef ctx_config_t*	y2_config;
	typedef context_t*		y2_context;
	typedef param_t*		  y2_param;

	typedef model_t*		  y2_model;
	typedef type_t			  y2_type;
	typedef term_t			  y2_expr;
	typedef yval_t			  y2_val;
#ifdef Y2_EXP
	typedef stats_t			  y2_stats_t;
#endif

	typedef term_t			  y2_ftype;

	typedef smt_status		y2_result;
	typedef y2_type			  y2_type_ptr;
	typedef y2_expr			  y2_expr_ptr;
	typedef y2_ftype		  y2_ftype_ptr;
  typedef term_vector_t y2_expr_vector;
  typedef yval_vector_t y2_val_vector;

	typedef std::vector<y2_expr_ptr>	y2_expr_vec;
	typedef std::list<y2_expr_ptr>		y2_expr_list;

	#define Y2_INVALID_EXPR -1

#ifdef Y2_EXP
	class y2_stat {
	public:
		y2_stats_t st;

		void clear(void) {
			st.restarts = 0;         // number of restarts
			st.simplify_calls = 0;   // number of calls to simplify_clause_database
			st.reduce_calls = 0;     // number of calls to reduce_learned_clause_set
			st.remove_calls = 0;     // number of calls to remove_irrelevant_learned_clauses

			st.decisions = 0;        // number of decisions
			st.random_decisions = 0; // number of random decisions
			st.propagations = 0;     // number of boolean propagations
			st.conflicts = 0;        // number of conflicts/backtrackings

			st.th_props = 0;         // number of theory propagation
			st.th_prop_lemmas = 0;   // number of propagation/explanation turned into clauses
			st.th_conflicts = 0;     // number of calls to record_conflict
			st.th_conflict_lemmas = 0;  // number of theory conflicts turned into clauses

			st.prob_literals = 0;     // number of literals in problem clauses
			st.learned_literals = 0;  // number of literals in learned clauses

			st.prob_clauses_deleted = 0;     // number of problem clauses deleted
			st.learned_clauses_deleted = 0;  // number of learned clauses deleted
			st.bin_clauses_deleted = 0;      // number of binary clauses deleted

			st.literals_before_simpl = 0;
			st.subsumed_literals = 0;

			st.boolean_variables = 0;
			st.atoms = 0;

			// Egraph
			st.egraph_app_reductions = 0;

			st.egraph_eq_props = 0;         // equalities propagated by satellite solvers (simplex)
			st.egraph_th_props = 0;         // propagations from egraph to core
			st.egraph_th_conflicts = 0;     // conflicts detected by egraph
			st.egraph_nd_lemmas = 0;        // number of non-distinct lemmas

			// counters related to ackermann clauses
			st.egraph_aux_eqs = 0;          // number of equality terms created
			st.egraph_boolack_lemmas = 0;   // number of boolean ackermann instances created
			st.egraph_ack_lemmas = 0;       // number of non-boolean ackermann instances created

			// statistics on interface equalities
			st.egraph_final_checks = 0;     // number of calls to final check
			st.egraph_interface_eqs = 0;    // number of interface equalities generated

			st.egraph_terms = 0;

			// Array/function
			// initial size
			st.num_init_vars = 0;
			st.num_init_edges = 0;

			// number of axioms generated
			st.num_update_axiom1 = 0;
			st.num_update_axiom2 = 0;
			st.num_extensionality_axiom = 0;

			// Bit-vectors
			st.bv_variables = 0;
			st.bv_atoms = 0;
			st.bv_eq_atoms = 0;
			st.bv_dyn_eq_atoms = 0;
			st.bv_ge_atoms = 0;
			st.bv_sge_atoms = 0;
			st.bv_equiv_lemmas = 0;
			st.bv_equiv_conflicts = 0;
			st.bv_semi_equiv_lemmas = 0;
			st.bv_interface_lemmas = 0;

			// Time stats
      st.boolean_propagation = 0;
      st.theory_propagation = 0;
      st.resolve_conflict = 0;
			st.smt_restart = 0;
      st.select_unassigned_literal = 0;
      st.decide_literal = 0;
      st.add_all_lemmas = 0;
			st.delete_irrelevant_variables = 0;
			st.simplify_clause_database = 0;
			st.reduce_clause_database = 0;

			// Time adding assertions
			st.base_bool_propagate = 0;
			st.base_th_propagate = 0;
			st.flatten_assertion = 0;
			st.preprocess_assertion = 0;
			st.assert_toplevel_formula = 0;
			st.assert_toplevel_intern = 0;

			st.nassert_rounds = 0;
			st.nassert = 0;
			st.nassert_atom = 0;                     // number of atoms asserted

		  // Time (egraph propagation)
			st.propagate = 0;
			st.internal_propagation = 0;
			st.reactivate_dynamic_terms = 0;
			st.process_equality = 0;
			st.inconsistent_edge = 0;
			st.invert_branch = 0;
			st.remove_parents = 0;
			st.assign_new_label = 0;
			st.collect_eqterms = 0;
			st.reprocess_parents = 0;
			st.check_false_eq = 0;
			st.atom_propagation = 0;
			st.propagate_boolean_equality = 0;

		  // statistics on propagation
		  st.nprocess_eq = 0;                     // number of equalities processed
		  st.nprocess_eq_redundant = 0;           // number of equalities processed found to be redundant
		}

		void add_stat(y2_stat& in) {
		  st.restarts += in.st.restarts;
		  st.simplify_calls += in.st.simplify_calls;
		  st.reduce_calls += in.st.reduce_calls;
		  st.remove_calls += in.st.remove_calls;
		  st.decisions += in.st.decisions;
		  st.random_decisions += in.st.random_decisions;
		  st.propagations += in.st.propagations;
		  st.conflicts += in.st.conflicts;
		  st.th_props += in.st.th_props;
		  st.th_prop_lemmas += in.st.th_prop_lemmas;
		  st.th_conflicts += in.st.th_conflicts;
		  st.th_conflict_lemmas += in.st.th_conflict_lemmas;
		  st.prob_literals += in.st.prob_literals;
		  st.learned_literals += in.st.learned_literals;
		  st.prob_clauses_deleted += in.st.prob_clauses_deleted;
		  st.learned_clauses_deleted += in.st.learned_clauses_deleted;
		  st.bin_clauses_deleted += in.st.bin_clauses_deleted;
		  st.literals_before_simpl += in.st.literals_before_simpl;
		  st.subsumed_literals += in.st.subsumed_literals;
		  st.boolean_variables += in.st.boolean_variables;
		  st.atoms += in.st.atoms;
		  st.egraph_app_reductions += in.st.egraph_app_reductions;
		  st.egraph_eq_props += in.st.egraph_eq_props;
		  st.egraph_th_props += in.st.egraph_th_props;
		  st.egraph_th_conflicts += in.st.egraph_th_conflicts;
		  st.egraph_nd_lemmas += in.st.egraph_nd_lemmas;
		  st.egraph_aux_eqs += in.st.egraph_aux_eqs;
		  st.egraph_boolack_lemmas += in.st.egraph_boolack_lemmas;
		  st.egraph_ack_lemmas += in.st.egraph_ack_lemmas;
		  st.egraph_final_checks += in.st.egraph_final_checks;
		  st.egraph_interface_eqs += in.st.egraph_interface_eqs;
		  st.egraph_terms += in.st.egraph_terms;
		  st.num_init_vars += in.st.num_init_vars;
		  st.num_init_edges += in.st.num_init_edges;
		  st.num_update_axiom1 += in.st.num_update_axiom1;
		  st.num_update_axiom2 += in.st.num_update_axiom2;
		  st.num_extensionality_axiom += in.st.num_extensionality_axiom;
		  st.bv_variables += in.st.bv_variables;
		  st.bv_atoms += in.st.bv_atoms;
		  st.bv_eq_atoms += in.st.bv_eq_atoms;
		  st.bv_dyn_eq_atoms += in.st.bv_dyn_eq_atoms;
		  st.bv_ge_atoms += in.st.bv_ge_atoms;
		  st.bv_sge_atoms += in.st.bv_sge_atoms;
		  st.bv_equiv_lemmas += in.st.bv_equiv_lemmas;
		  st.bv_equiv_conflicts += in.st.bv_equiv_conflicts;
		  st.bv_semi_equiv_lemmas += in.st.bv_semi_equiv_lemmas;
		  st.bv_interface_lemmas += in.st.bv_interface_lemmas;
		  st.boolean_propagation += in.st.boolean_propagation;
		  st.theory_propagation += in.st.theory_propagation;
		  st.resolve_conflict += in.st.resolve_conflict;
		  st.smt_restart += in.st.smt_restart;
		  st.select_unassigned_literal += in.st.select_unassigned_literal;
		  st.decide_literal += in.st.decide_literal;
		  st.add_all_lemmas += in.st.add_all_lemmas;
		  st.delete_irrelevant_variables += in.st.delete_irrelevant_variables;
		  st.simplify_clause_database += in.st.simplify_clause_database;
		  st.reduce_clause_database += in.st.reduce_clause_database;
		  st.base_bool_propagate += in.st.base_bool_propagate;
		  st.base_th_propagate += in.st.base_th_propagate;
		  st.flatten_assertion += in.st.flatten_assertion;
		  st.preprocess_assertion += in.st.preprocess_assertion;
		  st.assert_toplevel_formula += in.st.assert_toplevel_formula;
		  st.assert_toplevel_intern += in.st.assert_toplevel_intern;
		  st.nassert_rounds += in.st.nassert_rounds;
		  st.nassert += in.st.nassert;
		  st.nassert_atom += in.st.nassert_atom;
		  st.propagate += in.st.propagate;
		  st.internal_propagation += in.st.internal_propagation;
		  st.reactivate_dynamic_terms += in.st.reactivate_dynamic_terms;
		  st.process_equality += in.st.process_equality;
		  st.inconsistent_edge += in.st.inconsistent_edge;
		  st.invert_branch += in.st.invert_branch;
		  st.remove_parents += in.st.remove_parents;
		  st.assign_new_label += in.st.assign_new_label;
		  st.collect_eqterms += in.st.collect_eqterms;
		  st.reprocess_parents += in.st.reprocess_parents;
		  st.check_false_eq += in.st.check_false_eq;
		  st.atom_propagation += in.st.atom_propagation;
		  st.propagate_boolean_equality += in.st.propagate_boolean_equality;
		  st.nprocess_eq += in.st.nprocess_eq;
		  st.nprocess_eq_redundant += in.st.nprocess_eq_redundant;
		}

    void max_stat(y2_stat& in) {
      st.restarts = max(st.restarts, in.st.restarts);
      st.simplify_calls = max(st.simplify_calls, in.st.simplify_calls);
      st.reduce_calls = max(st.reduce_calls, in.st.reduce_calls);
      st.remove_calls = max(st.remove_calls, in.st.remove_calls);
      st.decisions = max(st.decisions, in.st.decisions);
      st.random_decisions = max(st.random_decisions, in.st.random_decisions);
      st.propagations = max(st.propagations, in.st.propagations);
      st.conflicts = max(st.conflicts, in.st.conflicts);
      st.th_props = max(st.th_props, in.st.th_props);
      st.th_prop_lemmas = max(st.th_prop_lemmas, in.st.th_prop_lemmas);
      st.th_conflicts = max(st.th_conflicts, in.st.th_conflicts);
      st.th_conflict_lemmas = max(st.th_conflict_lemmas, in.st.th_conflict_lemmas);
      st.prob_literals = max(st.prob_literals, in.st.prob_literals);
      st.learned_literals = max(st.learned_literals, in.st.learned_literals);
      st.prob_clauses_deleted = max(st.prob_clauses_deleted, in.st.prob_clauses_deleted);
      st.learned_clauses_deleted = max(st.learned_clauses_deleted, in.st.learned_clauses_deleted);
      st.bin_clauses_deleted = max(st.bin_clauses_deleted, in.st.bin_clauses_deleted);
      st.literals_before_simpl = max(st.literals_before_simpl, in.st.literals_before_simpl);
      st.subsumed_literals = max(st.subsumed_literals, in.st.subsumed_literals);
      st.boolean_variables = max(st.boolean_variables, in.st.boolean_variables);
      st.atoms = max(st.atoms, in.st.atoms);
      st.egraph_app_reductions = max(st.egraph_app_reductions, in.st.egraph_app_reductions);
      st.egraph_eq_props = max(st.egraph_eq_props, in.st.egraph_eq_props);
      st.egraph_th_props = max(st.egraph_th_props, in.st.egraph_th_props);
      st.egraph_th_conflicts = max(st.egraph_th_conflicts, in.st.egraph_th_conflicts);
      st.egraph_nd_lemmas = max(st.egraph_nd_lemmas, in.st.egraph_nd_lemmas);
      st.egraph_aux_eqs = max(st.egraph_aux_eqs, in.st.egraph_aux_eqs);
      st.egraph_boolack_lemmas = max(st.egraph_boolack_lemmas, in.st.egraph_boolack_lemmas);
      st.egraph_ack_lemmas = max(st.egraph_ack_lemmas, in.st.egraph_ack_lemmas);
      st.egraph_final_checks = max(st.egraph_final_checks, in.st.egraph_final_checks);
      st.egraph_interface_eqs = max(st.egraph_interface_eqs, in.st.egraph_interface_eqs);
      st.egraph_terms = max(st.egraph_terms, in.st.egraph_terms);
      st.num_init_vars = max(st.num_init_vars, in.st.num_init_vars);
      st.num_init_edges = max(st.num_init_edges, in.st.num_init_edges);
      st.num_update_axiom1 = max(st.num_update_axiom1, in.st.num_update_axiom1);
      st.num_update_axiom2 = max(st.num_update_axiom2, in.st.num_update_axiom2);
      st.num_extensionality_axiom = max(st.num_extensionality_axiom, in.st.num_extensionality_axiom);
      st.bv_variables = max(st.bv_variables, in.st.bv_variables);
      st.bv_atoms = max(st.bv_atoms, in.st.bv_atoms);
      st.bv_eq_atoms = max(st.bv_eq_atoms, in.st.bv_eq_atoms);
      st.bv_dyn_eq_atoms = max(st.bv_dyn_eq_atoms, in.st.bv_dyn_eq_atoms);
      st.bv_ge_atoms = max(st.bv_ge_atoms, in.st.bv_ge_atoms);
      st.bv_sge_atoms = max(st.bv_sge_atoms, in.st.bv_sge_atoms);
      st.bv_equiv_lemmas = max(st.bv_equiv_lemmas, in.st.bv_equiv_lemmas);
      st.bv_equiv_conflicts = max(st.bv_equiv_conflicts, in.st.bv_equiv_conflicts);
      st.bv_semi_equiv_lemmas = max(st.bv_semi_equiv_lemmas, in.st.bv_semi_equiv_lemmas);
      st.bv_interface_lemmas = max(st.bv_interface_lemmas, in.st.bv_interface_lemmas);
      st.boolean_propagation = max(st.boolean_propagation, in.st.boolean_propagation);
      st.theory_propagation = max(st.theory_propagation, in.st.theory_propagation);
      st.resolve_conflict = max(st.resolve_conflict, in.st.resolve_conflict);
      st.smt_restart = max(st.smt_restart, in.st.smt_restart);
      st.select_unassigned_literal = max(st.select_unassigned_literal, in.st.select_unassigned_literal);
      st.decide_literal = max(st.decide_literal, in.st.decide_literal);
      st.add_all_lemmas = max(st.add_all_lemmas, in.st.add_all_lemmas);
      st.delete_irrelevant_variables = max(st.delete_irrelevant_variables, in.st.delete_irrelevant_variables);
      st.simplify_clause_database = max(st.simplify_clause_database, in.st.simplify_clause_database);
      st.reduce_clause_database = max(st.reduce_clause_database, in.st.reduce_clause_database);
      st.base_bool_propagate = max(st.base_bool_propagate, in.st.base_bool_propagate);
      st.base_th_propagate = max(st.base_th_propagate, in.st.base_th_propagate);
      st.flatten_assertion = max(st.flatten_assertion, in.st.flatten_assertion);
      st.preprocess_assertion = max(st.preprocess_assertion, in.st.preprocess_assertion);
      st.assert_toplevel_formula = max(st.assert_toplevel_formula, in.st.assert_toplevel_formula);
      st.assert_toplevel_intern = max(st.assert_toplevel_intern, in.st.assert_toplevel_intern);
      st.nassert_rounds = max(st.nassert_rounds, in.st.nassert_rounds);
      st.nassert = max(st.nassert, in.st.nassert);
      st.nassert_atom = max(st.nassert_atom, in.st.nassert_atom);
      st.propagate = max(st.propagate, in.st.propagate);
      st.internal_propagation = max(st.internal_propagation, in.st.internal_propagation);
      st.reactivate_dynamic_terms = max(st.reactivate_dynamic_terms, in.st.reactivate_dynamic_terms);
      st.process_equality = max(st.process_equality, in.st.process_equality);
      st.inconsistent_edge = max(st.inconsistent_edge, in.st.inconsistent_edge);
      st.invert_branch = max(st.invert_branch, in.st.invert_branch);
      st.remove_parents = max(st.remove_parents, in.st.remove_parents);
      st.assign_new_label = max(st.assign_new_label, in.st.assign_new_label);
      st.collect_eqterms = max(st.collect_eqterms, in.st.collect_eqterms);
      st.reprocess_parents = max(st.reprocess_parents, in.st.reprocess_parents);
      st.check_false_eq = max(st.check_false_eq, in.st.check_false_eq);
      st.atom_propagation = max(st.atom_propagation, in.st.atom_propagation);
      st.propagate_boolean_equality = max(st.propagate_boolean_equality, in.st.propagate_boolean_equality);
      st.nprocess_eq = max(st.nprocess_eq, in.st.nprocess_eq);
      st.nprocess_eq_redundant = max(st.nprocess_eq_redundant, in.st.nprocess_eq_redundant);
    }

    void print_stat(ostream& out, string comment = "") {
      out << comment << endl;
      out << "\trestarts\t=\t" << st.restarts << endl;
      out << "\tsimplify_calls\t=\t" << st.simplify_calls << endl;
      out << "\treduce_calls\t=\t" << st.reduce_calls << endl;
      out << "\tremove_calls\t=\t" << st.remove_calls << endl;
      out << "\tdecisions\t=\t" << st.decisions << endl;
      out << "\trandom_decisions\t=\t" << st.random_decisions << endl;
      out << "\tpropagations\t=\t" << st.propagations << endl;
      out << "\tconflicts\t=\t" << st.conflicts << endl;
      out << "\tth_props\t=\t" << st.th_props << endl;
      out << "\tth_prop_lemmas\t=\t" << st.th_prop_lemmas << endl;
      out << "\tth_conflicts\t=\t" << st.th_conflicts << endl;
      out << "\tth_conflict_lemmas\t=\t" << st.th_conflict_lemmas << endl;
      out << "\tprob_literals\t=\t" << st.prob_literals << endl;
      out << "\tlearned_literals\t=\t" << st.learned_literals << endl;
      out << "\tprob_clauses_deleted\t=\t" << st.prob_clauses_deleted << endl;
      out << "\tlearned_clauses_deleted\t=\t" << st.learned_clauses_deleted << endl;
      out << "\tbin_clauses_deleted\t=\t" << st.bin_clauses_deleted << endl;
      out << "\tliterals_before_simpl\t=\t" << st.literals_before_simpl << endl;
      out << "\tsubsumed_literals\t=\t" << st.subsumed_literals << endl;
      out << "\tboolean_variables\t=\t" << st.boolean_variables << endl;
      out << "\tatoms\t=\t" << st.atoms << endl;
      out << "\tegraph_app_reductions\t=\t" << st.egraph_app_reductions << endl;
      out << "\tegraph_eq_props\t=\t" << st.egraph_eq_props << endl;
      out << "\tegraph_th_props\t=\t" << st.egraph_th_props << endl;
      out << "\tegraph_th_conflicts\t=\t" << st.egraph_th_conflicts << endl;
      out << "\tegraph_nd_lemmas\t=\t" << st.egraph_nd_lemmas << endl;
      out << "\tegraph_aux_eqs\t=\t" << st.egraph_aux_eqs << endl;
      out << "\tegraph_boolack_lemmas\t=\t" << st.egraph_boolack_lemmas << endl;
      out << "\tegraph_ack_lemmas\t=\t" << st.egraph_ack_lemmas << endl;
      out << "\tegraph_final_checks\t=\t" << st.egraph_final_checks << endl;
      out << "\tegraph_interface_eqs\t=\t" << st.egraph_interface_eqs << endl;
      out << "\tegraph_terms\t=\t" << st.egraph_terms << endl;
      out << "\tnum_init_vars\t=\t" << st.num_init_vars << endl;
      out << "\tnum_init_edges\t=\t" << st.num_init_edges << endl;
      out << "\tnum_update_axiom1\t=\t" << st.num_update_axiom1 << endl;
      out << "\tnum_update_axiom2\t=\t" << st.num_update_axiom2 << endl;
      out << "\tnum_extensionality_axiom\t=\t" << st.num_extensionality_axiom << endl;
      out << "\tbv_variables\t=\t" << st.bv_variables << endl;
      out << "\tbv_atoms\t=\t" << st.bv_atoms << endl;
      out << "\tbv_eq_atoms\t=\t" << st.bv_eq_atoms << endl;
      out << "\tbv_dyn_eq_atoms\t=\t" << st.bv_dyn_eq_atoms << endl;
      out << "\tbv_ge_atoms\t=\t" << st.bv_ge_atoms << endl;
      out << "\tbv_sge_atoms\t=\t" << st.bv_sge_atoms << endl;
      out << "\tbv_equiv_lemmas\t=\t" << st.bv_equiv_lemmas << endl;
      out << "\tbv_equiv_conflicts\t=\t" << st.bv_equiv_conflicts << endl;
      out << "\tbv_semi_equiv_lemmas\t=\t" << st.bv_semi_equiv_lemmas << endl;
      out << "\tbv_interface_lemmas\t=\t" << st.bv_interface_lemmas << endl;
      out << "\tboolean_propagation\t=\t" << st.boolean_propagation << endl;
      out << "\ttheory_propagation\t=\t" << st.theory_propagation << endl;
      out << "\tresolve_conflict\t=\t" << st.resolve_conflict << endl;
      out << "\tsmt_restart\t=\t" << st.smt_restart << endl;
      out << "\tselect_unassigned_literal\t=\t" << st.select_unassigned_literal << endl;
      out << "\tdecide_literal\t=\t" << st.decide_literal << endl;
      out << "\tadd_all_lemmas\t=\t" << st.add_all_lemmas << endl;
      out << "\tdelete_irrelevant_variables\t=\t" << st.delete_irrelevant_variables << endl;
      out << "\tsimplify_clause_database\t=\t" << st.simplify_clause_database << endl;
      out << "\treduce_clause_database\t=\t" << st.reduce_clause_database << endl;
      out << "\tbase_bool_propagate\t=\t" << st.base_bool_propagate << endl;
      out << "\tbase_th_propagate\t=\t" << st.base_th_propagate << endl;
      out << "\tflatten_assertion\t=\t" << st.flatten_assertion << endl;
      out << "\tpreprocess_assertion\t=\t" << st.preprocess_assertion << endl;
      out << "\tassert_toplevel_formula\t=\t" << st.assert_toplevel_formula << endl;
      out << "\tassert_toplevel_intern\t=\t" << st.assert_toplevel_intern << endl;
      out << "\tnassert_rounds\t=\t" << st.nassert_rounds << endl;
      out << "\tnassert\t=\t" << st.nassert << endl;
      out << "\tnassert_atom\t=\t" << st.nassert_atom << endl;
      out << "\tpropagate\t=\t" << st.propagate << endl;
      out << "\tinternal_propagation\t=\t" << st.internal_propagation << endl;
      out << "\treactivate_dynamic_terms\t=\t" << st.reactivate_dynamic_terms << endl;
      out << "\tprocess_equality\t=\t" << st.process_equality << endl;
      out << "\tinconsistent_edge\t=\t" << st.inconsistent_edge << endl;
      out << "\tinvert_branch\t=\t" << st.invert_branch << endl;
      out << "\tremove_parents\t=\t" << st.remove_parents << endl;
      out << "\tassign_new_label\t=\t" << st.assign_new_label << endl;
      out << "\tcollect_eqterms\t=\t" << st.collect_eqterms << endl;
      out << "\treprocess_parents\t=\t" << st.reprocess_parents << endl;
      out << "\tcheck_false_eq\t=\t" << st.check_false_eq << endl;
      out << "\tatom_propagation\t=\t" << st.atom_propagation << endl;
      out << "\tpropagate_boolean_equality\t=\t" << st.propagate_boolean_equality << endl;
      out << "\tnprocess_eq\t=\t" << st.nprocess_eq << endl;
      out << "\tnprocess_eq_redundant\t=\t" << st.nprocess_eq_redundant << endl;    }

		y2_stat() {
			clear();
		}
	};
#endif

#endif

#ifdef _M5
	typedef msat_config      m5_config;
	typedef msat_env         m5_context;
	typedef msat_model       m5_model;
	typedef msat_type        m5_type;
	typedef msat_term        m5_expr;
	typedef msat_decl        m5_ftype;
	typedef msat_result    	 m5_result;
	typedef msat_truth_value m5_bool_value;
	typedef msat_symbol_tag	 m5_symbol;

	typedef msat_config*     m5_config_ptr;
	typedef msat_env*        m5_context_ptr;
	typedef msat_model*      m5_model_ptr;
	typedef m5_type			     m5_type_ptr;
	typedef m5_expr			     m5_expr_ptr;
	typedef m5_ftype		     m5_ftype_ptr;

	typedef std::vector<m5_expr_ptr>	m5_expr_vec;
	typedef std::list<m5_expr_ptr>		m5_expr_list;

#endif

#ifdef _BT
	typedef Btor*        		 bt_context;
	typedef BoolectorSort    bt_type;
	typedef BoolectorNode*   bt_expr;
	typedef bt_expr          bt_ftype;
	typedef int32_t				   bt_result;

	typedef Btor*            bt_context_ptr;
	typedef BoolectorSort    bt_type_ptr;
	typedef BoolectorNode*   bt_expr_ptr;
	typedef bt_expr_ptr	     bt_ftype_ptr;

	typedef std::list<bt_expr_ptr>		bt_expr_list;
//	typedef bt_expr_list	bt_expr_vec;
	typedef std::vector<bt_expr_ptr>	bt_expr_vec;

	#define BT_INVALID_EXPR NULL
#endif



#define	AVR_BASIS_IDX 0
#define	AVR_CTI_IDX 1
#define	AVR_EXTRA_IDX 2
#define	AVR_BV_IDX 3
#define	AVR_FRAME_BASE_IDX 4

#define REFRESH_CONTEXT													// Reset solver context after a threshold (after forward propagation)
#ifdef REFRESH_CONTEXT
	#define REFRESH_CONTEXT_THRESHOLD	100					// Maximum fallbacks to oneshot before resetting context (after forward propagation)
#endif


#endif /* SRC_REACH_AVR_BACKEND_H_ */
