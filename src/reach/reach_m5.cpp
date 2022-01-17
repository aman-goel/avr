/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


/*
 * reach_m5.cpp
 *
 *  Created on: Feb 11, 2019
 *      Author: rock
 */


#include "reach_m5.h"
#include "reach_m5_utils.h"

#ifdef _M5

#include <cstdlib>
#include <fstream>
#include <cmath>
#include <csignal>
#include <pthread.h>
#include <functional>

using namespace std;

namespace _m5 {

m5_IntBvM m5_API::m_sz_to_bv;
m5_IntUtM m5_API::m_sz_to_ut;
m5_StringToFunctM m5_API::m_funct;

m5_StringToDecl m5_API::m_var_decs;
m5_InstToFuncDecl m5_API::m_func_decs;
m5_MpzToNum m5_API::m_num_to_const;

#ifdef ASSERT_DISTINCT_NUMBERS
	pair < int, m5_expr_vec > m5_API::m_distinct_constraints = make_pair(-1, m5_expr_vec());
#endif

m5_expr_ptr m5_API::m_v0;
m5_expr_ptr m5_API::m_v1;

m5_expr_ptr m5_API::m_b0;
m5_expr_ptr m5_API::m_b1;

m5_config 	m5_API::g_config;
m5_context	m5_API::g_ctx;

m5_type_ptr m5_API::g_ufboolt;
m5_expr_ptr m5_API::g_uftrue;
m5_expr_ptr m5_API::g_uffalse;
bool m5_API::g_setufbool = false;

#define OPT_(cfg, n,v) if (msat_set_option(cfg, n, v) != 0) {                     \
	                  cout << "error setting option: " << n << " -> " << v << endl; \
	                  assert(0);                                                    \
                  }


string print_type(m5_type_ptr y) {
//	return "";
	char* tmp = msat_type_repr(y);
	string str(tmp);
	msat_free(tmp);
	return str;
}

string print_term(m5_expr y) {
//	return "";
	char* tmp = msat_term_repr(y);
	string str(tmp);
	msat_free(tmp);
	return str;
}

string print_ftype(m5_ftype_ptr y) {
//	return "";
	char* tmp = msat_decl_repr(y);
	string str(tmp);
	msat_free(tmp);
	return str;
}

string print_terms(m5_expr_vec& yV) {
	ostringstream ostr;
	for (auto& y: yV)
		ostr << "\t" << print_term(y) << endl;
	return ostr.str();
}

string print_terms(list<m5_expr_ptr>& yV) {
	string s = "";
	for (auto& y: yV)
		s = s + print_term(y) + " ";
	return s;
}

static void print_model(msat_env env)
{
    /* we use a model iterator to retrieve the model values for all the
     * variables, and the necessary function instantiations */
    msat_model_iterator iter = msat_create_model_iterator(env);
		cout << &env << "\t" << msat_last_error_message(env) << endl;
    if (MSAT_ERROR_MODEL_ITERATOR(iter)) {
			cout << "assertions" << endl;
			size_t numassert = 0;
			m5_expr* f = msat_get_asserted_formulas(env, &numassert);
			for (int i = 0; i < numassert; i++) {
				cout << print_term(f[i]) << endl;
			}
			msat_free(f);
    }
    assert(!MSAT_ERROR_MODEL_ITERATOR(iter));

//		cout << "assertions" << endl;
//		size_t numassert = 0;
//		m5_expr* f = msat_get_asserted_formulas(env, &numassert);
//		for (int i = 0; i < numassert; i++) {
//			cout << print_term(f[i]) << "\t" << print_term(msat_get_model_value(env, f[i])) << endl;
//		}
//		msat_free(f);
    printf("Model:\n");
    while (msat_model_iterator_has_next(iter)) {
        msat_term t, v;
        char *s;
        msat_model_iterator_next(iter, &t, &v);
        s = msat_term_repr(t);
        assert(s);
        printf(" %s = ", s);
        msat_free(s);
        s = msat_term_repr(v);
        assert(s);
        printf("%s\n", s);
        msat_free(s);
    }
    msat_destroy_model_iterator(iter);
}

void m5_API::debug() {
	cout << "backtrack point: " << msat_num_backtrack_points(m_ctx) << endl;
	cout << "stats: " << msat_get_search_stats(m_ctx) << endl;
	size_t numassert = 0;
	m5_expr* f = msat_get_asserted_formulas(m_ctx, &numassert);
	cout << "assertions #" << numassert << endl;
	for (int i = 0; i < numassert; i++) {
		cout << print_term(f[i]) << endl;
	}
	msat_free(f);
}

SolverType m5_API::fetch_solv_name(void) {
	return SMT_MathSAT5;
}

void m5_API::m5_interrupt(int signum) {
	s_check_timed_out = true;
}

void m5_API::m5_exit() {
	if (!MSAT_ERROR_ENV(g_ctx))
		msat_destroy_env(g_ctx);
	if (!MSAT_ERROR_CONFIG(g_config))
		msat_destroy_config(g_config);
}

void m5_API::m5_init() {
  char *s = msat_get_version();
  AVR_LOG(11, 1, "Using " << s << endl);
  msat_free(s);

	M5_INFO::inc_m5_key();
	g_config = msat_create_config();

//  std::string name = QUERY_PATH;
//  name += "trace/" + _benchmark + "_g.smt2";
//  msat_set_option(g_config, "debug.api_call_trace", "1");
//  msat_set_option(g_config, "debug.api_call_trace_filename", name.c_str());
//	msat_set_option(g_config, "debug.api_call_trace_dump_config", "false");

#ifdef M5_INTERPOLATION
	bool interpolation = true;
#else
	bool interpolation = false;
#endif
	ModelGeneration model = FULL_MODEL;

	// these are usually reasonable settings for the IC3 use case

	// no random decisions in the SAT solver
	OPT_(g_config, "dpll.branching_random_frequency", "0");

	// try not assigning values to theory atoms that occur only in
	// already-satisfied clauses. Example: given a clause (P | (t >= 0)), if P
	// is true, the value of (t >= 0) doesn't matter, and so it is a "ghost"
	OPT_(g_config, "dpll.ghost_filtering", "true");

	// Handling disequalities might be potentially quite expensive (especially
	// over the integers, where splitting of !(t = 0) into ((t < 0) | (t > 0))
	// is needed), so we want to avoid this as much as possible. If (t = 0)
	// occurs only positively in the input formula, but the SAT solver assigns
	// it to false, we can avoid sending the literal !(t = 0) to the
	// arithmetic solver, since if !(t = 0) causes an arithmetic conflict, we
	// can always flip it (as the atom never occurs negated in the input
	// formula, so assigning it to true can't cause any Boolean conflict)
	OPT_(g_config, "theory.la.pure_equality_filtering", "true");

	// Turn off propagation of toplevel information. This is just overhead in
	// an IC3 context (where the solver is called hundreds of thousands of
	// times). Moreover, using it makes "lightweight" model generation (see
	// below) not effective
	OPT_(g_config, "preprocessor.toplevel_propagation", "false");

	// Avoid splitting negated equalities !(t = 0) if t is of rational
	// type. Over the rationals, it is often cheaper to handle negated
	// equalities in a special way rather than relying on the general
	// splitting described above
	OPT_(g_config, "theory.la.split_rat_eq", "false");

	// Do not reset the internal scores for variables in the SAT solver
	// whenever a pop_backtrack_point() command is issued. In an IC3 context,
	// the solver is called very often on very similar problems, so it makes
	// sense to keep the variable scores computed so far, and maybe perform a
	// full solver reset only every few thousand calls rather than
	// reinitializing the scores at every pop()
	OPT_(g_config, "dpll.pop_btpoint_reset_var_order", "false");

	// enable interpolation if required
	OPT_(g_config, "interpolation", (interpolation ? "true" : "false"));
	OPT_(g_config, "preprocessor.interpolation_ite_elimination", "true");

	OPT_(g_config, "theory.bv.bit_blast_mode", "1");
	if (interpolation) {
			// interpolation for BV requires the lazy solver
			OPT_(g_config, "theory.bv.bit_blast_mode", "0");
			OPT_(g_config, "theory.bv.eager", "false");
	}

	OPT_(g_config, "model_generation", "false");
	OPT_(g_config, "bool_model_generation", "false");
	switch (model) {
	case NO_MODEL:
			break;
	case BOOL_MODEL:
			// light-weight model generation, giving values only to atoms known to
			// the SAT solver
			OPT_(g_config, "bool_model_generation", "true");
			break;
	case FULL_MODEL:
			// full model generation, giving values to arbitrary terms
			OPT_(g_config, "model_generation", "true");
			break;
	}

	g_ctx = msat_create_env(g_config);

	m_v0 = msat_make_bv_int_number(g_ctx, 0, 1);
	m_v1 = msat_make_bv_int_number(g_ctx, 1, 1);
	m_b0 = msat_make_false(g_ctx);
	m_b1 = msat_make_true(g_ctx);
#ifdef ASSERT_DISTINCT_NUMBERS
	m_distinct_constraints = make_pair(-1, m5_expr_vec());
#endif
	g_setufbool = false;
}

void m5_API::m5_set_bool_uf() {
	if (!g_setufbool) {
		g_setufbool = true;
		g_ufboolt = msat_get_simple_type(g_ctx, "utt$bool");
		g_uftrue = msat_make_constant(g_ctx, msat_declare_function(g_ctx, "uftrue", g_ufboolt));
		g_uffalse = msat_make_constant(g_ctx, msat_declare_function(g_ctx, "uffalse", g_ufboolt));
		AVR_LOG(11, 3, "creating ufbool: " << print_term(g_uftrue) << " and " << print_term(g_uffalse) << " of type " << print_type(g_ufboolt) << endl);
	}
	assert(!MSAT_ERROR_TYPE(g_ufboolt));
	assert(!MSAT_ERROR_TERM(g_uftrue));
	assert(!MSAT_ERROR_TERM(g_uffalse));
}

void m5_API::m5_exit_ctx() {
	if (m_model != NULL) {
		assert(!MSAT_ERROR_MODEL(*m_model));
		msat_destroy_model(*m_model);
	}
	if (!MSAT_ERROR_ENV(m_ctx))
		msat_destroy_env(m_ctx);
	if (!MSAT_ERROR_CONFIG(m_config))
		msat_destroy_config(m_config);
}

void m5_API::m5_init_ctx() {
	string lname = get_logic_name();
	if (lname == "")
		m_config = msat_create_config();
	else
		m_config = msat_create_default_config(lname.c_str());

	if (m_abstract && (queryType == cti) && (Solver::num_ab_query < 5)) {
		std::string name = QUERY_PATH;
		name += "test/" + _benchmark + ".smt2";
		msat_set_option(m_config, "debug.api_call_trace", "1");
		msat_set_option(m_config, "debug.api_call_trace_filename", name.c_str());
		msat_set_option(m_config, "debug.api_call_trace_dump_config", "false");
	}
//	if (m_solver_id == 543) {
////  std::string name = "local_" + to_string(m_solver_id) + ".smt2";
//	if (queryType == prt) {
//		string name = Inst::config->get_working_dir() + "/output.smt2";
//		std::string name = Inst::config->get_working_dir() + "/output_" + to_string(m_solver_id) + ".smt2";
//		msat_set_option(m_config, "debug.api_call_trace", "1");
//		msat_set_option(m_config, "debug.api_call_trace_filename", name.c_str());
//		msat_set_option(m_config, "debug.api_call_trace_dump_config", "false");
//	}
//  cout << "printing trace for solver id: " << m_solver_id << endl;
//	}
#ifdef M5_INTERPOLATION
	bool interpolation = true;
#else
	bool interpolation = false;
#endif
	ModelGeneration model = need_model ? FULL_MODEL : NO_MODEL;

	// these are usually reasonable settings for the IC3 use case

	// no random decisions in the SAT solver
	OPT_(m_config, "dpll.branching_random_frequency", "0");

	// try not assigning values to theory atoms that occur only in
	// already-satisfied clauses. Example: given a clause (P | (t >= 0)), if P
	// is true, the value of (t >= 0) doesn't matter, and so it is a "ghost"
	OPT_(m_config, "dpll.ghost_filtering", "true");

	// Handling disequalities might be potentially quite expensive (especially
	// over the integers, where splitting of !(t = 0) into ((t < 0) | (t > 0))
	// is needed), so we want to avoid this as much as possible. If (t = 0)
	// occurs only positively in the input formula, but the SAT solver assigns
	// it to false, we can avoid sending the literal !(t = 0) to the
	// arithmetic solver, since if !(t = 0) causes an arithmetic conflict, we
	// can always flip it (as the atom never occurs negated in the input
	// formula, so assigning it to true can't cause any Boolean conflict)
	OPT_(m_config, "theory.la.pure_equality_filtering", "true");

	// Turn off propagation of toplevel information. This is just overhead in
	// an IC3 context (where the solver is called hundreds of thousands of
	// times). Moreover, using it makes "lightweight" model generation (see
	// below) not effective
	OPT_(m_config, "preprocessor.toplevel_propagation", "false");

	// Avoid splitting negated equalities !(t = 0) if t is of rational
	// type. Over the rationals, it is often cheaper to handle negated
	// equalities in a special way rather than relying on the general
	// splitting described above
	OPT_(m_config, "theory.la.split_rat_eq", "false");

	// Do not reset the internal scores for variables in the SAT solver
	// whenever a pop_backtrack_point() command is issued. In an IC3 context,
	// the solver is called very often on very similar problems, so it makes
	// sense to keep the variable scores computed so far, and maybe perform a
	// full solver reset only every few thousand calls rather than
	// reinitializing the scores at every pop()
	OPT_(m_config, "dpll.pop_btpoint_reset_var_order", "false");

	// enable interpolation if required
	OPT_(m_config, "interpolation", (interpolation ? "true" : "false"));
	OPT_(m_config, "preprocessor.interpolation_ite_elimination", "true");

	OPT_(m_config, "theory.bv.bit_blast_mode", "1");
	if (interpolation) {
			// interpolation for BV requires the lazy solver
			OPT_(m_config, "theory.bv.bit_blast_mode", "0");
			OPT_(m_config, "theory.bv.eager", "false");
	}

	OPT_(m_config, "model_generation", "false");
	OPT_(m_config, "bool_model_generation", "false");
	switch (model) {
	case NO_MODEL:
			break;
	case BOOL_MODEL:
			// light-weight model generation, giving values only to atoms known to
			// the SAT solver
			OPT_(m_config, "bool_model_generation", "true");
			break;
	case FULL_MODEL:
			// full model generation, giving values to arbitrary terms
			OPT_(m_config, "model_generation", "true");
			break;
	}

	assert(!MSAT_ERROR_ENV(g_ctx));
	m_ctx = msat_create_shared_env(m_config, g_ctx);
	m_model = NULL;

#ifdef M5_INTERPOLATION
	int g = msat_create_itp_group(m_ctx);
	if (g == -1) {
		m5_loge("itp error: " << msat_last_error_message(m_ctx) << endl);
	}
	assert(g != -1);
	int res = msat_set_itp_group(m_ctx, g);
	assert(res == 0);
#endif
}

m5_API::m5_API(TheoryMapper* m, unsigned ba_idx, bool is_inc, int type) :
			Solver(m, ba_idx, type) {
	assert(m);

	AVR_LOG(11, 1, "Creating new M5 instance for BA[" << m_ba_idx << "] with solver_id [" << m_solver_id << "]" << endl);

	m5_init_ctx();

	m_constraints.clear();
	m_assumptions.clear();
	m5_expr_vec tmp;
	m_cList.push_back(make_pair(m_cList.size() + 1, tmp));
#ifdef ASSERT_DISTINCT_NUMBERS
	if (m_abstract) {
		assert_distinct_constants();
	}
#endif
}

m5_API::~m5_API() {
	AVR_LOG(11, 1, "Deleting M5 instance for BA[" << m_ba_idx << "] with solver_id [" << m_solver_id << "]" << endl);

	m_constraints.clear();
	m_cList.clear();
	m5_exit_ctx();
}

bool m5_API::check_sat(Inst* e, long timeout_value, bool getModel) {
	AVR_LOG(11, 1, "[SID:" << m_solver_id << ", SBA:" << m_ba_idx << "]----------" << endl);
	init_inst2yices();
	inst2yices(e);
	force(e);
	add_assert(e);
	s_assert_constraints();
	AVR_LOG(11, 3, "calling MSAT" << endl);
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

int m5_API::forward_propagation(long timeout_value, int frame_idx, InstL& forwarded,
			vector<vector<CLAUSE>>& cubes, void *inst) {
	int next_frame_idx = frame_idx + 1;
	num_scalls_sat_fp_non_accum = 0;
	num_scalls_unsat_fp_non_accum = 0;
	num_scalls_contained_fp_non_accum = 0;
	long timeout_value_original = timeout_value;

	vector<CLAUSE>::iterator it_c = cubes[frame_idx].begin();
	while (it_c != cubes[frame_idx].end()) {
		Inst* cube = (*it_c).cube;
		Inst *ve_next_c = Inst::all_pre2next(cube);
		InstL conjunct_query;
		InstS relevantNext;
		Inst::collect_next_reg(ve_next_c, relevantNext, true);
		for (auto& sigNext : relevantNext) {
			conjunct_query.push_back(Inst::fetch_trelation(sigNext));
		}
		int res = AVR_QTO;
		res = s_check(AB_QUERY_TIMEOUT, false);
		if (res != AVR_QUSAT) {
		m_constraints.clear();
		s_push();
		init_inst2yices();
		for (auto& c: conjunct_query) {
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
		}
		if (res == AVR_QSAT) {
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
			assert(res == AVR_QUSAT);

		CLAUSE& blockC = (*it_c);
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

int m5_API::get_muses(long timeout_value, InstL& vel_1, InstL& vel_2, InstLL& muses, int& numSat, int& numUnsat, Solver* core_solver) {
	AVR_LOG(17, 4, "Entering MUSes extraction " << endl);
	AVR_LOG(17, 4, "(initial assertions)" << vel_1 << endl);
	init_inst2yices();
	m_constraints.clear();
	if (!vel_1.empty()) {
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

int m5_API::get_muses_2(long timeout_value, InstL& vel, InstLL& muses, int& numSat, int& numUnsat, Solver* core_solver) {
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
	if (status == AVR_QSAT) {
		return 0;
	}
	else if (status == AVR_QTO) {
		cout << "\t\t(core extraction T.O.)" << endl;
	}

	vel.sort(Inst::CompareInstByChildInfoTier);
	minimize_core(timeout_value, core, muses, numSat, numUnsat);
	if (muses.empty() && status == AVR_QUSAT) {
		core_solver->s_assert(core);
		cout << "core solver says " << core_solver->s_check(0, false) << " for core " << core << endl;
    s_assert(core);
    cout << "min solver says " << s_check(0, false) << " for core " << core << endl;
		print_query(0, ERROR, "error");
		assert(0);
	}
#endif

	if (!muses.empty()) {
		AVR_LOG(17, 4, "\t(#muses: " << muses.size() << ", exit)" << endl);
		if (m_model != NULL) {
			assert(!MSAT_ERROR_MODEL(*m_model));
			msat_destroy_model(*m_model);
			m_model = NULL;
		}
		return 1;
	}
	else {
		AVR_LOG(17, 4, "\t(no mus, exit)" << endl);
		return 0;
	}
}

int m5_API::get_unsat_core(long timeout_value, InstL& vel, InstL& core, int& numSat, int& numUnsat) {
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
  int res = -1;
  unsigned sz = vel.size();

  AVR_LOG(17, 5, "\tEntering unsat core extraction from M5" << endl);
  AVR_LOG(17, 5, "\t[Input]: " << vel << " (sz: " << sz << ")" << endl);
  assert(!vel.empty());

  m_constraints.clear();
  m_assumptions.clear();
  map< m5_expr, Inst* >& y_to_inst = m_y_to_inst;
  m_y_to_inst.clear();
  m_unsatCore.clear();

  int count = 0;
  m5_expr_vec constraints;
  m5_expr_list constraints2;
  InstL induct_clause;
  for (InstL::iterator it = vel.begin(); it != vel.end(); it++) {
    init_inst2yices();
    inst2yices(*it);
    force(*it);
    add_assume(*it);
    string iName = "_p_$" + get_m5_temp_name(*it, count);
    m5_expr_ptr indVar = create_bool_var(iName);
    AVR_LOG(17, 5, "\t\t\t(inst: " << *(*it) << ", indicator: " << print_term(indVar) << ")" << endl);
    assert (!m_constraints.empty());
		AVR_LOG(17, 7, "\t\t\t\t(assertions " << print_term(indVar) << " => " << print_terms(m_constraints) << endl);
		for (auto& c: m_constraints)
			constraints.push_back(m5_make_implies(m_ctx, indVar, c));
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
      m5_expr_ptr c2 = force_wo_add(ve2);
      induct_clause.push_back(OpInst::create(OpInst::LogNot, ve2));
      string iName = "_pi_$" + get_m5_temp_name(*it, count);
      m5_expr_ptr indVar2 = create_bool_var(iName);
      AVR_LOG(17, 5, "\t\t\t(induct inst: " << *ve2 << ", indicator: " << print_term(indVar2) << ")" << endl);
      if (!m_constraints.empty()) {
				AVR_LOG(17, 7, "\t\t\t\t(induct assertions " << print_term(indVar2) << " => " << print_terms(m_constraints) << endl);
				for (auto& c: m_constraints)
					constraints.push_back(m5_make_implies(m_ctx, indVar, c));
				m_constraints.clear();
      }
			constraints.push_back(msat_make_eq(m_ctx, indVar2, c2));
      indVar2 = msat_make_not(m_ctx, indVar2);
			constraints2.push_back(indVar2);
    }
    count++;
  }
  if (uType != no_induct) {
  	assert(!constraints2.empty());
//		AVR_LOG(17, 7, "\t\t\t(induct assertions " << print_terms(constraints2) << endl);

  	Inst* clause = OpInst::create(OpInst::LogOr, induct_clause);
//  	add_assume(clause);
		string iName = "_pi_$" + get_m5_temp_name(clause, count);
    m5_expr_ptr a = create_bool_var(iName);
    AVR_LOG(17, 5, "\t\t\t(induct indicator: " << print_term(a) << ")" << endl);
    constraints2.push_back(msat_make_not(m_ctx, a));
  	m5_expr_ptr cInd = m5_make_or(m_ctx, constraints2);
  	constraints.push_back(cInd);
    m_assumptions.push_back(a);
    y_to_inst[a] = NULL;
  }
  m_constraints.swap(constraints);
  assert (!m_constraints.empty());
	AVR_LOG(17, 7, "\t\t\t\t(assertions " << print_terms(m_constraints) << endl);
	s_push();
	s_assert_constraints();

//  m5_result initial_res = s_check_inc(timeout_value, false);
//  AVR_LOG(17, 5, "\t\t(initial-check) " << initial_res << endl);

  TIME_S(start_time);
  m5_result query_res = s_check_mus(timeout_value, m_assumptions, m_unsatCore, false);
  TIME_E(start_time, end_time, time_res);
  AVR_LOG(17, 4, "\t\t(query-check) " << query_res << endl);

  if (query_res == MSAT_UNSAT) {
    numUnsat++;
    time_unsat_core_muses_reach += time_diff;
    if (time_diff > time_max_unsat_core_muses_reach)
      time_max_unsat_core_muses_reach = time_diff;

    AVR_LOG(17, 4, "unsat core: (sz: " << m_unsatCore.size() << endl);
    for (int i = 0; i < m_unsatCore.size(); i++) {
      m5_expr_ptr curr = m_unsatCore[i];
      assert(!MSAT_ERROR_TERM(curr));
      AVR_LOG(17, 5, "\t" << i << ": " << print_term(curr) << endl);
      Inst *tve = y_to_inst[curr];
      if (tve != NULL) {
				core.push_back(tve);
				AVR_LOG(17, 4, "adding to mus: " << *tve << endl);
      }
    }
    if (core.empty()) {
      cout << "warning: mus.empty()" << endl;
      core.push_back(vel.front());
//      assert(0);
    }
    AVR_LOG(15, 0, "\t\t(" << (m_abstract?"ab":"cc") << " core: " << m_assumptions.size() << " -> " << core.size() << ")" << endl);
    res = AVR_QUSAT;
  }
  else {
    assert(query_res == MSAT_SAT);
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

int m5_API::find_unsat_core(long timeout_value, InstL& hardQ, InstL& vel, InstL& mus, int& numSat, int& numUnsat) {
  m_constraints.clear();
  init_inst2yices();
  if (!hardQ.empty())
    s_assert(OpInst::create(OpInst::LogAnd, hardQ));
  int result = get_unsat_core(timeout_value, vel, mus, numSat, numUnsat);
  return result;
}

int m5_API::get_mus(long timeout_value, InstL& vel, InstL& mus, int& numSat, int& numUnsat, bool recordTime) {
	int qType_orig = queryType;
	queryType = mus_min;
  struct rusage usage;
  struct timeval start_time, end_time;
  long long time_diff;
  long long time_res = 0;
	unsigned sz = vel.size();
	int res = -1;

	AVR_LOG(17, 2, "\tEntering MUS core extraction from M5" << endl);
	AVR_LOG(17, 5, "\t[Input]: " << vel << " (sz: " << sz << ")" << endl);
	assert(!vel.empty());

	m_constraints.clear();
	m5_InstToExprM& inst_to_y = m_inst_to_y;
	inst_to_y.clear();

	InstL stack;
	int initialPush = false;
	int count = 0;
	InstL queue;
  m5_expr_vec constraints;
	for (InstL::iterator it = vel.begin(); it != vel.end(); it++) {
		init_inst2yices();
		inst2yices(*it);
		force(*it);
		string iName = "_q_$" + get_m5_temp_name(*it, count);
    m5_expr_ptr indVar = create_bool_var(iName);
		AVR_LOG(17, 5, "\t\t\t(inst: " << *(*it) << ", indicator: " << print_term(indVar) << ")" << endl);
		if (!m_constraints.empty()) {
			AVR_LOG(17, 7, "\t\t\t\t(assertions " << print_term(indVar) << " => " << print_terms(m_constraints) << endl);
      for (auto& c: m_constraints)
        constraints.push_back(m5_make_implies(m_ctx, indVar, c));
      m_constraints.clear();
		}
		queue.push_back(*it);
		inst_to_y[*it] = make_pair(indVar, indVar);
    count++;
	}
  m_constraints.swap(constraints);
	assert (!m_constraints.empty());

	s_push();
	initialPush = true;
	s_assert_constraints();

	for (InstL::iterator sit = queue.begin(); sit != queue.end(); sit++) {
		s_push();
		m5_expr_ptr indVar = inst_to_y[*sit].first;
		s_assert_constraint(indVar);
		stack.push_front(*sit);
		add_assert(*sit);
	}

  TIME_S(start_time);
	m5_result initial_res = s_check_inc(timeout_value, false);
  TIME_E(start_time, end_time, time_res);
//  clear_assume();
  AVR_LOG(17, 5, "\t\t(initial-check) " << initial_res << endl);

	InstL satBucket;
	if (initial_res == MSAT_UNSAT) {
		numUnsat++;
		if (recordTime) {
	    time_unsat_min_muses_reach += time_diff;
	    if (time_diff > time_max_unsat_min_muses_reach)
	      time_max_unsat_min_muses_reach = time_diff;
		}
		m_constraints.clear();
		while(!stack.empty()) {
			s_pop();
			Inst* currInst = stack.front();
			stack.pop_front();
			AVR_LOG(17, 5, "curr: " << *currInst << endl);
			bool pushed = !mus.empty();
			if (pushed) {
				s_push();
				for (auto& v: mus) {
					pair < m5_expr, m5_expr > p = inst_to_y[v];
					m_constraints.push_back(p.first);
					add_assert(v);
				}
				s_assert_constraints();
			}

		  TIME_S(start_time);
		  m5_result result = s_check_inc(timeout_value, false);
		  TIME_E(start_time, end_time, time_res);
			AVR_LOG(17, 5, "status_check: " << result << endl);

			if (result == MSAT_UNSAT) {
				numUnsat++;
		    if (recordTime) {
		      time_unsat_min_muses_reach += time_diff;
		      if (time_diff > time_max_unsat_min_muses_reach)
		        time_max_unsat_min_muses_reach = time_diff;
		    }
			}
			else {
				if (result != MSAT_SAT) {
					assert(result == MSAT_UNKNOWN);
					cout << "Timeout while deriving MUS_a" << endl;
					cout << "Core: " << vel << endl;
					assert(0);
				}
				else
					numSat++;

		    if (recordTime) {
	        time_sat_min_muses_reach += time_diff;
	        if (time_diff > time_max_sat_min_muses_reach)
	          time_max_sat_min_muses_reach = time_diff;
		    }
				mus.push_back(currInst);
				AVR_LOG(17, 5, "adding to mus: " << *currInst << endl);
			}
			if (pushed)
				s_pop();
		}
		m_constraints.clear();
		if (mus.empty()) {
			cout << "warning: mus.empty()" << endl;
      mus.push_back(vel.front());
//      assert(0);
		}
		res = 1;
	}
	else {
		numSat++;
		assert(initial_res == MSAT_SAT);
    if (recordTime) {
      time_sat_min_muses_reach += time_diff;
      if (time_diff > time_max_sat_min_muses_reach)
        time_max_sat_min_muses_reach = time_diff;
    }
		while(!stack.empty()) {
			s_pop();
			stack.pop_front();
		}
		res = 0;			//the given formula is SAT, i.e. there's no MUS
	}
	if (initialPush)
		s_pop();
	queryType = qType_orig;
	return res;
}

void m5_API::minimize_core(long timeout_value, InstL& vel, InstLL& muses, int& numSat, int& numUnsat, bool recordTime) {
	collect_stats_muses(vel.size());
	InstL remainingList = vel;
	int itCount = 0;
	while(!remainingList.empty()) {
		InstL mus;
		int res = get_mus(timeout_value, remainingList, mus, numSat, numUnsat, recordTime);
		if (res == 0)
			break;
		else {
			assert(res == 1);
			AVR_LOG(17, 4, "\t(mus) " << mus << endl);
			muses.push_back(mus);

			/// Early exit after getting a single MUS
			break;
		}
	}
	if (m_abstract)
		Solver::total_itr_ab_muses_input += itCount;
	else
		Solver::total_itr_bv_muses_input += itCount;
}

void m5_API::extract_predicates(TermSet &in, InstL& out, bool minimize) {
	VmtFrontend vp(&m_ctx);

	for (auto& p: in) {
		Inst* node = vp.traverse_node(p);
		if (minimize) {
			if (node->get_type() == Op) {
				OpInst* op = OpInst::as(node);
				assert(op);
				if (op->get_op() == OpInst::Eq || op->get_op() == OpInst::NotEq) {
					AVR_LOG(19, 5, "skipping predicate: " << *node << endl);
					continue;
				}
			}
		}
		out.push_back(node);
	}
}

void m5_API::get_predicates(msat_term t, TermSet &out, bool minimize) {
    struct Data {
        TermSet &s;
        bool minimize;

        Data(TermSet &out, bool b): s(out), minimize(b) {}
    };

    auto visit = [](msat_env e, msat_term t, int preorder,
                    void *data) -> msat_visit_status
        {
            Data *d = static_cast<Data *>(data);
            TermSet &s = d->s;
            if (preorder && msat_term_is_atom(e, t)) {
            	if (d->minimize) {
            		if (!msat_term_is_boolean_constant(e, t)) {
              		if (!msat_term_is_equal(e, t)) {
              			s.insert(t);
                    return MSAT_VISIT_SKIP;
              		}
              		else {
              			if (!msat_term_is_constant(e, msat_term_get_arg(t, 0)) ||
              					!msat_term_is_constant(e, msat_term_get_arg(t, 1))) {
											s.insert(t);
											return MSAT_VISIT_SKIP;
              			}
              		}
            		}
            	}
            	else {
                s.insert(t);
                return MSAT_VISIT_SKIP;
            	}
            }
            return MSAT_VISIT_PROCESS;
        };
    Data d(out, minimize);
    msat_visit_term(m_ctx, t, visit, &d);
}

int m5_API::get_interpolant(long timeout_value, InstL& velA, InstL& velB, InstL& new_preds, int& numSat, int& numUnsat) {
#ifdef RANDOM_SHUFFLE_CORE
	if (Config::g_random)
	{
		vector< Inst* > velVec;
		for (auto& v: velA)
			velVec.push_back(v);
		random_shuffle(velVec.begin(), velVec.end());
		velA.clear();
		for (auto& v: velVec)
			velA.push_back(v);
	}
#endif
	int res;

	AVR_LOG(19, 2, "\tEntering interpolant extraction from MathSAT5" << endl);
	AVR_LOG(19, 3, "\t[InputA]: #" << velA.size() << "\n" << velA << endl);
	AVR_LOG(19, 3, "\t[InputB]: #" << velB.size() << "\n" << velB << endl);
	assert(!velA.empty());
	assert(!velB.empty());

  map< m5_expr, Inst*> y_to_inst;

	AVR_LOG(19, 4, "\tcreating constraints for A" << endl);
	m5_expr_vec expA;
//	{
//		assert(m_constraints.empty());
//		init_inst2yices();
//		for (InstL::iterator it = velA.begin(); it != velA.end(); it++) {
//			inst2yices(*it);
//			force(*it);
//		}
//		for (auto& c: m_constraints)
//			expA.push_back(c);
//		expA.swap(m_constraints);
//		m_constraints.clear();
//	}
	{
		int count = 0;
		m5_expr_vec constraints;
		for (InstL::iterator it = velA.begin(); it != velA.end(); it++) {
			init_inst2yices();
			inst2yices(*it);
			force(*it);
			add_assert(*it);

			string iName = "_p_$" + get_m5_temp_name(*it, count);
			m5_expr_ptr indVar = create_bool_var(iName);
			AVR_LOG(19, 4, "\t\t\t(inst: " << *(*it) << ", indicator: " << print_term(indVar) << ")" << endl);

			assert (!m_constraints.empty());
			for (auto& c: m_constraints)
				constraints.push_back(m5_make_implies(m_ctx, indVar, c));
			m_constraints.clear();

			expA.push_back(indVar);
			y_to_inst[indVar] = (*it);
		}
		for (auto& c: constraints)
			expA.push_back(c);
//		constraints.swap(m_constraints);
	}

	AVR_LOG(19, 4, "\tcreating constraints for B" << endl);
	{
		init_inst2yices();
		for (InstL::iterator it = velB.begin(); it != velB.end(); it++) {
			inst2yices(*it);
			force(*it);
		}
	}

	AVR_LOG(19, 4, "\tasserting constraints for A" << endl);
	int gA = msat_create_itp_group(m_ctx);
	if (gA == -1) {
		m5_loge("itp error: " << msat_last_error_message(m_ctx) << endl);
	}
	assert(gA != -1);
	res = msat_set_itp_group(m_ctx, gA);
	assert(res == 0);
	for (auto& v: expA)
		s_assert_constraint(v);
	AVR_LOG(19, 4, "Group A id: " << gA << endl);

	AVR_LOG(19, 4, "\tasserting all other constraints as B" << endl);
	int gB = msat_create_itp_group(m_ctx);
	if (gB == -1) {
		m5_loge("itp error: " << msat_last_error_message(m_ctx) << endl);
	}
	assert(gB != -1);
	res = msat_set_itp_group(m_ctx, gB);
	assert(res == 0);
	s_assert_constraints();
	AVR_LOG(19, 4, "Group B id: " << gB << endl);

	AVR_LOG(19, 4, "\tsolving constraints A & B" << endl);
	res = s_check(timeout_value, false);
	AVR_LOG(19, 2, "itp solve result: " << res << endl);

	if (res == AVR_QUSAT) {
		AVR_LOG(19, 4, "\tcomputing interpolant" << endl);
		m5_expr interpolant = msat_get_interpolant(m_ctx, &gA, 1);
		if (MSAT_ERROR_TERM(interpolant)) {
			AVR_LOG(19, 4, "\titp: " << msat_last_error_message(m_ctx) << endl);
			return AVR_QTO;
		}
		assert(!MSAT_ERROR_TERM(interpolant));
		AVR_LOG(19, 3, "got interpolant: " << "\t" << print_term(interpolant) << endl);
		AVR_LOG(19, 5, "itp interp smt2: " << "\t" << msat_to_smtlib2(m_ctx, interpolant) << endl);
		if (!msat_term_is_false(m_ctx, interpolant)) {
			TermSet preds;
			get_predicates(interpolant, preds);
			AVR_LOG(19, 2, "interpolant term preds: #" << preds.size() << endl);
			for (auto& p: preds) {
				AVR_LOG(19, 3, print_term(p) << endl);
			}
			extract_predicates(preds, new_preds);
//			assert(0);
		}
	}
	else {
		AVR_LOG(19, 0, "itp solve result: " << res << endl);
		assert(0);
	}
	AVR_LOG(19, 0, "\t(new preds from interpolant) #" << new_preds.size() << endl);
	for (auto& v: new_preds) {
		AVR_LOG(19, 0, "\t\t" << *v << endl);
	}
	return res;
}

string m5_API::print_name(Inst* e) {
	unsigned yIdx = get_vIdx();
	m5_expr& yvar = e->m5_node.m5_var[yIdx];
	if (MSAT_ERROR_TERM(yvar)) {
		assert_all_wire_constraints();
		init_inst2yices();
		inst2yices(e);
		yvar = e->m5_node.m5_var[yIdx];
	}
	if (MSAT_ERROR_TERM(yvar))
		return "";
	char* tmp = msat_to_smtlib2_term(m_ctx, yvar);
	string str(tmp);
	msat_free(tmp);
	return str;
}

void m5_API::print_expression(InstL& vel, ofstream& out) {
	size_t sz = 0;
	msat_term* tt = NULL;
	assert_all_wire_constraints();

 	init_inst2yices();
	m_constraints.clear();
	for (auto& e: vel) {
		inst2yices(e);
		force(e);
	}
	sz = m_constraints.size();
	tt = &m_constraints[0];

//	for (auto& v: vel)
//		s_assert(v);
//	tt = msat_get_asserted_formulas(m_ctx, &sz);

	out << "; size " << sz << "\n";
	out << "(and\n";
	for (int i = 0; i < sz; i++) {
		char* tmp = msat_to_smtlib2_term(m_ctx, tt[i]);
		string str(tmp);
		msat_free(tmp);
		out << "\t" << str << "\n";
	}
	out << ")" << endl;

//	msat_free(tt);
}

Inst* m5_API::read_expression(ifstream& in) {
	string s((istreambuf_iterator<char>(in)), istreambuf_iterator<char>());
	msat_term t = msat_from_string(m_ctx, s.c_str());
  assert(!MSAT_ERROR_TERM(t));

	VmtFrontend vp(&m_ctx);
	Inst* node = vp.traverse_node(t);
	return node;
}

int32_t m5_API::s_push(void) {
  AVR_LOG(17, 5, m_solver_id << "\t(push)\t" << m_numpush << endl);
	assert(m_numpush >= m_numpop);
	int32_t res = msat_push_backtrack_point(m_ctx);
	if (res == 0) {
		m_numpush++;
	}
	else {
		cout << msat_last_error_message(m_ctx) << endl;
		m5_result status = msat_solve(m_ctx);
    if (status != MSAT_UNSAT) {
      cout << "status: " << status << endl;
    }
		assert(status == MSAT_UNSAT);
		print_asserts();
		assert(0);
	}
	m5_expr_vec tmp;
	m_cList.push_back(make_pair(m_cList.size() + 1, tmp));
	push_assert();
	return res;
}

int32_t m5_API::s_pop(void) {
  AVR_LOG(17, 5, m_solver_id << "\t(pop)\t" << m_numpop << endl);
	assert(m_numpush >= m_numpop);
	int32_t res = msat_pop_backtrack_point(m_ctx);
	if (res == 0) {
		m_numpop++;
	}
	else
		assert(0);
	m_cList.pop_back();
	pop_assert();
	return res;
}

bool m5_API::s_assert(Inst* e) {
	AVR_LOG(11, 1, "[SID:" << m_solver_id << ", SBA:" << m_ba_idx << "]----------" << endl);
 	init_inst2yices();
	m_constraints.clear();
	inst2yices(e);
	force(e);
	add_assert(e);
	s_assert_constraints();
	return true;
}

bool m5_API::s_assert(InstL& vel) {
	AVR_LOG(11, 1, "[SID:" << m_solver_id << ", SBA:" << m_ba_idx << "]----------" << endl);
 	init_inst2yices();
	m_constraints.clear();
	for (auto& e: vel) {
		inst2yices(e);
		force(e);
		add_assert(e);
	}
	s_assert_constraints();
	return true;
}

bool m5_API::s_assert_retractable(InstL vel) {
	init_inst2yices();
	m_constraints.clear();
	s_push();
	for (InstL::iterator it = vel.begin(); it != vel.end(); it++) {
		inst2yices(*it);
	}
	for (InstL::iterator it = vel.begin(); it != vel.end(); it++) {
		m5_expr ye = force_wo_add(*it);
		m_constraints.push_back(ye);
		add_assert(*it);
	}
#ifdef Y2_USE_RETRACTABLE_ASSUMPTIONS
	m_assumptions.clear();
	m_unsatCore.clear();

	Solver::incremental_count++;
	Inst* ve = OpInst::create(OpInst::LogAnd, vel);
	string iName = "_a_$" + get_m5_temp_name(ve, Solver::incremental_count);
	m5_expr_ptr indVar = create_bool_var(iName);
	m_assumptions.push_back(indVar);
	s_assert_constraints(indVar);
#else
	s_assert_constraints();
#endif
	return true;
}

bool m5_API::s_retract_assertions() {
#ifdef Y2_USE_RETRACTABLE_ASSUMPTIONS
	m_assumptions.clear();
	m_unsatCore.clear();
#endif
	s_pop();
	assert(m_numpush == m_numpop);
	return true;
}

bool m5_API::s_retract_all_assertions() {
	assert(0);
}

int m5_API::s_check(long timeout_value, bool getModel) {
	AVR_LOG(11, 1, "solving with MSAT for solver id: " << m_solver_id << endl);
	update_query_sz();
	struct rusage usage;
	struct timeval start_time, end_time;
	long long time_diff;
	long long time_res = 0;
	M5_SET_TIMEOUT(m_ctx);
	TIME_S(start_time);
	m5_result res = msat_solve(m_ctx);
	M5_CHECK_TIMEOUT;
	TIME_E(start_time, end_time, time_res);
	if (res == MSAT_SAT) {
		if (m_numpush == 0)
			collect_stats_query(time_res, ONESHOT_SAT);
		else
			collect_stats_query(time_res, INC_SAT);
		if (getModel) {
			if (m_model != NULL) {
				assert(!MSAT_ERROR_MODEL(*m_model));
				msat_destroy_model(*m_model);
			}
			m_model = new m5_model();
			*m_model = msat_get_model(m_ctx);
			if (MSAT_ERROR_MODEL(*m_model)) {
				cout << &m_ctx << "\t" << msat_last_error_message(m_ctx) << endl;
				print_query(time_res, ERROR, "error");
			}
			assert(!MSAT_ERROR_MODEL(*m_model));
		}
		return AVR_QSAT;
	}
	else if (res == MSAT_UNSAT) {
		if (m_numpush == 0)
			collect_stats_query(time_res, ONESHOT_UNSAT);
		else
			collect_stats_query(time_res, INC_UNSAT);
		return AVR_QUSAT;
	}
	else {
		collect_stats_query(time_res, TIME_TO);
		AVR_LOG(11, 0, "error: msat query result unknown, last msg: " << msat_last_error_message(m_ctx) << endl);
		assert(0);
	}
}

m5_result m5_API::s_check_inc(long timeout_value, bool getModel) {
	AVR_LOG(11, 1, "solving inc with MSAT for solver id: " << m_solver_id << endl);
  update_query_sz();
  struct rusage usage;
  struct timeval start_time, end_time;
  long long time_diff;
  long long time_res = 0;
  M5_SET_TIMEOUT(m_ctx);
  TIME_S(start_time);
  m5_result res = msat_solve(m_ctx);
  M5_CHECK_TIMEOUT;
  TIME_E(start_time, end_time, time_res);
  if (res == MSAT_SAT) {
    if (m_numpush == 0)
      collect_stats_query(time_res, ONESHOT_SAT);
    else
      collect_stats_query(time_res, INC_SAT);
    if (getModel) {
			if (m_model != NULL) {
				assert(!MSAT_ERROR_MODEL(*m_model));
				msat_destroy_model(*m_model);
			}
			m_model = new m5_model();
			*m_model = msat_get_model(m_ctx);
			if (MSAT_ERROR_MODEL(*m_model)) {
		    print_query(time_res, ERROR, "error");
			}
			assert(!MSAT_ERROR_MODEL(*m_model));
    }
  }
  else if (res == MSAT_UNSAT) {
    if (m_numpush == 0)
      collect_stats_query(time_res, ONESHOT_UNSAT);
    else
      collect_stats_query(time_res, INC_UNSAT);
  }
  else {
    assert(res != MSAT_UNKNOWN);
    collect_stats_query(time_res, TIME_TO);
		AVR_LOG(11, 0, "error: msat inc query result unknown, last msg: " << msat_last_error_message(m_ctx) << endl);
		assert(0);
  }
  return res;
}

int m5_API::s_check_assume(long timeout_value, bool getModel) {
#ifdef Y2_USE_RETRACTABLE_ASSUMPTIONS
	m5_loge("TODO");
#else
	int res = s_check(timeout_value, getModel);
#endif
  return res;
}

m5_result m5_API::s_check_mus(long timeout_value, m5_expr_vec& assumptions, m5_expr_vec& unsatCore, bool getModel) {
	AVR_LOG(11, 1, "solving with assumptions MSAT for solver id: " << m_solver_id << endl);
  update_query_sz();
  struct rusage usage;
  struct timeval start_time, end_time;
  long long time_diff;
  long long time_res = 0;
  M5_SET_TIMEOUT(m_ctx);
  TIME_S(start_time);
	m5_result res = msat_solve_with_assumptions(m_ctx, &(assumptions.front()), assumptions.size());
  M5_CHECK_TIMEOUT;
  TIME_E(start_time, end_time, time_res);

  if (res == MSAT_SAT) {
  	collect_stats_query(time_res, MUS_SAT);
		if (getModel) {
			if (m_model != NULL) {
				assert(!MSAT_ERROR_MODEL(*m_model));
				msat_destroy_model(*m_model);
			}
			m_model = new m5_model();
			*m_model = msat_get_model(m_ctx);
			if (MSAT_ERROR_MODEL(*m_model)) {
		    print_query(time_res, ERROR, "error");
			}
			assert(!MSAT_ERROR_MODEL(*m_model));
		}
	}
	else if (res == MSAT_UNSAT) {
    collect_stats_query(time_res, MUS_UNSAT);
    size_t n = 0;
		m5_expr* uassumptions = msat_get_unsat_assumptions(m_ctx, &n);
		unsatCore.clear();
		for (int i = 0; i < n; i++)
			unsatCore.push_back(uassumptions[i]);
		msat_free(uassumptions);
	}
	else {
	  assert(res != MSAT_UNKNOWN);
    collect_stats_query(time_res, TIME_TO);
		AVR_LOG(11, 0, "error: msat mus query result unknown, last msg: " << msat_last_error_message(m_ctx) << endl);
		assert(0);
	}
	return res;
}

bool m5_API::get_relation(Inst* lhs, Inst* rhs, bool expected) {
	return true;
}

bool m5_API::get_assignment(Inst* e, int& val) {
	assert(e->get_sort_type() == bvtype);
	assert(e->get_size() == 1);
	assert(m_model != NULL);
	assert(!MSAT_ERROR_MODEL(*m_model));

	val = INVALID_SVAL;
	m5_expr decl = e->m5_node.solv_var(get_vIdx());
	assert(!MSAT_ERROR_TERM(decl));

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
		m5_expr result = msat_model_eval(*m_model, decl);
		if (MSAT_ERROR_TERM(result)) {
			cout << *e << "\t" << e->get_sort().sort2str() << "\t" << print_term(decl) << endl;
			cout << msat_last_error_message(m_ctx) << endl;
			assert(0);
		}
		assert(!MSAT_ERROR_TERM(result));
    switch (msat_decl_get_tag(m_ctx, msat_term_get_decl(result))) {
    case MSAT_TAG_TRUE:
    	val = 1;
			break;
    case MSAT_TAG_FALSE:
    	val = 0;
			break;
    default:
    	val = INVALID_SVAL;
    }
	}
	assert(val != INVALID_SVAL);

	if (done) {
		if (val2 != val) {
			cout << "got conflicting assignment for " << *e << endl;
			cout << "m5 says " << val << endl;
			cout << "children says " << val2 << endl;
			cout << "solver id: " << m_solver_id << endl;
			assert(0);
		}
	}
	if (val == 1) {
		e->set_bval(1);
	}
	else {
		assert(val == 0);
		e->set_bval(0);
	}
//	if (m_solver_id == 417) {
//	AVR_LOG(11, 0, "[VALB] " << *e << "\t" << print_term(decl) << " (" << print_type(msat_term_get_type(decl)) << ") \t" << val << endl);
//	}
//	else {
	AVR_LOG(11, 4, "[VALB] " << *e << "\t" << print_term(decl) << " (" << print_type(msat_term_get_type(decl)) << ") \t" << val << endl);
//	}
	return true;
}

void m5_API::get_value_bv(unsigned sz, m5_expr_ptr decl, string& sval) {
	assert(sz > 0);
	if (sz == 1 && msat_is_bool_type(m_ctx, msat_term_get_type(decl))) {
		int val;
    switch (msat_decl_get_tag(m_ctx, msat_term_get_decl(decl))) {
    case MSAT_TAG_TRUE:
    	val = 1;
			break;
    case MSAT_TAG_FALSE:
    	val = 0;
			break;
    default:
    	val = INVALID_SVAL;
    }
    assert(val != INVALID_SVAL);
		sval = val_to_str(val, sz, false);
	}
	else {
		assert(msat_term_is_number(m_ctx, decl));
		mpq_t m;
		mpq_init(m);
		int result = msat_term_to_number(m_ctx, decl, m);
		assert(result == 0);
		sval = string(mpq_get_str(NULL, 2, m));
		while (sval.size() < sz)
			sval = "0" + sval;
	}
	assert(sval.size() == sz);
}

void m5_API::get_value_int(unsigned sz, m5_expr_ptr decl, string& sval) {
	assert(sz == INT_SZ);
	assert(msat_term_is_number(m_ctx, decl));
	mpq_t m;
	mpq_init(m);
	int result = msat_term_to_number(m_ctx, decl, m);
	assert(result == 0);
	sval = string(mpq_get_str(NULL, 10, m));
}

void m5_API::get_value_utt(unsigned sz, m5_expr_ptr decl, string& sval) {
	assert(sz > 0);
	if (sz == 1 && msat_is_bool_type(m_ctx, msat_term_get_type(decl))) {
		int val;
    switch (msat_decl_get_tag(m_ctx, msat_term_get_decl(decl))) {
    case MSAT_TAG_TRUE:
    	val = 1;
			break;
    case MSAT_TAG_FALSE:
    	val = 0;
			break;
    default:
    	val = INVALID_SVAL;
    }
    assert(val != INVALID_SVAL);
		sval = val_to_str(val, sz, false);
	}
	else {
		assert(msat_decl_get_tag(m_ctx, msat_term_get_decl(decl)) == MSAT_TAG_UNKNOWN);
		char* tmp = msat_term_repr(decl);
		string str(tmp);
		msat_free(tmp);
		sval = "u" + str;
	}

//	cout << &m_ctx << "\t" << print_term(decl) << "\t" << sval << "\tsz: " << sz << endl;
//	msat_free(msat_term_get_decl(decl).repr)	;
//	cout << "decl: " << print_ftype(msat_term_get_decl(decl)) << endl;

//	msat_model_iterator mit = msat_model_create_iterator(*m_model);
//	while(msat_model_iterator_has_next(mit)) {
//		m5_expr lhs, rhs;
//		int result = msat_model_iterator_next(mit, &lhs, &rhs);
//		assert(result == 0);
//		cout << "value: " << print_term(lhs) << " -> " << print_term(rhs) << endl;
//	}
//	msat_destroy_model_iterator(mit);
//
//	cout << "assertions" << endl;
//	size_t numassert = 0;
//	m5_expr* f = msat_get_asserted_formulas(m_ctx, &numassert);
//	for (int i = 0; i < numassert; i++) {
//		cout << print_term(f[i]) << endl;
//	}
//	msat_free(f);
//	assert(0);
}

void m5_API::get_value(bool abstract, SORT& sort, m5_expr_ptr decl, string& sval) {
	assert(!MSAT_ERROR_TERM(decl));
	switch(sort.type) {
	case bvtype:
		if (abstract)
			get_value_utt(sort.sz, decl, sval);
		else
			get_value_bv(sort.sz, decl, sval);
		break;
	case inttype:
		if (abstract)
			get_value_utt(sort.sz, decl, sval);
		else
			get_value_int(sort.sz, decl, sval);
		break;
	case arraytype:
		get_value_arr(abstract, sort, decl, sval);
		break;
	default:
		assert(0);
	}
}

void m5_API::get_value_arr(bool abstract, SORT& sort, m5_expr_ptr decl, string& sval) {
	assert(sort.type == arraytype);
	assert(sort.args.size() == 2);
	assert(!MSAT_ERROR_TERM(decl));

  SORT& d = sort.args.front();
  SORT& r = sort.args.back();

	string defstr;
	map < string, string > vMap;
  switch (msat_decl_get_tag(m_ctx, msat_term_get_decl(decl))) {
  case MSAT_TAG_ARRAY_CONST: {
  	assert(msat_term_arity(decl) == 1);
  	m5_expr def = msat_term_get_arg(decl, 0);
  	get_value(abstract, r, def, defstr);
  }
		break;
  case MSAT_TAG_ARRAY_WRITE: {
  	m5_expr t = decl;
  	while (msat_decl_get_tag(m_ctx, msat_term_get_decl(t)) == MSAT_TAG_ARRAY_WRITE) {
    	assert(msat_term_arity(t) == 3);
    	m5_expr arr = msat_term_get_arg(t, 0);

    	string addrstr;
    	m5_expr address = msat_term_get_arg(t, 1);
//    	cout << "address: " << print_term(address) << "\t" << print_ftype(msat_term_get_decl(address)) << endl;
//    	cout << "tag: " << msat_decl_get_tag(m_ctx, msat_term_get_decl(address)) << endl;
    	get_value(abstract, d, address, addrstr);

    	string valstr;
    	m5_expr value = msat_term_get_arg(t, 2);
    	get_value(abstract, r, value, valstr);

    	if (vMap.find(addrstr) == vMap.end())
				vMap[addrstr] = valstr;
//			cout << addrstr << " -> " << valstr << endl;
			assert(arr != t);
			t = arr;
  	}
  	assert(msat_decl_get_tag(m_ctx, msat_term_get_decl(t)) == MSAT_TAG_ARRAY_CONST);
  	assert(msat_term_arity(t) == 1);
  	m5_expr def = msat_term_get_arg(t, 0);
  	get_value(abstract, r, def, defstr);
  }
		break;
  default:
  	m5_loge("TODO");
  }

//	cout << sort.sort2str() << "\tdef: " << defstr << endl;
//  for (auto& v: vMap)
//    cout << v.first << " -> " << v.second << endl;

//	if (false && !abstract && d.type == bvtype) {
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
//	m5_loge("TODO");
}

bool m5_API::get_assignment(Inst* e, mpz_class* val) {
  assert(e->get_size() != 1);
  assert(m_model != NULL);
  assert(!MSAT_ERROR_MODEL(*m_model));

  m5_expr decl = e->m5_node.solv_var(get_vIdx());
  assert(!MSAT_ERROR_TERM(decl));

  string sval;
  int base = 2;

  m5_expr result = msat_model_eval(*m_model, decl);
	if (MSAT_ERROR_TERM(result)) {
		cout << *e << "\t" << e->get_sort().sort2str() << "\t" << print_term(decl) << endl;
		cout << msat_last_error_message(m_ctx) << endl;
		assert(0);
	}
	assert(!MSAT_ERROR_TERM(result));
  SORT sort = e->get_sort();

  if (m_mapper->fetch_var(e) == TheoryMapper::BV_VAR) {
		if (e->get_sort_type() == bvtype) {
			get_value_bv(e->get_size(), result, sval);
		}
		else if (e->get_sort_type() == inttype) {
			base = 10;
			get_value_int(e->get_size(), result, sval);
		}
		else if (e->get_sort_type() == arraytype) {
	    get_value_arr(false, sort, result, sval);
//	    cout << *e << " bv has value: " << sval << endl;
//	    assert(0);
		}
		else {
			assert(0);
		}
	}
  else {
    assert (m_mapper->fetch_var(e) == TheoryMapper::EUF_VAR);
		if (e->get_sort_type() == bvtype || e->get_sort_type() == inttype) {
			get_value_utt(e->get_size(), result, sval);
//			cout << *e << " ab has value: " << sval << endl;
		}
		else if (e->get_sort_type() == arraytype) {
	    get_value_arr(true, sort, result, sval);
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
  if (pval == INVALID_SMPZ) {
    mpz_class zval;
    if (m_mapper->fetch_var(e) == TheoryMapper::BV_VAR) {
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
    else {
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
//	if (m_solver_id == 417) {
//	AVR_LOG(11, 0, "[VALE] " << *e << "\t" << print_term(decl) << " (" << print_type(msat_term_get_type(decl)) << ") \t" << *pval << "\t" << sval << endl);
//	}
//	else {
  AVR_LOG(11, 4, "[VALE] " << *e << "\t" << print_term(decl) << " (" << print_type(msat_term_get_type(decl)) << ") \t" << *pval << "\t" << sval << endl);
//	}
  return true;
}

void m5_API::print_smt2(string fname, string header) {
//	cout << "assertions" << endl;
//	size_t numassert = 0;
//	m5_expr* f = msat_get_asserted_formulas(m_ctx, &numassert);
//	for (int i = 0; i < numassert; i++) {
//		cout << print_term(f[i]) << endl;
//	}
//	msat_free(f);
//	m5_loge("TODO");
}

#ifdef ASSERT_DISTINCT_NUMBERS
void m5_API::assert_distinct_constants(void) {
	if (m_mapper->fetch_logic() == TheoryMapper::QF_BV)
		return;
  if (Config::g_ab_interpret) {
  	if ((Config::g_ab_interpret_excc >= LEVEL_EXCC_ALL) || (Config::g_ab_interpret_limit == 0))
  		return;
  }
	m_constraints.clear();
	int idx = m5_API::m_distinct_constraints.first;
	if (false && idx != -1) {
		m5_expr_vec& dV = m5_API::m_distinct_constraints.second;
		for (auto& dis : dV) {
			add_constraint(dis, "forcing distinct constant: ");
//			cout << "SID: " << m_solver_id << "\t" << print_term(dis) << endl;
		}
	}
	else {
		m5_expr_vec dV;
		for (auto& i : NumInst::m_sz_to_constants) {
			pair<unsigned, SORT> sz = i.first;
			InstS& consts = i.second;
			unsigned numConsts = consts.size();
			if (numConsts > 1) {
				Inst* top = (*consts.begin());
				if (m_mapper->fetch_var(top) == TheoryMapper::BV_VAR)
					continue;
				m5_expr_vec yV;
				for (auto& e : consts) {
					e->m5_node.set_key();
					m5_expr& y = e->m5_node.m5_var[get_vIdx()];
					if (!(e->m5_node.solv_vset(get_vIdx()))) {
						string name = get_m5_name(e);
						y = create_int_var(name, sz);
						e->m5_node.m5_vset[get_vIdx()] = true;
					}
					assert (!MSAT_ERROR_TERM(y));
					yV.push_back(y);
				}
				unsigned vSz = yV.size();
				if (vSz > 1) {
					m5_expr dis = m_b1;
					for (int i = 0; i < vSz; i++) {
						for (int j = i+1; j < vSz; j++) {
							dis = msat_make_and(m_ctx, dis, m5_make_neq(m_ctx, yV[i], yV[j]));
						}
					}
					assert (!MSAT_ERROR_TERM(dis));
					dV.push_back(dis);
					add_constraint(dis, "forcing distinct constant: ");
//					cout << "SID: " << m_solver_id << "\t" << print_term(dis) << endl;
				}
			}
		}
		m_distinct_constraints = make_pair(1, dV);
	}
	if (!m_constraints.empty()) {
		s_assert_constraints();
	}
}
#endif

void m5_API::print_constraints(int loc, int level) {
	m5_loge("TODO");
}

bool m5_API::s_another_solution(void) {
	m5_loge("TODO");
}

string m5_API::get_logic_name() {
	string lname = "QF_";
	if (Inst::en_array)
		lname += "A";
	if (m_abstract) {
		if (m_mapper->fetch_logic() == TheoryMapper::QF_UF)
			lname += "UF";
		else {
			assert (m_mapper->fetch_logic() == TheoryMapper::QF_UFBV);
			lname += "UFBV";
			if (Inst::en_integer)
				lname += "LIA";
		}
	}
	else {
		assert (m_mapper->fetch_logic() == TheoryMapper::QF_BV);
		lname += "BV";
		if (Inst::en_integer)
			lname += "LIA";
	}
	return lname;
}

string m5_API::get_m5_name(Inst*e) {
	string prefix = "";
	string suffix = "";
	if (queryType != prt) {
		prefix = "m$";
		switch(get_vIdx()) {
		case UFBV_V: suffix = "_ufbv"; break;
		case BV_V:   suffix = "_bv";   break;
		}
	}

	string output = "";

	if (queryType == prt) {
		if (e->get_type() == Sig) {
			SigInst* sig = SigInst::as(e);
			output = prefix + sig->get_name() + suffix;
		}
		else if (e->get_type() == Wire) {
			WireInst* w = WireInst::as(e);
			output = prefix + w->get_name() + suffix;
		}
		else if (e->get_type() == Num) {
			NumInst* num = NumInst::as(e);
			ostringstream str;
			str << prefix << "n" << *(num->get_mpz()) << "s" << num->get_sort().sort2str() << suffix;
			output = str.str();
		}
		else if (e->get_type() == Op) {
			OpInst* op = OpInst::as(e);
			Inst* wire = op->get_wire();
			if (wire) {
				WireInst* w = WireInst::as(wire);
				output = prefix + w->get_name() + "_op" + suffix;
			}
			else {
				ostringstream str;
				str << prefix << "i" << e->get_id() << suffix;
				output = str.str();
			}
		}
		else {
			ostringstream str;
			str << prefix << "i" << e->get_id() << suffix;
			output = str.str();
		}
		replace(output.begin(), output.end(), '|', '$');
		replace(output.begin(), output.end(), '\\', '.');
		replace(output.begin(), output.end(), ':', '_');
	}
	else {
		ostringstream str;
		str << prefix << "i" << e->get_id() << suffix;
		output = str.str();
	}

	Solver::m_nameToInst[output] = e;
	return output;
}

std::string m5_API::get_m5_temp_name(Inst*e, int count) {
//	return to_string(count);
	return to_string(e->get_id()) + (m_abstract?"":"_bv");
//	return to_string(e->get_id()) + "$" + to_string(count);
}

m5_type m5_API::create_bv_sort(pair< unsigned, SORT > sz) {
	m5_type bv;
	m5_IntBvM::iterator it = m_sz_to_bv.find(sz);
	if (it == m_sz_to_bv.end()) {
		if (sz.second.type == bvtype) {
			if (sz.first == 1)
				bv = msat_get_bool_type(m_ctx);
			else {
				bv = msat_get_bv_type(m_ctx, sz.first);
			}
		}
		else if (sz.second.type == arraytype) {
			SORT& d = sz.second.args.front();
			SORT& r = sz.second.args.back();
			m5_type dt = create_bv_sort(make_pair(d.sz, d));
			m5_type rt = create_bv_sort(make_pair(r.sz, r));
			if (msat_is_bool_type(m_ctx, dt))
				dt = msat_get_bv_type(m_ctx, 1);
			if (msat_is_bool_type(m_ctx, rt))
				rt = msat_get_bv_type(m_ctx, 1);
			bv = msat_get_array_type(m_ctx, dt, rt);
		}
		else if (sz.second.type == inttype)
			bv = msat_get_integer_type(m_ctx);
		else {
			AVR_LOG(11, 0, "unsupported sort: " << sz.second.type << endl);
			assert(0);
		}
		if (MSAT_ERROR_TYPE(bv)) {
			cout << "sort: " << sz.second << endl;
			cout << "msat: " << msat_last_error_message(m_ctx) << endl;
		}
		assert(!MSAT_ERROR_TYPE(bv));
		m_sz_to_bv.insert(make_pair(sz, bv));
		AVR_LOG(11, 3, "inserting conc var type: " << print_type(bv) << " (sz = " << sz.first << ", " << sz.second << ")" << endl);
	}
	else
		bv = (*it).second;
	return bv;
}

m5_type m5_API::create_int_sort(pair< unsigned, SORT > sz) {
	m5_type ut;
	m5_IntUtM::iterator it = m_sz_to_ut.find(sz);
	if (it == m_sz_to_ut.end()) {
		if (sz.second.type == bvtype || sz.second.type == inttype) {
			if (sz.first == 1)
				ut = msat_get_bool_type(m_ctx);
			else {
				string typeName = "utt$";
				if (sz.second.type != bvtype)
					typeName += sz.second.sort2str();
				else
					typeName += to_string(sz.first);
				char* n = const_cast<char*> (typeName.c_str());
				ut = msat_get_simple_type(m_ctx, n);
			}
		}
		else if (sz.second.type == arraytype) {
			SORT& d = sz.second.args.front();
			SORT& r = sz.second.args.back();
			m5_type dt = create_int_sort(make_pair(d.sz, d));
			m5_type rt = create_int_sort(make_pair(r.sz, r));
			if (msat_is_bool_type(m_ctx, dt))
				dt = msat_get_bv_type(m_ctx, 1);
			if (msat_is_bool_type(m_ctx, rt))
				rt = msat_get_bv_type(m_ctx, 1);
			ut = msat_get_array_type(m_ctx, dt, rt);
		}
		else {
			AVR_LOG(11, 0, "unsupported sort: " << sz.second.type << endl);
			assert(0);
		}
		if (MSAT_ERROR_TYPE(ut)) {
			cout << "msat: " << msat_last_error_message(m_ctx) << endl;
		}
		assert(!MSAT_ERROR_TYPE(ut));
		m_sz_to_ut.insert(make_pair(sz, ut));
		AVR_LOG(11, 3, "inserting ut var type: " << print_type(ut) << " (sz = " << sz.first << ", " << sz.second << ")" << endl);
	}
	else
		ut = (*it).second;
	return ut;
}

m5_expr m5_API::create_bv_var(std::string name, pair< unsigned, SORT > sz) {
	m5_expr d;
	m5_StringToDecl::iterator tit = m_var_decs.find(name);
	if (tit == m_var_decs.end()) {
		m5_type bv = create_bv_sort(sz);
		d = msat_make_constant(m_ctx, msat_declare_function(m_ctx, name.c_str(), bv));
		m_var_decs[name] = d;
		AVR_LOG(11, 3, "creating conc var: " << print_term(d) << " (sz = " << sz.first << ", " << sz.second << ")" << endl);
	}
	else {
		d = (*tit).second;
	}
	return d;
}

m5_expr m5_API::create_int_var(std::string name, pair< unsigned, SORT > sz) {
	m5_expr d;
	m5_StringToDecl::iterator tit = m_var_decs.find(name);
	if (tit == m_var_decs.end()) {
		m5_type ut = create_int_sort(sz);
		d = msat_make_constant(m_ctx, msat_declare_function(m_ctx, name.c_str(), ut));
		m_var_decs[name] = d;
		AVR_LOG(11, 3, "creating ut var: " << print_term(d) << " (sz = " << sz.first << ", " << sz.second << ")" << endl);
	}
	else {
		d = (*tit).second;
	}
	return d;
}

m5_expr m5_API::create_bool_var(std::string name) {
	m5_expr d;
	m5_StringToDecl::iterator tit = m_var_decs.find(name);
	if (tit == m_var_decs.end()) {
		m5_type bt = msat_get_bool_type(m_ctx);
		d = msat_make_constant(m_ctx, msat_declare_function(m_ctx, name.c_str(), bt));
		m_var_decs[name] = d;
		AVR_LOG(11, 3, "creating bool var: " << print_term(d) << endl);
	}
	else {
    d = (*tit).second;
	}
	return d;
}

void m5_API::force(Inst* e) {
	if (m_mapper->fetch_var(e) == TheoryMapper::BV_VAR) {
		add_constraint(e->m5_node.solv_var(get_vIdx()), "forcing for BV", e, false);
	}
	else if (m_mapper->fetch_var(e) == TheoryMapper::BOOL_VAR) {
		add_constraint(e->m5_node.solv_var(get_vIdx()), "forcing for BOOL", e, false);
	}
	else if (m_mapper->fetch_var(e) == TheoryMapper::EUF_VAR) {
		assert(0);
	}
	else {
		assert(0);
	}
}

m5_expr m5_API::force_wo_add(Inst* e) {
	if (m_mapper->fetch_var(e) == TheoryMapper::BV_VAR) {
		return e->m5_node.solv_var(get_vIdx());
	}
	else if (m_mapper->fetch_var(e) == TheoryMapper::BOOL_VAR) {
		return e->m5_node.solv_var(get_vIdx());
	}
	else if (m_mapper->fetch_var(e) == TheoryMapper::EUF_VAR) {
		assert(0);
	}
	else {
		assert(0);
	}
}

void m5_API::add_constraint(m5_expr_ptr y, std::string comment, Inst*e, bool storeC) {
	if (MSAT_ERROR_TERM(y)) {
		cout << *e << endl;
		cout << e->get_size() << endl;
		cout << m_abstract << endl;
		cout << comment << endl;
		cout << get_vIdx() << endl;
		cout << get_cIdx() << endl;
		assert(0);
	}
	m_constraints.push_back(y);
	if (e != 0) {
		if (storeC) {
			unsigned cIdx = get_cIdx();
			e->m5_node.m5_constraints[cIdx].push_back(y);
			AVR_LOG(11, 2, "     storing (" << comment << "): " << print_term(y) << " for " << *e << endl);
		}
		else {
			AVR_LOG(11, 3, "     adding constraints (" << comment << "): " << print_term(y) << " for " << *e << endl);
		}
	}
	else {
		AVR_LOG(11, 3, "     adding constraints (" << comment << "): " << print_term(y) << endl);
	}
}

void m5_API::s_assert_constraints(m5_expr_ptr indVar, bool reset) {
	pair< int, m5_expr_vec>& tmp = m_cList.back();
	int sz = m_constraints.size();
	if (sz != 0) {
		int res = 0;
		if (MSAT_ERROR_TERM(indVar)) {
			for (auto& ye: m_constraints) {
				AVR_LOG(11, 8, "(assert " << print_term(ye) << " )" << endl);
				res = msat_assert_formula(m_ctx, ye);
			}
		}
		else {
			for (auto& c: m_constraints) {
				m5_expr_ptr ye = msat_make_or(m_ctx, msat_make_not(m_ctx, indVar), c);
				AVR_LOG(11, 8, "(assert " << print_term(ye) << " )" << endl);
				int resTmp = msat_assert_formula(m_ctx, ye);
				if (resTmp != 0)
					res = resTmp;
			}
		}
		if (res != 0) {
			AVR_LOG(11, 0, "error: " << msat_last_error_message(m_ctx) << endl);
		}
		assert(res == 0);
		for (auto& c : m_constraints) {
			tmp.second.push_back(c);
		}
		m_query_sz += sz;
		if (reset)
			m_constraints.clear();
	}
}

int m5_API::s_assert_constraint(m5_expr_ptr ye) {
	pair< int, m5_expr_vec>& tmp = m_cList.back();
  AVR_LOG(17, 7, "(assert " << print_term(ye) << " )" << endl);
	int res = msat_assert_formula(m_ctx, ye);
	if (res != 0) {
		AVR_LOG(11, 0, "error: " << msat_last_error_message(m_ctx) << endl);
	}
	assert (res == 0);
	tmp.second.push_back(ye);
	m_query_sz += 1;
	return res;
}

m5_expr_ptr m5_API::create_m5_number(NumInst* num) {
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
		else {
			m5_expr_ptr c = msat_make_bv_number(m_ctx, num->get_mpz()->get_str(10).c_str(), sz, 10);
			return c;
		}
	}
	else if (num->get_sort_type() == inttype) {
		m5_expr_ptr c = msat_make_int_number(m_ctx, num->get_num());
		return c;
	}
	else {
		cout << *num << endl;
		assert(0);
	}
}

void m5_API::add_yices_func(m5_expr& var, std::string op, bool pred, m5_expr_list& ch, Ints& sz, Inst* e) {
	assert(m_abstract);
	m5_expr func;
	pair <Inst*, string> typeKey = make_pair(e, op);
	m5_InstToFuncDecl::iterator tit = m_func_decs.find(typeKey);
	if (tit == m_func_decs.end()) {
		bool hasbool = false;
		for (auto& v: ch) {
			if (msat_is_bool_type(m_ctx, msat_term_get_type(v))) {
				hasbool = true;
				break;
			}
		}
		if (hasbool)
			m5_set_bool_uf();

		ostringstream str;
		str << op;
		str << "_" << e->get_size();
		m5_expr_list::iterator chIt = ch.begin();
		for (Ints::iterator it = sz.begin(), end_it = sz.end(); it != end_it; ++it, ++chIt) {
			str << "_" << *it;
		}

		op = str.str();
		m5_ftype_ptr funct;
		m5_StringToFunctM::iterator it = m_funct.find(op);
		if (it == m_funct.end()) {
			m5_type target = msat_term_get_type(var);
			m5_type domain[ch.size()];
			unsigned i = 0;
			for (m5_expr_list::iterator it = ch.begin(), end_it = ch.end(); it != end_it; ++it) {
				m5_expr_ptr tmp = *it;
				if (hasbool && msat_is_bool_type(m_ctx, msat_term_get_type(tmp)))
					domain[i] = g_ufboolt;
				else
					domain[i] = msat_term_get_type(tmp);
				i++;
			}
			m5_type functt = msat_get_function_type(m_ctx, domain, ch.size(), target);
			funct = msat_declare_function(m_ctx, op.c_str(), functt);
			m_funct.insert(make_pair(op, funct));
			AVR_LOG(11, 3, "inserting function template: " << print_ftype(funct) << " of type " << print_type(functt) << endl);
		}
		else
			funct = (*it).second;

		InstL::const_iterator cit = e->get_children()->begin();
		m5_expr args[ch.size()];
		unsigned i = 0;
		for (m5_expr_list::iterator it = ch.begin(), end_it = ch.end(); it != end_it; ++it, ++i, ++cit) {
			if (hasbool && msat_is_bool_type(m_ctx, msat_term_get_type(*it)))
				args[i] = msat_make_term_ite(m_ctx, *it, g_uftrue, g_uffalse);
			else
				args[i] = *it;
		}
		func = msat_make_uf(m_ctx, funct, args);
		m_func_decs[typeKey] = func;
		if (MSAT_ERROR_TERM(func)) {
			cout << *e << endl;
			cout << "present type: " << (it != m_funct.end()) << endl;
			{
				int i = 0;
				for (auto& ch: (*e->get_children())) {
					cout << i++ << ": " << *ch << endl;
					ch->m5_node.print();
				}
			}
		}
		assert (!MSAT_ERROR_TERM(func));
		AVR_LOG(11, 3, "creating function application: " << print_term(func) << " of type " << print_ftype(funct) << endl);
	}
	else {
		func = (*tit).second;
	}
	assert (!MSAT_ERROR_TERM(var));
	if (MSAT_ERROR_TERM(func)) {
		cout << *e << endl;
		cout << "present: " << (tit != m_func_decs.end()) << endl;
	}
	assert (!MSAT_ERROR_TERM(func));

	if (!allow_flatten)
		var = func;
	else
		add_constraint(msat_make_eq(m_ctx, var, func), "func link", e);
}

void m5_API::inst2yices(Inst*e, bool bvAllConstraints) {
	assert(e != 0);
	assert(m_mapper);
	if (e->get_visit()) {
		assert (e->m5_node.get_m5_key() == M5_INFO::st_m5_key);
		return;
	}
	e->set_visit();

	// do the children first.
	m5_expr_list y_ch;
	const InstL* ch = e->get_children();
	Ints s_sz;
	unsigned yIdx = get_vIdx();
	unsigned cIdx = get_cIdx();
	bool reuseAllowed = true && (queryType != prt);
	/// Disable recursion inside an internal wire in case of concrete query
	if (!m_abstract && !bvAllConstraints) {
		WireInst* w = WireInst::as(e);
		if (w) {
			Inst* port = w->get_port();
			assert (port);
#ifndef SUBSTITUTE
			reuseAllowed = false;
			if (!allow_all) {
//				if (w->get_name().length() > 5 && w->get_name().substr(w->get_name().length() - 5) == "$next")
//				{
//					ch = 0;
//				}
//				else
				{
					if (w->is_connected(WireInst::get_connect_key())) {
					}
					else {
						ch = 0;
//						cout << "(ignoring wire: " << *w << ")" << endl;
					}
				}
			}
#endif
		}
	}

	// first, collect data
	if (m_mapper->fetch_var(e) == TheoryMapper::BV_VAR) {
//		assert(!m_abstract);
	}
	else if (m_mapper->fetch_var(e) == TheoryMapper::EUF_VAR) {
		num_of_terms++;
		assert(m_abstract);
	}
	else if (m_mapper->fetch_var(e) == TheoryMapper::BOOL_VAR) {
		num_of_bools++;
		assert(m_abstract);
	}
	else {
		assert(0);
	}
	e->m5_node.set_key();
	m5_expr& yvar = e->m5_node.m5_var[yIdx];
	if (!(e->m5_node.solv_vset(yIdx))) {
		string name = get_m5_name(e);
		// first, what type of variable should we allocate
		if (m_mapper->fetch_var(e) == TheoryMapper::BV_VAR) {
			yvar = create_bv_var(name, make_pair(e->get_size(), e->get_sort()));
		}
		else if (m_mapper->fetch_var(e) == TheoryMapper::EUF_VAR) {
			yvar = create_int_var(name, make_pair(e->get_size(), e->get_sort()));
		}
		else if (m_mapper->fetch_var(e) == TheoryMapper::BOOL_VAR) {
			yvar = create_bool_var(name);
		}
		else {
			assert(0);
		}
		assert(!MSAT_ERROR_TERM(yvar));
		e->m5_node.m5_vset[yIdx] = true;
	}

	if (ch) {
		for (auto& v: *ch) {
			inst2yices(v);
			y_ch.push_back(v->m5_node.solv_var(yIdx));
			s_sz.push_back(v->get_size());
			assert(!MSAT_ERROR_TERM(y_ch.back()));
			assert(v->m5_node.solv_vset(yIdx));
		}
	}

#ifdef INTERPRET_EX_CC
	if (m_allow_ex_cc) {
		if (Config::g_uf_mult_only || (m_mapper->fetch_op(e) == TheoryMapper::EUF_OP) ||
				(m_mapper->fetch_op(e->t_simple) == TheoryMapper::EUF_OP)) {
			Inst* simplified = e->t_simple;
			if (OpInst::as(e) && e != simplified) {
				Inst* simplified = e->t_simple;
				if (e != simplified)
					inst2yices(simplified);
			}
		}
	}
#endif

	if (reuseAllowed && e->m5_node.solv_vset(yIdx)) {
		if (e->m5_node.solv_cset(cIdx)) {
			/// Constraints already set, use stored constraints.
	//		cout << "reusing stored constraints " << *e << " nC: " << e->y_constraints[yIdx].size() << endl;
			for (auto& c : e->m5_node.solv_constraints(cIdx)) {
				add_constraint(c, "reusing stored constraints", e, false);
			}
			return;
		}
	}
	e->m5_node.m5_cset[cIdx] = true;

	switch (e->get_type())
	{
	case Num: {
		NumInst* num = NumInst::as(e);
		assert(num != 0);

		if (m_mapper->fetch_var(e) == TheoryMapper::BV_VAR) {
			m5_expr_ptr c = create_m5_number(num);
			if (!allow_flatten)
				yvar = c;
			else
				add_constraint(msat_make_eq(m_ctx, yvar, c), "constant link", e);

//			// required to remain in QF_LIA
//			if (e->get_sort_type() == inttype)
//				yvar = c;
		}
		else if (m_mapper->fetch_var(e) == TheoryMapper::BOOL_VAR) {
			yvar = ((*(num->get_mpz()) == 0) ? m_b0 : m_b1);
		}
		else {
		}
	}
		break;
	case Sig: {
		// nothing!
	}
		break;
	case Wire: {
		if (m_mapper->fetch_op(e) == TheoryMapper::BV_OP) {
			if (y_ch.size() == 0) {
			}
			else {
				m5_expr_ptr res = y_ch.front();
				bool done = false;
				if (queryType == prt) {
					if (!allow_flatten) {
						yvar = res;
						done = true;
					}
				}
				if (!done)
					add_constraint(msat_make_eq(m_ctx, yvar, res), "port connection", e);
			}
		}
		else if (m_mapper->fetch_op(e) == TheoryMapper::EUF_OP || m_mapper->fetch_op(e) == TheoryMapper::CLU_OP) {
			assert(y_ch.size() == 1);
			m5_expr_ptr res = y_ch.front();
			if (!allow_flatten)
				yvar = res;
			else
				add_constraint(msat_make_eq(m_ctx, yvar, res), "port connection", e);
		}
		else {
			assert(0);
		}
	}
		break;
	case Const: {
		// nothing!
	}
		break;
	case Op: {
		OpInst* op = OpInst::as(e);
		assert(op != 0);
		m5_expr res;
		MSAT_MAKE_ERROR_TERM(res);
		string opstr = "";
		bool interpreted = false;
		m5_expr_list::iterator it = y_ch.begin(), it2 = y_ch.begin(), end_it = y_ch.end();
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
			m5_expr log;
			MSAT_MAKE_ERROR_TERM(log);
			switch (o) {

			case OpInst::LogNot: {
				if (m_mapper->fetch_var(e) == TheoryMapper::BV_VAR) {
					log = msat_make_not(m_ctx, *it);
				} else if (m_mapper->fetch_var(e) == TheoryMapper::BOOL_VAR) {
					log = msat_make_not(m_ctx, *it);
				} else {
					assert(0);
				}
				interpreted = true;
			}
				break;
			case OpInst::LogNand:
			case OpInst::LogNor:
			case OpInst::LogAnd:
			case OpInst::LogOr: {
				log = (o == OpInst::LogAnd) || (o == OpInst::LogNand) ? m5_make_and(m_ctx, y_ch) :
						                                                    m5_make_or(m_ctx, y_ch);
				if((o == OpInst::LogNor) || (o == OpInst::LogNand)){
					log = msat_make_not(m_ctx, log);
				}
				interpreted = true;
			}
				break;
			case OpInst::LogXNor:
			case OpInst::LogXor: {
				log = *it;
				for (m5_expr_list::iterator argIt = it2; argIt != end_it; argIt++) {
					if (m_mapper->fetch_var(e) == TheoryMapper::BV_VAR) {
						log = msat_make_or(m_ctx, msat_make_and(m_ctx, log, msat_make_not(m_ctx, *argIt)), msat_make_and(m_ctx, msat_make_not(m_ctx, log), *argIt));
					} else if (m_mapper->fetch_var(e) == TheoryMapper::BOOL_VAR) {
						log = msat_make_or(m_ctx, msat_make_and(m_ctx, log, msat_make_not(m_ctx, *argIt)), msat_make_and(m_ctx, msat_make_not(m_ctx, log), *argIt));
					} else {
						assert(0);
					}
				}
				if(o == OpInst::LogXNor){
					log = msat_make_not(m_ctx, log);
				}
				interpreted = true;
			}
				break;
			case OpInst::Eq:{
				assert(y_ch.size() == 2);
				log = msat_make_eq(m_ctx, *it, *it2);
				interpreted = true;
			}
				break;
			case OpInst::NotEq: {
				assert(y_ch.size() == 2);
				log = m5_make_neq(m_ctx, *it, *it2);
				interpreted = true;
			}
				break;
			case OpInst::ArrayConst: {
				if (m_mapper->fetch_var(e) == TheoryMapper::BV_VAR) {
					m5_type functt = create_bv_sort(make_pair(e->get_size(), e->get_sort()));
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

					Inst* defval;
					for (int i = 0; i <= maxaddress; i++) {
						string v = value.substr(i*size, size);
						Inst* data = NumInst::create(v, size, 2, SORT());
						if (i == 0) {
							defval = data;
							m5_expr_ptr b = create_m5_number(NumInst::as(data));
							if (msat_is_bool_type(m_ctx, msat_term_get_type(b)))
								b = msat_make_term_ite(m_ctx, b, m_v1, m_v0);
							log = msat_make_array_const(m_ctx, functt, b);
//						cout << "constarray: " << print_term(log) << " of type " << log->get_sort() << endl;
						}
						else if (data != defval){
							Inst* address = NumInst::create(maxaddress - i, width, SORT());
							m5_expr_ptr a = create_m5_number(NumInst::as(address));
							m5_expr_ptr b = create_m5_number(NumInst::as(data));
							if (msat_is_bool_type(m_ctx, msat_term_get_type(a)))
								a = msat_make_term_ite(m_ctx, a, m_v1, m_v0);
							if (msat_is_bool_type(m_ctx, msat_term_get_type(b)))
								b = msat_make_term_ite(m_ctx, b, m_v1, m_v0);
							log = msat_make_array_write(m_ctx, log, a, b);
						}
					}
//				cout << "final constarray: " << print_term(log) << endl;
				} else if (m_mapper->fetch_var(e) == TheoryMapper::EUF_VAR) {
					m5_type functt = create_int_sort(make_pair(e->get_size(), e->get_sort()));
					string name = "constarray_" + to_string(e->get_id());
					m5_expr funct = msat_make_constant(m_ctx, msat_declare_function(m_ctx, name.c_str(), functt));
					log = funct;
					cout << "constarray: " << print_term(log) << " of type " << print_type(msat_term_get_type(log)) << endl;
//					m5_loge("TODO");

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
				assert(!MSAT_ERROR_TERM(log));
				interpreted = true;
			}
				break;
			case OpInst::ArraySelect: {
				m5_expr a = *it;
				m5_expr b = *it2;
				if (msat_is_bool_type(m_ctx, msat_term_get_type(b)))
					b = msat_make_term_ite(m_ctx, b, m_v1, m_v0);
				log = msat_make_array_read(m_ctx, a, b);
//				cout << "selectarray: " << print_term(log) << " of type " << print_type(yices_type_of_term(log)) << endl;
				if (MSAT_ERROR_TERM(log)) {
					cout << msat_last_error_message(m_ctx) << endl;
				}
				assert(!MSAT_ERROR_TERM(log));
				interpreted = true;
			}
				break;
			case OpInst::ArrayStore: {
				m5_expr a = *it;
				m5_expr b = *it2;
				it2++;
				m5_expr c = *it2;
				if (msat_is_bool_type(m_ctx, msat_term_get_type(b)))
					b = msat_make_term_ite(m_ctx, b, m_v1, m_v0);
				if (msat_is_bool_type(m_ctx, msat_term_get_type(c)))
					c = msat_make_term_ite(m_ctx, c, m_v1, m_v0);
				log = msat_make_array_write(m_ctx, a, b, c);
//				cout << "storearray: " << print_term(log) << " of type " << print_type(yices_type_of_term(log)) << endl;
				assert(!MSAT_ERROR_TERM(log));
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

					m5_expr_ptr y1 = *it;
					m5_expr_ptr y2 = *it2;
					Inst* c1 = e->get_children()->front();
					Inst* c2 = e->get_children()->back();
					int c1Sz = c1->get_size();
					int c2Sz = c2->get_size();

					if (msat_is_bool_type(m_ctx, msat_term_get_type(y1)))
						y1 = msat_make_term_ite(m_ctx, y1, m_v1, m_v0);
					if (msat_is_bool_type(m_ctx, msat_term_get_type(y2)))
						y2 = msat_make_term_ite(m_ctx, y2, m_v1, m_v0);

					if (c1Sz < c2Sz)
						y1 = msat_make_bv_zext(m_ctx, (c2Sz - c1Sz), y1);
					if (c2Sz < c1Sz)
						y2 = msat_make_bv_zext(m_ctx, (c1Sz - c2Sz), y2);

					switch (o) {
					case OpInst::Gr:
						log = msat_make_not(m_ctx, msat_make_bv_uleq(m_ctx, y1, y2));
						break;
					case OpInst::SGr:
						log = msat_make_not(m_ctx, msat_make_bv_sleq(m_ctx, y1, y2));
						break;
					case OpInst::Le:
						log = msat_make_bv_ult(m_ctx, y1, y2);
						break;
					case OpInst::SLe:
						log = msat_make_bv_slt(m_ctx, y1, y2);
						break;
					case OpInst::GrEq:
						log = msat_make_not(m_ctx, msat_make_bv_ult(m_ctx, y1, y2));
						break;
					case OpInst::SGrEq:
						log = msat_make_not(m_ctx, msat_make_bv_slt(m_ctx, y1, y2));
						break;
					case OpInst::LeEq:
						log = msat_make_bv_uleq(m_ctx, y1, y2);
						break;
					case OpInst::SLeEq:
						log = msat_make_bv_sleq(m_ctx, y1, y2);
						break;
					case OpInst::IntLe:
						log = m5_make_lt(m_ctx, y1, y2);
						break;
					case OpInst::IntLeEq:
						log = msat_make_leq(m_ctx, y1, y2);
						break;
					case OpInst::IntGr:
						log = m5_make_gt(m_ctx, y1, y2);
						break;
					case OpInst::IntGrEq: {
						log = m5_make_geq(m_ctx, y1, y2);
					}
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
				if (y_ch.size() == 1) {
					res = *it;
				} else {
					res = *it;
					if (msat_is_bool_type(m_ctx, msat_term_get_type(res)))
						res = msat_make_term_ite(m_ctx, res, m_v1, m_v0);
					for (m5_expr_list::iterator argIt = it2; argIt != end_it; argIt++) {
						m5_expr_ptr h = *argIt;
						if (msat_is_bool_type(m_ctx, msat_term_get_type(h)))
							h = msat_make_term_ite(m_ctx, h, m_v1, m_v0);
						res = msat_make_bv_concat(m_ctx, h, res);
					}
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

				m5_expr_ptr a = (*it);
				if (msat_is_bool_type(m_ctx, msat_term_get_type(a)))
					a = msat_make_term_ite(m_ctx, a, m_v1, m_v0);
				Inst* c1 = e->get_children()->front();
				int outSz = e->get_size();
				int c1Sz = c1->get_size();
				if (c1Sz < outSz)
					a = msat_make_bv_zext(m_ctx, (outSz - c1Sz), a);

				switch (o) {
				case OpInst::Minus: {
					assert(y_ch.size() == 1);
					res = msat_make_bv_neg(m_ctx, a);
				}
					break;
				case OpInst::BitWiseNot: {
					assert(y_ch.size() == 1);
					res = msat_make_bv_not(m_ctx, a);
				}
					break;
				case OpInst::IntFloor: {
					assert(y_ch.size() == 1);
					res = msat_make_floor(m_ctx, a);
				}
					break;
				case OpInst::IntMinus: {
					assert(y_ch.size() == 1);
					res = msat_make_times(m_ctx, msat_make_int_number(m_ctx, -1), a);
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
					m5_expr_ptr b = (*it2);
					if (msat_is_bool_type(m_ctx, msat_term_get_type(b)))
						b = msat_make_term_ite(m_ctx, b, m_v1, m_v0);

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
							a = msat_make_bv_zext(m_ctx, (maxSz - outSz), a);
						}
						if (c2Sz < maxSz)
						{
							b = msat_make_bv_zext(m_ctx, (maxSz - c2Sz), b);
						}
					}

					switch (o) {
					case OpInst::Add:{
						assert(y_ch.size() == 2);
						res = msat_make_bv_plus(m_ctx, a, b);
					}break;
					case OpInst::Sub: {
						assert(y_ch.size() == 2);
						res = msat_make_bv_minus(m_ctx, a, b);
					}
						break;
					case OpInst::Mult:{
						assert(y_ch.size() == 2);
						res = msat_make_bv_times(m_ctx, a, b);
					}
						break;
					case OpInst::Div:{
						assert(y_ch.size() == 2);
						res = msat_make_bv_udiv(m_ctx, a, b);
					}
						break;
					case OpInst::SDiv:{
						assert(y_ch.size() == 2);
						res = msat_make_bv_sdiv(m_ctx, a, b);
					}
						break;
					case OpInst::Rem:{
						assert(y_ch.size() == 2);
						res = msat_make_bv_urem(m_ctx, a, b);
					}
						break;
					case OpInst::SRem:{
						assert(y_ch.size() == 2);
						res = msat_make_bv_srem(m_ctx, a, b);
					}
						break;
					case OpInst::SMod:{
						assert(y_ch.size() == 2);
						res = msat_make_bv_srem(m_ctx, a, b);
					}
						break;
					case OpInst::BitWiseAnd: {
						assert(y_ch.size() == 2);
						res = msat_make_bv_and(m_ctx, a, b);
					}
						break;
					case OpInst::BitWiseNand: {
						assert(y_ch.size() == 2);
						res = msat_make_bv_not(m_ctx, msat_make_bv_and(m_ctx, a, b));
					}
						break;
					case OpInst::BitWiseOr: {
						assert(y_ch.size() == 2);
						res = msat_make_bv_or(m_ctx, a, b);
					}
						break;
					case OpInst::BitWiseNor: {
						assert(y_ch.size() == 2);
						res = msat_make_bv_not(m_ctx, msat_make_bv_or(m_ctx, a, b));
					}
						break;
					case OpInst::BitWiseXor: {
						assert(y_ch.size() == 2);
						res = msat_make_bv_xor(m_ctx, a, b);
					}
						break;
					case OpInst::BitWiseXNor: {
						assert(y_ch.size() == 2);
						res = msat_make_bv_not(m_ctx, msat_make_bv_xor(m_ctx, a, b));
					}
						break;
					case OpInst::ShiftL: {
						assert(y_ch.size() == 2);
						res = msat_make_bv_lshl(m_ctx, a, b);
					}
					  break;
					case OpInst::ShiftR: {
						assert(y_ch.size() == 2);
						res = msat_make_bv_lshr(m_ctx, a, b);
					}
						break;
					case OpInst::AShiftR: {
						assert(y_ch.size() == 2);
						res = msat_make_bv_ashr(m_ctx, a, b);
					}
						break;
					case OpInst::Sext:
					case OpInst::Zext: {
						assert(y_ch.size() == 2);
						m5_expr_ptr a2 = (*it);
						if (msat_is_bool_type(m_ctx, msat_term_get_type(a2)))
							a2 = msat_make_term_ite(m_ctx, a2, m_v1, m_v0);
						InstL::const_iterator ve_it = ch->begin();
						int amount = e->get_size() - (*ve_it)->get_size();
						assert(amount >= 0);
						if (o == OpInst::Sext)
							res = msat_make_bv_sext(m_ctx, amount, a2);
						else
							res = msat_make_bv_zext(m_ctx, amount, a2);
					}
						break;
					case OpInst::IntAdd: {
						assert(y_ch.size() == 2);
						res = msat_make_plus(m_ctx, a, b);
					}
						break;
					case OpInst::IntSub: {
						assert(y_ch.size() == 2);
						b = msat_make_times(m_ctx, msat_make_int_number(m_ctx, -1), b);
						res = msat_make_plus(m_ctx, a, b);
					}
						break;
					case OpInst::IntMult: {
						assert(y_ch.size() == 2);
						res = msat_make_times(m_ctx, a, b);
					}
						break;
					case OpInst::IntDiv: {
						assert(y_ch.size() == 2);
						res = msat_make_divide(m_ctx, a, b);
					}
						break;
					case OpInst::IntMod: {
						m5_loge("TODO");
					}
						break;
					default:
						assert(0);
					}
					if (e->get_sort_type() == bvtype) {
						if (outSz < maxSz)
							res = msat_make_bv_extract(m_ctx, (outSz - 1), 0, res);
					}
				}
					break;

				case OpInst::AddC:
				case OpInst::AShiftL:
					assert(0); // for now.

				case OpInst::ReductionAnd:
				case OpInst::ReductionNand: {
					assert(y_ch.size() == 1);
					unsigned sz = (*(ch->begin()))->get_size();
					assert(sz > 1);
					m5_expr bit = msat_make_bv_extract(m_ctx, 0, 0, a);
					m5_expr bit2 = msat_make_bv_extract(m_ctx, 1, 1, a);
					bit = msat_make_bv_and(m_ctx, bit, bit2);
					for (unsigned i = 2; i < sz; i++)
					{
						bit = msat_make_bv_and(m_ctx, bit, msat_make_bv_extract(m_ctx, i, i, a));
					}
					if (o == OpInst::ReductionNand)		bit = msat_make_bv_not(m_ctx, bit);
					res = bit;
				}
					break;
				case OpInst::ReductionOr:
				case OpInst::ReductionNor: {
					assert(y_ch.size() == 1);
					unsigned sz = (*(ch->begin()))->get_size();
					assert(sz > 1);
					m5_expr bit = msat_make_bv_extract(m_ctx, 0, 0, a);
					m5_expr bit2 = msat_make_bv_extract(m_ctx, 1, 1, a);
					bit = msat_make_bv_or(m_ctx, bit, bit2);
					for (unsigned i = 2; i < sz; i++)
					{
						bit = msat_make_bv_or(m_ctx, bit, msat_make_bv_extract(m_ctx, i, i, a));
					}
					if (o == OpInst::ReductionNor)		bit = msat_make_bv_not(m_ctx, bit);
					res = bit;
				}
					break;
				case OpInst::ReductionXor:
				case OpInst::ReductionXNor: {
					assert(y_ch.size() == 1);
					unsigned sz = (*(ch->begin()))->get_size();
					assert(sz > 1);
					m5_expr bit = msat_make_bv_extract(m_ctx, 0, 0, a);
					m5_expr bit2 = msat_make_bv_extract(m_ctx, 1, 1, a);
					bit = msat_make_bv_xor(m_ctx, bit, bit2);
					for (unsigned i = 2; i < sz; i++)
					{
						bit = msat_make_bv_xor(m_ctx, bit, msat_make_bv_extract(m_ctx, i, i, a));
					}
					if (o == OpInst::ReductionXNor)		bit = msat_make_bv_not(m_ctx, bit);
					res = bit;
				}
					break;
				case OpInst::VRotateR:{
					m5_loge("TODO");
				}
				  break;
				case OpInst::VRotateL:{
					m5_loge("TODO");
				}
				  break;
				case OpInst::VShiftL:
				case OpInst::VShiftR:
				case OpInst::VAShiftL:
				case OpInst::VAShiftR:
				case OpInst::VEx:{
					m5_loge("TODO");
				}
				  break;
				default:
					assert(0);
				}
			} else if (m_mapper->fetch_op(e) == TheoryMapper::EUF_OP || m_mapper->fetch_op(e) == TheoryMapper::CLU_OP) {
				switch (o) {
				case OpInst::VShiftL:
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
						opstr = "Add";
					} else if (m_mapper->fetch_op(e) == TheoryMapper::CLU_OP) {
					} else
						assert(0);
					break;
				case OpInst::Sub:
					if (m_mapper->fetch_op(e) == TheoryMapper::EUF_OP) {
						opstr = "Sub";
					} else if (m_mapper->fetch_op(e) == TheoryMapper::CLU_OP)
					{
						assert(0);
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
			assert(y_ch.size() == 3);
			m5_expr_list::iterator it3 = it2;
			it3++;
			m5_expr_ptr cond = (*it);
			m5_expr_ptr y1 = (*it2);
			m5_expr_ptr y2 = (*it3);
			if (!msat_is_bool_type(m_ctx, msat_term_get_type(cond)))
				cond = msat_make_eq(m_ctx, cond, m_v1);
			if (msat_is_bool_type(m_ctx, msat_term_get_type(y1))) {
				assert (msat_is_bool_type(m_ctx, msat_term_get_type(y2)));
				// res = cond. y1 + !cond. y2
				res = msat_make_or(m_ctx, msat_make_and(m_ctx, cond, y1),
						                           msat_make_and(m_ctx, msat_make_not(m_ctx, cond), y2));
			}
			else
				res = msat_make_term_ite(m_ctx, cond, y1, y2);
			interpreted = true;
		}
			break;
		default:
			AVR_COUT << o << endl;
			assert(0);
		}
		if (m_mapper->fetch_op(e) == TheoryMapper::BV_OP) {
			assert(!MSAT_ERROR_TERM(yvar));
			assert(!MSAT_ERROR_TERM(res));
			if (msat_is_bool_type(m_ctx, msat_term_get_type(yvar))) {
				if (!msat_is_bool_type(m_ctx, msat_term_get_type(res)))
					res = msat_make_eq(m_ctx, res, m_v1);
			}
			else {
				if (msat_is_bool_type(m_ctx, msat_term_get_type(res)))
					res = msat_make_term_ite(m_ctx, res, m_v1, m_v0);
			}
			if (!msat_type_equals(msat_term_get_type(yvar), msat_term_get_type(res))) {
				cout << "inconsistent term types for node " << *e << endl;
				cout << "yvar: " << print_term(yvar) << " of type " << print_type(msat_term_get_type(yvar)) << endl;
				cout << "res: " << print_term(res) << " of type " << print_type(msat_term_get_type(res)) << endl;
				assert(0);
			}

			if (!allow_flatten)
				yvar = res;
			else
				add_constraint(msat_make_eq(m_ctx, yvar, res), "result of a bv op", e);
		}
		else if (m_mapper->fetch_op(e) == TheoryMapper::EUF_OP || m_mapper->fetch_op(e) == TheoryMapper::CLU_OP) {
			if (interpreted) {
				assert(!MSAT_ERROR_TERM(yvar));
				assert(!MSAT_ERROR_TERM(res));
				if (msat_is_bool_type(m_ctx, msat_term_get_type(yvar))) {
					if (!msat_is_bool_type(m_ctx, msat_term_get_type(res)))
						res = msat_make_eq(m_ctx, res, m_v1);
				}
				else {
					if (msat_is_bool_type(m_ctx, msat_term_get_type(res)))
						res = msat_make_term_ite(m_ctx, res, m_v1, m_v0);
				}
				if (!msat_type_equals(msat_term_get_type(yvar), msat_term_get_type(res))) {
					cout << "inconsistent term types for node " << *e << endl;
					cout << "yvar: " << print_term(yvar) << " of type " << print_type(msat_term_get_type(yvar)) << endl;
					cout << "res: " << print_term(res) << " of type " << print_type(msat_term_get_type(res)) << endl;
					assert(0);
				}

				if (!allow_flatten)
					yvar = res;
				else
					add_constraint(msat_make_eq(m_ctx, yvar, res), "interpreted operator constraint for EUF", e);
			}
			else {
				if (opstr == "") {
					cout << OpInst::op2str(o) << endl;
					assert(0);
				}
				add_yices_func(yvar, opstr, e->get_size() == 1, y_ch, s_sz, e);
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
			m5_expr_ptr res = msat_make_bv_extract(m_ctx, ex->get_hi(), ex->get_lo(), y_ch.front());
			assert(!MSAT_ERROR_TERM(res));
			if (msat_is_bool_type(m_ctx, msat_term_get_type(yvar))) {
				if (!msat_is_bool_type(m_ctx, msat_term_get_type(res)))
					res = msat_make_eq(m_ctx, res, m_v1);
			}
			else {
				if (msat_is_bool_type(m_ctx, msat_term_get_type(res)))
					res = msat_make_term_ite(m_ctx, res, m_v1, m_v0);
			}

			if (!allow_flatten)
				yvar = res;
			else
				add_constraint(msat_make_eq(m_ctx, yvar, res), "result of a bv EX", e);

		} else if (m_mapper->fetch_op(e) == TheoryMapper::EUF_OP || m_mapper->fetch_op(e) == TheoryMapper::CLU_OP) {
			assert(y_ch.size() == 1);
			s_sz.clear();
			s_sz.push_back(ex->get_hi());
			s_sz.push_back(ex->get_lo());
			s_sz.push_back((*(ch->begin()))->get_size());
			add_yices_func(yvar, "Extract", e->get_size() == 1, y_ch, s_sz, e);
		} else
			assert(0);
	}
		break;
	case UF: {
		UFInst* uf = UFInst::as(e);
		assert(uf != 0);
		assert(ch != 0);
		assert(ch->size() > 0);
		add_yices_func(yvar, clean_str(uf->get_name()), e->get_size() == 1, y_ch, s_sz, e);
	}
		break;
	case Mem:
	default:
		AVR_COUT << e->get_type() << endl;
		assert(0);
	}

#ifdef INTERPRET_EX_CC
	if (m_allow_ex_cc) {
		if (Config::g_uf_mult_only || (m_mapper->fetch_op(e) == TheoryMapper::EUF_OP) ||
				(m_mapper->fetch_op(e->t_simple) == TheoryMapper::EUF_OP)) {
			Inst* simplified = e->t_simple;
			if (e != simplified) {
				m5_expr_ptr a = simplified->m5_node.solv_var(get_vIdx());
				add_constraint(msat_make_eq(m_ctx, yvar, a), "(partial interpretation)", e);
			}
		}
	}
#endif
}


};

#endif


