/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


/*
 * reach_bt.cpp
 *
 *  Created on: Jul 23, 2019
 *      Author: amangoel
 */

#include "reach_bt.h"

#ifdef _BT

#include <cstdlib>
#include <fstream>
#include <cmath>
#include <csignal>
#include <pthread.h>
#include <functional>

using namespace std;

namespace _bt {

bt_IntBvM bt_API::m_sz_to_bv;
bt_IntUtM bt_API::m_sz_to_ut;
bt_StringToFunctM bt_API::m_funct;

bt_StringToDecl bt_API::m_var_decs;
bt_InstToFuncDecl bt_API::m_func_decs;
bt_MpzToNum bt_API::m_num_to_const;

#ifdef ASSERT_DISTINCT_NUMBERS
	pair < int, bt_expr_vec > bt_API::m_distinct_constraints = make_pair(-1, bt_expr_vec());
#endif

bt_expr_ptr bt_API::m_b0;
bt_expr_ptr bt_API::m_b1;

bt_context	bt_API::g_ctx;
FILE* bt_API::g_fd;

list< pair<Inst*, bt_expr_ptr> > bt_API::g_gateList;


string print_type(bt_type_ptr y) {
	return "";
}

string print_term(bt_expr y) {
	FILE * tempFile = tmpfile();
	string n = "";
	if(tempFile) {
		boolector_dump_smt2_node(boolector_get_btor(y), tempFile, y);
		rewind(tempFile);

		char line[1000];
		string value;
		while (fgets(line, sizeof(line), tempFile)) {
				/* note that fgets don't strip the terminating \n, checking its
					 presence would allow to handle lines longer that sizeof(line) */
			n += string(line) + " ";
//			break;
		}
		fclose(tempFile);
	}
	replace(n.begin(), n.end(), '\n', ' ');
	return n;
}

string print_ftype(bt_ftype_ptr y) {
	return print_term(y);
}

string print_terms(bt_expr_vec& yV) {
	ostringstream ostr;
	for (auto& y: yV)
		ostr << "\t" << print_term(y) << endl;
	return ostr.str();
}

string print_terms(list<bt_expr_ptr>& yV) {
	string s = "";
	for (auto& y: yV)
		s = s + print_term(y) + " ";
	return s;
}

static void print_model(bt_context env) {
	char n[] = "smt2";
	boolector_print_model(env, n, stdout);
}

void bt_API::debug() {
//  boolector_dump_smt2(g_ctx, stdout);
//  cout << "asserts" << endl;
//  for (auto& v: m_assertions) {
//  	cout << print_term(v) << "\t" << boolector_failed(g_ctx, v) << endl;
//  }
//  cout << "assumes" << endl;
//  for (auto& v: m_assumptions) {
//  	cout << print_term(v) << "\t" << boolector_failed(g_ctx, v) << endl;
//  }
}

SolverType bt_API::fetch_solv_name(void) {
	return SMT_Boolector;
}

void bt_API::bt_interrupt(int signum) {
	s_check_timed_out = true;
}

void bt_API::bt_exit() {
	if (g_ctx) {
//		boolector_print_stats(g_ctx);
//		boolector_reset_stats(g_ctx);
//		boolector_reset_time(g_ctx);

		boolector_release_all(g_ctx);
		boolector_delete(g_ctx);
//		fclose(g_fd);
	}
}

void bt_API::bt_init() {
	g_ctx = boolector_new();

	const char *s = boolector_version(g_ctx);
  AVR_LOG(11, 1, "Using " << s << endl);

	BT_INFO::inc_bt_key();

//	std::string name = QUERY_PATH;
//	name += "trace/" + _benchmark + "_trace.smt2";
//	AVR_LOG(11, 0, "Boolector trace file: " << name << endl);
//	g_fd = fopen (name.c_str(), "r");
//	boolector_set_trapi(g_ctx, g_fd);//

	// set options here
//	boolector_set_opt(g_ctx, BTOR_OPT_VERBOSITY, 2);

	boolector_set_opt(g_ctx, BTOR_OPT_INCREMENTAL, 1);
	if (!Config::g_bmc_en || Config::g_print_witness)
		boolector_set_opt(g_ctx, BTOR_OPT_MODEL_GEN, 1);
	boolector_set_opt(g_ctx, BTOR_OPT_AUTO_CLEANUP, 0);
	boolector_set_opt(g_ctx, BTOR_OPT_VAR_SUBST, 1);

	boolector_set_opt(g_ctx, BTOR_OPT_SAT_ENGINE, BTOR_SAT_ENGINE_CADICAL);
//	boolector_set_opt(g_ctx, BTOR_OPT_SAT_ENGINE, BTOR_SAT_ENGINE_CMS);

//	boolector_set_sat_solver(g_ctx, "Lingeling");
//	boolector_set_sat_solver(g_ctx, "CaDiCaL");


//	boolector_set_opt(g_ctx, BTOR_OPT_REWRITE_LEVEL, 0);
//	boolector_set_opt(g_ctx, BTOR_OPT_FUN_PREPROP, 0);
//	boolector_set_opt(g_ctx, BTOR_OPT_FUN_PRESLS, 0);
//	boolector_set_opt(g_ctx, BTOR_OPT_FUN_DUAL_PROP, 0);
//	boolector_set_opt(g_ctx, BTOR_OPT_FUN_JUST, 0);

//	boolector_set_opt(g_ctx, BTOR_OPT_ELIMINATE_SLICES, 1);
//	boolector_set_opt(g_ctx, BTOR_OPT_FUN_LAZY_SYNTHESIZE, 0);



	m_b0 = boolector_false(g_ctx);
	m_b1 = boolector_true(g_ctx);
#ifdef ASSERT_DISTINCT_NUMBERS
	m_distinct_constraints = make_pair(-1, bt_expr_vec());
#endif
}

void bt_API::bt_exit_ctx() {
//	for (auto& v: m_gateList)
//		boolector_release(g_ctx, v.second);
}

void bt_API::bt_init_ctx() {
}

bt_API::bt_API(TheoryMapper* m, unsigned ba_idx, bool is_inc, int type) :
			Solver(m, ba_idx, type) {
	assert(m);

	AVR_LOG(11, 1, "Creating new BT instance for BA[" << m_ba_idx << "] with solver_id [" << m_solver_id << "]" << endl);

	bt_init_ctx();

	m_constraints.clear();
	m_assertions.clear();
	m_assertions_retract.clear();
	m_assumptions.clear();
	bt_expr_vec tmp;
#ifdef ASSERT_DISTINCT_NUMBERS
	if (m_abstract) {
		assert_distinct_constants();
	}
#endif
}

bt_API::~bt_API() {
	AVR_LOG(11, 1, "Deleting M5 instance for BA[" << m_ba_idx << "] with solver_id [" << m_solver_id << "]" << endl);

	m_constraints.clear();
	bt_exit_ctx();
}

bool bt_API::check_sat(Inst* e, long timeout_value, bool getModel) {
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

int bt_API::forward_propagation(long timeout_value, int frame_idx, InstL& forwarded,
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
			conjunct_query.push_back(ve_next_c);
			s_assert_retractable(conjunct_query);
			res = s_check_assume(AB_QUERY_TIMEOUT, false);
			s_retract_assertions();
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

int bt_API::get_muses(long timeout_value, InstL& vel_1, InstL& vel_2, InstLL& muses, int& numSat, int& numUnsat, Solver* core_solver) {
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

int bt_API::get_muses_2(long timeout_value, InstL& vel, InstLL& muses, int& numSat, int& numUnsat, Solver* core_solver) {
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

//	cout << "core: " << core << endl;

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
		return 1;
	}
	else {
		AVR_LOG(17, 4, "\t(no mus, exit)" << endl);
		return 0;
	}
}

int bt_API::get_unsat_core(long timeout_value, InstL& vel, InstL& core, int& numSat, int& numUnsat) {
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
  map< bt_expr, Inst* >& y_to_inst = m_y_to_inst;
  m_y_to_inst.clear();
  m_unsatCore.clear();

  int count = 0;
  bt_expr_list constraints2;
  InstL induct_clause;
  for (InstL::iterator it = vel.begin(); it != vel.end(); it++) {
    init_inst2yices();
    inst2yices(*it);
    bt_expr_ptr indVar = force_wo_add(*it);
    add_assume(*it);
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
      bt_expr_ptr indVar2 = force_wo_add(ve2);
      induct_clause.push_back(OpInst::create(OpInst::LogNot, ve2));
      indVar2 = boolector_not(g_ctx, indVar2);
			constraints2.push_back(indVar2);
    }
    count++;
  }
  if (uType != no_induct) {
  	assert(!constraints2.empty());
//		AVR_LOG(17, 7, "\t\t\t(induct assertions " << print_terms(constraints2) << endl);

  	Inst* clause = OpInst::create(OpInst::LogOr, induct_clause);
//  	add_assume(clause);
		string iName = "_pi_$" + get_bt_temp_name(clause, count);
    bt_expr_ptr a = create_bool_var(iName);
    AVR_LOG(17, 5, "\t\t\t(induct indicator: " << print_term(a) << ")" << endl);
    constraints2.push_back(boolector_not(g_ctx, a));
    bt_expr_list::iterator yit = constraints2.begin();
  	bt_expr_ptr cInd = (*yit);
  	yit++;
		for (bt_expr_list::iterator argIt = yit; argIt != constraints2.end(); argIt++) {
			cInd = boolector_or(g_ctx, cInd, (*argIt));
		}
  	m_constraints.push_back(cInd);
    m_assumptions.push_back(a);
    y_to_inst[a] = NULL;
  }
	AVR_LOG(17, 7, "\t\t\t\t(assertions " << print_terms(m_constraints) << endl);
	s_assert_constraints();

  TIME_S(start_time);
  bt_result query_res = s_check_mus(timeout_value, m_assumptions, m_unsatCore, false);
  TIME_E(start_time, end_time, time_res);
  AVR_LOG(17, 4, "\t\t(query-check) " << query_res << endl);

  if (query_res == BOOLECTOR_UNSAT) {
    numUnsat++;
    time_unsat_core_muses_reach += time_diff;
    if (time_diff > time_max_unsat_core_muses_reach)
      time_max_unsat_core_muses_reach = time_diff;

    AVR_LOG(17, 4, "unsat core: (sz: " << m_unsatCore.size() << endl);
    int i = 0;
    for (auto& curr: m_unsatCore) {
      assert(curr != BT_INVALID_EXPR);
      AVR_LOG(17, 5, "\t" << i++ << ": " << print_term(curr) << endl);
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
    assert(query_res == BOOLECTOR_SAT);
    numSat++;
    time_sat_core_muses_reach += time_diff;
    if (time_diff > time_max_sat_core_muses_reach)
      time_max_sat_core_muses_reach = time_diff;
    res = AVR_QSAT;      //the given formula is SAT, i.e. there's no MUS
  }
  m_constraints.clear();
  clear_assume();
  queryType = qType_orig;
  return res;
}

int bt_API::find_unsat_core(long timeout_value, InstL& hardQ, InstL& vel, InstL& mus, int& numSat, int& numUnsat) {
  m_constraints.clear();
  init_inst2yices();
  if (!hardQ.empty())
    s_assert(OpInst::create(OpInst::LogAnd, hardQ));
  int result = get_unsat_core(timeout_value, vel, mus, numSat, numUnsat);
  return result;
}

int bt_API::get_mus(long timeout_value, InstL& vel, InstL& mus, int& numSat, int& numUnsat, bool recordTime) {
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
	m_assumptions.clear();
	m_unsatCore.clear();

	bt_InstToExprM& inst_to_y = m_inst_to_y;
  map< bt_expr, Inst* >& y_to_inst = m_y_to_inst;
	inst_to_y.clear();
	y_to_inst.clear();

	// uniquifying is important
	InstS uniqueVel;
	for (InstL::iterator it = vel.begin(); it != vel.end(); ) {
		if (uniqueVel.find(*it) == uniqueVel.end()) {
			uniqueVel.insert(*it);
			it++;
		}
		else
			it = vel.erase(it);
	}

	for (InstL::iterator it = vel.begin(); it != vel.end(); it++) {
		init_inst2yices();
		inst2yices(*it);
		bt_expr_ptr indVar = force_wo_add(*it);
		inst_to_y[*it] = make_pair(indVar, indVar);
    m_assumptions.push_back(indVar);
    add_assume(*it);
    y_to_inst[indVar] = (*it);
	}
	s_assert_constraints();

  TIME_S(start_time);
	bt_result initial_res = s_check_mus(timeout_value, m_assumptions, m_unsatCore, false);
  TIME_E(start_time, end_time, time_res);
  AVR_LOG(17, 5, "\t\t(initial-check) " << initial_res << endl);

	if (initial_res == BOOLECTOR_UNSAT) {
		numUnsat++;
		if (recordTime) {
	    time_unsat_min_muses_reach += time_diff;
	    if (time_diff > time_max_unsat_min_muses_reach)
	      time_max_unsat_min_muses_reach = time_diff;
		}

		InstL undone;
		InstS done;
    AVR_LOG(17, 4, "unsat core: (sz: " << m_unsatCore.size() << endl);
    int i = 0;
    for (auto& curr: m_unsatCore) {
      assert(curr != BT_INVALID_EXPR);
      AVR_LOG(17, 5, "\t" << i << ": " << print_term(curr) << endl);
      map< bt_expr, Inst* >::iterator mit = y_to_inst.find(curr);
      if (mit != y_to_inst.end()) {
				Inst *tve = (*mit).second;
				assert(tve);
				if (done.find(tve) == done.end())
					undone.push_back(tve);
      }
    }
		while(!undone.empty()) {
			AVR_LOG(17, 5, "\t\t(undone)" << undone << endl);
			AVR_LOG(17, 5, "\t\t(mus)" << mus << endl);
			Inst* currInst = undone.back();
			undone.pop_back();
			AVR_LOG(17, 5, "curr: " << *currInst << endl);
			done.insert(currInst);

			m_assumptions.clear();
			m_unsatCore.clear();
			clear_assume();
			for (auto& v: mus) {
				pair < bt_expr, bt_expr > p = inst_to_y[v];
				m_assumptions.push_back(p.first);
				add_assume(v);
			}
			for (auto& v: undone) {
				pair < bt_expr, bt_expr > p = inst_to_y[v];
				m_assumptions.push_back(p.first);
				add_assume(v);
			}

		  TIME_S(start_time);
		  bt_result result = s_check_mus(timeout_value, m_assumptions, m_unsatCore, false);
		  TIME_E(start_time, end_time, time_res);
			AVR_LOG(17, 5, "status_check: " << result << endl);

			if (result == BOOLECTOR_UNSAT) {
				numUnsat++;
		    if (recordTime) {
		      time_unsat_min_muses_reach += time_diff;
		      if (time_diff > time_max_unsat_min_muses_reach)
		        time_max_unsat_min_muses_reach = time_diff;
		    }
		    undone.clear();
		    for (auto& curr: m_unsatCore) {
		      assert(curr != BT_INVALID_EXPR);
		      map< bt_expr, Inst* >::iterator mit = y_to_inst.find(curr);
		      if (mit != y_to_inst.end()) {
						Inst *tve = (*mit).second;
						assert(tve);
						if (done.find(tve) == done.end())
							undone.push_back(tve);
		      }
		    }
			}
			else {
				if (result != BOOLECTOR_SAT) {
					assert(result == BOOLECTOR_UNKNOWN);
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
		}
		m_constraints.clear();
		m_unsatCore.clear();
		if (mus.empty()) {
			cout << "warning: mus.empty()" << endl;
      mus.push_back(vel.front());
//      assert(0);
		}
		res = 1;
	}
	else {
		numSat++;
		assert(initial_res == BOOLECTOR_SAT);
    if (recordTime) {
      time_sat_min_muses_reach += time_diff;
      if (time_diff > time_max_sat_min_muses_reach)
        time_max_sat_min_muses_reach = time_diff;
    }
		res = 0;			//the given formula is SAT, i.e. there's no MUS
	}
	queryType = qType_orig;
	return res;
}

void bt_API::minimize_core(long timeout_value, InstL& vel, InstLL& muses, int& numSat, int& numUnsat, bool recordTime) {
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

bool bt_API::s_assert(Inst* e) {
	AVR_LOG(11, 1, "[SID:" << m_solver_id << ", SBA:" << m_ba_idx << "]----------" << endl);
 	init_inst2yices();
	m_constraints.clear();
	inst2yices(e);
	force(e);
	add_assert(e);
	s_assert_constraints();
	return true;
}

bool bt_API::s_assert(InstL& vel) {
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

bool bt_API::s_assert_retractable(InstL vel) {
	m_constraints.clear();

	Inst* ve = OpInst::create(OpInst::LogAnd, vel);

	init_inst2yices();
	inst2yices(ve);
	bt_expr ye = force_wo_add(ve);
	m_assertions_retract.push_back(ye);
	add_assume(ve);
	s_assert_constraints();

	return true;
}

bool bt_API::s_retract_assertions() {
	m_assertions_retract.pop_back();
	assert(m_assertions_retract.empty());
	return true;
}

bool bt_API::s_retract_all_assertions() {
	assert(0);
}

int bt_API::s_check(long timeout_value, bool getModel) {
	AVR_LOG(11, 1, "solving with Boolector for solver id: " << m_solver_id << endl);
	update_query_sz();
	struct rusage usage;
	struct timeval start_time, end_time;
	long long time_diff;
	long long time_res = 0;
	BT_SET_TIMEOUT(g_ctx);
	TIME_S(start_time);
  boolector_reset_assumptions(g_ctx);
  random_shuffle(m_assertions.begin(), m_assertions.end());
  for (auto& v: m_assertions)
		boolector_assume(g_ctx, v);
	for (auto& v: m_assertions_retract)
		boolector_assume(g_ctx, v);

	bt_result res = boolector_sat(g_ctx);
	BT_CHECK_TIMEOUT;
	TIME_E(start_time, end_time, time_res);
	if (res == BOOLECTOR_SAT) {
		if (m_numpush == 0)
			collect_stats_query(time_res, ONESHOT_SAT);
		else
			collect_stats_query(time_res, INC_SAT);
		if (getModel) {
		}
		return AVR_QSAT;
	}
	else if (res == BOOLECTOR_UNSAT) {
		if (m_numpush == 0)
			collect_stats_query(time_res, ONESHOT_UNSAT);
		else
			collect_stats_query(time_res, INC_UNSAT);
		return AVR_QUSAT;
	}
	else {
		collect_stats_query(time_res, TIME_TO);
		AVR_LOG(11, 0, "error: boolector query result unknown" << endl);
		assert(0);
	}
}

int bt_API::s_check_assume(long timeout_value, bool getModel) {
	int res = s_check(timeout_value, getModel);
  return res;
}

bt_result bt_API::s_check_mus(long timeout_value, bt_expr_vec& assumptions, bt_expr_vec& unsatCore, bool getModel) {
	AVR_LOG(11, 1, "solving with assumptions Boolector for solver id: " << m_solver_id << endl);
  update_query_sz();
  struct rusage usage;
  struct timeval start_time, end_time;
  long long time_diff;
  long long time_res = 0;
  BT_SET_TIMEOUT(g_ctx);
  TIME_S(start_time);
  boolector_reset_assumptions(g_ctx);
  random_shuffle(m_assertions.begin(), m_assertions.end());
  random_shuffle(assumptions.begin(), assumptions.end());
	for (auto& v: m_assertions)
		boolector_assume(g_ctx, v);
	for (auto& v: m_assertions_retract)
		boolector_assume(g_ctx, v);
	for (auto& v: assumptions)
		boolector_assume(g_ctx, v);

	bt_result res = boolector_sat(g_ctx);
  BT_CHECK_TIMEOUT;
  TIME_E(start_time, end_time, time_res);

  if (res == BOOLECTOR_SAT) {
  	collect_stats_query(time_res, MUS_SAT);
		if (getModel) {
		}
	}
	else if (res == BOOLECTOR_UNSAT) {
    collect_stats_query(time_res, MUS_UNSAT);
		unsatCore.clear();
		for (auto& v: assumptions) {
			if (boolector_failed(g_ctx, v)) {
				unsatCore.push_back(v);
			}
		}

//		bt_expr_ptr* uassumptions = boolector_get_failed_assumptions(g_ctx);
//    size_t i = 0;
//		bt_expr_ptr curr = uassumptions[i];
//		while (curr) {
//			unsatCore.push_back(curr);
//			i++;
//			curr = uassumptions[i];
//		}

	}
	else {
	  assert(res != BOOLECTOR_UNKNOWN);
    collect_stats_query(time_res, TIME_TO);
		AVR_LOG(11, 0, "error: boolector mus query result unknown" << endl);
		assert(0);
	}
	return res;
}

bool bt_API::get_relation(Inst* lhs, Inst* rhs, bool expected) {
	return true;
}

bool bt_API::get_assignment(Inst* e, int& val) {
	assert(e->get_sort_type() == bvtype);
	assert(e->get_size() == 1);

	val = INVALID_SVAL;
	bt_expr decl = e->bt_node.solv_var(get_vIdx());
	if (decl == BT_INVALID_EXPR) {
		cout << *e << endl;
		e->bt_node.print();
		cout << "Locals" << endl;
		for (auto& v: m_gateList)
			cout << *v.first << "\t" << print_term(v.second) << endl;
		cout << "Globals" << endl;
		for (auto& v: g_gateList)
			cout << *v.first << "\t" << print_term(v.second) << endl;
	}
	assert(decl != BT_INVALID_EXPR);

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

	if (!done)
	{
		const char* result = boolector_bv_assignment(g_ctx, decl);
		string vals = string(result);
		boolector_free_bv_assignment(g_ctx, result);
		if (vals == "1")
			val = 1;
		else if (vals == "0")
			val = 0;
		else {
			val = INVALID_SVAL;
			bt_loge("invalid bool value: " << vals);
		}
	}
	assert(val != INVALID_SVAL);

	if (done) {
		if (val2 != val) {
			cout << "got conflicting assignment for " << *e << endl;
			cout << "bt says " << val << endl;
			cout << "children says " << val2 << endl;
			cout << "solver id: " << m_solver_id << endl;

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
							cout << "lhs = " << valL->get_str() << endl;
							cout << "rhs = " << valR->get_str() << endl;
						}
					}
				}
			}

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
	AVR_LOG(11, 4, "[VALB] " << *e << "\t" << print_term(decl) << " (" << print_type(boolector_get_sort(g_ctx, decl)) << ") \t" << val << endl);
	return true;
}

void bt_API::get_value_bv(unsigned sz, bt_expr_ptr decl, string& sval) {
	assert(sz > 0);
	assert(boolector_is_bitvec_sort(g_ctx, boolector_get_sort(g_ctx, decl)));
	const char* result = boolector_bv_assignment(g_ctx, decl);
	sval = string(result);
	boolector_free_bv_assignment(g_ctx, result);
	assert(sval.size() == sz);
}

void bt_API::get_value_int(unsigned sz, bt_expr_ptr decl, string& sval) {
	bt_loge("unsupported");
}

void bt_API::get_value_utt(unsigned sz, bt_expr_ptr decl, string& sval) {
	bt_loge("unsupported");
}

void bt_API::get_value(bool abstract, SORT& sort, bt_expr_ptr decl, string& sval) {
	assert(decl != BT_INVALID_EXPR);
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


void bt_API::get_value_arr(bool abstract, SORT& sort, bt_expr_ptr decl, string& sval) {
	assert(sort.type == arraytype);
	assert(sort.args.size() == 2);

  char **indices;
  char **values;
  uint32_t size;
	boolector_array_assignment (g_ctx, decl, &indices, &values, &size);

  SORT& d = sort.args.front();
  SORT& r = sort.args.back();

  string defstr = "";
	map < string, string > vMap;
	for (int i = 0; i < size; i++) {
		string addrstr = (indices)[i];
		string valstr = (values)[i];
		vMap[addrstr] = valstr;
	}
//	for (int i = 0; i < size; i++) {
//		boolector_free_bv_assignment(g_ctx, (indices)[i]);
//		boolector_free_bv_assignment(g_ctx, (values)[i]);
//	}
	boolector_free_array_assignment(g_ctx, indices, values, size);

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
//  cout << "sval: " << sval << endl;
}


bool bt_API::get_assignment(Inst* e, mpz_class* val) {
  assert(e->get_size() != 1);

  bt_expr decl = e->bt_node.solv_var(get_vIdx());
  if (decl == BT_INVALID_EXPR) {
  	cout << *e << endl;
  }
  assert(decl != BT_INVALID_EXPR);

  string sval;
  int base = 2;

  SORT sort = e->get_sort();
  if (m_mapper->fetch_var(e) == TheoryMapper::BV_VAR) {
		if (e->get_sort_type() == bvtype) {
			get_value_bv(e->get_size(), decl, sval);
		}
		else if (e->get_sort_type() == inttype) {
			base = 10;
			get_value_int(e->get_size(), decl, sval);
		}
		else if (e->get_sort_type() == arraytype) {
	    get_value_arr(false, sort, decl, sval);
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
			get_value_utt(e->get_size(), decl, sval);
//			cout << *e << " ab has value: " << sval << endl;
		}
		else if (e->get_sort_type() == arraytype) {
	    get_value_arr(true, sort, decl, sval);
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
  AVR_LOG(11, 4, "[VALE] " << *e << "\t" << print_term(decl) << " (" << print_type(boolector_get_sort(g_ctx, decl)) << ") \t" << *pval << "\t" << sval << endl);
  return true;
}


void bt_API::print_expression(InstL& vel, FILE* out) {
	assert(0);

//	size_t sz = 0;
//	assert_all_wire_constraints();
//
// 	init_inst2yices();
//	m_constraints.clear();
//	for (auto& e: vel) {
//		inst2yices(e);
//		force(e);
//	}
//  boolector_reset_assumptions(g_ctx);
////  random_shuffle(m_assertions.begin(), m_assertions.end());
//  boolector_push(g_ctx, 1);
//  for (auto& v: m_assertions)
//		boolector_assert(g_ctx, v);
//	for (auto& v: m_assertions_retract)
//		boolector_assert(g_ctx, v);
//  boolector_pop(g_ctx, 1);
//
//	sz = m_constraints.size();
//
//	boolector_dump_btor2(g_ctx, out);
}

void bt_API::print_smt2(string fname, string header) {
}

#ifdef ASSERT_DISTINCT_NUMBERS
void bt_API::assert_distinct_constants(void) {
	if (m_mapper->fetch_logic() == TheoryMapper::QF_BV)
		return;
  if (Config::g_ab_interpret) {
  	if ((Config::g_ab_interpret_excc >= LEVEL_EXCC_ALL) || (Config::g_ab_interpret_limit == 0))
  		return;
  }
  bt_loge("unsupported");
}
#endif


void bt_API::print_constraints(int loc, int level) {
	bt_loge("TODO");
}

bool bt_API::s_another_solution(void) {
	bt_loge("TODO");
}


string bt_API::get_logic_name() {
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


string bt_API::get_bt_name(Inst*e) {
	string prefix = "";
	string suffix = "";
	if (queryType != prt) {
		prefix = "b$";
		switch(get_vIdx()) {
		case UFBV_V: suffix = "_ufbv"; break;
		case BV_V:   suffix = "_bv";   break;
		}
	}

	string output = "";
#if 1
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
#else
	{
		ostringstream str;
		str << prefix << "i" << e->get_id() << suffix;
		output = str.str();
	}
#endif

	Solver::m_nameToInst[output] = e;
	return output;
}

std::string bt_API::get_bt_temp_name(Inst*e, int count) {
//	return to_string(count);
	return to_string(e->get_id()) + (m_abstract?"":"_bv");
//	return to_string(e->get_id()) + "$" + to_string(count);
}

bt_type bt_API::create_bv_sort(pair< unsigned, SORT > sz) {
	bt_type bv;
	bt_IntBvM::iterator it = m_sz_to_bv.find(sz);
	if (it == m_sz_to_bv.end()) {
		if (sz.second.type == bvtype) {
			if (sz.first == 1)
				bv = boolector_bool_sort(g_ctx);
			else {
				bv = boolector_bitvec_sort(g_ctx, sz.first);
			}
		}
		else if (sz.second.type == arraytype) {
			SORT& d = sz.second.args.front();
			SORT& r = sz.second.args.back();
			bt_type dt = create_bv_sort(make_pair(d.sz, d));
			bt_type rt = create_bv_sort(make_pair(r.sz, r));
			bv = boolector_array_sort(g_ctx, dt, rt);
		}
		else if (sz.second.type == inttype) {
			bt_loge("unsupported");
		}
		else {
			AVR_LOG(11, 0, "unsupported sort: " << sz.second.type << endl);
			assert(0);
		}
		m_sz_to_bv.insert(make_pair(sz, bv));
		AVR_LOG(11, 3, "inserting conc var type: " << print_type(bv) << " (sz = " << sz.first << ", " << sz.second << ")" << endl);
	}
	else
		bv = (*it).second;
	return bv;
}

bt_type bt_API::create_int_sort(pair< unsigned, SORT > sz) {
	bt_type ut;
	bt_IntUtM::iterator it = m_sz_to_ut.find(sz);
	if (it == m_sz_to_ut.end()) {
		if (sz.second.type == bvtype || sz.second.type == inttype) {
			if (sz.first == 1)
				ut = boolector_bool_sort(g_ctx);
			else {
				bt_loge("unsupported");
			}
		}
		else if (sz.second.type == arraytype) {
			SORT& d = sz.second.args.front();
			SORT& r = sz.second.args.back();
			bt_type dt = create_int_sort(make_pair(d.sz, d));
			bt_type rt = create_int_sort(make_pair(r.sz, r));
			ut = boolector_array_sort(g_ctx, dt, rt);
		}
		else {
			AVR_LOG(11, 0, "unsupported sort: " << sz.second.type << endl);
			assert(0);
		}
		m_sz_to_ut.insert(make_pair(sz, ut));
		AVR_LOG(11, 3, "inserting ut var type: " << print_type(ut) << " (sz = " << sz.first << ", " << sz.second << ")" << endl);
	}
	else
		ut = (*it).second;
	return ut;
}

bt_expr bt_API::create_bv_var(std::string name, pair< unsigned, SORT > sz) {
	bt_expr d;
	bt_StringToDecl::iterator tit = m_var_decs.find(name);
	if (tit == m_var_decs.end()) {
		bt_type bv = create_bv_sort(sz);
		if (sz.second.type == bvtype)
			d = boolector_var(g_ctx, bv, name.c_str());
		else if (sz.second.type == arraytype)
			d = boolector_array(g_ctx, bv, name.c_str());
		else {
			bt_loge("unsupported");
		}
		m_var_decs[name] = d;
		AVR_LOG(11, 3, "creating conc var: " << print_term(d) << " (sz = " << sz.first << ", " << sz.second << ")" << endl);
	}
	else {
		d = (*tit).second;
	}
	return d;
}

bt_expr bt_API::create_int_var(std::string name, pair< unsigned, SORT > sz) {
	bt_expr d;
	bt_StringToDecl::iterator tit = m_var_decs.find(name);
	if (tit == m_var_decs.end()) {
		bt_type ut = create_int_sort(sz);
		d = boolector_var(g_ctx, ut, name.c_str());
		m_var_decs[name] = d;
		AVR_LOG(11, 3, "creating ut var: " << print_term(d) << " (sz = " << sz.first << ", " << sz.second << ")" << endl);
	}
	else {
		d = (*tit).second;
	}
	return d;
}

bt_expr bt_API::create_bool_var(std::string name) {
	bt_expr d;
	bt_StringToDecl::iterator tit = m_var_decs.find(name);
	if (tit == m_var_decs.end()) {
		bt_type bt = boolector_bool_sort(g_ctx);
		d = boolector_var(g_ctx, bt, name.c_str());
		m_var_decs[name] = d;
		AVR_LOG(11, 3, "creating bool var: " << print_term(d) << endl);
	}
	else {
    d = (*tit).second;
	}
	return d;
}

bt_expr_ptr bt_API::en_implies(bt_expr_ptr ye) {
	return ye;
}

void bt_API::force(Inst* e) {
	if (m_mapper->fetch_var(e) == TheoryMapper::BV_VAR) {
		add_force_constraint(en_implies(e->bt_node.solv_var(get_vIdx())), "forcing for BV", e);
	}
	else if (m_mapper->fetch_var(e) == TheoryMapper::BOOL_VAR) {
		add_force_constraint(en_implies(e->bt_node.solv_var(get_vIdx())), "forcing for BOOL", e);
	}
	else if (m_mapper->fetch_var(e) == TheoryMapper::EUF_VAR) {
		assert(0);
	}
	else {
		assert(0);
	}
}

bt_expr bt_API::force_wo_add(Inst* e) {
	if (m_mapper->fetch_var(e) == TheoryMapper::BV_VAR) {
		return en_implies(e->bt_node.solv_var(get_vIdx()));
	}
	else if (m_mapper->fetch_var(e) == TheoryMapper::BOOL_VAR) {
		return en_implies(e->bt_node.solv_var(get_vIdx()));
	}
	else if (m_mapper->fetch_var(e) == TheoryMapper::EUF_VAR) {
		assert(0);
	}
	else {
		assert(0);
	}
}

void bt_API::add_force_constraint(bt_expr_ptr y, std::string comment, Inst*e) {
	if (y == BT_INVALID_EXPR) {
		cout << *e << endl;
		cout << e->get_size() << endl;
		cout << m_abstract << endl;
		cout << comment << endl;
		cout << get_vIdx() << endl;
		cout << get_cIdx() << endl;
		assert(0);
	}
	if (e != 0) {
		AVR_LOG(11, 3, "     adding constraints (" << comment << "): " << print_term(y) << " for " << *e << endl);
	}
	else {
		AVR_LOG(11, 3, "     adding constraints (" << comment << "): " << print_term(y) << endl);
	}
	if (y != m_b1) {
		bool add = true;
#ifdef EN_BMC
		if (Config::g_bmc_en) {
			add = false;
			boolector_assert(g_ctx, y);
		}
#endif
		if (add)
			m_assertions.push_back(y);
	}
	m_gateList.push_back(make_pair(e, y));
}

void bt_API::add_constraint(bt_expr_ptr y, std::string comment, Inst*e, bool storeC) {
	if (y == BT_INVALID_EXPR) {
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
			e->bt_node.bt_constraints[cIdx].push_back(y);
			AVR_LOG(11, 2, "     storing (" << comment << "): " << print_term(y) << " for " << *e << endl);
			g_gateList.push_back(make_pair(e, y));
		}
		else {
			AVR_LOG(11, 3, "     adding constraints (" << comment << "): " << print_term(y) << " for " << *e << endl);
		}
	}
	else {
		AVR_LOG(11, 3, "     adding constraints (" << comment << "): " << print_term(y) << endl);
	}
}

void bt_API::s_assert_constraints(bt_expr_ptr indVar, bool reset) {
	int sz = m_constraints.size();
	if (sz != 0) {
		if (indVar == BT_INVALID_EXPR) {
			for (auto& ye: m_constraints) {
				AVR_LOG(11, 8, "(assert " << print_term(ye) << " )" << endl);
				boolector_assert(g_ctx, ye);
			}
		}
		else {
			for (auto& c: m_constraints) {
				bt_expr_ptr ye = boolector_implies(g_ctx, indVar, c);
				AVR_LOG(11, 8, "(assert " << print_term(ye) << " )" << endl);
				boolector_assert(g_ctx, ye);
			}
		}
		m_query_sz += sz;
		if (reset)
			m_constraints.clear();
	}
}

int bt_API::s_assert_constraint(bt_expr_ptr ye) {
  AVR_LOG(17, 7, "(assert " << print_term(ye) << " )" << endl);
	boolector_assert(g_ctx, ye);
	m_query_sz += 1;
	return 0;
}

bt_expr_ptr bt_API::create_bt_number(NumInst* num) {
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
			bt_type bv = create_bv_sort(make_pair(sz, num->get_sort()));
//			cout << "creating b5 number: " << *num << endl;
			string n = num->get_mpz()->get_str(16);
			bt_expr_ptr c = boolector_consth(g_ctx, bv, n.c_str());
			return c;
		}
	}
	else if (num->get_sort_type() == inttype) {
		bt_loge("unsupported");
	}
	else {
		cout << *num << endl;
		assert(0);
	}
}

void bt_API::add_yices_func(bt_expr& var, std::string op, bool pred, bt_expr_list& ch, Ints& sz, Inst* e) {
	assert(m_abstract);
	bt_expr func;
	pair <Inst*, string> typeKey = make_pair(e, op);
	bt_InstToFuncDecl::iterator tit = m_func_decs.find(typeKey);
	if (tit == m_func_decs.end()) {
		ostringstream str;
		str << op;
		str << "_" << e->get_size();
		bt_expr_list::iterator chIt = ch.begin();
		for (Ints::iterator it = sz.begin(), end_it = sz.end(); it != end_it; ++it, ++chIt) {
			str << "_" << *it;
		}

		op = str.str();
		bt_ftype_ptr funct;
		bt_StringToFunctM::iterator it = m_funct.find(op);
		if (it == m_funct.end()) {
			bt_type target = boolector_get_sort(g_ctx, var);
			bt_type domain[ch.size()];
			unsigned i = 0;
			for (bt_expr_list::iterator it = ch.begin(), end_it = ch.end(); it != end_it; ++it) {
				bt_expr_ptr tmp = *it;
				domain[i] = boolector_get_sort(g_ctx, tmp);
				i++;
			}
			bt_type functt = boolector_fun_sort(g_ctx, domain, ch.size(), target);
			funct = boolector_uf(g_ctx, functt, op.c_str());
			m_funct.insert(make_pair(op, funct));
			AVR_LOG(11, 3, "inserting function template: " << print_ftype(funct) << " of type " << print_type(functt) << endl);
		}
		else
			funct = (*it).second;

		InstL::const_iterator cit = e->get_children()->begin();
		bt_expr args[ch.size()];
		unsigned i = 0;
		for (bt_expr_list::iterator it = ch.begin(), end_it = ch.end(); it != end_it; ++it, ++i, ++cit) {
			args[i] = *it;
		}
		func = boolector_apply(g_ctx, args, ch.size(), funct);
		m_func_decs[typeKey] = func;
		if (func == BT_INVALID_EXPR) {
			cout << *e << endl;
			cout << "present type: " << (it != m_funct.end()) << endl;
			{
				int i = 0;
				for (auto& ch: (*e->get_children())) {
					cout << i++ << ": " << *ch << endl;
					ch->bt_node.print();
				}
			}
		}
		assert (func != BT_INVALID_EXPR);
		AVR_LOG(11, 3, "creating function application: " << print_term(func) << " of type " << print_ftype(funct) << endl);
	}
	else {
		func = (*tit).second;
	}
	assert (var != BT_INVALID_EXPR);

	if (!allow_flatten)
		var = func;
	else
		add_constraint(boolector_eq(g_ctx, var, func), "func link", e);
}

void bt_API::inst2yices(Inst*e, bool bvAllConstraints) {
	unsigned cIdx = get_cIdx();
	if (e->bt_node.get_bt_key(cIdx) == BT_INFO::st_bt_key) {
		return;
	}
	assert(e != 0);
	assert(m_mapper);

	// do the children first.
	bt_expr_list y_ch;
	const InstL* ch = e->get_children();
	Ints s_sz;
	unsigned yIdx = get_vIdx();
	bool reuseAllowed = true && (queryType != prt);

// unsupported for now
//	/// Disable recursion inside an internal wire in case of concrete query
//	if (!m_abstract && !bvAllConstraints) {
//		WireInst* w = WireInst::as(e);
//		if (w) {
//			Inst* port = w->get_port();
//			assert (port);
//#ifndef SUBSTITUTE
//			reuseAllowed = false;
//			if (!allow_all) {
//				{
//					if (w->is_connected(WireInst::get_connect_key())) {
//					}
//					else {
//						ch = 0;
////						cout << "(ignoring wire: " << *w << ")" << endl;
//					}
//				}
//			}
//#endif
//		}
//	}

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
	e->bt_node.set_key(cIdx);
	bt_expr& yvar = e->bt_node.bt_var[yIdx];
	if (!(e->bt_node.solv_vset(yIdx))) {
		string name = get_bt_name(e);
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
		assert(yvar != BT_INVALID_EXPR);
		e->bt_node.bt_vset[yIdx] = true;
	}

	if (ch) {
		for (auto& v: *ch) {
			inst2yices(v);
			y_ch.push_back(v->bt_node.solv_var(yIdx));
			s_sz.push_back(v->get_size());
			assert(y_ch.back() != BT_INVALID_EXPR);
			assert(v->bt_node.solv_vset(yIdx));
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

	if (reuseAllowed && e->bt_node.solv_vset(yIdx)) {
		if (e->bt_node.solv_cset(cIdx)) {
			/// Constraints already set, use stored constraints.
	//		cout << "reusing stored constraints " << *e << " nC: " << e->y_constraints[yIdx].size() << endl;
			for (auto& c : e->bt_node.solv_constraints(cIdx)) {
				add_constraint(c, "reusing stored constraints", e, false);
			}
			return;
		}
	}
	e->bt_node.bt_cset[cIdx] = true;

	switch (e->get_type())
	{
	case Num: {
		NumInst* num = NumInst::as(e);
		assert(num != 0);

		if (m_mapper->fetch_var(e) == TheoryMapper::BV_VAR) {
			bt_expr_ptr c = create_bt_number(num);
			if (!allow_flatten)
				yvar = c;
			else
				add_constraint(boolector_eq(g_ctx, yvar, c), "constant link", e);

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
				bt_expr_ptr res = y_ch.front();
				if (!allow_flatten)
					yvar = res;
				else
					add_constraint(boolector_eq(g_ctx, yvar, res), "port connection", e);
			}
		}
		else if (m_mapper->fetch_op(e) == TheoryMapper::EUF_OP || m_mapper->fetch_op(e) == TheoryMapper::CLU_OP) {
			assert(y_ch.size() == 1);
			bt_expr_ptr res = y_ch.front();
			if (!allow_flatten)
				yvar = res;
			else
				add_constraint(boolector_eq(g_ctx, yvar, res), "port connection", e);
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
		bt_expr res = BT_INVALID_EXPR;
		string opstr = "";
		bool interpreted = false;
		bt_expr_list::iterator it = y_ch.begin(), it2 = y_ch.begin(), end_it = y_ch.end();
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
			bt_expr log = BT_INVALID_EXPR;
			switch (o) {

			case OpInst::LogNot: {
				if (m_mapper->fetch_var(e) == TheoryMapper::BV_VAR) {
					log = boolector_not(g_ctx, *it);
				} else if (m_mapper->fetch_var(e) == TheoryMapper::BOOL_VAR) {
					log = boolector_not(g_ctx, *it);
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
				log = (*it);
				for (bt_expr_list::iterator argIt = it2; argIt != end_it; argIt++) {
					log = (o == OpInst::LogAnd) || (o == OpInst::LogNand) ?
							boolector_and(g_ctx, log, (*argIt)) : boolector_or(g_ctx, log, (*argIt));
				}
				if((o == OpInst::LogNor) || (o == OpInst::LogNand)){
					log = boolector_not(g_ctx, log);
				}
				interpreted = true;
			}
				break;
			case OpInst::LogXNor:
			case OpInst::LogXor: {
				log = (*it);
				for (bt_expr_list::iterator argIt = it2; argIt != end_it; argIt++) {
					log = (o == OpInst::LogXor) ?
							boolector_xor(g_ctx, log, (*argIt)) : boolector_xnor(g_ctx, log, (*argIt));
				}
				interpreted = true;
			}
				break;
			case OpInst::Eq:{
				assert(y_ch.size() == 2);
				log = boolector_eq(g_ctx, *it, *it2);
				interpreted = true;
			}
				break;
			case OpInst::NotEq: {
				assert(y_ch.size() == 2);
				log = boolector_ne(g_ctx, *it, *it2);
				interpreted = true;
			}
				break;
			case OpInst::ArrayConst: {
				if (m_mapper->fetch_var(e) == TheoryMapper::BV_VAR) {
					bt_type functt = create_bv_sort(make_pair(e->get_size(), e->get_sort()));

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
					bool initialized = false;
					for (int i = 0; i <= maxaddress; i++) {
						string v = value.substr(i*size, size);
						Inst* address = NumInst::create(maxaddress - i, width, SORT());
						Inst* data = NumInst::create(v, size, 2, SORT());
						bt_expr_ptr b = create_bt_number(NumInst::as(data));
						if (i == 0) {
							initialized = true;
							log = boolector_const_array(g_ctx, functt, b);
//							cout << "constarray: " << print_term(log) << endl;
						}
						else {
							bt_expr_ptr a = create_bt_number(NumInst::as(address));
							log = boolector_write(g_ctx, log, a, b);
						}
					}
					assert(initialized);
//					cout << "updatearray: " << print_term(log) << endl;
				} else if (m_mapper->fetch_var(e) == TheoryMapper::EUF_VAR) {
					bt_loge("unsupported");
				} else {
					assert(0);
				}
				assert(log);
				interpreted = true;
			}
				break;
			case OpInst::ArraySelect: {
				assert(y_ch.size() == 2);
				log = boolector_read(g_ctx, *it, *it2);
				assert(log);
				interpreted = true;
			}
				break;
			case OpInst::ArrayStore: {
				bt_expr a = *it;
				bt_expr b = *it2;
				it2++;
				bt_expr c = *it2;
				log = boolector_write(g_ctx, a, b, c);
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

					bt_expr_ptr y1 = *it;
					bt_expr_ptr y2 = *it2;
					Inst* c1 = e->get_children()->front();
					Inst* c2 = e->get_children()->back();
					int c1Sz = c1->get_size();
					int c2Sz = c2->get_size();

					if (c1Sz < c2Sz)
						y1 = boolector_uext(g_ctx, y1, (c2Sz - c1Sz));
					if (c2Sz < c1Sz)
						y2 = boolector_uext(g_ctx, y2, (c1Sz - c2Sz));

					switch (o) {
					case OpInst::Gr:
						log = boolector_ugt(g_ctx, y1, y2);
						break;
					case OpInst::SGr:
						log = boolector_sgt(g_ctx, y1, y2);
						break;
					case OpInst::Le:
						log = boolector_ult(g_ctx, y1, y2);
						break;
					case OpInst::SLe:
						log = boolector_slt(g_ctx, y1, y2);
						break;
					case OpInst::GrEq:
						log = boolector_ugte(g_ctx, y1, y2);
						break;
					case OpInst::SGrEq:
						log = boolector_sgte(g_ctx, y1, y2);
						break;
					case OpInst::LeEq:
						log = boolector_ulte(g_ctx, y1, y2);
						break;
					case OpInst::SLeEq:
						log = boolector_slte(g_ctx, y1, y2);
						break;
					case OpInst::IntLe: {
						bt_loge("unsupported");
					}
						break;
					case OpInst::IntLeEq: {
						bt_loge("unsupported");
					}
						break;
					case OpInst::IntGr: {
						bt_loge("unsupported");
					}
						break;
					case OpInst::IntGrEq: {
						bt_loge("unsupported");
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
					for (bt_expr_list::iterator argIt = it2; argIt != end_it; argIt++) {
						bt_expr_ptr h = *argIt;
						res = boolector_concat(g_ctx, h, res);
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

				bt_expr_ptr a = (*it);
				Inst* c1 = e->get_children()->front();
				int outSz = e->get_size();
				int c1Sz = c1->get_size();
				if (c1Sz < outSz)
					a = boolector_uext(g_ctx, a, (outSz - c1Sz));

				switch (o) {
				case OpInst::Minus: {
					assert(y_ch.size() == 1);
					res = boolector_neg(g_ctx, a);
				}
					break;
				case OpInst::BitWiseNot: {
					assert(y_ch.size() == 1);
					res = boolector_not(g_ctx, a);
				}
					break;
				case OpInst::IntFloor: {
					bt_loge("unsupported");
				}
					break;
				case OpInst::IntMinus: {
					bt_loge("unsupported");
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
					bt_expr_ptr b = (*it2);

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
							a = boolector_uext(g_ctx, a, (maxSz - outSz));
						}
						if (c2Sz < maxSz)
						{
							b = boolector_uext(g_ctx, b, (maxSz - c2Sz));
						}
					}

					switch (o) {
					case OpInst::Add:{
						assert(y_ch.size() == 2);
						res = boolector_add(g_ctx, a, b);
					}break;
					case OpInst::Sub: {
						assert(y_ch.size() == 2);
						res = boolector_sub(g_ctx, a, b);
					}
						break;
					case OpInst::Mult:{
						assert(y_ch.size() == 2);
						res = boolector_mul(g_ctx, a, b);
					}
						break;
					case OpInst::Div:{
						assert(y_ch.size() == 2);
						res = boolector_udiv(g_ctx, a, b);
					}
						break;
					case OpInst::SDiv:{
						assert(y_ch.size() == 2);
						res = boolector_sdiv(g_ctx, a, b);
					}
						break;
					case OpInst::Rem:{
						assert(y_ch.size() == 2);
						res = boolector_urem(g_ctx, a, b);
					}
						break;
					case OpInst::SRem:{
						assert(y_ch.size() == 2);
						res = boolector_srem(g_ctx, a, b);
					}
						break;
					case OpInst::SMod:{
						assert(y_ch.size() == 2);
						res = boolector_smod(g_ctx, a, b);
					}
						break;
					case OpInst::BitWiseAnd: {
						assert(y_ch.size() == 2);
						res = boolector_and(g_ctx, a, b);
					}
						break;
					case OpInst::BitWiseNand: {
						assert(y_ch.size() == 2);
						res = boolector_nand(g_ctx, a, b);
					}
						break;
					case OpInst::BitWiseOr: {
						assert(y_ch.size() == 2);
						res = boolector_or(g_ctx, a, b);
					}
						break;
					case OpInst::BitWiseNor: {
						assert(y_ch.size() == 2);
						res = boolector_nor(g_ctx, a, b);
					}
						break;
					case OpInst::BitWiseXor: {
						assert(y_ch.size() == 2);
						res = boolector_xor(g_ctx, a, b);
					}
						break;
					case OpInst::BitWiseXNor: {
						assert(y_ch.size() == 2);
						res = boolector_xnor(g_ctx, a, b);
					}
						break;
					case OpInst::ShiftL: {
						assert(y_ch.size() == 2);
						res = boolector_sll(g_ctx, a, b);
					}
					  break;
					case OpInst::ShiftR: {
						assert(y_ch.size() == 2);
						res = boolector_srl(g_ctx, a, b);
					}
						break;
					case OpInst::AShiftR: {
						assert(y_ch.size() == 2);
						res = boolector_sra(g_ctx, a, b);
					}
						break;
					case OpInst::Sext:
					case OpInst::Zext: {
						assert(y_ch.size() == 2);
						bt_expr_ptr a2 = (*it);
						InstL::const_iterator ve_it = ch->begin();
						int amount = e->get_size() - (*ve_it)->get_size();
						assert(amount >= 0);
						if (o == OpInst::Sext)
							res = boolector_sext(g_ctx, a2, amount);
						else
							res = boolector_uext(g_ctx, a2, amount);
					}
						break;
					case OpInst::IntAdd: {
						bt_loge("unsupported");
					}
						break;
					case OpInst::IntSub: {
						bt_loge("unsupported");
					}
						break;
					case OpInst::IntMult: {
						bt_loge("unsupported");
					}
						break;
					case OpInst::IntDiv: {
						bt_loge("unsupported");
					}
						break;
					case OpInst::IntMod: {
						bt_loge("TODO");
					}
						break;
					default:
						assert(0);
					}
					if (e->get_sort_type() == bvtype) {
						if (outSz < maxSz)
							res = boolector_slice(g_ctx, res, (outSz - 1), 0);
					}
				}
					break;

				case OpInst::AddC:
				case OpInst::AShiftL:
					assert(0); // for now.

				case OpInst::ReductionAnd:
				case OpInst::ReductionNand: {
					assert(y_ch.size() == 1);
					res = boolector_redand(g_ctx, a);
					if (o == OpInst::ReductionNand)
						res = boolector_not(g_ctx, res);
				}
					break;
				case OpInst::ReductionOr:
				case OpInst::ReductionNor: {
					assert(y_ch.size() == 1);
					res = boolector_redor(g_ctx, a);
					if (o == OpInst::ReductionNor)
						res = boolector_not(g_ctx, res);
				}
					break;
				case OpInst::ReductionXor:
				case OpInst::ReductionXNor: {
					assert(y_ch.size() == 1);
					res = boolector_redxor(g_ctx, a);
					if (o == OpInst::ReductionXNor)
						res = boolector_not(g_ctx, res);
				}
					break;
				case OpInst::VRotateR:{
					bt_loge("TODO");
				}
				  break;
				case OpInst::VRotateL:{
					bt_loge("TODO");
				}
				  break;
				case OpInst::VShiftL:
				case OpInst::VShiftR:
				case OpInst::VAShiftL:
				case OpInst::VAShiftR:
				case OpInst::VEx:{
					bt_loge("TODO");
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
			bt_expr_list::iterator it3 = it2;
			it3++;
			bt_expr_ptr cond = (*it);
			bt_expr_ptr y1 = (*it2);
			bt_expr_ptr y2 = (*it3);
			res = boolector_cond(g_ctx, cond, y1, y2);
			interpreted = true;
		}
			break;
		default:
			AVR_COUT << o << endl;
			assert(0);
		}
		if (m_mapper->fetch_op(e) == TheoryMapper::BV_OP) {
			assert(yvar != BT_INVALID_EXPR);
			assert(res != BT_INVALID_EXPR);
			if (!boolector_is_equal_sort(g_ctx, yvar, res)) {
				cout << "inconsistent term types for node " << *e << endl;
				cout << "yvar: " << print_term(yvar) << " of type " << print_type(boolector_get_sort(g_ctx, yvar)) << endl;
				cout << "res: " << print_term(res) << " of type " << print_type(boolector_get_sort(g_ctx, res)) << endl;
				assert(0);
			}

			if (!allow_flatten)
				yvar = res;
			else
				add_constraint(boolector_eq(g_ctx, yvar, res), "result of a bv op", e);
		}
		else if (m_mapper->fetch_op(e) == TheoryMapper::EUF_OP || m_mapper->fetch_op(e) == TheoryMapper::CLU_OP) {
			if (interpreted) {
				assert(yvar != BT_INVALID_EXPR);
				assert(res != BT_INVALID_EXPR);
				if (!boolector_is_equal_sort(g_ctx, yvar, res)) {
					cout << "inconsistent term types for node " << *e << endl;
					cout << "yvar: " << print_term(yvar) << " of type " << print_type(boolector_get_sort(g_ctx, yvar)) << endl;
					cout << "res: " << print_term(res) << " of type " << print_type(boolector_get_sort(g_ctx, res)) << endl;
					assert(0);
				}

				if (!allow_flatten)
					yvar = res;
				else
					add_constraint(boolector_eq(g_ctx, yvar, res), "interpreted operator constraint for EUF", e);
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
			bt_expr_ptr res = boolector_slice(g_ctx, y_ch.front(), ex->get_hi(), ex->get_lo());
			assert(res != BT_INVALID_EXPR);

			if (!allow_flatten)
				yvar = res;
			else
				add_constraint(boolector_eq(g_ctx, yvar, res), "result of a bv EX", e);

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
				bt_expr_ptr a = simplified->bt_node.solv_var(get_vIdx());
				add_constraint(boolector_eq(g_ctx, yvar, a), "(partial interpretation)", e);
			}
		}
	}
#endif

	assert(yvar != BT_INVALID_EXPR);
}


};

#endif



