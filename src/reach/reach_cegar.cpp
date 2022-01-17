/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


#include "reach_core.h"
#include <execinfo.h>	// to dump call stacks (backtrace, backtrace_symbols)

namespace reach
{

#ifdef REFRESH_FRAME_SOLVERS_QUERY
int Reach::FRAME_SOLVER::maxQ = REFRESH_FRAMES_QUERY_THRESHOLD;
#endif
int Reach::FRAME_SOLVER::numResetFrames = 0;


int Reach::num_scalls_sat_ct = 0;
int Reach::num_scalls_unsat_ct = 0;

int Reach::num_scalls_sat_mus_sim = 0;
int Reach::num_scalls_unsat_mus_sim = 0;
int Reach::num_scalls_sat_muses_dpr = 0;
int Reach::num_scalls_unsat_muses_dpr = 0;
int Reach::num_scalls_sat_muses_reach = 0;
int Reach::num_scalls_unsat_muses_reach = 0;

int Reach::num_scalls_sat_core_muses_reach = 0;
int Reach::num_scalls_unsat_core_muses_reach = 0;
int Reach::num_scalls_sat_min_muses_reach = 0;
int Reach::num_scalls_unsat_min_muses_reach = 0;

int Reach::num_scalls_sat_correctness = 0;
int Reach::num_scalls_unsat_correctness = 0;


int Reach::sz_hard_core_muses_reach = 0;
int Reach::sz_soft_core_muses_reach = 0;
int Reach::sz_out_core_muses_reach = 0;
int Reach::sz_hard_min_muses_reach = 0;
int Reach::sz_soft_min_muses_reach = 0;
int Reach::sz_out_min_muses_reach = 0;
int Reach::num_muses_reach = 0;

int Reach::num_path_constraints_taken = 0;
int Reach::num_path_constraints = 0;

int Reach::num_sim_iterations = 0;

int Reach::num_local_eq = 0;
int Reach::num_local_eq_sig = 0;
int Reach::num_local_eq_num = 0;
int Reach::num_local_eq_uf = 0;

int Reach::refine_flush_count = 0;
long long Reach::refine_flush_len_acext = 0;
long long Reach::refine_flush_level = 0;
long long Reach::refine_flush_frames = 0;
long long Reach::refine_flush_clauses = 0;

map<int, int> Reach::num_excc_prop = map<int, int>();
map<int, int> Reach::num_excc_all  = map<int, int>();


void Reach::retrieve_ab_sol(Solver*solver, bool init_visit)
{
  if (init_visit)
  {
    Inst::inc_rkey();
    Inst::set_ba_idx(solver->m_ba_idx);
//    cout << "Updating rkey: " << Inst::get_rkey() << " (solver: " << Inst::get_bIdx() << ")" << endl;
    Inst::init_visit();
    Solver::solv_values.clear();

		_min_term.clear();
  }
}

void Reach::retrieve_ab_sol(Solver* solver, Inst* e, InstS& relSig, InstS& relConst, set< string >& relUFtype)
{
  assert(e != 0);

//    cout<<"retrieving for: "<<*e<<endl;

  assert(e != 0);
  if (e->get_visit3())
    return;
  e->set_visit3();

#ifdef INTERPRET_EX_CC
  if (solver->m_allow_ex_cc) {
		if (Config::g_uf_mult_only || (_abstract_mapper->fetch_op(e) == Solver::TheoryMapper::EUF_OP) ||
				(_abstract_mapper->fetch_op(e->t_simple) == Solver::TheoryMapper::EUF_OP)) {
      Inst* simplified = e->t_simple;
      if (e != simplified)
        retrieve_ab_sol(solver, simplified, relSig, relConst, relUFtype);
    }
  }
#endif


  // now do the children
  const InstL* ch = e->get_children();

	if (e->get_size() == 1) {
		if(e->get_type() == Sig) {
			_min_term.all_predicates.push_back(e);
		}
		else if (e->get_type() == Wire) {
			Inst* port = e->get_port();
				if(port->get_euf_func_name() != "0") {
				  if (!find_from_minset2(solver, e, relSig, relConst, relUFtype))
				  	return;
					_min_term.all_predicates.push_back(e);
				}
		}
	}
	else {
		if(e->get_type() == Sig) {
			_min_term.all_terms[make_pair(e->get_size(), e->get_sort())].push_back(e);
		}
		else if(e->get_type() == Num) {
			_min_term.all_terms[make_pair(e->get_size(), e->get_sort())].push_back(e);
		}
		else if (e->get_type() == Wire) {
			Inst* port = e->get_port();
			if(port->get_euf_func_name() != "0") {
			  if (!find_from_minset2(solver, e, relSig, relConst, relUFtype))
			  	return;
				_min_term.all_terms[make_pair(e->get_size(), e->get_sort())].push_back(e);
			}
		}
	}

  if (ch) {
		for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it)
			retrieve_ab_sol(solver, *it, relSig, relConst, relUFtype);
  }
}

void Reach::retrieve_cex_val(Inst* e, Solver*solver, bool abstract, bool init_visit, bool evalSimple)
{
  assert(e != 0);
  if (init_visit)
  {
    Inst::inc_rkey();
    Inst::set_ba_idx(solver->m_ba_idx);
//    cout << "Updating rkey: " << Inst::get_rkey() << " (solver: " << Inst::get_bIdx() << ")" << endl;

    Inst::init_visit();
    Solver::solv_values.clear();

		if (abstract)
			_min_term.clear();
		else
			_min_term_c.clear();
  }

//    cout<<"retrieving for: "<<*e<<endl;

  assert(e != 0);
  assert(solver != 0);
  if (e->get_visit())
    return;
  e->set_visit();

#ifdef INTERPRET_EX_CC
  if (Config::g_uf_mult_only || solver->m_allow_ex_cc && abstract && evalSimple)
  {
		if ((_abstract_mapper->fetch_op(e) == Solver::TheoryMapper::EUF_OP) ||
				(_abstract_mapper->fetch_op(e->t_simple) == Solver::TheoryMapper::EUF_OP)) {
      Inst* simplified = e->t_simple;
      if (e != simplified)
        retrieve_cex_val(simplified, solver, abstract, false, evalSimple);

      /// Test
//        const InstL* ch = op_cc->get_children();
//        if (ch)
//        {
//          unsigned s_loc = 0, e_loc = 0;
//          for (InstL::const_iterator cit = ch->begin(); cit != ch->end(); ++cit)
//          {
//            Inst *tve = *cit;
//            unsigned size = tve->get_size();
//            s_loc = e_loc;
//            e_loc += size;
//            Inst* ex_tve = ExInst::create(op_cc, (e_loc - 1), s_loc);
//            retrieve_cex_val(ex_tve, solver, abstract, false);
//          }
//        }
    }
  }
#endif

  // now do the children
  const InstL* ch = e->get_children();

  if (!abstract && !solver->allow_all_wires())
  {
    WireInst* w = WireInst::as(e);
    if (w)
    {
      Inst* port = w->get_port();
      assert (port);
#ifndef SUBSTITUTE
//      if (w->get_name().length() > 5 && w->get_name().substr(w->get_name().length() - 5) == "$next")
//      {
//        ch = 0;
//      }
//      else
      {
        if (w->is_connected(WireInst::get_connect_key()))
        {

        }
        else {
//        	cout << "skipping: " << *w << endl;
        	return;
        }
      }
#endif

//      WireInst* w = WireInst::as(e);
//      if (w)
//      {
//        if (w->is_connected(WireInst::get_connect_key()))
//        {
//          ch = 0;
//
//          Inst* rhs = w->get_connection();
//          retrieve_cex_val(rhs, solver, abstract, false, bvAllConstraints);
//        }
//      }
    }
  }

  bool dontcare = false;
	if (e->get_size() == 1)
	{
		int val = INVALID_SVAL;
		bool res = solver->get_assignment(e, val);
		if (!res)
			dontcare = true;
//		assert (val != INVALID_SVAL);
	}
	else
	{
		mpz_class* val;
		bool res = solver->get_assignment(e, val);
		if (!res)
			dontcare = true;
	}

	if (!dontcare) {
		if (abstract)
		{
			if (e->get_size() == 1)
			{
				int val = e->get_bval();
				assert (val != INVALID_SVAL);

				if(e->get_type() == Sig)
				{
					if (val == 1)
					{
//						_min_term.trueConditions.push_back(e);
						_min_term.s.predicates.push_back(e);
					}
					else if (val == 0)
					{
//						_min_term.falseConditions.push_back(e);
						Inst* ne = OpInst::create(OpInst::LogNot, e);
						ne->set_bval(1);
						_min_term.s.predicates.push_back(ne);
					}
					else
					{
	//					cout << "e: " << *e << endl;
	//					assert(0);
					}
				}
				else if(e->get_type() == Op || e->get_type() == Ex)
				{
//				assert(op);
//				Inst* tve = op;
//				Inst* w = op->get_wire();
//				if (w != NULL)
//					tve = w;
//
//
//				if (val == 1) {
//					_min_term.trueConditions.push_back(tve);
//
//          if(e->get_euf_func_name() != "0")
//            _min_term.s.predicates.push_back(tve);
//				}
//				else if (val == 0) {
//					_min_term.falseConditions.push_back(tve);
//
//          if(e->get_euf_func_name() != "0")
//          {
//            Inst* ne = OpInst::create(OpInst::LogNot, tve);
//            ne->set_bval(1);
//            _min_term.s.predicates.push_back(ne);
//          }
//				}
//				else
//				{
////					cout << "e: " << *e << endl;
////					assert(0);
//				}
				}
				else if (e->get_type() == Wire)
				{
					Inst* port = e->get_port();
					if (val == 1)
					{
//						_min_term.trueConditions.push_back(e);

						if(port->get_euf_func_name() != "0")
							_min_term.s.predicates.push_back(e);
					}
					else if (val == 0)
					{
//						_min_term.falseConditions.push_back(e);

						if(port->get_euf_func_name() != "0")
						{
							Inst* ne = OpInst::create(OpInst::LogNot, e);
							ne->set_bval(1);
							_min_term.s.predicates.push_back(ne);
						}
					}
					else
					{
	//					cout << "e: " << *e << endl;
	//					assert(0);
					}

	//				if (val != 0 && val != 1)
	//				{
	//					cout << "e: " << *e << endl;
	//					assert(0);
	//				}
				}

				if (!e->find_next())
				{
					bool preCondFlag = false;
					/// If it is a sinle bit signal
					if (e->get_type() == Sig)
						preCondFlag = true;
					else
					{
						OpInst* op = OpInst::as(e);
						if(op)
						{
							/// If it is a ==/!=
							if (op->get_op() == OpInst::Eq || op->get_op() == OpInst::NotEq)
								preCondFlag = true;
							/// If it is a UP
							else if(e->get_euf_func_name() != "0")
								preCondFlag = true;
						}
					}

					if (preCondFlag)
					{
						if (val == 1);
//							_min_term.presentConditions.insert(e);
						else if (val == 0)
						{
							Inst* negE = OpInst::create(OpInst::LogNot, e);
							negE->set_bval(1);
//							_min_term.presentConditions.insert(negE);
						}
					}
				}
			}
			else
			{
				mpz_class* valp = e->get_ival();
				assert (valp != INVALID_SMPZ);
				mpz_class val = *valp;

				if(e->get_type() == Sig)
				{
//					_min_term.partition[make_pair(e->get_size(), val)].push_back(e);
					_min_term.s.partitions[make_pair(e->get_size(), e->get_sort())][val].push_back(e);
				}
				else if(e->get_type() == Num)
				{
//					_min_term.partition[make_pair(e->get_size(), val)].push_back(e);
					_min_term.s.partitions[make_pair(e->get_size(), e->get_sort())][val].push_back(e);
				}
				else if(e->get_type() == Op || e->get_type() == Ex)
				{
	//			  assert(op);
	//				Inst* tve = op;
	//				Inst* w = op->get_wire();
	//				if (w != NULL)
	//					tve = w;
	//
	//        _min_term.partition[make_pair(e->get_size(), val)].push_back(tve);
	//
	//        if(e->get_euf_func_name() != "0")
	//          _min_term.s.partitions[e->get_size()][val].push_back(tve);
				}
				else if (e->get_type() == Wire)
				{
//					_min_term.partition[make_pair(e->get_size(), val)].push_back(e);

					Inst* port = e->get_port();
					if(port->get_euf_func_name() != "0")
						_min_term.s.partitions[make_pair(e->get_size(), e->get_sort())][val].push_back(e);
				}
			}
		}
		else
		{
			mpz_class* valp;
			if (e->get_size() == 1) {
				int valb = e->get_bval();
				assert(valb != INVALID_SVAL);
				valp = NumInst::as(NumInst::create(valb, 1, SORT()))->get_mpz();
			}
			else
				valp = e->get_ival();

			assert (valp != INVALID_SMPZ);
			if (e->get_type() == Num)
				valp = NumInst::as(e)->get_mpz();

			_min_term_c[e] = *valp;
		}
	}
	else {
		AVR_LOG(11, 2, "got don't care: " << *e << endl);
	}

  if (!dontcare && ch)
  {
  	bool done = false;
//  	OpInst* op = OpInst::as(e);
//  	if (op) {
//  		OpInst::OpType op_type = op->get_op();
//  		switch(op_type) {
//  		case OpInst::LogAnd:
//  		case OpInst::LogOr: {
//  			int eVal = e->get_bval();
//  			for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it)
//  			{
//  				retrieve_cex_val(*it, solver, abstract, false, evalSimple);
//  				int itVal = (*it)->get_bval();
//
//  				if (eVal == controlling(op_type))
//  				{
//  					if (itVal == controlling(op_type))
//  					{
//  						break;
//  					}
//  				}
//  				else
//  				{
//  				}
//  			}
//  			done = true;
//  		}break;
//  		case OpInst::Ternary: {
//  			InstL::const_iterator it = ch->begin();
//  			Inst* if_e = *(it++);
//  			Inst* then_e = *(it++);
//  			Inst* else_e = *(it++);
//				retrieve_cex_val(if_e, solver, abstract, false, evalSimple);
//
//  			int ifVal = if_e->get_bval();
//  			if (ifVal == 0) {
//  				retrieve_cex_val(else_e, solver, abstract, false, evalSimple);
//  			} else if (ifVal == 1) {
//  				retrieve_cex_val(then_e, solver, abstract, false, evalSimple);
//  			} else {
//  				assert(0);
//  			}
//  			done = true;
//			}break;
//  		}
//  	}

  	if (!done)
  	{
			for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it)
				retrieve_cex_val(*it, solver, abstract, false, evalSimple);
  	}
  }

//  REACH_COUT_A("  " << *e << " <= " << e->cex_mpz << endl);
}

void Reach::refine(InstL& hardConstraints, ABSTRACT_CUBE& abCube, Inst *top_wo_ref, bool ab) {
	// 0: not using CAMUS, 1: CAMUS with the option, one mus, 2: CAMUS with the option, all mus
	AVR_LOG(4, 1, "Trying refining --->" << endl);
	struct rusage usage;
	struct timeval start_time, end_time;
	long long time_diff;

	int camus_type = 1;
	if (_config->get_arg(CAMUS_GROUPS_ARG) != "0") {
		camus_type = 2;
	}

//	REACH_COUT_A("CAMUS MODE = 1" << endl);

	_refs.clear();
	_iter = 0;
	int refine_loop_idx = -1;
	AVR_LOG(4, 1, "AR loop starts - " << "refine_idx: " << _refine_idx << endl);
	while (1) { //refine()

		refine_loop_idx++;

		/// Aman
		assert (top_wo_ref != NULL);

		InstL viol;

		collect_cubes(top_wo_ref, true);
		viol = _collected_cubes;
//		if (top_wo_ref->find_next())
		{
//			viol.push_back(_ve_assume);
			for (auto& v: _all_assumptions) {
				if (Config::g_lazy_assume >= LAZY_ASSUME_L2)
					viol.push_back(v.first);
				else
					hardConstraints.push_back(v.first);
			}
			for (auto& v: _assume_T) {
				if (Config::g_lazy_assume > LAZY_ASSUME_NONE)
					viol.push_back(v.first);
				else
					hardConstraints.push_back(v.first);
			}
			if (!hardConstraints.empty()) {
				viol.push_back(OpInst::create(OpInst::LogAnd, hardConstraints));
				hardConstraints.clear();
			}
		}
//		else {
//			for (auto& v: _assumptions)
//				viol.push_back(v);
//		}

//		collect_cubes(OpInst::create(OpInst::LogAnd, hardConstraints), true);
//		for (auto& v: _collected_cubes)
//			viol.push_back(v);
//		hardConstraints.clear();

#ifndef SUBSTITUTE
		WireInst::inc_connect_key();

		AVR_LOG(4, 4, "wires:" << endl);
		for (auto& w: (*abCube.relevantWires))
		{
			AVR_LOG(4, 4, "\t" << *w << endl);

			WireInst* w_lhs = WireInst::as(w);
			assert(w_lhs);
			w_lhs->set_connect();
		}
		for (auto& w: (*abCube.relevantWiresNext))
		{
			AVR_LOG(4, 4, "\t" << *w << endl);

			WireInst* w_lhs = WireInst::as(w);
			assert(w_lhs);
			w_lhs->set_connect();
		}
		for (auto& w: _assume_wires)
		{
			AVR_LOG(4, 4, "\t" << *w << endl);

			WireInst* w_lhs = WireInst::as(w);
			assert(w_lhs);
			w_lhs->set_connect();
		}
		if (top_wo_ref->find_next()) {
			for (auto& w: _assume_Twires)
			{
				AVR_LOG(4, 4, "\t" << *w << endl);

				WireInst* w_lhs = WireInst::as(w);
				assert(w_lhs);
				w_lhs->set_connect();
			}
		}
#endif

//		viol.reverse();

//		cout << "Viol: " << viol << endl;

//		while(1)
//		{
//			if(generalize_ref_with_wires(viol) == false)
//			{
//				break;
//			}
//		}

//		retrieve_cex_val(top_wo_ref, _euf_solver, true, true);
//		evaluate_refine_relation(1, top_wo_ref, viol, true);

//		cout << "Viol: " << viol << endl;

//		if (retrieve_abst_cex()) {
//			// 			retrieve_cex_val(_prop, _euf_solver, true, true);
//			// 			eval_formula(1, _prop, true);
//
//			retrieve_cex_val(top, _euf_solver, true, true);
//
// 			if(top_wo_ref != NULL){
//				top_wo_ref->cex_val = 1;
//				top_wo_ref->cex_mpz = 1;
//				// do we need to call eval_formula()? maybe no
//				eval_formula(1, top_wo_ref, true);
//			}else{
//				top->cex_val = 1;
//				top->cex_mpz = 1;
//				eval_formula(1, top, true);
//			}
//
//			// property is trivially falsifiable!
//			if (_viol.empty()) {
//				_feas_sat_res = true;
//				return;
//			}
//
//
//#if 0
//			collect_cubes(OpInst::create(OpInst::LogAnd, _viol), true);
//			_viol.clear();
//			for (InstL::iterator it3 = _collected_cubes.begin(); it3 != _collected_cubes.end(); ++it3) {
//				_viol.push_back(*it3);
//			}
//#endif
//
//
//			//Below two statements often slow-down the performance, but I don't know why.
//			uniqify_viol(_viol);
//			// 			clean_viol(_viol);
//			assert(!_viol.empty());
//		}
		/// END

		assert(!viol.empty());

//		if (_config->get_arg(DUMP_VIOL_ARG) != "") {
//			ostringstream str;
//			str << _config->get_working_dir() << "/" << _config->get_arg(DUMP_VIOL_ARG) << "_" << _num_dp_refine << "_"
//				<< _refine_idx << "_" << _refine_seq_idx << "_" << _iter << ".txt";
//			ofstream violf;
//			access_file(violf, str.str());
//			violf << _viol;
//			//new_print(violf, _viol, true);
//			AVR_LOG(4, 6, (string("viol dumped to: ") + str.str()) << endl);
//			violf.close();
//		}

		//_new_refs.clear();
		_feas_sat_res = false;

		ofstream reff;
		ostringstream str;
		if (_config->get_arg(DUMP_REF_ARG) != "") {
			str << _config->get_working_dir() << "/" << _config->get_arg(DUMP_REF_ARG) << "_" << _num_dp_refine << "_"
				<< _refine_idx << "_" << _refine_seq_idx << "_" << _iter << ".txt";
			access_file(reff, str.str());
			AVR_LOG(4, 6, (string("ref dumped to: ") + str.str()) << endl);
		}

		//BV_BV_Mapper bv_mapper;
		InstLL muses;
		Solver* core_solver = NULL;
		int get_muses_input_size = viol.size();
		int res = 0;

		if (ab)
		{
			InstL violSub;
			violSub = viol;
			cout << "\t\t(ab input core size: " << violSub.size() << ")" << endl;
			SOLVER_AB tmpSolver(_abstract_mapper, AVR_EXTRA_IDX, true, regular);
			Solver* ab_solver = &tmpSolver;
			res = ab_solver->get_muses(AB_QUERY_TIMEOUT, hardConstraints, violSub, muses, num_scalls_sat_muses_dpr, num_scalls_unsat_muses_dpr, ab_solver);

			InstL violSub2;
			if (res == 0) {
				violSub2 = violSub;
				Inst* subV = OpInst::create(OpInst::LogAnd, violSub);
				pair< Inst*, Inst* > p = reduce_ref(subV);
				if (p.second != NumInst::create(0, 1, SORT())) {
					collect_cubes(p.second, true);
					_collected_cubes.swap(violSub);
					res = ab_solver->get_muses_2(AB_QUERY_TIMEOUT, violSub, muses, num_scalls_sat_muses_dpr, num_scalls_unsat_muses_dpr, ab_solver);
				}
			}

			if (res == 1) {
				AVR_LOG(15, 0, "\n\t\t(abstract infeasibility)" << endl);

//				if (!violSub2.empty()) {
//					Inst* ref = OpInst::create(OpInst::LogAnd, muses.front());
//					Inst* nref = OpInst::create(OpInst::LogNot, ref);
//					ab_solver->s_assert(nref);
//					InstLL muses2;
//					int res2 = ab_solver->get_muses_2(AB_QUERY_TIMEOUT, viol, muses2, num_scalls_sat_muses_dpr, num_scalls_unsat_muses_dpr, ab_solver);
//					if (res2 == 1) {
//						for (auto& mus2: muses2)
//							muses.push_back(mus2);
//					}
//					else {
//						assert(0);
//					}
//				}

//				cout << "violSub: " << violSub << endl;
//				assert(0);
			}

			if (res == 0) {
				// the given formula is SAT
				_feas_sat_res = true;
//				retrieve_cex_val(viol, ab_solver, true, true);
//	      collect_values(viol, ab_solver, true, true);
//				print_abstract_min_term();
				break;
			}
		}
		else
		{
			cout << "\t\t(bv input core size: " << viol.size() << ")" << endl;
			Solver* bv_solver = (new_conc_solver(true, AVR_BV_IDX));
			core_solver = bv_solver;
//
//			cout << "Viol: " << viol << endl;
//
//			for (InstL::iterator vit = viol.begin(); vit != viol.end();)
//			{
//				if (is_gate_consistency(*vit))
//				{
//					bv_solver->s_assert(*vit);
//					vit = viol.erase(vit);
//					continue;
//				}
//				else
//				{
//					OpInst* op = OpInst::as(*vit);
//					if (op && op->get_op() == OpInst::Eq)
//					{
//						Inst* lhs = op->get_children()->front();
//						Inst* rhs = op->get_children()->back();
//						if (lhs->get_type() == Sig && rhs->get_type() == Wire)
//						{
//							InstToInstM::iterator mit = Inst::_m_sn.find(lhs);
//							if (mit != Inst::_m_sn.end() && (*mit).second == rhs)
//							{
//								bv_solver->s_assert(*vit);
//								vit = viol.erase(vit);
//								continue;
//							}
//						}
//					}
//				}
//				vit++;
//			}
//			assert(!viol.empty());
//
//			cout << "Viol: " << viol << endl;

			//_refine_bv_solver = bv_solver;

			getrusage(RUSAGE_SELF, &usage);
			timeradd(&usage.ru_utime, &usage.ru_stime, &start_time);
			InstL dummy_list;

			AVR_LOG(4, 1, "viol (concrete check):" << viol);

#ifdef USE_Z3_CORE_BV
			z3_API solverCore(_concrete_mapper, AVR_BV_IDX, true, conc);
			core_solver = &solverCore;
#endif
//			core_solver->enable_model();
//			core_solver->need_model = true;
			res = bv_solver->get_muses(BV_QUERY_TIMEOUT, hardConstraints, viol, muses, num_scalls_sat_muses_dpr, num_scalls_unsat_muses_dpr, core_solver);

			if (res == 0) {
				// the given formula is SAT
//				Solver* mdl_solver = (new_conc_solver(false, AVR_BV_IDX, mdl));
//				mdl_solver->s_assert(viol);
//				int resNew = mdl_solver->s_check(BV_QUERY_TIMEOUT, true);
//				assert(resNew == AVR_QSAT);
//				retrieve_cex_val(viol, mdl_solver, false, true);
//	      collect_values(viol, mdl_solver, false, true);
//				print_concrete_min_term();

				_feas_sat_res = true;
				break;
			}
		}

		if (refine_loop_idx == 0)
			AVR_LOG(15, 0, (res?"UNSAT":"SAT") << endl);

		getrusage(RUSAGE_SELF, &usage);
		timeradd(&usage.ru_utime, &usage.ru_stime, &end_time);
		time_diff = Timevaldiff(&start_time, &end_time);

		int num_muses_terms = 0;
		int musIdx = 0;

		if (res)
		{
			AVR_LOG(15, 0, "\n\t\t[MUS(s)]:" << endl);
			for (InstLL::iterator it_muses2 = muses.begin(); it_muses2 != muses.end(); ++it_muses2)
			{
				musIdx++;
				num_muses_terms += it_muses2->size();
				AVR_LOG(15, 0, "\t\t[" << musIdx << "] " << *(OpInst::create(OpInst::LogAnd, (*it_muses2))) << endl);
//				cout << "\t\t[" << musIdx << "] " << (*it_muses2) << endl;

//	      SOLVER_BV tmpSolver(_concrete_mapper, AVR_EXTRA_IDX, true, mus_core);
//	      tmpSolver.assert_all_wire_constraints();
//	      tmpSolver.s_assert(*it_muses2);
//	      int res1 = tmpSolver.s_check(BV_QUERY_TIMEOUT, false);
//				cout << "res1: " << res1 << endl;
//
//	      InstL conjunct_tmp = viol;
//				collect_cubes(OpInst::create(OpInst::LogAnd, hardConstraints), true);
//				for (auto& v: _collected_cubes)
//					conjunct_tmp.push_back(v);
//				InstLL muses2;
//				int res2 = tmpSolver.get_muses_2(BV_QUERY_TIMEOUT, conjunct_tmp, muses2, num_scalls_sat_muses_dpr, num_scalls_unsat_muses_dpr, &tmpSolver);
//				cout << "res2: " << res2 << endl;
//				cout << "mus: " << muses2.front();
//				assert(0);

			}
		}

		AVR_LOG(4, 1, "bv_solver->get_muses(): " << get_muses_input_size << " => " << muses.size() << ", " << num_muses_terms << " : res = " << res << endl);
		AVR_LOG(4, 1, "bv_solver->get_muses(), runtime: " << double(time_diff)/1000000 << endl);

		int added_lemmas_cnt = 0;
		InstS set_refs;
		for (InstLL::iterator it_muses = muses.begin(); it_muses != muses.end(); ++it_muses) {
			InstL conjunction_ref = *it_muses;

			AVR_LOG(4, 6, "conjunction_ref: " << conjunction_ref << endl);

			Inst* ref = 0;
			Inst* tve_before = 0;
			if (conjunction_ref.size() == 1) {
				ref = conjunction_ref.front();

//				ref = make_lemmas(conjunction_ref);

				tve_before = OpInst::create(OpInst::LogNot, ref);
			} else if (conjunction_ref.size() > 1) {

				/// TODO: Deal with Generalize ref issues with simulation
#ifdef AVR_GENERALIZE_REF
				Inst* tve;
				tve = OpInst::create(OpInst::LogAnd, conjunction_ref);
				tve = OpInst::create(OpInst::LogNot, tve);
				tve_before = tve;

				while(1){
					if(generalize_ref(conjunction_ref) == false){
						ref = OpInst::create(OpInst::LogAnd, conjunction_ref);
						#ifdef AVR_DUMP_ACCUM_REFF
							//accum_reff << "ref: " << *ref << endl;
						#endif
						break;
					}
				}

				if(0){ // temporary code for an experiment
					Inst* tve1 = conjunction_ref.front();
					Inst* tve2 = conjunction_ref.back();
					bool negated = true;

					if((tve1->get_type() == Op) && ((OpInst::as(tve1))->get_op() == OpInst::LogNot)){
						tve1 = (tve1->get_children())->front();
					}else if((tve2->get_type() == Op) && ((OpInst::as(tve2))->get_op() == OpInst::LogNot)){
						tve2 = (tve2->get_children())->front();
					}else{
						negated = false;
					}


					if(((tve1->get_type() == Op) && ((OpInst::as(tve1))->get_op() == OpInst::Eq)) &&
						((tve2->get_type() == Op) && ((OpInst::as(tve2))->get_op() == OpInst::Eq))){
						Inst *ve_lhs1 = (tve1->get_children())->front();
						Inst *ve_rhs1 = (tve1->get_children())->back();
						Inst *ve_lhs2 = (tve2->get_children())->front();
						Inst *ve_rhs2 = (tve2->get_children())->back();
						if(ve_rhs1 == ve_rhs2){
							if(negated == false){
								ref = OpInst::create(OpInst::Eq, ve_lhs1, ve_lhs2);
							}else{
								ref = OpInst::create(OpInst::LogNot, OpInst::create(OpInst::Eq, ve_lhs1, ve_lhs2));
							}
						}
					}
				}
#else
				ref = OpInst::create(OpInst::LogAnd, conjunction_ref);
//				ref = make_lemmas(conjunction_ref);
#endif

#ifdef GEN_DP_LEMMAS_BY_INTERNAL_NODES
				// pattern #1
				// !(A & !{B, A}[24:0][0])	->	{B, 1'b1}[24:0][0] + replace B with its original circuit node
				// conjunction_ref contains A and !{B, A}[24:0][0]
				// Note! If A is not a signal (i.e. operators), then constant propagation can not condcuct :
				// !(A & !{B, A}[24:0][0])	->	{B, 1'b1}[24:0][0]
				//if(0){
				Inst* ref_original = ref;
				if(conjunction_ref.size() == 1){
// 					DEBUG_REF_ADV_GEN << "^^^^	escape case 1" << endl;
					Inst* tve1 = conjunction_ref.front();

					Inst* ch_tve1 = tve1;
					while(ch_tve1->get_children() && ((ch_tve1->get_children())->size() == 1)){	// Ex, LogNot, trivial Concat, ...
						ch_tve1 = (ch_tve1->get_children())->front();
					}
// 					DEBUG_REF_ADV_GEN << "^^^^	escape case 3" << endl;
					if((ch_tve1->get_type() == Op) && ((OpInst::as(ch_tve1))->get_op() == OpInst::Concat)){
						const InstL* ch = ch_tve1->get_children();
						bool need_new = false;
						bool err_encounted = false;
						InstL new_ch;
						set<InstsPair> substitution_pairs;
						int free_var_idx = 0;
						for(InstL::const_iterator it = ch->begin(); it != ch->end(); ++it){
							Inst* concat_ch = *it;
							if((concat_ch->get_size() == 1) && (concat_ch->get_type() == Num)){
								new_ch.push_back(concat_ch);
							}else{
								Inst* target_node = concat_ch;
								ostringstream oss;
								// I put "$" intentionally to the temporary variable name, because
								// the variables in the original formula should not include the character
								// unless "$next", "$n" are added by me.
								oss << "ref$temp" << free_var_idx << "$sz" << target_node->get_size();
								free_var_idx++;
								Inst *free_var = SigInst::create(oss.str(), target_node->get_size());
								// we SHOULD find the original node before substitute_nodes(),
								// because substitute_nodes updates Inst::acex_coi
								Inst *ve_new = (concat_ch->ve_orig == NULL) ? target_node : target_node->ve_orig;
								substitution_pairs.insert(make_pair(free_var, ve_new));
								new_ch.push_back(free_var);
							}
						}
						if(err_encounted == false){

							Inst* ch_tve1_original = ch_tve1;
							ch_tve1 = ch_tve1->apply_children(new_ch);
							substitute_nodes(tve1, ch_tve1_original, ch_tve1, true);
							ref = tve1->acex_coi;
							DEBUG_REF_ADV_GEN << "$$$$	ref_original: " << *ref_original << endl;
							DEBUG_REF_ADV_GEN << "$$$$	ref substitution: " << *ref << endl;

							z3_API* bv_solver = dynamic_cast<z3_API*> (new_conc_solver(1));
							bool bv_res = bv_solver->check_sat(ref);
							if(bv_res == false){
								// TODO apply substitute_nodes for every entries in substitution_pairs
// 								DEBUG_REF_ADV_GEN << "ref_free_vars: " << *ref << endl;
								for(set<InstsPair>::iterator sp_it = substitution_pairs.begin(); sp_it != substitution_pairs.end(); ++sp_it){
									substitute_nodes(ref, sp_it->first, sp_it->second, true);
									ref = ref->acex_coi;
								}
							}else{
								DEBUG_REF_ADV_GEN << ">>>>	bv_solver->check_sat(ref) is SAT !!!" << endl;
								ref = ref_original;
							}
						}else{
							ref = ref_original;
						}
					}else{
// 						DEBUG_REF_ADV_GEN << "^^^^	escape case 1" << endl;
// 						DEBUG_REF_ADV_GEN << "ch_tve1: " << *ch_tve1 << endl;
					}
				}else if(conjunction_ref.size() == 2){
// 					Inst* tve1 = conjunction_ref.front();
// 					Inst* tve2 = conjunction_ref.back();
					Inst* tve1 = conjunction_ref.back();
					Inst* tve2 = conjunction_ref.front();


					Inst* ch_tve1 = tve1;
					Inst* ch_tve2 = tve2;
					while(ch_tve1->get_children() && ((ch_tve1->get_children())->size() == 1)){
						ch_tve1 = (ch_tve1->get_children())->front();
					}
					if((ch_tve1->get_type() == Op) && ((OpInst::as(ch_tve1))->get_op() == OpInst::Concat)){
						Inst* tve2_negated = OpInst::create(OpInst::LogNot, tve2);

						const InstL* ch = ch_tve1->get_children();
						bool need_new = false;
						bool err_encounted = false;
						InstL new_ch;
						set<InstsPair> substitution_pairs;
						int free_var_idx = 0;
						for(InstL::const_iterator it = ch->begin(); it != ch->end(); ++it){
							Inst* concat_ch = *it;
							if(concat_ch == tve2){
								new_ch.push_back(NumInst::create(1, 1));
								need_new = true;
							}else if(concat_ch == tve2_negated){
								new_ch.push_back(NumInst::create(0, 1));
								need_new = true;
							}else{
								Inst* target_node = concat_ch;
								ostringstream oss;
								// I put "$" intentionally to the temporary variable name, because
								// the variables in the original formula should not include the character
								// unless "$next", "$n" are added by me.
								oss << "ref$temp" << free_var_idx << "$sz" << target_node->get_size();
								free_var_idx++;
								Inst *free_var = SigInst::create(oss.str(), target_node->get_size());
								// we SHOULD find the original node before substitute_nodes(),
								// because substitute_nodes updates Inst::acex_coi
								Inst *ve_new = (concat_ch->ve_orig == NULL) ? target_node : target_node->ve_orig;
								substitution_pairs.insert(make_pair(free_var, ve_new));
								new_ch.push_back(free_var);
							}
						}
						if(err_encounted == false){
							Inst* ch_tve1_original = ch_tve1;
							ch_tve1 = ch_tve1->apply_children(new_ch);
							substitute_nodes(tve1, ch_tve1_original, ch_tve1, true);
							ref = tve1->acex_coi;
							DEBUG_REF_ADV_GEN << "$$$$	ref_original: " << *ref_original << endl;
							DEBUG_REF_ADV_GEN << "$$$$	ref substitution: " << *ref << endl;

							z3_API* bv_solver = dynamic_cast<z3_API*> (new_conc_solver(1));
							bool bv_res = bv_solver->check_sat(ref);
							if(bv_res == false){
								// TODO apply substitute_nodes for every entries in substitution_pairs
								for(set<InstsPair>::iterator sp_it = substitution_pairs.begin(); sp_it != substitution_pairs.end(); ++sp_it){
									substitute_nodes(ref, sp_it->first, sp_it->second, true);
									ref = ref->acex_coi;
								}
							}else{
								DEBUG_REF_ADV_GEN << ">>>>	bv_solver->check_sat(ref) is SAT !!!" << endl;
								ref = ref_original;
							}
						}else{
							ref = ref_original;
						}
					}else{	//	Then, 1) swap tve1 and tve2, and 2) do the same procedure for the substitution
						Inst* tve1 = conjunction_ref.front();
						Inst* tve2 = conjunction_ref.back();

						Inst* ch_tve1 = tve1;
						Inst* ch_tve2 = tve2;
						while(ch_tve1->get_children() && ((ch_tve1->get_children())->size() == 1)){
							ch_tve1 = (ch_tve1->get_children())->front();
						}
						if((ch_tve1->get_type() == Op) && ((OpInst::as(ch_tve1))->get_op() == OpInst::Concat)){
							Inst* tve2_negated = OpInst::create(OpInst::LogNot, tve2);

							const InstL* ch = ch_tve1->get_children();
							bool err_encounted = false;
							InstL new_ch;
							set<InstsPair> substitution_pairs;
							int free_var_idx = 0;
							for(InstL::const_iterator it = ch->begin(); it != ch->end(); ++it){
								Inst* concat_ch = *it;
								if(concat_ch == tve2){
									new_ch.push_back(NumInst::create(1, 1));
								}else if(concat_ch == tve2_negated){
									new_ch.push_back(NumInst::create(0, 1));
								}else{
									Inst* target_node = concat_ch;
									ostringstream oss;
									// I put "$" intentionally to the temporary variable name, because
									// the variables in the original formula should not include the character
									// unless "$next", "$n" are added by me.
									oss << "ref$temp" << free_var_idx << "$sz" << target_node->get_size();
									free_var_idx++;
									Inst *free_var = SigInst::create(oss.str(), target_node->get_size());
									// we SHOULD find the original node before substitute_nodes(),
									// because substitute_nodes updates Inst::acex_coi
									Inst *ve_new = (concat_ch->ve_orig == NULL) ? target_node : target_node->ve_orig;
									substitution_pairs.insert(make_pair(free_var, ve_new));
									new_ch.push_back(free_var);
								}
							}
							if(err_encounted == false){
								Inst* ch_tve1_original = ch_tve1;
								ch_tve1 = ch_tve1->apply_children(new_ch);
								substitute_nodes(tve1, ch_tve1_original, ch_tve1, true);
								ref = tve1->acex_coi;
								DEBUG_REF_ADV_GEN << "$$$$	ref_original: " << *ref_original << endl;
								DEBUG_REF_ADV_GEN << "$$$$	ref substitution: " << *ref << endl;

								z3_API* bv_solver = dynamic_cast<z3_API*> (new_conc_solver(1));
								bool bv_res = bv_solver->check_sat(ref);
								if(bv_res == false){
									// TODO apply substitute_nodes for every entries in substitution_pairs
									for(set<InstsPair>::iterator sp_it = substitution_pairs.begin(); sp_it != substitution_pairs.end(); ++sp_it){
										substitute_nodes(ref, sp_it->first, sp_it->second, true);
										ref = ref->acex_coi;
									}
									//DEBUG_REF_ADV_GEN << "ref_after: " << *ref << endl;
								}else{
// 									DEBUG_REF_ADV_GEN << ">>>>	bv_solver->check_sat(ref) is SAT !!!" << endl;
									ref = ref_original;
								}
							}else{
								ref = ref_original;
							}
						}

					}
				}

				if(ref_original == ref){
					DEBUG_REF_ADV_GEN << "###	ref: " << *ref << endl;
				}
#endif

			} else {
				//break;
				assert(0);
			}
			if(set_refs.find(ref) == set_refs.end()){

//					{
//						collect_cubes(ref, true);
//						Inst::inc_dckey();
//						SolverAPI* bv_solver = dynamic_cast<SolverAPI*> (new_conc_solver(true, 1));
//						int res = bv_solver->identify_dont_cares(BV_QUERY_TIMEOUT, _collected_cubes, num_scalls_sat_correctness, num_scalls_unsat_correctness);
//						draw_graph(ref, "", 0, true);
//						if (res != AVR_QUSAT)
//						{
//							cout << "ref: " << *ref << endl;
//							cout << "status: " << res << endl;
//							assert(res == AVR_QTO);
//
//							ostringstream ostr;
//							ostr << "error/" << *ref << "_to";
//							draw_graph(ref, ostr.str(), 0, false);
//							AVR_LOG(15, 0, "\t\t\t(simplify check timeout for: " << *ref << ")" << endl);
//						}
//						else
//						{
//							int numOptions = 1;
//							Inst* refNew = eliminate_dont_cares(ref, abCube, numOptions, true);
//							if (refNew != ref)
//							{
//								if (numOptions > 1)
//								{
//									cout << "\t\t\t#Options = " << numOptions << endl;
//									/// Add ref as well
//									_new_refs.push_back(ref);

#ifdef AVR_ADD_NEXT_REF
				/// Aman
				if (!ref->find_next() && !find_input(ref))
				{
					Inst *cube_next = Inst::all_pre2next(ref);
					if(cube_next != ref)
					{
						_new_refs.push_back(cube_next);
					}
				}
				else if (!find_pre(ref))
#else
				if (!find_pre(ref))
#endif
				{
					Inst *cube_pre = Inst::all_next2pre(ref);
					if((cube_pre != ref) && !find_input(cube_pre))
					{
						_new_refs.push_back(cube_pre);
					}
				}

//								}
//
//								ostringstream ostr;
//								ostr << "diff/" << *ref << "_diff";
//								ref = refNew;
//								draw_graph(ref, ostr.str(), 0, false);
//								AVR_LOG(15, 0, "\t\t\t(simplified: " << *ref << ")" << endl);
//								bool alreadyPresent = false;
//								Inst* tve = OpInst::create(OpInst::LogNot, ref);
//								for (auto& r: _negated_refs)
//								{
//									if (tve == r)
//									{
//										alreadyPresent = true;
//										break;
//									}
//								}
//								assert(!alreadyPresent);
//
//	//							assert(0);
//							}
//	//						else
//	//						{
//	//							ostringstream ostr;
//	//							ostr << "ref/" << *ref;
//	//							draw_graph(ref, ostr.str(), 0, false);
//	//						}
//						}
//					}

				set_refs.insert(ref);
				DEBUG_REF_ADV_GEN << "ref has been inserted in set_refs." << endl;
				_new_refs.push_back(ref);


				//_refs.push_back(ref);
				Inst* tve = OpInst::create(OpInst::LogNot, ref);
				//_negated_refs.push_back(tve);

				/// Aman
//				if (!find_next(ref))
//				{
//					Inst *cube_next = all_pre2next(ref, true);
//					if(cube_next != ref)
//					{
//						_new_refs.push_back(cube_next);
////						cout << "Adding next: " << *cube_next << endl;
//					}
//				}

				/// Below ref can be wrong in rare case (when I violates this ref).
//				else if (!find_pre(ref, true))
//				{
//					Inst *cube_pre = all_next2pre(ref, true);
//					if(cube_pre != ref)
//					{
//						_new_refs.push_back(cube_pre);
//					}
//				}
//				if ((conjunction_ref.size() > 1) && (tve_before != tve)){
// 				if (tve_before != tve){
// 					#ifdef AVR_DUMP_ACCUM_REFF
// 						#if 1
// 							accum_reff << "Before: " << endl;// << *tve_before << endl;
// 							new_print(accum_reff, tve_before, true);
// 						#else
// 							accum_reff << "Before: " << endl << *tve_before << endl;
// 							new_print(accum_reff, tve_before, true);
// 						#endif
// 					#endif
// 					AVR_LOG(4, 3, "Before: " << endl << *tve_before << endl);
// 				}
				AVR_LOG(4, 2, "DP_" << _num_dp_refine << "_R_" << _refine_idx << "_F_"
						<< _refine_seq_idx << "_I_" << _iter << " : " << endl << "\t" << *tve << endl);

				#ifdef AVR_DUMP_ACCUM_REFF
					#if 0
						accum_reff << "DP_" << _num_dp_refine << "_R_" << _refine_idx << "_F_"
								<< _refine_seq_idx << "_I_" << _iter << " : " << endl;// << *tve << endl;
						new_print(accum_reff, tve, true);
					#else
						accum_reff << "DP_" << _num_dp_refine << "_R_" << _refine_idx << "_F_"
								<< _refine_seq_idx << "_I_" << _iter << " : " << endl << *tve << endl;
					#endif
					accum_reff.flush();
				#endif
				if (_config->get_arg(DUMP_REF_ARG) != "") {
					reff << *ref << endl;
					//new_print(reff, ref, true);
					reff.flush();
				}
				added_lemmas_cnt++;
			}/*else{
				cout << "DP_" << _num_dp_refine << "_R_" << _refine_idx << "_F_"
						<< _refine_seq_idx << "_I_" << _iter << " : " << endl << *ref << endl;
			}*/
		}
		if (_config->get_arg(DUMP_REF_ARG) != "") {
			reff.close();
		}

		AVR_LOG(4, 1, "refine_loop_idx: " << refine_loop_idx << ", " << (_feas_sat_res ? "FEASIBLE" : "SPURIOUS") << endl);
		AVR_LOG(4, 1, added_lemmas_cnt << " lemma(s) added" << endl);

		if (!_feas_sat_res) {
			//cout << "refine(), top: \n" << *top << endl;
			assert(!_new_refs.empty());
		} else {
			//process_feas_cex();
			break;
		}

		_iter++;

		assert(!(_new_refs.empty()));

//		Inst* bad_behavior = 0;
//		if (_new_refs.size() > 1)
//		{
////			InstL conjunct_tmp;
////			for (auto& r: _new_refs)
////			{
////				conjunct_tmp.push_back(OpInst::create(OpInst::LogNot, r));
////			}
////			Inst* good = OpInst::create(OpInst::LogAnd, conjunct_tmp);
////			bad_behavior = OpInst::create(OpInst::LogNot, good);
//
//			bad_behavior = OpInst::create(OpInst::LogOr, _new_refs);
//		}
//		else
//			bad_behavior = *(_new_refs.begin());
//
//		Inst* good_behavior = OpInst::create(OpInst::LogNot, bad_behavior);
//
//		getrusage(RUSAGE_SELF, &usage);
//		start_time = usage.ru_utime;
////		cout << *good_behavior << endl;
//		_sat_res = _euf_solver->check_sat(good_behavior);
//		getrusage(RUSAGE_SELF, &usage);
//		end_time = usage.ru_utime;
//		time_diff = Timevaldiff(&start_time, &end_time);
//		AVR_LOG(4, 1, "_euf_solver->check_sat() after adding lemmas : " << (_sat_res ? "SAT" : "UNSAT") << endl);
//		AVR_LOG(4, 2, "_euf_solver->check_sat(good_behavior), res: " << (_sat_res ? "SAT" : "UNSAT") << ", runtime: " << double(time_diff)/1000000 << endl);
//
//		if (!_sat_res) {
//			break;
//		}
//		/// Aman
//		else
//		{
//#ifndef EXTRA_CHECKS
//			_sat_res = false;
//			break;
//#endif
//			assert(0);
//		}
//		/// END
//		assert(!(_new_refs.empty()));

		break;
	}
	AVR_LOG(4, 1, "AR loop done !!, idx: " << _refine_idx << ", sat_res: " << _sat_res
			<< ", feas_sat_res: " << _feas_sat_res << ", refine_loop_idx: " << refine_loop_idx << endl);
	_refine_idx++;
}

Inst* Reach::compare_and_simplify(Inst* v)
{
	if (v->fcLevel > 0)
	{
		OpInst* op = OpInst::as(v);
		if (op)
		{
			bool eq;
			if (op->get_op() == OpInst::NotEq)
			{
				/// Process disequality
				eq = false;
			}
//			else if (op->get_op() == OpInst::Eq)
//			{
//				/// Process equality
//				eq = true;
//			}
			else
				return v;

			InstPairS comparableChildren;
			list < pair < Inst*, Inst* > > q;
			q.push_back(make_pair(op->get_children()->front(), op->get_children()->back()));
			int itCount = 0;
			bool allExCc = true;
			while (!q.empty())
			{
				Inst* lhs = q.front().first;
				Inst* rhs = q.front().second;
//				cout << "Comparing " << *lhs << " with " << *rhs << endl;
				q.pop_front();

				if (lhs->fcLevel != rhs->fcLevel)
				{
					comparableChildren.insert(make_pair(lhs, rhs));
//					cout << "inserting " << *lhs << " with " << *rhs << endl;
				}
				else if (lhs->fcLevel == 0)
				{
					comparableChildren.insert(make_pair(lhs, rhs));
//					cout << "inserting " << *lhs << " with " << *rhs << endl;
				}
				else
				{
					OpInst* opLHS = OpInst::as(lhs);
					OpInst* opRHS = OpInst::as(rhs);
					assert(opLHS);
					assert(opRHS);

					if (opLHS->get_euf_func_name() != opRHS->get_euf_func_name())
					{
//						if (allExCc && opLHS->get_op() != OpInst::Concat)
//							allExCc = false;

						comparableChildren.insert(make_pair(lhs, rhs));
//						cout << "inserting " << *lhs << " with " << *rhs << endl;
					}
					else
					{
						ExInst* exLHS = ExInst::as(lhs);
						if (exLHS)
						{
							ExInst* exRHS = ExInst::as(rhs);
							assert(exRHS);
							if ((exLHS->get_lo() != exRHS->get_lo()) || (exLHS->get_hi() != exRHS->get_hi()))
							{
								comparableChildren.insert(make_pair(lhs, rhs));
//								cout << "inserting " << *lhs << " with " << *rhs << endl;
							}
							else
								q.push_back(make_pair(exLHS->get_exp(), exRHS->get_exp()));
						}
						else
						{
							if (allExCc && opLHS->get_op() != OpInst::Concat)
								allExCc = false;

							InstL::const_iterator chLHS = lhs->get_children()->begin();
							InstL::const_iterator chRHS = rhs->get_children()->begin();
							int numCh = lhs->get_children()->size();
							for (int i = 0; i < numCh; i++)
							{
								q.push_back(make_pair(*chLHS, *chRHS));
								chLHS++;
								chRHS++;
							}
						}
						itCount++;
					}
				}
			}

			if (itCount == 0)
				return v;
			else if (allExCc)
			{
//				cout << "(skipping since interpretable: " << *v << ")" << endl;
				return v;
			}
			else
			{
				assert(comparableChildren.size() > 0);
				InstL compareList;
				for (auto& c: comparableChildren)
				{
					if (c.first == c.second)
						continue;
//					if ((c.first->get_type() == Num) && (c.second->get_type() == Num))
//						continue;
//					cout << *(c.first) << " == " << *(c.second) << endl;
					Inst* tve = OpInst::create(OpInst::Eq, c.first, c.second);
					compareList.push_back(tve);
				}
//				if (compareList.empty())
//				{
////					cout << *v << endl;
//					return v;
//				}
				assert(!compareList.empty());
				Inst* vSimple = OpInst::create(OpInst::LogAnd, compareList);
//				if (!eq)
				vSimple = OpInst::create(OpInst::LogNot, vSimple);

//				cout << "Returning  \t" << *vSimple << endl;
//				cout << "Instead of \t" << *v << endl;
//				assert(0);
				return vSimple;
			}
		}
	}
	return v;
}

// trace_back
// mode AB_REACH     : AVR reachability (except top query) (default)
// mode AB_REACH_TOP : AVR reachability (top query)
// mode AB_CC_ACEXT  : AVR abstract continuity check of ACEXT (whole cube in mainConstraints)
void Reach::trace_back(Solver*solver, Inst *full_formula, InstL& assumptions, Inst *e_v, Inst* e_p, int mode)
{
	//cout << "trace_back: " << *e << endl;

	struct rusage usage;
	struct timeval start_time_full;
	struct timeval start_time, end_time;
	long long time_diff;
	long long time_diff_total = 0;

	TIME_S(start_time_full);

	_abViol.clear();

	int pmode = -1;
	if (mode != AB_CC_ACEXT)
	{
		pmode = 1;
	}

	//	retrieve_cex_val(e, _euf_solver, true, true);

  bool ctiCheck = (e_v == _ve_model_next);

	e_v->set_bval(1);
	Inst* e;
	if (e_p == NumInst::create(1, 1, SORT()))
	{
		e = e_v;
	}
	else
	{
#ifndef REACH_ADD_PATH_CONSTRAINTS
		assert(0);
#endif

		e_p->set_bval(1);
		e = OpInst::create(OpInst::LogAnd, e_v, e_p);
		e->set_bval(1);
	}

	InstL conjunct_q = assumptions;
	conjunct_q.push_back(full_formula);

	/// Aman - Collecting next state assignments
	/// TODO: Faster ways of doing below possible

	InstS relevantPresent;
	InstS relevantNextStates;
	InstS relevantPresentInp;
	InstS relevantNextInp;
	InstS relevantConst = _s_constants;
	set< string > relevantUFtype = _s_uf_types;
//	map< string, map < mpz_class, InstL > > relevantUFs;

	InstToInstM dummyMap;

	EVAL tb(_abViol, dummyMap, relevantPresent, relevantNextStates, relevantPresentInp, relevantNextInp, relevantConst, relevantUFtype, solver);

	KEY_COI_VALUE::inc_coi_key();
#ifndef PERFORMANCE_NODRAW
	if (Config::g_print_dot[DRAW_TRANSITION] != '0')
		Inst::inc_drkey();
#endif

//  Inst::init_visit();
//  COI_generalize(e, tb);
//  tb.print_all();
//  tb.clear_all();

	/// COI (next)
	{
    Inst::init_visit();
		TIME_S(start_time);
		{
			COI_prune_relation(e, tb, 0);
#ifdef LEARN_INIT_PREDICATE_TRAVERSE_INIT
#else
			if (mode == AB_REACH_INIT)
#endif
			{
//				cout << "traversing init" << endl;
				for (auto& v: _init_preds)
					COI_prune_relation(v, tb, 0);
			}
      tb.print_all();
		}
		TIME_E(start_time, end_time, _tb_eval_time);
		time_diff_total += time_diff;
	}

//	if (mode == AB_REACH_TOP)
//		_bad_cube.nextStateSubConstraints.clear();

//	cout << "\t(relevant next)" << endl;
//	for (auto& r: relevantNextStates)
//		cout << "\t\t" << *r << endl;
//  cout << "\t(relevant next const)" << endl;
//  for (auto& r: relevantConst)
//    cout << "\t\t" << *r << endl;
//  cout << "\t(relevant next uf)" << endl;
//  for (auto& r: relevantUFtype)
//    cout << "\t\t" << r << endl;

	InstL projectionNext;

	/// Projection (next)
#ifdef DEFAULT_PROJECTION
	{
		TIME_S(start_time);
		if (mode == AB_REACH_TOP)
		{
			InstS importantWires;
			for (auto& w: _bad_cube.relevantWiresNext)
				importantWires.insert(w);

//			for (auto& c: _bad_cube.nextStateConstraints)
//			{
//				Inst* tve = c;
//				if (tve->childrenInfo[WIRE])
//				{
//					OpInst* opC = OpInst::as(c);
//					if (opC && opC->get_op() == OpInst::LogNot)
//						tve = c->get_children()->front();
//					if (tve->get_type() == Wire)
//						importantWires.insert(tve);
//					else
//					{
//						const InstL* children = tve->get_children();
//						if (children)
//						{
//							for (auto& ch: (*children))
//							{
//								if (ch->get_type() == Wire)
//									importantWires.insert(ch);
//							}
//						}
//					}
//				}
//			}

			AVR_LOG(15, 0, "\t(projection next [in !P+])" << endl);
			if (mode != AB_CC_ACEXT)
			{
				AVR_LOG(15, 0, "\t\t#next: " << relevantNextStates.size() << endl);
			}

			project_abstract_min_term(pmode, projectionNext, projectionNext, relevantNextStates, relevantConst, _min_term);
#ifndef RESTRICT_ALL_PROJECTION_CONSTRAINTS_IN_CONCRETE_CUBE
			for (auto& p: projectionNext)
			{
#ifdef RESTRICT_PROJECTION_NUMBERS_IN_CONCRETE_CUBE
				if (p->childrenInfo[NUM])
					continue;
#endif
				_bad_cube.nextStateConstraints.push_back(p);
			}

			/// Wires
			if (mode != AB_CC_ACEXT)
			{
				AVR_LOG(15, 0, "\t\t#bad_wires: " << importantWires.size() << endl);
			}

			InstL wFprojectionBad;
			InstL wProjectionBad;
			project_abstract_min_term(pmode, wFprojectionBad, wProjectionBad, importantWires, relevantConst, _min_term, Wire, false);
			for (auto& p: wFprojectionBad)
			{
#ifdef RESTRICT_PROJECTION_NUMBERS_IN_CONCRETE_CUBE
				if (p->childrenInfo[NUM])
					continue;
#endif
				_bad_cube.nextStateConstraints.push_back(p);
			}
#endif

#ifndef LIMIT_CONCRETE_PROJECTION_USING_STRUCTURAL_INFORMATION
			for (auto& p: wProjectionBad)
			{
#ifdef RESTRICT_PROJECTION_NUMBERS_IN_CONCRETE_CUBE
				if (p->childrenInfo[NUM])
					continue;
#endif
				_bad_cube.nextStateConstraints.push_back(p);
			}
#endif
		}
		else
		{
			AVR_LOG(15, 0, "\t(projection next)" << endl);
			if (mode != AB_CC_ACEXT)
			{
				AVR_LOG(15, 0, "\t\t#next: " << relevantNextStates.size() << endl);
			}
			InstL dummyList;
			project_abstract_min_term(pmode, dummyList, dummyList, relevantNextStates, relevantConst, _min_term);
		}
		TIME_E(start_time, end_time, _tb_proj_time);
		time_diff_total += time_diff;
	}
#endif


	InstL conjunct_t;

	InstL nextStateConstraints = _abViol.nextStateConstraints;

	{
		TIME_S(start_time);
		Inst::init_visit();
		for (InstS::iterator it = relevantNextStates.begin(); it != relevantNextStates.end(); it++)
		{
			SigInst* sig = SigInst::as(*it);
			assert (sig);

			assert(Inst::has_trelation(sig));

//			if (sig->get_size() == 1)
//			{
//				COI_prune_relation((*mit).second.first, tb);
////        COI_generalize((*mit).second, tb);
//			}
//			else
//			{
//				COI_prune_term((*mit).second.first, tb);
////        COI_generalize((*mit).second, tb);
//			}

			// not required
			Inst* tve = Inst::fetch_trelation(sig);
      _abViol.nextStateConstraints.push_back(tve);

#ifndef PERFORMANCE_NODRAW
    	if (Config::g_print_dot[DRAW_TRANSITION] != '0') {
				Inst* rel = Inst::fetch_trelation(sig);
				rel->set_drVal(1);
				conjunct_t.push_back(rel);
    	}
#endif
		}
		TIME_E(start_time, end_time, _tb_eval_time);
		time_diff_total += time_diff;
	}
  tb.print_all();

#ifndef PERFORMANCE_NODRAW
	if (Config::g_print_dot[DRAW_TRANSITION] != '0') {
		Inst* v = e;
		Inst* u;
		if (conjunct_t.empty())
			u = NumInst::create(1, 1, SORT());
		else if (conjunct_t.size() == 1)
			u = conjunct_t.front();
		else
			u = OpInst::create(OpInst::LogAnd, conjunct_t);
		u->set_drVal(1);

		AVR_LOG(15, 0, "\t(key) #" << Inst::get_drkey() << "\t(#" << u->get_id() << " -> #" << v->get_id() << ")" << endl);
		{
			ostringstream ostr;
	//    ostr << "ab/" << Inst::get_drkey() << "_v#" << v->get_id();
			ostr << "ab/" << Inst::get_drkey() << "_v";
			draw_graph(2, v, ostr.str(), 0, false);
		}
		{
			ostringstream ostr;
	//    ostr << "ab/" << Inst::get_drkey() << "_u#" << u->get_id();
			ostr << "ab/" << Inst::get_drkey() << "_u";
			draw_graph(2, u, ostr.str(), 0, false);
		}
	}
#endif

	/// Minterm solution contains boolean predicates and partitions involving state variables, constants, wires (or their negation)
//  print_solution(_min_term.s, "solver solution");

	/// Merge relevant present and next state variables
	InstS relevantStates = _s_signals;
	relevantStates.insert(relevantNextStates.begin(), relevantNextStates.end());
	relevantStates.insert(relevantNextInp.begin(), relevantNextInp.end());

	relevantStates.insert(relevantPresent.begin(), relevantPresent.end());
	relevantStates.insert(relevantPresentInp.begin(), relevantPresentInp.end());

//	for (auto& s: relevantStates) {
//		AVR_LOG(15, 0, *s << "\t" << s->get_id() << endl);
//	}
//	assert(0);

  if (true)
  {
  	_abViol.print_cubes();

		simplify_solution2();

//    print_solution(_min_term.s, "minterm solution");

		/// Generalize solution to include relevant terms only (by dropping terms from minterm solution)
		model_generalize2(solver, conjunct_q, _min_term, relevantStates, relevantConst, relevantUFtype, mode);

		/// Project generalized solution on present, next and input variables (mixed constains cases where inputs and present variables are mixed)
		SOLUTION pre_c, inp_c, next_c, mixed_c;
		model_abstract2(_min_term.s, pre_c, inp_c, next_c, mixed_c, false);

//		for(auto& v: nextStateConstraints)
//			_abViol.nextStateConstraints.push_back(v);

		uniquify_list(_abViol.nextStateConstraints);

		if (mode == AB_REACH_TOP)
		{
			nextStateConstraints = _abViol.nextStateConstraints;
			add_pred_from_solution(next_c, nextStateConstraints, "adding pred. from next_c to next");
			/// Add relevant wires
			add_wires_from_list(nextStateConstraints, _abViol.relevantWiresNext);

      _bad_cube.clear();
			_bad_cube.relevantWiresNext = _abViol.relevantWiresNext;
			_bad_cube.nextStateConstraints = nextStateConstraints;

//			add_pred_from_solution(next_c, _bad_cube.nextStateConstraints, "adding pred. from next_c to bad. cube");
//
//			/// Add relevant wires
//			add_wires_from_list(_bad_cube.nextStateConstraints, _bad_cube.relevantWiresNext);

//			add_from_solution(solver, next_c, _bad_cube.nextStateConstraints, "adding from next_c to cc. dest.");

			/// Add concrete constraints from generalized solution
//			add_wires_from_solution(next_c, _bad_cube.relevantWires, _bad_cube.relevantWiresNext);
//			add_wires_from_solution(next_c, _abViol.relevantWires, _abViol.relevantWiresNext);
		}

		add_from_solution(solver, pre_c, _abViol.mainConstraints, "adding from pre_c to ab. cube");
		add_required_pred_from_solution(mixed_c, _abViol.mainConstraints, AB_GRANULARITY_MIXED, "adding required pred. from mixed_c to ab. cube");
		add_required_pred_from_solution(inp_c, _abViol.mainConstraints, AB_GRANULARITY_INPUT, "adding required pred. from inp_c to ab. cube");
//		add_pred_from_solution(mixed_c, _abViol.mainConstraints, "adding pred. from mixed_c to ab. cube");
//		add_pred_from_solution(inp_c, _abViol.mainConstraints, "adding pred. from inp_c to ab. cube");

		/// Add concrete constraints from generalized solution
		add_from_solution(solver, pre_c, _abViol.concreteConstraints, "adding from pre_c to cc. cube");
		add_pred_from_solution(mixed_c, _abViol.concreteConstraints, "adding pred. from mixed_c to cc. cube");
		add_pred_from_solution(inp_c, _abViol.concreteConstraints, "adding pred. from inp_c to cc. cube");

		/// Add relevant wires
		add_wires_from_list(_abViol.concreteConstraints, _abViol.relevantWires);

		for (auto& v: _abViol.mainConstraints) {
			if (v->find_next()) {
				cout << *v << "\t" << v->coi.str() << endl;
				assert(0);
			}
		}
		for (auto& v: _abViol.concreteConstraints) {
			if (v->find_next())
				assert(0);
		}

//		cout << "main: " << _abViol.mainConstraints << endl;

//  	_abViol.print_cubes();
  }

#ifdef INTERACTIVE_CUBE
  {
    InstL cubeInter = _abViol.mainConstraints;
    for (InstL::iterator lit = cubeInter.begin(); lit != cubeInter.end(); ) {
    	if (_assumptions.find((*lit)->get_port()) != _assumptions.end())
    		lit = cubeInter.erase(lit);
    	else
    		lit++;
    }

		m5_API inout_solver(_concrete_mapper, AVR_BV_IDX, false, prt);

		string fname_smt2 = _config->get_working_dir() + "/cube.smt2";
		ofstream out_smt2;
		out_smt2.open(fname_smt2.c_str());
		inout_solver.print_expression(cubeInter, out_smt2);
		out_smt2.close();

		cout << "\t(interactive cube) original cube (#" << cubeInter.size() << "): " << cubeInter << endl;
		cout.flush();
		cerr << "\n(interactive cube) original cube of size " << cubeInter.size() << endl;
		cerr << "(interactive cube) edit file cube.smt2 and press enter...";
		do {
		} while (cin.get() != '\n');

		ifstream in_smt2;
		in_smt2.open(fname_smt2.c_str());
		Inst* newTve = inout_solver.read_expression(in_smt2);

		collect_cubes(newTve, true);

		Inst::init_visit2();
		_abViol.mainConstraints.clear();
		for (auto& v: _collected_cubes)
			_abViol.mainConstraints.push_back(add_missing_wires(v));

		cerr << "(interactive cube) read cube of size " << _abViol.mainConstraints.size() << endl;
		cerr << "\t" << *newTve << endl;
		cout << "\t(interactive cube) cube (#" << _abViol.mainConstraints.size() << "): " << *newTve << endl;

//		assert(0);
	}
#endif

#ifdef	FIND_SUB_EXPRESSION
  else
  {
		/// Substitute wires with their respective evaluations (each evaluation expression stores a list of original wire expressions)
		InstToListM opMap;
		{
			TIME_S(start_time);
			simplify_solution(_min_term.s, opMap);
			TIME_E(start_time, end_time, _tb_eval_time);
			time_diff_total += time_diff;
		}
	//	AVR_LOG(15, 0, "x+: " << relevantNextStates << endl);
	//	AVR_LOG(15, 0, "y+ : " << relevantNextInp << endl);
	//	AVR_LOG(15, 0, "x : " << relevantPresent << endl);
	//	AVR_LOG(15, 0, "y : " << relevantPresentInp << endl);

		/// Project generalized solution on present, next and input variables (mixed constains cases where inputs and present variables are mixed)
		SOLUTION pre, inp, next, mixed;
		model_abstract(_min_term.s, pre, inp, next, mixed, true);

		/// Undo simplification (done for abstraction and generalization) of UPs/UFs
		_abViol.generalized_s = _min_term.s;
		SOLUTION pre_c, inp_c, next_c, mixed_c;
		InstToInstM subMap, subMapR;
		resimplify_solution(_min_term.s, opMap, subMap, subMapR);

		model_abstract(_min_term.s, pre_c, inp_c, next_c, mixed_c, subMapR, false);
	//  model_convert(next, next_c, subMap, "next");
//	model_convert(pre, pre_c, subMap, "pre");
//  model_convert(inp, inp_c, subMap, "inp");
//  model_convert(mixed, mixed_c, subMap, "mixed");

	#ifdef CORRECT_GENERALIZATION
	#ifndef GENERALIZATION_SKIP_CONCRETE
		/// Add next state concrete constraints from generalized solution
		if (mode == AB_REACH_TOP)
		{
	//	  /// Add relevant wires from partition
	//		add_wires_from_solution(next_c, _bad_cube.relevantWires, _bad_cube.relevantWiresNext);
	//		merge_lists(_bad_cube.relevantWiresNext, _bad_cube.relevantWires);
	//		_abViol.relevantWiresNext = _bad_cube.relevantWiresNext;
	//    /// Add concrete constraints from generalized solution
	//    add_from_solution(solver, next_c, _bad_cube.nextStateConstraints, "adding to concrete next");

			add_from_solution(solver, next, _bad_cube.nextStateSubConstraints, "adding to next");
		}
	#endif

		int countInp = 0;
		for (auto& v: _abViol.mainConstraints)
		{
			if (find_input(v))
			{
				countInp++;
	//			cout << "\t\t(input involved in " << *v << " )" << endl;
			}
		}
		if (countInp != 0)
		{
			AVR_LOG(15, 0, "\t(inp. cond.) #" << countInp << endl);
		}

	//	_abViol.mainConstraints.clear();

		/// Add abstract constraints from generalized solution
	//  add_from_solution(solver, pre, _abViol.mainConstraints, subMap, "adding to pre");
	//  add_from_solution(solver, mixed, _abViol.mainConstraints, subMap, "adding to mixed");
	//  add_from_solution(solver, inp, _abViol.mainConstraints, subMap, "adding to inp");

	//  add_from_solution(solver, pre, _abViol.mainConstraints, "adding to pre");
	//  add_from_solution(solver, mixed, _abViol.mainConstraints, "adding to mixed");
	//  add_from_solution(solver, inp, _abViol.mainConstraints, "adding to inp");

		AVR_LOG(15, 0, "\t(sub. map) #" << subMap.size() << endl);
	//	for (auto& m: subMap) {
	//	  Inst* simple = simplify_expr(m.first);
	//	  if (m.first != simple) {
	//	    AVR_LOG(15,0, "\t\t" << *(m.second) << " = " << *simple << "\ti.e. " << *(m.first) << endl);
	//	  }
	//	  else {
	//      AVR_LOG(15,0, "\t\t" << *(m.second) << " = " << *(m.first) << endl);
	//	  }
	//	}

		add_from_solution(solver, pre, _abViol.mainSubConstraints, "adding to pre_sub");

		add_from_solution(solver, pre_c, _abViol.mainConstraints, "adding to pre_c");
	//  add_from_solution(solver, mixed, _abViol.mainConstraints, "adding to mixed");
	//  add_from_solution(solver, inp, _abViol.mainConstraints, "adding to inp");
		//  add_from_solution(solver, mixed, _abViol.mainConstraints, "adding to mixed");
		//  add_from_solution(solver, inp, _abViol.mainConstraints, "adding to inp");

	//  add_from_solution(solver, pre, _abViol.mainConstraints, subMap, "adding to pre");
	//  add_from_solution(solver, mixed, _abViol.mainConstraints, subMap, "adding to mixed");
	//  add_from_solution(solver, inp, _abViol.mainConstraints, subMap, "adding to inp");

	//	add_from_solution(solver, pre_c, _abViol.mainConstraints, subMap, "adding to pre");
	//	add_from_solution(solver, mixed_c, _abViol.mainConstraints, subMap, "adding to mixed");
	//  add_from_solution(solver, inp_c, _abViol.mainConstraints, subMap, "adding to inp");

	#ifndef GENERALIZATION_SKIP_CONCRETE
		/// Add concrete constraints from generalized solution
		{
	//	  _abViol.concreteConstraints.clear();

	//	  /// Add relevant wires from partition
			add_wires_from_solution(pre_c, _abViol.relevantWires, _abViol.relevantWiresNext);
	//    add_wires_from_solution(mixed_c, _abViol.relevantWires, _abViol.relevantWiresNext);
	//    add_wires_from_solution(inp_c, _abViol.relevantWires, _abViol.relevantWiresNext);

			/// Add concrete constraints from generalized solution
			add_from_solution(solver, pre_c, _abViol.concreteConstraints, "adding to concrete pre");
	//	  add_from_solution(solver, mixed_c, _abViol.concreteConstraints,  "adding to concrete mixed_c");
	//    add_from_solution(solver, inp_c, _abViol.concreteConstraints,  "adding to concrete inp_c");
		}
	#endif
	#endif
  }
#endif

//	for (auto& v: _abViol.mainConstraints) {
//		AVR_LOG(15, 0, *v << "\t" << v->get_id() << endl);
//	}
//	assert(0);


//	if (mode == AB_REACH_TOP) {
//	  AVR_log(15, 0, "\t(next state final)    \t" << _bad_cube.nextStateConstraints << endl);
//	  AVR_log(15, 0, "\t(next state sub final)\t" << _bad_cube.nextStateSubConstraints << endl);
//	}
//	AVR_log(15, 0, "\t(main final)            \t" << _abViol.mainConstraints << endl);
//	AVR_log(15, 0, "\t(main sub final)        \t" << _abViol.mainSubConstraints << endl);

//	_abViol.mainConstraints = _abViol.mainSubConstraints;

	if (false)
	{
    InstL tsim_in = _abViol.mainConstraints;
    InstL tsim_inp;
    for (auto& inp: relevantNextInp) {
      if (inp->get_size() == 1) {
        switch(inp->get_bval()) {
        case 1:
          tsim_inp.push_back(inp);
          break;
        case 0:
          tsim_inp.push_back(OpInst::create(OpInst::LogNot, inp));
          break;
        }
      }
    }
    for (auto& inp: relevantPresentInp) {
      if (inp->get_size() == 1) {
        switch(inp->get_bval()) {
        case 1:
          tsim_inp.push_back(inp);
          break;
        case 0:
          tsim_inp.push_back(OpInst::create(OpInst::LogNot, inp));
          break;
        }
      }
    }

    Inst* tsim_dest = e;
    if (ctiCheck) {
      tsim_dest = OpInst::create(OpInst::LogAnd, e, _ve_prop_next_eq_0);
    }
    tsim.ternary_sim(tsim_inp, tsim_in, tsim_dest);
    assert(0);
	}


//	cout << "\t(relevant pre)" << endl;
//	for (auto& r: relevantPresent)
//		cout << "\t\t" << *r << endl;

	/// Projection (pre)
#ifdef DEFAULT_PROJECTION
	{
		TIME_S(start_time);
		if (mode != AB_CC_ACEXT)
		{
			pmode = 1;
			AVR_LOG(15, 0, "\t(projection pre)" << endl);
		}

//		/// Separate Inputs and State vars
//		InstS relevantInput;
//		for (InstS::iterator sit = relevantPresent.begin(); sit != relevantPresent.end(); )
//		{
//			if (Inst::_s_reg.find(*sit) == Inst::_s_reg.end())
//			{
//				relevantInput.insert(*sit);
//				sit = relevantPresent.erase(sit);
//			}
//			else
//				sit++;
//		}

		/// Present
		if (mode != AB_CC_ACEXT)
		{
			AVR_LOG(15, 0, "\t\t#sv: " << relevantPresent.size() << endl);
		}
		InstL fprojectionConstraints;
		InstL projectionConstraints;
		project_abstract_min_term(pmode, fprojectionConstraints, projectionConstraints, relevantPresent, relevantConst, _min_term);
		for (auto& c: fprojectionConstraints)
		{
			_abViol.fprojAbConstraints.push_front(c);

#ifndef RESTRICT_ALL_PROJECTION_CONSTRAINTS_IN_CONCRETE_CUBE
#ifdef RESTRICT_PROJECTION_NUMBERS_IN_CONCRETE_CUBE
				if (c->childrenInfo[NUM])
					continue;
#endif
			_abViol.fprojCcConstraints.push_front(c);
#endif
		}
		for (auto& c: projectionConstraints)
		{
			_abViol.projAbConstraints.push_front(c);

#ifndef RESTRICT_ALL_PROJECTION_CONSTRAINTS_IN_CONCRETE_CUBE
#ifdef RESTRICT_PROJECTION_NUMBERS_IN_CONCRETE_CUBE
				if (c->childrenInfo[NUM])
					continue;
#endif
			_abViol.projCcConstraints.push_front(c);
#endif
		}

//		/// Inputs
//		if (mode != AB_CC_ACEXT)
//		{
//			AVR_LOG(15, 0, "\t\t#input: " << relevantInput.size() << endl);
//		}
//		project_abstract_min_term(pmode, _abViol.mainConstraints, relevantInput, _min_term);

		TIME_E(start_time, end_time, _tb_proj_time);
		time_diff_total += time_diff;
	}
#endif
	/// END

	/// Projection (important wires)
#ifdef DEFAULT_PROJECTION
	{
		TIME_S(start_time);
		/// Collect important wires
		InstS importantWires;
		for (auto& w: _abViol.relevantWires)
			importantWires.insert(w);

//		for (auto& c: _abViol.concreteConstraints)
//		{
//			Inst* tve = c;
//			if (tve->childrenInfo[WIRE])
//			{
//				OpInst* opC = OpInst::as(c);
//				if (opC && opC->get_op() == OpInst::LogNot)
//					tve = c->get_children()->front();
//				if (tve->get_type() == Wire)
//					importantWires.insert(tve);
//				else
//				{
//					const InstL* children = tve->get_children();
//					if (children)
//					{
//						for (auto& ch: (*children))
//						{
//							if (ch->get_type() == Wire)
//								importantWires.insert(ch);
//						}
//					}
//				}
//			}
//		}

	//	cout << "\t(important wires)" << endl;
	//	for (auto& r: importantWires)
	//		cout << "\t\t" << *r << endl;

		if (mode != AB_CC_ACEXT)
		{
			pmode = 1;
			AVR_LOG(15, 0, "\t(projection wires)" << endl);
		}

		/// Wires
		if (mode != AB_CC_ACEXT)
		{
			AVR_LOG(15, 0, "\t\t#wires: " << importantWires.size() << endl);
		}
#ifndef RESTRICT_ALL_PROJECTION_CONSTRAINTS_IN_CONCRETE_CUBE
		InstL wFprojectionConstraints;
		InstL wProjectionConstraints;
		project_abstract_min_term(pmode, wFprojectionConstraints, wProjectionConstraints, importantWires, relevantConst, _min_term, Wire, false);
		for (auto& c: wFprojectionConstraints)
		{
#ifdef RESTRICT_PROJECTION_NUMBERS_IN_CONCRETE_CUBE
				if (c->childrenInfo[NUM])
					continue;
#endif
			_abViol.fprojCcConstraints.push_front(c);
		}
#ifndef LIMIT_CONCRETE_PROJECTION_USING_STRUCTURAL_INFORMATION
		for (auto& c: wProjectionConstraints)
		{
#ifdef RESTRICT_PROJECTION_NUMBERS_IN_CONCRETE_CUBE
				if (c->childrenInfo[NUM])
					continue;
#endif
			_abViol.projCcConstraints.push_front(c);
		}
#endif
#endif

		TIME_E(start_time, end_time, _tb_proj_time);
		time_diff_total += time_diff;
	}
#endif
	/// END

	{
		TIME_S(start_time);
		InstS wireSet;
		add_predicate_constraints(solver, _abViol.predConstraints, wireSet);

		for (auto& w:wireSet)
			_abViol.relevantWires.push_back(w);

		TIME_E(start_time, end_time, _tb_pred_time);
		time_diff_total += time_diff;
	}

//	cout << _abViol.relevantWires << endl;
//	cout << _abViol.relevantWiresNext << endl;

//	{
//		AVR_LOG(15, 2, "\t(next)" << endl);
//		for (InstToInstM::iterator mit = nextMap.begin(); mit != nextMap.end(); mit++)
//		{
//			AVR_LOG(15, 2, "\t\t\t" << *((*mit).first) << " <= " << *((*mit).second) << endl);
//		}
//	}

	/// Check correctness
//	{
//		for (auto& v: _abViol.mainConstraints)
//		{
//			OpInst* op = OpInst::as(v);
//			if (op)
//			{
//				if (op->get_op() == OpInst::Eq || op->get_op() == OpInst::NotEq)
//				{
//					bool eq = (op->get_op() == OpInst::Eq);
//					Inst* lhs = op->get_children()->front();
//					Inst* rhs = op->get_children()->back();
//					if (lhs->get_size() == 1)
//					{
//						bool veq = (lhs->get_bval() == rhs->get_bval());
//						assert(eq == veq);
//					}
//					else
//					{
//						bool veq = (lhs->get_ival() == rhs->get_ival());
//						if (eq != veq)
//						{
//							cout << "Error asserting " <<  *op << endl;
//							cout << *lhs << " is id" << lhs->get_ival() << endl;
//							cout << *rhs << " is id" << rhs->get_ival() << endl;
//							cout << solver->m_ba_idx << endl;
//							cout << "rkey: " << Inst::get_rkey() << " (solver: " << Inst::get_bIdx() << ")" << endl;
//						}
//						assert(eq == veq);
//						continue;
//					}
//				}
//				else if (op->get_op() == OpInst::LogNot)
//				{
//					Inst* child = op->get_children()->front();
//					assert(op->get_bval() == 1);
//					assert(child->get_bval() == 0);
//					continue;
//				}
//			}
//
//			if (v->get_bval() == 0)
//			{
//				cout << "Error asserting " <<  *v << endl;
//				cout << *v << " is id" << v->get_bval() << endl;
//				cout << solver->m_ba_idx << endl;
//				cout << "rkey: " << Inst::get_rkey() << " (solver: " << Inst::get_bIdx() << ")" << endl;
//			}
//			assert(v->get_bval() != 0);
//		}
//	}

	TIME_S(start_time);

#ifdef PROJECTION_SUBSTITUTION
	AVR_LOG(15, 0, "\t(projection next sub: ");
	int psCount = 0;
	for (auto& v: projectionNext)
	{
		OpInst* op = OpInst::as(v);
		assert(op);
		OpInst::OpType opt = op->get_op();
		assert(opt == OpInst::Eq || opt == OpInst::NotEq);
		Inst* lhs = op->get_children()->front();
		Inst* rhs = op->get_children()->back();

		if (lhs->get_type() == Sig)
		{
			InstToInstM::iterator mit = nextMap.find(lhs);
			assert(mit != nextMap.end());
			lhs = (*mit).second;
		}
		if (rhs->get_type() == Sig)
		{
			InstToInstM::iterator mit = nextMap.find(rhs);
			assert(mit != nextMap.end());
			rhs = (*mit).second;
		}
		Inst* newCond = OpInst::create(opt, lhs, rhs);
		if (!is_redundant(newCond))
		{
			_abViol.subsConstraints.push_back(newCond);
			psCount++;
//			AVR_LOG(15, 0, "\t\t" << *newCond << endl);
		}
	}
	AVR_LOG(15, 0, psCount << ")" << endl);
#endif

#ifdef SEQUENTIAL_SUBSTITUTION_LEVEL1
	int s1Count = _abViol.subsConstraints.size();
	collect_cubes(e_v, true);
	Inst::init_visit();
	for(InstL::iterator it = _collected_cubes.begin(); it != _collected_cubes.end(); it++)
	{
		evaluate_path_relation(1, (*it), _abViol, nextMap, false);
	}

#ifdef BIT_PRECISE
	Inst::init_visit2();
	for (auto& v: _abViol.subsConstraints)
	{
		v = replace_inputs_with_val(v);
	}
#endif

	AVR_LOG(15, 0, "\t(seq. sub): ");
	for (auto& v: _abViol.subsConstraints)
	{
		AVR_LOG(15, 0, "\t\t" << *v << endl);
	}

	s1Count = _abViol.subsConstraints.size() - s1Count;
	AVR_LOG(15, 0, s1Count << ")" << endl);
#endif

	TIME_E(start_time, end_time, _tb_subs_time);
	time_diff_total += time_diff;


	InstS violSet;
	InstL violNew;

	InstS concreteSet;
	InstL concreteNew;

	int coiAbSz = 0;
	int predAbSz = 0;
	int fprojAbSz = 0;
	int projAbSz = 0;
	int subsAbSz = 0;

	int coiCcSz = 0;
	int predCcSz = 0;
	int fprojCcSz = 0;
	int projCcSz = 0;

	int coiNumEqAbSz = 0;
	int coiNumNeqAbSz = 0;
	int coiSigEqAbSz = 0;
	int coiSigNeqAbSz = 0;
	int coiOtherAbSz = 0;

	int fprojNumEqAbSz = 0;
	int fprojNumNeqAbSz = 0;
	int fprojSigEqAbSz = 0;
	int fprojSigNeqAbSz = 0;

	int projNumEqAbSz = 0;
	int projNumNeqAbSz = 0;
	int projSigEqAbSz = 0;
	int projSigNeqAbSz = 0;

	int projNumEqCcSz = 0;
	int projNumNeqCcSz = 0;
	int projSigEqCcSz = 0;
	int projSigNeqCcSz = 0;

	int fprojNumEqCcSz = 0;
	int fprojNumNeqCcSz = 0;
	int fprojSigEqCcSz = 0;
	int fprojSigNeqCcSz = 0;


	for (InstL::iterator it = _abViol.mainConstraints.begin(), end_it = _abViol.mainConstraints.end(); it != end_it; ++it)
	{
		if (violSet.find(*it) != violSet.end())
			continue;

		coiAbSz++;
		OpInst* op = OpInst::as(*it);
		if (op)
		{
			if (op->get_op() == OpInst::Eq)
			{
				Inst* lhs = op->get_children()->front();
				Inst* rhs = op->get_children()->back();

				if (lhs->get_type() == Num || rhs->get_type() == Num)
					coiNumEqAbSz++;
				else if (lhs->get_type() == Sig || rhs->get_type() == Sig)
					coiSigEqAbSz++;
				else
					coiOtherAbSz++;
			}
			else if (op->get_op() == OpInst::NotEq)
			{
				Inst* lhs = op->get_children()->front();
				Inst* rhs = op->get_children()->back();

				if (lhs->get_type() == Num || rhs->get_type() == Num)
					coiNumNeqAbSz++;
				else if (lhs->get_type() == Sig || rhs->get_type() == Sig)
					coiSigNeqAbSz++;
				else
					coiOtherAbSz++;
			}
			else
				coiOtherAbSz++;
		}
		else
			coiOtherAbSz++;

		violNew.push_back(*it);
		violSet.insert(*it);
		_abViol.coiAbSet.insert(*it);
	}
	for (InstL::iterator it = _abViol.concreteConstraints.begin(), end_it = _abViol.concreteConstraints.end(); it != end_it; ++it)
	{
		if (concreteSet.find(*it) != concreteSet.end())
			continue;

		coiCcSz++;
		concreteNew.push_back(*it);
		concreteSet.insert(*it);
		_abViol.coiCcSet.insert(*it);
	}

	for (InstL::iterator it = _abViol.predConstraints.begin(), end_it = _abViol.predConstraints.end(); it != end_it; ++it)
	{
		if (violSet.find(*it) != violSet.end())
			continue;

		predAbSz++;
		violNew.push_back(*it);
		violSet.insert(*it);
		_abViol.predAbSet.insert(*it);
	}
	for (InstL::iterator it = _abViol.predConstraints.begin(), end_it = _abViol.predConstraints.end(); it != end_it; ++it)
	{
		if (concreteSet.find(*it) != concreteSet.end())
			continue;

		predCcSz++;
		concreteNew.push_back(*it);
		concreteSet.insert(*it);
		_abViol.predCcSet.insert(*it);
	}

	for (InstL::iterator it = _abViol.fprojAbConstraints.begin(), end_it = _abViol.fprojAbConstraints.end(); it != end_it; ++it)
	{
		if (violSet.find(*it) != violSet.end())
			continue;

		fprojAbSz++;
		if ((*it)->childrenInfo[NUM])
		{
			if (OpInst::as(*it)->get_op() == OpInst::Eq)
				fprojNumEqAbSz++;
			else
				fprojNumNeqAbSz++;
		}
		else
		{
			if (OpInst::as(*it)->get_op() == OpInst::Eq)
				fprojSigEqAbSz++;
			else
				fprojSigNeqAbSz++;
		}

		violNew.push_back(*it);
		violSet.insert(*it);
		_abViol.fprojAbSet.insert(*it);
	}
	for (InstL::iterator it = _abViol.fprojCcConstraints.begin(), end_it = _abViol.fprojCcConstraints.end(); it != end_it; ++it)
	{
		if (concreteSet.find(*it) != concreteSet.end())
			continue;

		fprojCcSz++;
		if ((*it)->childrenInfo[NUM])
		{
			if (OpInst::as(*it)->get_op() == OpInst::Eq)
				fprojNumEqCcSz++;
			else
				fprojNumNeqCcSz++;
		}
		else
		{
			if (OpInst::as(*it)->get_op() == OpInst::Eq)
				fprojSigEqCcSz++;
			else
				fprojSigNeqCcSz++;
		}

		concreteNew.push_back(*it);
		concreteSet.insert(*it);
		_abViol.fprojCcSet.insert(*it);
	}

	for (InstL::iterator it = _abViol.projAbConstraints.begin(), end_it = _abViol.projAbConstraints.end(); it != end_it; ++it)
	{
		if (violSet.find(*it) != violSet.end())
			continue;

		projAbSz++;
		if ((*it)->childrenInfo[NUM])
		{
			if (OpInst::as(*it)->get_op() == OpInst::Eq)
				projNumEqAbSz++;
			else
				projNumNeqAbSz++;
		}
		else
		{
			if (OpInst::as(*it)->get_op() == OpInst::Eq)
				projSigEqAbSz++;
			else
				projSigNeqAbSz++;
		}

		violNew.push_back(*it);
		violSet.insert(*it);
		_abViol.projAbSet.insert(*it);
	}
	for (InstL::iterator it = _abViol.projCcConstraints.begin(), end_it = _abViol.projCcConstraints.end(); it != end_it; ++it)
	{
		if (concreteSet.find(*it) != concreteSet.end())
			continue;

		projCcSz++;
		if ((*it)->childrenInfo[NUM])
		{
			if (OpInst::as(*it)->get_op() == OpInst::Eq)
				projNumEqCcSz++;
			else
				projNumNeqCcSz++;
		}
		else
		{
			if (OpInst::as(*it)->get_op() == OpInst::Eq)
				projSigEqCcSz++;
			else
				projSigNeqCcSz++;
		}

		concreteNew.push_back(*it);
		concreteSet.insert(*it);
		_abViol.projCcSet.insert(*it);
	}

	for (InstL::iterator it = _abViol.subsConstraints.begin(), end_it = _abViol.subsConstraints.end(); it != end_it; ++it)
	{
		if (violSet.find(*it) != violSet.end())
			continue;

#ifndef SEQUENTIAL_SUBSTITUTION_LEVEL2
		/// Not allowing Ex/Cc and limiting max function composition
		if (((*it)->fcLevel == (*it)->trueFcLevel) && ((*it)->trueFcLevel <= _max_funcLevel))
#endif
		{
			subsAbSz++;
#ifndef TWO_STEP_SUBSTITUTION
			violNew.push_back(*it);
			violSet.insert(*it);
#endif
			_abViol.subsAbSet.insert(*it);
		}
	}

#ifdef ASSERT_DISTINCT_NUMBERS
	{
		InstS sigConsts;
		for (auto& v: violNew)
		{
			OpInst* op = OpInst::as(v);
			if (op && op->get_op() == OpInst::Eq)
			{
				Inst* lhs = op->get_children()->front();
				Inst* rhs = op->get_children()->back();
				if (lhs->get_type() != Num && rhs->get_type() == Num)
					sigConsts.insert(lhs);
				else if (lhs->get_type() == Num && rhs->get_type() != Num)
				{
					sigConsts.insert(rhs);
				}
			}
		}

		for (InstL::iterator it = violNew.begin(); it != violNew.end();)
		{
			OpInst* op = OpInst::as(*it);
			if (op && op->get_op() == OpInst::NotEq)
			{
				Inst* lhs = op->get_children()->front();
				Inst* rhs = op->get_children()->back();
				if (lhs->get_type() != Num && rhs->get_type() == Num)
				{
					if (sigConsts.find(lhs) != sigConsts.end())
					{
						if (_abViol.subsAbSet.find(*it) != _abViol.subsAbSet.end())
							subsAbSz--;
						else if (_abViol.projAbSet.find(*it) != _abViol.projAbSet.end())
						{
							projAbSz--;
							projNumNeqAbSz--;
						}
						else if (_abViol.fprojAbSet.find(*it) != _abViol.fprojAbSet.end())
						{
							fprojAbSz--;
							fprojNumNeqAbSz--;
						}
						else if (_abViol.predAbSet.find(*it) != _abViol.predAbSet.end())
							predAbSz--;
						else
						{
							assert(_abViol.coiAbSet.find(*it) != _abViol.coiAbSet.end());
							coiAbSz--;
							coiNumNeqAbSz--;
						}

						violSet.erase(*it);
						it = violNew.erase(it);

						continue;
					}
				}
				else if (lhs->get_type() == Num && rhs->get_type() != Num)
				{
					if (sigConsts.find(rhs) != sigConsts.end())
					{
						if (_abViol.subsAbSet.find(*it) != _abViol.subsAbSet.end())
							subsAbSz--;
						else if (_abViol.projAbSet.find(*it) != _abViol.projAbSet.end())
						{
							projAbSz--;
							projNumNeqAbSz--;
						}
						else if (_abViol.fprojAbSet.find(*it) != _abViol.fprojAbSet.end())
						{
							fprojAbSz--;
							fprojNumNeqAbSz--;
						}
						else if (_abViol.predAbSet.find(*it) != _abViol.predAbSet.end())
							predAbSz--;
						else
						{
							assert(_abViol.coiAbSet.find(*it) != _abViol.coiAbSet.end());
							coiAbSz--;
							coiNumNeqAbSz--;
						}

						violSet.erase(*it);
						it = violNew.erase(it);

						continue;
					}
				}
			}
			it++;
		}
	}

///
	{
		InstS sigConsts;
		for (auto& v: concreteNew)
		{
			OpInst* op = OpInst::as(v);
			if (op && op->get_op() == OpInst::Eq)
			{
				Inst* lhs = op->get_children()->front();
				Inst* rhs = op->get_children()->back();
				if (lhs->get_type() != Num && rhs->get_type() == Num)
					sigConsts.insert(lhs);
				else if (lhs->get_type() == Num && rhs->get_type() != Num)
				{
					sigConsts.insert(rhs);
				}
			}
		}

		for (InstL::iterator it = concreteNew.begin(); it != concreteNew.end();)
		{
			OpInst* op = OpInst::as(*it);
			if (op && op->get_op() == OpInst::NotEq)
			{
				Inst* lhs = op->get_children()->front();
				Inst* rhs = op->get_children()->back();
				if (lhs->get_type() != Num && rhs->get_type() == Num)
				{
					if (sigConsts.find(lhs) != sigConsts.end())
					{
						if (_abViol.projCcSet.find(*it) != _abViol.projCcSet.end())
						{
							projCcSz--;
							if ((*it)->childrenInfo[NUM])
							{
								if (OpInst::as(*it)->get_op() == OpInst::Eq)
									projNumEqCcSz--;
								else
									projNumNeqCcSz--;
							}
							else
							{
								if (OpInst::as(*it)->get_op() == OpInst::Eq)
									projSigEqCcSz--;
								else
									projSigNeqCcSz--;
							}
						}
						else if (_abViol.fprojCcSet.find(*it) != _abViol.fprojCcSet.end())
						{
							fprojCcSz--;
							if ((*it)->childrenInfo[NUM])
							{
								if (OpInst::as(*it)->get_op() == OpInst::Eq)
									fprojNumEqCcSz--;
								else
									fprojNumNeqCcSz--;
							}
							else
							{
								if (OpInst::as(*it)->get_op() == OpInst::Eq)
									fprojSigEqCcSz--;
								else
									fprojSigNeqCcSz--;
							}
						}
						else if (_abViol.predCcSet.find(*it) != _abViol.predCcSet.end())
							predCcSz--;
						else
							coiCcSz--;

						concreteSet.erase(*it);
						it = concreteNew.erase(it);

						continue;
					}
				}
				else if (lhs->get_type() == Num && rhs->get_type() != Num)
				{
					if (sigConsts.find(rhs) != sigConsts.end())
					{
						if (_abViol.projCcSet.find(*it) != _abViol.projCcSet.end())
						{
							projCcSz--;
							if ((*it)->childrenInfo[NUM])
							{
								if (OpInst::as(*it)->get_op() == OpInst::Eq)
									projNumEqCcSz--;
								else
									projNumNeqCcSz--;
							}
							else
							{
								if (OpInst::as(*it)->get_op() == OpInst::Eq)
									projSigEqCcSz--;
								else
									projSigNeqCcSz--;
							}
						}
						else if (_abViol.fprojCcSet.find(*it) != _abViol.fprojCcSet.end())
						{
							fprojCcSz--;
							if ((*it)->childrenInfo[NUM])
							{
								if (OpInst::as(*it)->get_op() == OpInst::Eq)
									fprojNumEqCcSz--;
								else
									fprojNumNeqCcSz--;
							}
							else
							{
								if (OpInst::as(*it)->get_op() == OpInst::Eq)
									fprojSigEqCcSz--;
								else
									fprojSigNeqCcSz--;
							}
						}
						else if (_abViol.predCcSet.find(*it) != _abViol.predCcSet.end())
							predCcSz--;
						else
							coiCcSz--;

						concreteSet.erase(*it);
						it = concreteNew.erase(it);

						continue;
					}
				}
			}
			it++;
		}
	}

	if (mode == AB_REACH_TOP)
	{
		interpret_distinct_constant(_bad_cube.nextStateConstraints);

		if (mode != AB_CC_ACEXT)
		{
			AVR_LOG(15, 0, "\t(bad cube [in !P+]) sz: " << _bad_cube.nextStateConstraints.size() << endl);
//			for (auto& v: _bad_cube.nextStateConstraints)
//				AVR_LOG(15, 0, "\t\t" << *v << endl);
		}
	}
#endif

	Inst::init_visit2();
	for (auto vit = violNew.begin(); vit != violNew.end(); vit++)
	{
		Inst* tveNext = Inst::all_pre2next(*vit);

		if ((*vit)->is_t1())
		{
			_abViol.t1Constraints.push_back(tveNext);
			_abViol.t1Set.insert(*vit);
		}
		else if ((*vit)->is_t2() || (_abViol.subsAbSet.find(*vit) == _abViol.subsAbSet.end() && _abViol.projAbSet.find(*vit) == _abViol.projAbSet.end()))
		{
			if (!(*vit)->is_t2())
			{
				(*vit)->set_t2();
				OpInst::create(OpInst::LogNot, (*vit))->set_t2();
			}

			_abViol.t2Constraints.push_back(tveNext);
			_abViol.t2Set.insert(*vit);
		}
		else if ((*vit)->is_t3() || _abViol.subsAbSet.find(*vit) == _abViol.subsAbSet.end())
		{
			if (!(*vit)->is_t3())
			{
				(*vit)->set_t3();
				OpInst::create(OpInst::LogNot, (*vit))->set_t3();
			}

			_abViol.t3Constraints.push_back(tveNext);
			_abViol.t3Set.insert(*vit);
		}
		else
		{
			assert ((*vit)->is_t4());
			_abViol.t4Constraints.push_back(tveNext);
			_abViol.t4Set.insert(*vit);
		}
	}

//	cout << "\t(t1)" << endl;
//	for (auto& v: _abViol.t1Constraints)
//		cout << "\t\t" << *v << endl;
//
//	cout << "\t(t2)" << endl;
//	for (auto& v: _abViol.t2Constraints)
//		cout << "\t\t" << *v << endl;
//
//	cout << "\t(t3)" << endl;
//	for (auto& v: _abViol.t3Constraints)
//		cout << "\t\t" << *v << endl;
//
//	cout << "\t(t4)" << endl;
//	for (auto& v: _abViol.t4Constraints)
//		cout << "\t\t" << *v << endl;


	_abViol.mainConstraints.swap(violNew);
	_abViol.concreteConstraints.swap(concreteNew);

  int cube_ab_SigEqSig = 0;
  int cube_ab_SigEqNum = 0;
  int cube_ab_SigEqOther = 0;
  int cube_ab_NumEqOther = 0;
  int cube_ab_OtherEqOther = 0;
  int cube_ab_SigNeqSig = 0;
  int cube_ab_SigNeqNum = 0;
  int cube_ab_SigNeqOther = 0;
  int cube_ab_NumNeqOther = 0;
  int cube_ab_OtherNeqOther = 0;
  int cube_ab_SigBool = 0;
  int cube_ab_Up = 0;
  int cube_ab_Other = 0;
  for (InstL::iterator it = _abViol.mainConstraints.begin(), end_it = _abViol.mainConstraints.end(); it != end_it; ++it)
  {
    Inst* tve = (*it)->get_port();
    OpInst* op = OpInst::as(tve);
    if (op)
    {
      if (op->get_op() == OpInst::Eq)
      {
        Inst* lhs = op->get_children()->front();
        Inst* rhs = op->get_children()->back();

        if (lhs->get_type() == Sig) {
          if (rhs->get_type() == Sig)
            cube_ab_SigEqSig++;
          else if (rhs->get_type() == Num)
            cube_ab_SigEqNum++;
          else
            cube_ab_SigEqOther++;
        }
        else if (lhs->get_type() == Num) {
          if (rhs->get_type() == Sig)
            cube_ab_SigEqNum++;
          else if (rhs->get_type() == Num) {
            cout << "\t(error: Num == Num not expected)\t" << *op << endl;
            assert(0);
          }
          else
            cube_ab_NumEqOther++;
        }
        else {
          if (rhs->get_type() == Sig)
            cube_ab_SigEqOther++;
          else if (rhs->get_type() == Num)
            cube_ab_NumEqOther++;
          else
            cube_ab_OtherEqOther++;
        }
      }
      else if (op->get_op() == OpInst::NotEq)
      {
        Inst* lhs = op->get_children()->front();
        Inst* rhs = op->get_children()->back();

        if (lhs->get_type() == Sig) {
          if (rhs->get_type() == Sig)
            cube_ab_SigNeqSig++;
          else if (rhs->get_type() == Num)
            cube_ab_SigNeqNum++;
          else
            cube_ab_SigNeqOther++;
        }
        else if (lhs->get_type() == Num) {
          if (rhs->get_type() == Sig)
            cube_ab_SigNeqNum++;
          else if (rhs->get_type() == Num) {
            cout << "\t(error: Num != Num not expected)\t" << *op << endl;
            assert(0);
          }
          else
            cube_ab_NumNeqOther++;
        }
        else {
          if (rhs->get_type() == Sig)
            cube_ab_SigNeqOther++;
          else if (rhs->get_type() == Num)
            cube_ab_NumNeqOther++;
          else
            cube_ab_OtherNeqOther++;
        }
      }
      else if (op->get_op() == OpInst::LogNot) {
        Inst* child = op->get_children()->front()->get_port();
        if (child->get_type() == Sig)
          cube_ab_SigBool++;
        else if (OpInst::as(child))
          cube_ab_Up++;
        else {
          cube_ab_Other++;
          cout << "error1: " << *op << endl;
          assert(0);
        }
      }
      else
        cube_ab_Up++;
    }
    else if (tve->get_type() == Sig)
      cube_ab_SigBool++;
    else {
      cube_ab_Other++;
      cout << "error3: " << *op << endl;
      assert(0);
    }
  }

#ifdef TWO_STEP_SUBSTITUTION
	for (auto vit = _abViol.subsAbSet.begin(); vit != _abViol.subsAbSet.end(); vit++)
	{
		Inst* tveNext = all_pre2next(*vit);
#ifdef SINGLE_TIER
		_abViol.t1Constraints.push_back(tveNext);
		_abViol.t1Set.insert(*vit);
#else
	#ifdef DOUBLE_TIER
		_abViol.t2Constraints.push_back(tveNext);
		_abViol.t2Set.insert(*vit);
	#else
		_abViol.t4Constraints.push_back(tveNext);
		_abViol.t4Set.insert(*vit);
	#endif
#endif
	}
#endif

	AVR_LOG(15, 0, "\t(abstract cube) " << _abViol.mainConstraints.size() << "\t("
			<< coiAbSz << " + "
			<< predAbSz << " + "
			<< fprojAbSz << " + "
			<< projAbSz << " + "
			<< subsAbSz << ")" << endl);

	AVR_LOG(15, 0, "\t(concrete cube) " << _abViol.concreteConstraints.size() << "\t("
			<< coiCcSz << " + "
			<< predCcSz << " + "
			<< fprojCcSz << " + "
			<< projCcSz << ")" << endl);

	/// Print main constraints
//	if (mode != AB_CC_ACEXT)
//	{
//		unsigned sz = _abViol.mainConstraints.size();
//		if (_abViol.mainConstraints.size() < 20)
//		{
//			for (auto& v: _abViol.mainConstraints)
//			{
//				if (concreteSet.find(v) != concreteSet.end())
//				{
//					AVR_LOG(15, 0, "\t\t" << *v << endl);
//				}
//				else
//				{
//					AVR_LOG(15, 0, "\t\t" << *v << "\t[a]" << endl);
//				}
//			}
//		}
//	}

#ifndef TWO_STEP_SUBSTITUTION
	assert(_abViol.mainConstraints.size() == (coiAbSz + predAbSz + fprojAbSz + projAbSz + subsAbSz));
#else
	assert(_abViol.mainConstraints.size() == (coiAbSz + predAbSz + fprojAbSz + projAbSz));
#endif

	if (_abViol.concreteConstraints.size() != (coiCcSz + predCcSz + fprojCcSz + projCcSz))
	{
		cout << "cc: " << _abViol.concreteConstraints << endl;
		cout << "coi: " << _abViol.coiCcSet << endl;
		cout << "pre: " << _abViol.predCcSet << endl;
		cout << "fpr: " << _abViol.fprojCcSet << endl;
		cout << "pro: " << _abViol.projCcSet << endl;
	}

//	cout << "\t(coi)" << endl;
//	for (auto& c: _abViol.coiAbSet)
//		cout << "\t\t" << *c << endl;
//
//	cout << "\t(fp)" << endl;
//	for (auto& c: _abViol.fprojAbSet)
//		cout << "\t\t" << *c << endl;

	assert(_abViol.concreteConstraints.size() == (coiCcSz + predCcSz + fprojCcSz + projCcSz));

	assert(coiAbSz == (coiNumEqAbSz + coiNumNeqAbSz + coiSigEqAbSz + coiSigNeqAbSz + coiOtherAbSz));

	assert(fprojAbSz == (fprojNumEqAbSz + fprojNumNeqAbSz + fprojSigEqAbSz + fprojSigNeqAbSz));
	assert(fprojCcSz == (fprojNumEqCcSz + fprojNumNeqCcSz + fprojSigEqCcSz + fprojSigNeqCcSz));

#ifdef DEFAULT_PROJECTION
	assert(projAbSz == (projNumEqAbSz + projNumNeqAbSz + projSigEqAbSz + projSigNeqAbSz));
	assert(projCcSz == (projNumEqCcSz + projNumNeqCcSz + projSigEqCcSz + projSigNeqCcSz));
#endif

	/// Print concrete constraints
//	if (mode != AB_CC_ACEXT)
//	{
//		AVR_LOG(15, 0, "\t(concrete)" << endl);
//		for (auto& v: _abViol.concreteConstraints)
//		{
//			if (violSet.find(v) == violSet.end())
//			{
//				AVR_LOG(15, 0, "\t\t" << *v << endl);
//			}
//		}
//	}

#ifdef PRINT_RELEVANT_WIRES
	/// Print relevant wires next
	if (mode != AB_CC_ACEXT)
	{
		AVR_LOG(15, 0, "\t(next wires)" << endl);
		for (auto& w: _abViol.relevantWiresNext)
		{
			AVR_LOG(15, 0, "\t\t" << *w << endl);
			if (!is_next_wire(w))
				assert(0);
		}
	}

	/// Print relevant wires
	if (mode != AB_CC_ACEXT)
	{
		AVR_LOG(15, 0, "\t(wires)" << endl);
		for (auto& w: _abViol.relevantWires)
		{
			AVR_LOG(15, 0, "\t\t" << *w << endl);
			if (is_next_wire(w))
				assert(0);
		}
	}
#endif

	if (_abViol.mainConstraints.empty())
	{
		AVR_LOG(15, 0, "\t(main constraints empty)" << endl);
//		AVR_LOG(15, 0, _abViol << endl);
//
//		assert(0);

//		AVR_LOG(15, 0, "\t(allowing restricted constraints, since main is empty)" << endl);
//		_abViol.mainConstraints.swap(_abViol.restrictedConstraints);
	}
//	if (_abViol.mainConstraints.empty())
//	{
//		AVR_LOG(15, 0, "\t(allowing path constraints, since main is empty)" << endl);
//		_abViol.mainConstraints.swap(_abViol.pathConstraints);
//	}

//	if (mode != AB_CC_ACEXT)
//	{
//		AVR_LOG(1, 0, _abViol << endl);
//	}

	_numTbCalls++;
	_sizeAbCube += _abViol.mainConstraints.size();
	_sizeCcCube += _abViol.concreteConstraints.size();
	if (_maxSzAbCube < _abViol.mainConstraints.size())
		_maxSzAbCube = _abViol.mainConstraints.size();
	if (_maxSzCcCube < _abViol.concreteConstraints.size())
		_maxSzCcCube = _abViol.concreteConstraints.size();

	_numSvAbCube += relevantPresent.size();
	if (_maxNumSvAbCube < relevantPresent.size())
		_maxNumSvAbCube = relevantPresent.size();

	int tsb = 0;
	for (auto& sv: relevantPresent)
		tsb += sv->get_size();
	_tsbSvAbCube += tsb;
	if (_maxTsbSvAbCube < tsb)
		_maxTsbSvAbCube = tsb;

	_szT1 += _abViol.t1Constraints.size();
	_szT2 += _abViol.t2Constraints.size();
	_szT3 += _abViol.t3Constraints.size();
	_szT4 += _abViol.t4Constraints.size();

	_sizeCoiAbCube += coiAbSz;
	_sizeCoiCcCube += coiCcSz;
	_sizePredAbCube += predAbSz;
	_sizePredCcCube += predCcSz;
	_sizefProjAbCube += fprojAbSz;
	_sizefProjCcCube += fprojCcSz;
	_sizeProjAbCube += projAbSz;
	_sizeProjCcCube += projCcSz;
	_sizeSubsAbCube += subsAbSz;

  _cube_ab_SigEqSig += cube_ab_SigEqSig;
  _cube_ab_SigEqNum += cube_ab_SigEqNum;
  _cube_ab_SigEqOther += cube_ab_SigEqOther;
  _cube_ab_NumEqOther += cube_ab_NumEqOther;
  _cube_ab_OtherEqOther += cube_ab_OtherEqOther;
  _cube_ab_SigNeqSig += cube_ab_SigNeqSig;
  _cube_ab_SigNeqNum += cube_ab_SigNeqNum;
  _cube_ab_SigNeqOther += cube_ab_SigNeqOther;
  _cube_ab_NumNeqOther += cube_ab_NumNeqOther;
  _cube_ab_OtherNeqOther += cube_ab_OtherNeqOther;
  _cube_ab_SigBool += cube_ab_SigBool;
  _cube_ab_Up += cube_ab_Up;
  _cube_ab_Other += cube_ab_Other;

  _sizeCoiNumEqAbCube   += coiNumEqAbSz;
  _sizeCoiNumNeqAbCube  += coiNumNeqAbSz;
  _sizeCoiSigEqAbCube   += coiSigEqAbSz;
  _sizeCoiSigNeqAbCube  += coiSigNeqAbSz;
  _sizeCoiOtherAbCube  += coiOtherAbSz;

	_sizefProjNumEqAbCube   += fprojNumEqAbSz;
	_sizefProjNumNeqAbCube  += fprojNumNeqAbSz;
	_sizefProjSigEqAbCube   += fprojSigEqAbSz;
	_sizefProjSigNeqAbCube  += fprojSigNeqAbSz;

	_sizeProjNumEqAbCube    += projNumEqAbSz;
	_sizeProjNumNeqAbCube   += projNumNeqAbSz;
	_sizeProjSigEqAbCube    += projSigEqAbSz;
	_sizeProjSigNeqAbCube   += projSigNeqAbSz;

	_sizefProjNumEqCcCube   += fprojNumEqCcSz;
	_sizefProjNumNeqCcCube  += fprojNumNeqCcSz;
	_sizefProjSigEqCcCube   += fprojSigEqCcSz;
	_sizefProjSigNeqCcCube  += fprojSigNeqCcSz;

	_sizeProjNumEqCcCube    += projNumEqCcSz;
	_sizeProjNumNeqCcCube   += projNumNeqCcSz;
	_sizeProjSigEqCcCube    += projSigEqCcSz;
	_sizeProjSigNeqCcCube   += projSigNeqCcSz;

	TIME_E(start_time_full, end_time, _tb_cube_time)
	/// END
}

#ifdef TEST_FULL_MUS_REACH
void Reach::generalize_unsat_query(BR_QUERY& q, InstLL& muses) {
	struct rusage usage;
	struct timeval start_time, end_time;
	long long time_diff;

	int nCoreQsat = 0;
	int nCoreQunsat = 0;
	int nMinQsat = 0;
	int nMinQunsat = 0;

	InstL hardQ, softQ;

	Solver* frameSolver = _reach_solvers[q.frameIdx].solver1;
	_collected_cubes.clear();

	for (auto& tve : frameSolver->m_asserts.assumptions)
		collect_cubes(tve);
	for (auto& l : frameSolver->m_asserts.assertions)
		for (auto& tve : l)
			collect_cubes(tve);

	hardQ.swap(_collected_cubes);
	for (auto& v: q.dest)
		softQ.push_back(v);

	AVR_LOG(17, 1, "Hard Query: " << hardQ);
	AVR_LOG(17, 1, "Soft Query: " << softQ);

	InstL unsatCore;

	TIME_S(start_time);
	z3_API* coreSolver = new z3_API(_abstract_mapper, AVR_EXTRA_IDX, true, false);
	coreSolver->s_assert(hardQ);
	int status = coreSolver->find_unsat_core(AB_QUERY_TIMEOUT, hardQ, softQ, unsatCore, nCoreQsat, nCoreQunsat);
	TIME_E(start_time, end_time, _tb_reach_mus_core);

	if (status != AVR_QUSAT)
	{
		Solver* frameSolver = _reach_solvers[q.frameIdx].solver1;
		string comment = "F[" + to_string(q.frameIdx) + "]";

		for (auto& v: q.dest)
			frameSolver->s_assert(v);
		frameSolver->print_asserts(comment);

		AVR_LOG(17, 0, "Hard Query: " << hardQ);
		AVR_LOG(17, 0, "Soft Query: " << softQ);
		cout << endl;
	}
	assert(status == AVR_QUSAT);

	AVR_LOG(17, 1, "Core: " << unsatCore);

	InstL& coreHardQ = hardQ;
	InstL& coreSoftQ = unsatCore;

	AVR_LOG(17, 1, "Core Hard Query: " << coreHardQ);
	AVR_LOG(17, 1, "Core Soft Query: " << coreSoftQ);

	TIME_S(start_time);
	y2_API* minSolver = new y2_API(_abstract_mapper, AVR_EXTRA_IDX, true, false);
	minSolver->s_assert(coreHardQ);
	assert(!softQ.empty());
	minSolver->minimize_unsat_core(AB_QUERY_TIMEOUT, coreSoftQ, muses, nMinQsat, nMinQunsat);
	TIME_E(start_time, end_time, _tb_reach_mus_min);

	assert(!muses.empty());

	AVR_LOG(17, 1, "Gen. Dest: " << muses.front());
	AVR_LOG(15, 0, "\t(" << softQ.size() << " -> " << (coreHardQ.size() + coreSoftQ.size()) << " -> " << (coreHardQ.size() + muses.front().size()) << ")" << endl);
	AVR_LOG(15, 0, "\t(" << q.dest.size() << " -> " << coreSoftQ.size() << " -> " << muses.front().size() << ")" << endl);

	delete coreSolver;
	delete minSolver;

	sz_hard_core_muses_reach += hardQ.size();
	sz_soft_core_muses_reach += softQ.size();
	sz_out_core_muses_reach += unsatCore.size();
	sz_hard_min_muses_reach += coreHardQ.size();
	sz_soft_min_muses_reach += coreSoftQ.size();
	sz_out_min_muses_reach += muses.front().size();
	num_muses_reach += 1;

	num_scalls_sat_muses_reach += nCoreQsat + nMinQsat;
	num_scalls_unsat_muses_reach += nCoreQunsat + nMinQunsat;

	num_scalls_sat_core_muses_reach += nCoreQsat;
	num_scalls_unsat_core_muses_reach += nCoreQunsat;
	num_scalls_sat_min_muses_reach += nMinQsat;
	num_scalls_unsat_min_muses_reach += nMinQunsat;
}
#else
#ifdef TEST_SEMI_MUS_REACH
void Reach::generalize_unsat_query(BR_QUERY& q, InstLL& muses) {
  struct rusage usage;
  struct timeval start_time, end_time;
  long long time_diff;

  int nCoreQsat = 0;
  int nCoreQunsat = 0;
  int nMinQsat = 0;
  int nMinQunsat = 0;

  InstL hardQ, softQ;

  Solver* frameSolver = _reach_solvers[q.frameIdx].solver1;
  _collected_cubes.clear();

  for (auto& tve : frameSolver->m_asserts.assumptions)
    collect_cubes(tve);
  for (auto& l : frameSolver->m_asserts.assertions)
    for (auto& tve : l)
      collect_cubes(tve);

  // Store all fixed constraints
  InstL fixedSet;
  fixedSet.swap(_collected_cubes);

  softQ = fixedSet;
  for (auto& v: q.dest)
    softQ.push_back(v);

  AVR_LOG(17, 1, "Hard Query: " << hardQ);
  AVR_LOG(17, 1, "Soft Query: " << softQ);

  InstL unsatCore;

  TIME_S(start_time);
  z3_API* coreSolver = new z3_API(_abstract_mapper, AVR_EXTRA_IDX, true, false);
  coreSolver->s_assert(hardQ);
  int status = coreSolver->find_unsat_core(AB_QUERY_TIMEOUT, hardQ, softQ, unsatCore, nCoreQsat, nCoreQunsat);
  TIME_E(start_time, end_time, _tb_reach_mus_core);

  if (status != AVR_QUSAT)
  {
    Solver* frameSolver = _reach_solvers[q.frameIdx].solver1;
    string comment = "F[" + to_string(q.frameIdx) + "]";

    for (auto& v: q.dest)
      frameSolver->s_assert(v);
    frameSolver->print_asserts(comment);

    AVR_LOG(17, 0, "Hard Query: " << hardQ);
    AVR_LOG(17, 0, "Soft Query: " << softQ);
    cout << endl;
  }
  assert(status == AVR_QUSAT);

  AVR_LOG(17, 1, "Core: " << unsatCore);

  InstL coreHardQ, coreSoftQ;

  InstS coreHardSet;
  InstS nextSigs;
  Inst::init_visit();
  for (InstL::iterator it = unsatCore.begin(); it != unsatCore.end(); it++)
  {
    Inst* v = *it;
    if (q.dest.find(v) != q.dest.end())
    {
      coreSoftQ.push_back(v);
      // Collect all next sigs
      collect_sig(v, nextSigs);
    }
    else
    {
      coreHardQ.push_back(v);
      coreHardSet.insert(v);
    }
  }

  // Collect all sigs in back cone of nextRegs
  InstToInstM relevantPre;
  for (auto& s: nextSigs)
  {
    InstToSetM::iterator sit = Inst::_m_backward_coi.find(s);
    if (sit != Inst::_m_backward_coi.end())
    {
      for (auto& pre: (*sit).second)
        relevantPre[pre] = pre;
    }
  }

  // Collect all contraints from fixedSet that involve relevantPre only
  for (auto& v: fixedSet)
  {
    if (coreHardSet.find(v) == coreHardSet.end())
    {
      if (q.dest.find(v) == q.dest.end())
      {
        if (find_limited_sigs(v, relevantPre))
          coreHardQ.push_back(v);
      }
    }
  }

  AVR_LOG(17, 1, "Core Hard Query: " << coreHardQ);
  AVR_LOG(17, 1, "Core Soft Query: " << coreSoftQ);

  TIME_S(start_time);
  y2_API* minSolver = new y2_API(_abstract_mapper, AVR_EXTRA_IDX, true, false);
  minSolver->s_assert(coreHardQ);
  assert(!softQ.empty());
  minSolver->minimize_unsat_core(AB_QUERY_TIMEOUT, coreSoftQ, muses, nMinQsat, nMinQunsat);
  TIME_E(start_time, end_time, _tb_reach_mus_min);

  assert(!muses.empty());

  AVR_LOG(17, 1, "Gen. Dest: " << muses.front());
  AVR_LOG(15, 0, "\t(" << softQ.size() << " -> " << (coreHardQ.size() + coreSoftQ.size()) << " -> " << (coreHardQ.size() + muses.front().size()) << ")" << endl);
  AVR_LOG(15, 0, "\t(" << q.dest.size() << " -> " << coreSoftQ.size() << " -> " << muses.front().size() << ")" << endl);

  delete coreSolver;
  delete minSolver;

  sz_hard_core_muses_reach += hardQ.size();
  sz_soft_core_muses_reach += softQ.size();
  sz_out_core_muses_reach += unsatCore.size();
  sz_hard_min_muses_reach += coreHardQ.size();
  sz_soft_min_muses_reach += coreSoftQ.size();
  sz_out_min_muses_reach += muses.front().size();
  num_muses_reach += 1;

  num_scalls_sat_muses_reach += nCoreQsat + nMinQsat;
  num_scalls_unsat_muses_reach += nCoreQunsat + nMinQunsat;

  num_scalls_sat_core_muses_reach += nCoreQsat;
  num_scalls_unsat_core_muses_reach += nCoreQunsat;
  num_scalls_sat_min_muses_reach += nMinQsat;
  num_scalls_unsat_min_muses_reach += nMinQunsat;
}
#else
void Reach::generalize_unsat_query(BR_QUERY& q, InstLL& muses) {
  bool en_y2_core = true;

#ifdef BACKEND_Z3
  en_y2_core = false;
#endif

#ifdef USE_Z3_CORE
  en_y2_core = false;
#endif

	struct rusage usage;
	struct timeval start_time, end_time;
	long long time_diff;

	int nCoreQsat = 0;
	int nCoreQunsat = 0;
	int nMinQsat = 0;
	int nMinQunsat = 0;

	InstL hardQ, softQ;

	if (q.frameIdx != -1) {
    Solver* frameSolver = _reach_solvers[q.frameIdx].solver_main;
    _collected_cubes.clear();

    for (auto& tve : frameSolver->m_asserts.assumptions)
      collect_cubes(tve);
    for (auto& l : frameSolver->m_asserts.assertions)
      for (auto& tve : l)
        collect_cubes(tve);

    hardQ.swap(_collected_cubes);
	}

  for (auto& v: q.dest)
    softQ.push_back(v);

	AVR_LOG(17, 1, "Hard Query: " << hardQ);
	AVR_LOG(17, 1, "Soft Query: " << softQ);

	InstL unsatCore;
	TIME_S(start_time);
	SOLVER_CORE coreSolver(_abstract_mapper, AVR_EXTRA_IDX, true, mus_core);
  int status = coreSolver.find_unsat_core(AB_QUERY_TIMEOUT, hardQ, softQ, unsatCore, nCoreQsat, nCoreQunsat);
  TIME_E(start_time, end_time, _tb_reach_mus_core);

	if (status == AVR_QSAT)
	{
	  if (q.frameIdx != -1) {
      Solver* frameSolver = _reach_solvers[q.frameIdx].solver_main;
      string comment = "F[" + to_string(q.frameIdx) + "]";

      for (auto& v: q.dest)
        frameSolver->s_assert(v);
      frameSolver->print_asserts(comment);
	  }
		AVR_LOG(17, 0, "Hard Query: " << hardQ);
		AVR_LOG(17, 0, "Soft Query: " << softQ);
		cout << endl;
		InstL conjunct_q = hardQ;
		for (auto& v: softQ)
		  conjunct_q.push_back(v);
	  SOLVER_AB tmpSolver(_abstract_mapper, AVR_EXTRA_IDX, false, regular);
	  tmpSolver.s_assert(conjunct_q);
	  int status = tmpSolver.s_check(AB_QUERY_TIMEOUT, false);
	  cout << "Test: Query is " << status << endl;
    tmpSolver.print_query(0, ERROR, "error");
	}
	assert(status == AVR_QUSAT || status == AVR_QTO);

	InstL coreHardQ, coreSoftQ;

  coreHardQ = hardQ;

  AVR_LOG(17, 1, "Core: " << unsatCore);

  coreSoftQ = unsatCore;

	AVR_LOG(17, 1, "Core Hard Query: " << coreHardQ);
	AVR_LOG(17, 1, "Core Soft Query: " << coreSoftQ);

	TIME_S(start_time);
  SOLVER_MUS minSolver(_abstract_mapper, AVR_EXTRA_IDX, true, regular);

  if (!coreHardQ.empty())
    minSolver.s_assert(OpInst::create(OpInst::LogAnd, coreHardQ));
//  int res = minSolver->s_check(AB_QUERY_TIMEOUT);
//  assert (res == AVR_QSAT);

  assert(!softQ.empty());
	minSolver.minimize_core(AB_QUERY_TIMEOUT, coreSoftQ, muses, nMinQsat, nMinQunsat, true);
	TIME_E(start_time, end_time, _tb_reach_mus_min);

  if (muses.empty())
  {
    cout << "Incorrect core derived by " << (en_y2_core?"Y2":"Z3") << endl;
    cout << "Wrong core: " << unsatCore << endl;

    SOLVER_AB ySolver(_abstract_mapper, AVR_EXTRA_IDX, true, regular);
    cout << "Asserting Hard queries" << endl;
    ySolver.s_assert(hardQ);
    cout << "Hard queries asserted" << endl;

    cout << "Checking satisfiability of hard queries" << endl;
    int res = ySolver.s_check(AB_QUERY_TIMEOUT, false);
    cout << "Result: " << res << endl;

    InstLL muses_correct;
    cout << "Asserting incorrect unsat core" << endl;
    ySolver.s_assert(unsatCore);
    cout << "Incorrect core asserted" << endl;
    cout << "Finding missing core assertions" << endl;
    ySolver.minimize_core(AB_QUERY_TIMEOUT, softQ, muses_correct, nMinQsat, nMinQunsat);
    assert(!muses_correct.empty());
    cout << "Missing assertions in MUS: " << muses_correct.front() << endl;


//    y2_API* ySolver = new y2_API(_abstract_mapper, AVR_EXTRA_IDX, true, false);
//    cout << "Asserting Hard queries" << endl;
//    ySolver->s_assert(coreHardQ);
//    cout << "Hard queries asserted" << endl;
//
//    cout << "Checking satisfiability of hard queries" << endl;
//    int res = ySolver->s_check(AB_QUERY_TIMEOUT);
//    cout << "Result: " << res << endl;
//
//    cout << "Adding push level" << endl;
//    ySolver->s_push();
//    cout << "Asserting Soft queries" << endl;
//    ySolver->s_assert(coreSoftQ);
//    cout << "Soft queries asserted" << endl;
//
//    cout << "Checking satisfiability of hard+soft queries" << endl;
//    res = ySolver->s_check(AB_QUERY_TIMEOUT);
//    cout << "Result: " << res << endl;
//    cout << "Printing core: " << res << endl;
//    ySolver->dump_core();

    assert(0);
  }

	AVR_LOG(17, 1, "Gen. Dest: " << muses.front());
	AVR_LOG(15, 0, "\t(" << hardQ.size() << " + " << softQ.size() << " -> " << coreHardQ.size() << " + " << coreSoftQ.size() << ")" << endl);
	AVR_LOG(15, 0, "\t(" << q.dest.size() << " -> " << coreSoftQ.size() << " -> " << muses.front().size() << ")" << endl);

  if (en_y2_core && (unsatCore.size() != muses.front().size()))
  {
    assert(muses.front().size() < unsatCore.size());

//    cout << "Not a minimal core: " << endl;
//    cout << "Non-minimal core: #" << unsatCore.size() << endl;
//    cout << unsatCore << endl;
//
//    cout << "Minimal unsat core: #" << muses.front().size() << endl;
//    cout << muses.front() << endl;

//    assert(0);
  }

	sz_hard_core_muses_reach += hardQ.size();
	sz_soft_core_muses_reach += softQ.size();
	sz_out_core_muses_reach += unsatCore.size();
	sz_hard_min_muses_reach += coreHardQ.size();
	sz_soft_min_muses_reach += coreSoftQ.size();
	sz_out_min_muses_reach += muses.front().size();
	num_muses_reach += 1;

	num_scalls_sat_muses_reach += nCoreQsat + nMinQsat;
	num_scalls_unsat_muses_reach += nCoreQunsat + nMinQunsat;

	num_scalls_sat_core_muses_reach += nCoreQsat;
	num_scalls_unsat_core_muses_reach += nCoreQunsat;
	num_scalls_sat_min_muses_reach += nMinQsat;
	num_scalls_unsat_min_muses_reach += nMinQunsat;

}
#endif
#endif

void Reach::generalize_unsat_query(BR_QUERY& q, InstLL& muses, Solver* coreSolver_orig, Solver* minSolver_orig) {
	Solver* coreSolver = coreSolver_orig;
	Solver* minSolver = minSolver_orig;

	bool en_y2_core = (coreSolver->fetch_solv_name() == SMT_Yices2);

  struct rusage usage;
	struct timeval start_time, end_time;
	long long time_diff;

	int nCoreQsat = 0;
	int nCoreQunsat = 0;
	int nMinQsat = 0;
	int nMinQunsat = 0;

	InstL hardQ, softAnd;

	if (q.frameIdx != -1) {
    Solver* frameSolver = _reach_solvers[q.frameIdx].solver_main;
    _collected_cubes.clear();

    for (auto& tve : frameSolver->m_asserts.assumptions)
      collect_cubes(tve);
    for (auto& l : frameSolver->m_asserts.assertions)
      for (auto& tve : l)
        collect_cubes(tve);

    hardQ.swap(_collected_cubes);
	}

  for (auto& v: q.dest)
    softAnd.push_back(v);

//	AVR_LOG(17, 0, "Soft Queryb4 : " << softAnd);

  if ((_numFrameRes % 50) == 0) {
  	InstV temp(softAnd.begin(), softAnd.end());
  	random_shuffle(temp.begin(), temp.end());
  	copy(temp.begin(), temp.end(), softAnd.begin());
  }
  else
  	softAnd.sort(Inst::CompareInstByChildInfo);

	AVR_LOG(17, 1, "Hard Query: " << hardQ);
	AVR_LOG(17, 1, "Soft Query: " << softAnd);

//	cout << "Soft Query" << endl;
//	for (auto& v: softAnd) {
//		cout << *v << "\t"
//									" " << v->fcLevel <<
//									" " << v->activity <<
//								  " " << v->childrenInfo[EQ] <<
//									" " << v->childrenInfo[NUM] <<
//									endl;
//	}
//
//	if (Solver::num_ab_query > 1000)
//		assert(0);

	InstL coreSoftAnd;

	TIME_S(start_time);
#ifdef NEW_SOLVER_FOR_AB_MUS
	SOLVER_CORE newCoreSolver(_abstract_mapper, AVR_EXTRA_IDX, true, mus_core);
	newCoreSolver.disable_model();
	newCoreSolver.s_assert(hardQ);
	coreSolver = &newCoreSolver;
	minSolver = &newCoreSolver;
#endif

#ifdef INDUCTIVE_BLOCKING
	coreSolver->enable_induct_np();
#endif
	int status = coreSolver->get_unsat_core(AB_QUERY_TIMEOUT, softAnd, coreSoftAnd, nCoreQsat, nCoreQunsat);
#ifdef INDUCTIVE_BLOCKING
  coreSolver->disable_induct();
#endif
  TIME_E(start_time, end_time, _tb_reach_mus_core);

	if (status == AVR_QSAT)
	{
		cout << "core solver id: " << coreSolver->get_solver_id() << endl;
#ifdef TRACE_SOLVER
  	coreSolver->print_trace("core", true);
#endif

		AVR_LOG(17, 0, "Hard Query: " << hardQ);
		AVR_LOG(17, 0, "Soft And  : " << softAnd);

		cout << endl;
		InstL conjunct_q = hardQ;
	  SOLVER_AB tmpSolver(_abstract_mapper, AVR_EXTRA_IDX, false, regular);
	  cout << "Asserting hard constraints" << endl;
	  tmpSolver.s_assert(conjunct_q);
	  cout << "Checking hard constraints" << endl;
	  int status = tmpSolver.s_check(AB_QUERY_TIMEOUT, false);
	  cout << "Query is " << status << endl;

	  cout << "Extracting core from soft constraints" << endl;
	  InstL tmp;
	  int status_tmp = tmpSolver.get_unsat_core(AB_QUERY_TIMEOUT, softAnd, tmp, nCoreQsat, nCoreQunsat);
	  cout << "Query is " << status_tmp << endl;
	  cout << "Core is " << tmp << endl;

    tmpSolver.print_query(0, ERROR, "error");
	}
	assert(status == AVR_QUSAT || status == AVR_QTO);

	InstL& coreHardQ = hardQ;

	AVR_LOG(15, 0, "\t(" << hardQ.size() << " + " << softAnd.size() << " -> " << coreHardQ.size() << " + " << coreSoftAnd.size() << ")" << endl);

	coreSoftAnd.sort(Inst::CompareInstByChildInfo);

  AVR_LOG(17, 1, "Core: " << coreSoftAnd);

	AVR_LOG(17, 6, "Core Hard Query: " << coreHardQ);
	AVR_LOG(17, 1, "Core Soft And  : " << coreSoftAnd);

	TIME_S(start_time);

  assert(!coreSoftAnd.empty());

  if (false && coreSoftAnd.size() == 1)
	  muses.push_back(coreSoftAnd);
  else {
#ifdef INDUCTIVE_BLOCKING
	  minSolver->enable_induct_np();
#endif
	  minSolver->minimize_core(AB_QUERY_TIMEOUT, coreSoftAnd, muses, nMinQsat, nMinQunsat, true);
#ifdef INDUCTIVE_BLOCKING
	minSolver->disable_induct();
#endif
  }
	TIME_E(start_time, end_time, _tb_reach_mus_min);

	AVR_LOG(15, 0, "\t(" << q.dest.size() << " -> " << coreSoftAnd.size() << " -> " << muses.front().size() << ")" << endl);

  if (muses.empty())
  {
#ifdef TRACE_SOLVER
  	coreSolver->print_trace("core", true);
#endif

  	cout << "Incorrect core derived by " << (en_y2_core?"Y2":"Z3") << endl;
    cout << "Wrong core: " << coreSoftAnd << endl;

    for (auto& v: coreSoftAnd) {
    	coreSolver->s_assert(v);
    	int result = coreSolver->s_check(0, false);
      cout << "asserting: " << *v;
    	cout << "\tresult: " << result << endl;
    }

    SOLVER_AB* ySolver = new SOLVER_AB(_abstract_mapper, AVR_EXTRA_IDX, true, regular);
    cout << "Asserting Hard queries" << endl;
    ySolver->s_assert(hardQ);
    cout << "Hard queries asserted" << endl;

    cout << "Checking satisfiability of hard queries" << endl;
    int res = ySolver->s_check(AB_QUERY_TIMEOUT, false);
    cout << "Result: " << res << endl;

    InstLL muses_correct;
    cout << "Asserting incorrect unsat core" << endl;
    ySolver->s_assert(coreSoftAnd);
    cout << "Incorrect core asserted" << endl;

    cout << "Checking satisfiability with core" << endl;
    int res2 = ySolver->s_check(AB_QUERY_TIMEOUT, false);
    cout << "Result: " << res2 << endl;

    if (res2 == AVR_QSAT) {
			cout << "Finding missing core assertions" << endl;
#ifdef INDUCTIVE_BLOCKING
			ySolver->enable_induct_np();
#endif
			ySolver->minimize_core(AB_QUERY_TIMEOUT, softAnd, muses_correct, nMinQsat, nMinQunsat);
			assert(!muses_correct.empty());
			cout << "Missing assertions in MUS: " << muses_correct.front() << endl;
    }
    else if (res2 == AVR_QUSAT) {
			cout << "Unknown error, core seems correct" << endl;
    }

    cout << "Retrying core extraction" << endl;

    SOLVER_AB* ySolver2 = new SOLVER_AB(_abstract_mapper, AVR_EXTRA_IDX, true, regular);
    cout << "Asserting Hard queries" << endl;
    ySolver2->s_assert(hardQ);
    cout << "Hard queries asserted" << endl;

    coreSoftAnd.clear();
  	status = ySolver2->get_unsat_core(AB_QUERY_TIMEOUT, softAnd, coreSoftAnd, nCoreQsat, nCoreQunsat);
  	cout << "Core: " << coreSoftAnd << endl;

    InstLL muses_tmp;
  	ySolver2->minimize_core(AB_QUERY_TIMEOUT, coreSoftAnd, muses_tmp, nCoreQsat, nCoreQunsat);
  	cout << "# Mus: " << muses_tmp.size() << endl;
  	for (auto& m: muses_tmp)
  		cout << "Mus: " << m << endl;

//    y2_API* ySolver = new y2_API(_abstract_mapper, AVR_EXTRA_IDX, true, false);
//    cout << "Asserting Hard queries" << endl;
//    ySolver->s_assert(coreHardQ);
//    cout << "Hard queries asserted" << endl;
//
//    cout << "Checking satisfiability of hard queries" << endl;
//    int res = ySolver->s_check(AB_QUERY_TIMEOUT);
//    cout << "Result: " << res << endl;
//
//    cout << "Adding push level" << endl;
//    ySolver->s_push();
//    cout << "Asserting Soft queries" << endl;
//    ySolver->s_assert(coreSoftQ);
//    cout << "Soft queries asserted" << endl;
//
//    cout << "Checking satisfiability of hard+soft queries" << endl;
//    res = ySolver->s_check(AB_QUERY_TIMEOUT);
//    cout << "Result: " << res << endl;
//    cout << "Printing core: " << res << endl;
//    ySolver->dump_core();

    assert(0);
  }
  assert(!muses.empty());

  InstL coreSoftAnd2;
	if (true)
	{
		InstLL muses2;
		coreSoftAnd2 = muses.front();

		coreSoftAnd2.sort(Inst::CompareInstByChildInfo);
		bool modified = add_constraints_using_numbers(coreSoftAnd2);

		if (modified) {
			muses.pop_front();
			AVR_LOG(17, 1, "Core2: " << coreSoftAnd2);

			AVR_LOG(17, 6, "Core Hard Query: " << coreHardQ);
			AVR_LOG(17, 1, "Core Soft And2  : " << coreSoftAnd2);

			TIME_S(start_time);

			assert(!coreSoftAnd2.empty());
			if (coreSoftAnd2.size() == 1)
			  muses2.push_back(coreSoftAnd2);
			else {
#ifdef INDUCTIVE_BLOCKING
			  minSolver->enable_induct_np();
#endif
			  minSolver->minimize_core(AB_QUERY_TIMEOUT, coreSoftAnd2, muses2, nMinQsat, nMinQunsat, true);
#ifdef INDUCTIVE_BLOCKING
			  minSolver->disable_induct();
#endif
			}
			TIME_E(start_time, end_time, _tb_reach_mus_min);

			for (auto& mus: muses2)
				muses.push_front(mus);
			AVR_LOG(15, 0, "\t(" << q.dest.size() << " -> " << coreSoftAnd.size() << " -> " << coreSoftAnd2.size() << " -> " << muses.front().size() << ")" << endl);
		}
		else {
			AVR_LOG(15, 0, "\t(" << q.dest.size() << " -> " << coreSoftAnd.size() << " -> " << muses.front().size() << ")" << endl);
		}
	}
	else {
		AVR_LOG(15, 0, "\t(" << q.dest.size() << " -> " << coreSoftAnd.size() << " -> " << muses.front().size() << ")" << endl);
	}

  if (muses.empty())
  {
#ifdef TRACE_SOLVER
  	minSolver->print_trace("min_trace", true);
#endif

    cout << "Incorrect core derived by " << (en_y2_core?"Y2":"Z3") << endl;
    cout << "Wrong core: " << coreSoftAnd << endl;
    cout << "Wrong core2: " << coreSoftAnd2 << endl;

//		// correctness
//		{
//    	minSolver->s_assert_retractable(coreSoftAnd2);
//			int final_res = minSolver->s_check_assume(AB_QUERY_TIMEOUT, false);
//			cout << "res min: " << final_res << endl;
//			assert(final_res == AVR_QUSAT);
//			minSolver->s_retract_assertions();
//		}

    SOLVER_AB* ySolver = new SOLVER_AB(_abstract_mapper, AVR_EXTRA_IDX, true, regular);
    cout << "Asserting Hard queries" << endl;
    ySolver->s_assert(hardQ);
    cout << "Hard queries asserted" << endl;

    cout << "Checking satisfiability of hard queries" << endl;
    int res = ySolver->s_check(AB_QUERY_TIMEOUT, false);
    cout << "Result: " << res << endl;

    InstLL muses_correct;
    cout << "Asserting incorrect unsat core" << endl;
    ySolver->s_assert(coreSoftAnd2);
    cout << "Incorrect core asserted" << endl;


		cout << "Checking satisfiability of hard + incorrect unsat core queries" << endl;
		res = ySolver->s_check(AB_QUERY_TIMEOUT, false);
		cout << "Result: " << res << endl;

		if (res == AVR_QUSAT) {
			cout << "hard + incorrect unsat core unsatisfiable, unable to locate error" << endl;
			assert(0);
//			coreSolver->print_trace("core", true);
//			ySolver->print_trace("fresh", true);
    }

    cout << "Finding missing core assertions" << endl;
#ifdef INDUCTIVE_BLOCKING
    ySolver->enable_induct_np();
#endif
    ySolver->minimize_core(AB_QUERY_TIMEOUT, softAnd, muses_correct, nMinQsat, nMinQunsat);
    assert(!muses_correct.empty());
    cout << "Missing assertions in MUS: " << muses_correct.front() << endl;


//    y2_API* ySolver = new y2_API(_abstract_mapper, AVR_EXTRA_IDX, true, false);
//    cout << "Asserting Hard queries" << endl;
//    ySolver->s_assert(coreHardQ);
//    cout << "Hard queries asserted" << endl;
//
//    cout << "Checking satisfiability of hard queries" << endl;
//    int res = ySolver->s_check(AB_QUERY_TIMEOUT);
//    cout << "Result: " << res << endl;
//
//    cout << "Adding push level" << endl;
//    ySolver->s_push();
//    cout << "Asserting Soft queries" << endl;
//    ySolver->s_assert(coreSoftQ);
//    cout << "Soft queries asserted" << endl;
//
//    cout << "Checking satisfiability of hard+soft queries" << endl;
//    res = ySolver->s_check(AB_QUERY_TIMEOUT);
//    cout << "Result: " << res << endl;
//    cout << "Printing core: " << res << endl;
//    ySolver->dump_core();

    assert(0);
  }
	assert(!muses.empty());

#ifdef VERIFY_MUS
  y2_API ySolver(_abstract_mapper, AVR_EXTRA_IDX, true, regular);
  ySolver.s_assert(hardQ);
  ySolver.s_assert(muses.front());
  int res = ySolver.s_check(AB_QUERY_TIMEOUT, false);
  if (res == AVR_QSAT) {
  	cout << "Incorrect mus derived by " << (en_y2_core?"Y2":"Z3") << endl;
    cout << "Wrong mus: " << muses.front() << endl;

    y2_API* tmpSolver = new y2_API(_abstract_mapper, AVR_EXTRA_IDX, true, regular);
    cout << "Asserting Hard queries" << endl;
    tmpSolver->s_assert(hardQ);
    cout << "Hard queries asserted" << endl;

    cout << "Checking satisfiability of hard queries" << endl;
    int res = tmpSolver->s_check(AB_QUERY_TIMEOUT, false);
    cout << "Result: " << res << endl;

    InstLL muses_correct;
    cout << "Finding missing core assertions" << endl;
    tmpSolver->minimize_core(AB_QUERY_TIMEOUT, coreSoftAnd, muses_correct, nMinQsat, nMinQunsat);
    assert(!muses_correct.empty());
    cout << "Correct MUS: " << muses_correct.front() << endl;

    assert(0);
  }
#endif

	AVR_LOG(17, 1, "Gen. Dest: " << muses.front());

  if (en_y2_core && (coreSoftAnd.size() != muses.front().size()))
  {
//    assert(muses.front().size() < coreSoftAnd.size());

//    cout << "Not a minimal core: " << endl;
//    cout << "Non-minimal core: #" << unsatCore.size() << endl;
//    cout << unsatCore << endl;
//
//    cout << "Minimal unsat core: #" << muses.front().size() << endl;
//    cout << muses.front() << endl;

//    assert(0);
  }

//  if (false)
//  {
//    m5_API tmpSolver(_abstract_mapper, AVR_EXTRA_IDX, true, regular);
//    InstL conjunct_q;
////    InstL conjunct_q = hardQ;
//    InstL conjunct_src;
//    negated_cubes(q.frameIdx, conjunct_src);
//
//    conjunct_q = conjunct_src;
//    conjunct_q.push_back(_ve_model);
//    conjunct_q.push_back(_ve_prop_eq_1);
//    conjunct_q.push_back(_ve_model_nsf);
//    conjunct_q.push_back(_ve_model_next);
//
//    for(auto& v: _negated_refs)
//      conjunct_q.push_back(v);
//
//
//    tmpSolver.s_assert(conjunct_q);
//    int tmp_res = tmpSolver.s_check(0, false);
//    cout << "F ^ P ^ T is " << tmp_res << endl;
//    assert(tmp_res == AVR_QSAT);
//
//    InstLL muses_tmp;
//  	tmp_res = tmpSolver.get_muses_2(AB_QUERY_TIMEOUT, muses.front(), muses_tmp, nCoreQsat, nCoreQunsat, &tmpSolver);
//
////  	if (tmp_res) {
////			cout << "# Mus: " << muses_tmp.size() << endl;
////			for (auto& m: muses_tmp)
////				cout << "Mus: " << m << endl;
////  	}
//  	assert(tmp_res);
//  }

	sz_hard_core_muses_reach += hardQ.size();
	sz_soft_core_muses_reach += softAnd.size();
	sz_out_core_muses_reach += coreSoftAnd.size();
	sz_hard_min_muses_reach += coreHardQ.size();
	sz_soft_min_muses_reach += coreSoftAnd.size();
	sz_out_min_muses_reach += muses.front().size();
	num_muses_reach += 1;

	num_scalls_sat_muses_reach += nCoreQsat + nMinQsat;
	num_scalls_unsat_muses_reach += nCoreQunsat + nMinQunsat;

	num_scalls_sat_core_muses_reach += nCoreQsat;
	num_scalls_unsat_core_muses_reach += nCoreQunsat;
	num_scalls_sat_min_muses_reach += nMinQsat;
	num_scalls_unsat_min_muses_reach += nMinQunsat;

}

int Reach::ccext_block() {
	struct rusage usage;
	struct timeval start_time_full, start_time, end_time;
	long long time_diff;

	unsigned priority = 100000;	//-1;

	_nBlocks++;
//#if 1
//	Inst *ve_seed_viol = OpInst::create(OpInst::LogAnd, _cube.mainConstraints);
//#else
//	Inst *ve_seed_viol;
//	{
//		Inst *cube_next = OpInst::create(OpInst::LogAnd, _ve_model_next);
//		ve_seed_viol = trace_back(cube_next);
//	}
//#endif

//	std::InstToInstM m_np;// map of next and present cubes

	//_tb_queue.push_back(make_pair(_frame_idx, ve_seed_viol));
	PQElement* temp = _tb_queue.PQ_push(priority--, _frame_idx, _abViol, NULL);
//	AVR_LOG(15, 0, "\n\tC: " << *temp->cube << " in F[" << temp->frame << "] " << "\t (Next: " << *(_next_state) << "])" << endl);

	AVR_LOG(6, 4, "Pushed " << temp->abViol << " at F[" << temp->frame << "] " << " with prio: " << temp->prio << endl);

	//assert(0);
	//	int ccext_block_loop_idx = 0;

	int oldFrameIdx = _frame_idx + 1;

	int itCount = 0;
	while (!_tb_queue.PQ_empty()) {
		//assert(_tb_queue.size() < 12);
		PQElement *head = _tb_queue.PQ_head();
		int idx = head->frame;
//		cout << "priority: " << priority << endl;
		if (idx == 0) {// This cannot happen in this function
			//_tb_queue.pop_back();
			return 1; // Property is violated
		}

		ABSTRACT_REACH_VIOL abViol = head->abViol;
		Inst* nextState;
		if (abViol.nextStateConstraints.empty())
			nextState = NumInst::create(1, 1, SORT());
		else
			nextState = OpInst::create(OpInst::LogAnd, abViol.nextStateConstraints);

		PQElement *PQ_next = head->pNext;
		//		Inst *cube_next = frame_down(cube);
		//_queue.PQ_print("POP1");
		AVR_LOG(6, 1, "@@	QUEUE POP " << idx << " (queue size : " << _tb_queue.PQ_size() << ")" << endl);
		_tb_queue.PQ_pop();
		_nObligs++;

//		cout << "cube_v: " << *cube_v << endl;
//		cout << "cube_p: " << *cube_p << endl;

		InstL conjunct_cube;
		InstL conjunct_cube_v;
		InstL conjunct_cube_p;

		InstS set_cube;

		for (auto& v: abViol.mainConstraints)
		{
			if (set_cube.find(v) == set_cube.end())
			{
				set_cube.insert(v);
				conjunct_cube.push_back(v);
				conjunct_cube_v.push_back(v);
			}
		}

#ifdef SUBSTITUTION
		for (auto& v: abViol.subsConstraints)
		{
			if (set_cube.find(v) == set_cube.end())
			{
				set_cube.insert(v);
				conjunct_cube.push_back(v);
			}
		}
#endif

#ifdef REACH_ADD_PATH_CONSTRAINTS
		for (auto& v: abViol.pathConstraints)
		{
			if (set_cube.find(v) == set_cube.end())
			{
				set_cube.insert(v);
				conjunct_cube.push_back(v);
				conjunct_cube_p.push_back(v);
			}
		}
#endif

		Inst* cube;
		if (conjunct_cube.empty())
			cube = NumInst::create(1, 1, SORT());
		else
			cube = OpInst::create(OpInst::LogAnd, conjunct_cube);

		Inst* cube_v;
		if (conjunct_cube_v.empty())
			cube_v = NumInst::create(1, 1, SORT());
		else
			cube_v = OpInst::create(OpInst::LogAnd, conjunct_cube_v);

		Inst* cube_p;
		if (conjunct_cube_p.empty())
			cube_p = NumInst::create(1, 1, SORT());
		else
			cube_p = OpInst::create(OpInst::LogAnd, conjunct_cube_p);

		TIME_S(start_time);


	if (Config::g_forward_check == FORWARDCHECK_ONESTEP) {
		CLAUSE cl_cube(conjunct_cube);
		if (check_blocked(idx, cl_cube)) {
			TIME_E(start_time, end_time, _tb_ct_time);
			continue;
		}
	}

		if (true) {
			bool hasInit = cube_contain_inits(cube);
			if (hasInit) {
				Inst::num_warnings++;
				AVR_LOG(15, 0, "\t(warning: cube intersects with initial states)\t" << *cube << endl);

//				if (Config::g_ab_interpret_limit != 0)
//					assert(0);

//				if (!Config::g_ab_interpret || Config::g_ab_interpret_limit != 0)
				{
					_tb_queue.PQ_push(priority--, idx, _abViol, PQ_next);
					TIME_E(start_time, end_time, _tb_ct_time);
					return 1; // We've got the CCEXT
				}

//				/// conjoining !I
//				Inst* init = OpInst::create(OpInst::LogAnd, _negated_cubes[0]);
//				conjunct_cube.push_back(OpInst::create(OpInst::LogNot, init));
//				cube = OpInst::create(OpInst::LogAnd, conjunct_cube);
//				AVR_LOG(15, 0, "\t\t   (forcing elimination of initial states from original cube)" << endl);

//      assert(0);
//			AVR_LOG(15, 0, "\t(flushing due to intersection with initial states)" << endl);
//			return 3;
			}
//    assert(!hasInit);
		}

		TIME_E(start_time, end_time, _tb_ct_time);

//		/// Aman (not working currently)
//		{
//			InstL dummy;
//			if (check_blocked_using_solver(idx, conjunct_cube, dummy, itCount))
//			{
//				AVR_LOG(15, 0, "\n\t\t(cube check in F[" << idx << "]: already blocked)" << endl);
////				if (itCount != 0)
////					continue;
//			}
//		}

    TIME_S(start_time_full);

		Inst *cube_next = Inst::all_pre2next(cube);
		Inst *cube_next_v = Inst::all_pre2next(cube_v);
		Inst *cube_next_p = Inst::all_pre2next(cube_p);

		BR_QUERY brQuery;

		InstL assumptions;

		for (auto& v: conjunct_cube)
		{
			Inst* vNext = Inst::all_pre2next(v);
      assumptions.push_back(vNext);
      brQuery.dest.insert(vNext);
		}

		InstL conjunct_reach;

//		InstL conjunct_reach_wo_ref;

		negated_cubes(idx - 1, conjunct_reach);
//		cout << "F" << (idx - 1) << " is " << conjunct_reach << endl;
		brQuery.frameIdx = (idx - 1);

//		cout << "conjunct_reach is " << conjunct_reach << endl;
		//if(idx > 1)
		{
			conjunct_reach.push_back(_ve_model);
//			conjunct_reach.push_back(_ve_prop_eq_1);
		}

		InstS relevantNext;
		Inst::collect_next_reg(cube_next, relevantNext, true);

//		for (auto& t: Inst::_m_sn)
//			relevantNext.insert(t.first);

		for (auto& sigNext : relevantNext)
		{
			Inst* coneT = Inst::fetch_trelation(sigNext);
			conjunct_reach.push_back(coneT);
			brQuery.Trel.insert(make_pair(sigNext, coneT));
		}
		_relevantT += relevantNext.size();

//		conjunct_reach.push_back(_ve_model_nsf);

		conjunct_reach.push_back(_ve_model_next);
		conjunct_reach.push_back(_ve_prop_next_eq_1);

//		conjunct_reach_wo_ref = conjunct_reach;

		for (InstL::iterator it3 = _negated_refs.begin(); it3 != _negated_refs.end(); ++it3)
			conjunct_reach.push_back(*it3);
		InstL conjunct_wo_cube_next = conjunct_reach;

#ifdef AVR_CUBE_SORT
		// sort _collected_cubes from the end of the string
		// a$7, b$7, a$6, b$6, a$5, b$5, c$5, ...
		InstL vel_sorted;
//		map<string, Inst*, cube_string_sort> m_filtered;
		map<string, Inst*> m_filtered;
		for (InstL::iterator it3 = _collected_cubes.begin(); it3 != _collected_cubes.end(); ++it3) {
			Inst *tve = *it3;
			if(tve->get_type() == Sig){
				string name = SigInst::as(tve)->get_name();
				reverse(name.begin(), name.end());;
				m_filtered[name] = tve;
				continue;
			}

			if((tve->get_type() == Op) && ((OpInst::as(tve))->get_op() == OpInst::LogNot)){
				Inst *ve_ch = (tve->get_children())->front();
				if(ve_ch->get_type() == Sig){
					string name = SigInst::as(ve_ch)->get_name();
					reverse(name.begin(), name.end());;
					m_filtered[name] = tve;
					continue;
				}
			}
			vel_sorted.push_back(tve);
		}

		for(map<string, Inst*>::iterator mit = m_filtered.begin(); mit != m_filtered.end(); ++mit){
			//cout << "CUBE: " << mit->first << endl;
			vel_sorted.push_back(mit->second);
		}
		_collected_cubes = vel_sorted;

//		cout << "_collected_cubes: " << _collected_cubes << endl;
#endif

//		cout << "conjunct reach: " << conjunct_reach << endl;

		AVR_LOG(6, 6, "# all_pre2next # cube: " << *cube << endl);
 		AVR_LOG(6, 6, "# all_pre2next # cube_next: " << *cube_next << endl);

		Inst* ve_reach = OpInst::create(OpInst::LogAnd, conjunct_reach);

		AVR_LOG(15, 2, "\n\tC: " << *cube << " in F[" << idx << "] (fl: " << cube->fcLevel << ")" << endl);
		AVR_LOG(15, 2, "\t\t(Next: " << *nextState << ")" << endl);

		AVR_LOG(15, 0, "\tSAT_a ? [ F[" << (idx - 1) << "] & T & C+ ]: ");

		AVR_LOG(6, 2, "Checking reachability from previous frame" << endl);
		AVR_LOG(6, 4, "C+: " << assumptions << endl);
		AVR_LOG(6, 6, node_count(ve_reach, true) << "ve_reach int : " << _int_node_cnt << ", bool : " << _bool_node_cnt << ", sum : " << _node_cnt << endl);

		AVR_LOG(6, 5, "ve_reach:" << conjunct_reach << endl);

    int frameIdx = idx - 1;

    assert(frameIdx < oldFrameIdx);

    assert(frameIdx < _reach_solvers.size());
    assert(_frame_idx == (_reach_solvers.size() - 1));

    assert(_reach_solvers.size() > frameIdx);
    FRAME_SOLVER& y_solver = _reach_solvers[frameIdx];

//    {
//    	getrusage( RUSAGE_SELF, &usage );
//			unsigned memory_usage = usage.ru_maxrss/1024;
//			if (memory_usage > 0.005 * _global_memory_limit) {
//				cout << "mem: " << memory_usage << endl;
//				delete_solvers();
//				reset_solv();
//				numResetContext++;
//
//	    	getrusage( RUSAGE_SELF, &usage );
//				unsigned memory_usage_pre = usage.ru_maxrss/1024;
//
//				set_frame_solvers();
//				set_cti_solver();
//
//	    	getrusage( RUSAGE_SELF, &usage );
//				unsigned memory_usage_new = usage.ru_maxrss/1024;
//
//				AVR_LOG(15, 0, "\t(memory usage (MB): " << memory_usage << " -> " << memory_usage_pre << " -> " << memory_usage_new << ")" << endl);
//
//				if (memory_usage != memory_usage_pre || memory_usage != memory_usage_new)
//					assert(0);
//			}
//    }


		bool reset = false;
#ifdef REFRESH_FRAME_SOLVERS
		if (y_solver.solver_main->countRefresh > REFRESH_FRAMES_THRESHOLD ||
				y_solver.solver1->countRefresh > REFRESH_FRAMES_THRESHOLD) {
			AVR_LOG(15, 0, "\t(force resetting F[" << frameIdx << "])" << endl);
			reset = true;
		}
#endif
#ifdef REFRESH_FRAME_SOLVERS_QUERY
		if (y_solver.numQ > FRAME_SOLVER::maxQ) {
			AVR_LOG(15, 0, "\t(force resetting (query limit reached) F[" << frameIdx << "])" << endl);
			reset = true;
		}
#endif
		if (reset) {
			reset_frame_solver(frameIdx);
			set_frame_solver(frameIdx);
			y_solver = _reach_solvers[frameIdx];
		}

		AVR_LOG(13, 7, " idx = " << idx << " frame_idx = " << _frame_idx << " rs_idx = " << frameIdx << endl);

		TIME_S(start_time);

		bool added = false;
		InstL conjunct_coneT;
    assert(Inst::_relevantCones.size() > frameIdx);
		for (auto& sigNext: relevantNext)
		{
			if (Inst::_relevantCones[frameIdx].find(sigNext) == Inst::_relevantCones[frameIdx].end())
			{
				added = true;
				Inst::_relevantCones[frameIdx].insert(sigNext);
				Inst* coneT = Inst::fetch_trelation(sigNext);
				y_solver.solver_main->s_assert(coneT);
#ifdef FRAME_SOLVER_MULTI
				y_solver.solver1->s_assert(coneT);
#endif
				conjunct_coneT.push_back(coneT);
			}
		}

		_queryT += Inst::_relevantCones[frameIdx].size();


		/// Aman - Sanity check
#ifdef DO_CORRECTNESS_CHECKS
		TIME_E(start_time, end_time, _tb_reach_time);
		TIME_S(start_time);
		int res = y_solver.solver1->s_check(AB_QUERY_TIMEOUT);
		if (res != 1)
		{
			cout << "res: " << res << endl;
			if (res == 0)
			{
				InstL conjunct_tmp;
				conjunct_tmp = _negated_cubes[idx - 1];
				conjunct_tmp.push_back(_ve_model);
				conjunct_tmp.push_back(_ve_prop_eq_1);
				conjunct_tmp.push_back(_ve_model_next);
				conjunct_tmp.push_back(_ve_prop_next_eq_1);
				for (InstL::iterator it3 = _negated_refs.begin(); it3 != _negated_refs.end(); ++it3) {
					conjunct_tmp.push_back(*it3);
				}

				z3_API* tmpSolver = new z3_API(&_abstract_mapper, AVR_EXTRA_IDX, true, true);
				tmpSolver->s_assert(_ve_model_nsf);
				InstLL muses;
				int res = tmpSolver->get_muses_2(AB_QUERY_TIMEOUT, conjunct_tmp, muses, num_scalls_sat_correctness, num_scalls_unsat_correctness, tmpSolver);
				int count = 0;
				for (InstLL::iterator it_muses2 = muses.begin(); it_muses2 != muses.end(); ++it_muses2)
				{
					count++;
					cout << "[" << count << "]: " << *it_muses2 << endl;
				}
				delete tmpSolver;
			}
		}
		assert(res == 1);
		TIME_E(start_time, end_time, _cc_extra_tb_time);
		TIME_S(start_time);
#endif
		/// END

		if (assumptions.empty()) {
		  AVR_LOG(15, 0, "(warning: cube empty)" << endl);
		  Inst::num_warnings++;
//		  assert(0);
		  assumptions.push_back(NumInst::create(1,1, SORT()));
		}

		int s_check_result = AVR_QTO;

//		if (added)
		{
			s_check_result = y_solver.solver_main->s_check(AB_QUERY_TIMEOUT, false);
			if (s_check_result == AVR_QUSAT) {
				assumptions.clear();
				cube = conjunct_cube.front();
				// possible in relational inputs (like vmt - gulwani_cegar1)
				AVR_LOG(15, 0, "\t(warning: F[" << frameIdx << "] has become UNSAT)" << endl);


//			  {
//			    SOLVER_AB tmpSolver(_abstract_mapper, AVR_EXTRA_IDX, true, regular);
//			    InstL conjunct_q;
//
//			  	negated_cubes(frameIdx, conjunct_q);
//			  	conjunct_q.push_back(_ve_model);
//			  	conjunct_q.push_back(_ve_prop_eq_1);
//			  	for (auto& sigNext : Inst::_relevantCones[frameIdx]) {
//			  		conjunct_q.push_back(Inst::fetch_trelation(sigNext));
//			  	}
//			  	conjunct_q.push_back(_ve_model_next);
//			  	for (InstL::iterator it3 = _negated_refs.begin(); it3 != _negated_refs.end(); ++it3)
//			  		conjunct_q.push_back(*it3);
//
//			  	_collected_cubes.clear();
//			  	for (auto& v: conjunct_q)
//			  		collect_cubes(v, false);
//
//			    InstLL muses_tmp;
//			  	tmpSolver.get_muses_2(AB_QUERY_TIMEOUT, _collected_cubes, muses_tmp, num_scalls_sat_correctness, num_scalls_unsat_correctness, &tmpSolver);
//			  	cout << "# Mus: " << muses_tmp.size() << endl;
//			  	Inst::print_cc();
//			  	for (auto& mus: muses_tmp) {
//			  		cout << "Mus: " << endl;
//				  	for (auto& m: mus) {
//				  		cout << *m << endl;
//				  	}
//			  	}
//			  }
//
//			  assert(0);
			}
			else
				s_check_result = AVR_QTO;
		}

		if (s_check_result == AVR_QTO) {
#if 0
			s_check_result = solveRelative(frameIdx, assumptions, br, false, false);
			if (s_check_result == AVR_QSAT) {
				s_check_result = solveRelative(frameIdx, assumptions, br, true, true);
				if (s_check_result != AVR_QSAT) {
					cout << s_check_result << endl;
					cout << "solver1: " << y_solver.solver1->s_check(0, true) << endl;
					y_solver.solver1->debug();
					cout << "solver2: " << y_solver.solver_main->s_check(0, false) << endl;
					y_solver.solver_main->debug();
				}
				assert(s_check_result == AVR_QSAT);
			}
			else {
				assert(s_check_result == AVR_QUSAT);
			}
			y_solver.solver_main->s_retract_assertions();
#else
			s_check_result = solveRelative(frameIdx, assumptions, br, true, true);
			if (s_check_result == AVR_QSAT) {
			}
			else {
				assert(s_check_result == AVR_QUSAT);
				y_solver.solver1->s_retract_assertions();
			}
#endif
		}
		assert (s_check_result != AVR_QTO);

		/// Aman - Sanity check
#ifndef EX_CC_LEVEL1
#ifdef DO_CORRECTNESS_CHECKS
		TIME_E(start_time, end_time, _tb_reach_time);
		TIME_S(start_time);
		z3_API* y_solver2 = new z3_API(&_abstract_mapper, AVR_EXTRA_IDX, false, true);
		Inst* tve2 = OpInst::create(OpInst::LogAnd, conjunct_wo_cube_next);
		y_solver2->s_assert(tve2);
#ifdef ASSERT_DISTINCT_NUMBERS
		y_solver2->assert_distinct_constants();
#endif
//		for (InstL::iterator cit = conjunct_wo_cube_next.begin(); cit != conjunct_wo_cube_next.end(); cit++)
//		{
//			y_solver2->s_assert(*cit);
//		}
		y_solver2->s_assert_retractable(assumptions);
		int tmpResult = y_solver2->s_check(AB_QUERY_TIMEOUT);

		if ((s_check_result != -1) && (tmpResult != s_check_result))
		{
			cout << endl << "Error in reachability" << endl;
			cout << "Reach: " << s_check_result << endl;
			cout << "Check: " << tmpResult << endl;
//			cout << conjunct_wo_cube_next << endl;
//			cout << conjunct_cube_next << endl;

//			cout << "F[top]: " << _frame_idx << endl;
//			cout << "F[src]: " << (idx - 1) << endl;

			if (tmpResult == 0)
			{
				z3_API* tmpSolver = new z3_API(&_abstract_mapper, AVR_EXTRA_IDX, true, true);
				tmpSolver->s_assert(tve2);
				InstLL muses;
				int res = tmpSolver->get_muses_2(AB_QUERY_TIMEOUT, assumptions, muses, num_scalls_sat_correctness, num_scalls_unsat_correctness);
				int count = 0;
				for (InstLL::iterator it_muses2 = muses.begin(); it_muses2 != muses.end(); ++it_muses2)
				{
					count++;
					cout << "[" << count << "]: " << *it_muses2 << endl;
				}
				tmpResult = y_solver->s_check(AB_QUERY_TIMEOUT);
				delete tmpSolver;
			}
			else if (s_check_result == 0)
			{
#ifdef DEBUG_ERROR
				ofstream out;
				out.open("../bug_yices/query.ys");
				y_solver->s_print_exact_query(out);
				out.close();
//				ofstream out2;
//				out2.open("../bug_yices/query2.ys");
//				y_solver2->s_print_query(out2);
//				out2.close();
//				y_solver->s_debug_c(conjunct_wo_cube_next, conjunct_cube_next);
#endif

//				string fname1 = "y_solver";
//				y_solver->print_smt2(fname1);
//
//				string fname2 = "y_solver2";
//				y_solver2->print_smt2(fname2);

				y_solver->s_retract_assertions();
				InstLL muses;
				int res = y_solver->get_muses_2(AB_QUERY_TIMEOUT, assumptions, muses, num_scalls_sat_correctness, num_scalls_unsat_correctness);
				int count = 0;
				for (InstLL::iterator it_muses2 = muses.begin(); it_muses2 != muses.end(); ++it_muses2)
				{
					count++;
					cout << "[" << count << "]: " << *it_muses2 << endl;
				}
			}
			assert(0);
		}
		y_solver2->s_retract_assertions();
		delete y_solver2;
		TIME_E(start_time, end_time, _cc_extra_tb_time);
		TIME_S(start_time);
#endif
#endif
		/// END

		TIME_E(start_time, end_time, _tb_reach_time);

		if (s_check_result == AVR_QUSAT)
			_sat_res = false;
		else if (s_check_result == AVR_QSAT)
			_sat_res = true;
		else {
			AVR_LOG(6, 0, "br query timed out, exiting" << endl);
			assert(0);
		}
//		AVR_LOG(6, 1, "block, R" << (idx - 1) << " && P && T && C+ && P+ : " << (_sat_res ? "SAT" : "UNSAT") << endl);
		AVR_LOG(6, 2, "bp_reach, res: " << (_sat_res ? "SAT" : "UNSAT") << ", idx: " << (idx - 1) << ", runtime: " << double(time_diff)/1000000 << endl);

		_feas_sat_res = true;

		AVR_LOG(15, 0, (_sat_res ? "SAT" : "UNSAT") << endl);
		AVR_LOG(6, 2, "ccext_reach, res: " << (_sat_res ? "SAT" : "UNSAT") << ", idx: " << (idx - 1) << ", runtime: " << double(time_diff)/1000000 << endl);


		if (_sat_res) {
			_nObligsS++;
	    oldFrameIdx = frameIdx;

			//			get_abst_viols(ve_reach);
			//			derive_eq(_euf_solver);
			PQ_next = _tb_queue.PQ_push(priority--, idx, abViol, PQ_next);

			InstL conjunct_tmp = conjunct_wo_cube_next;
			conjunct_tmp.insert(conjunct_tmp.end(), assumptions.begin(), assumptions.end());
			print_all_abstract_min_term(conjunct_tmp, y_solver.solver1);

			// Correctness check
//			{
//				InstL conjunct_reach;
//				conjunct_reach = _negated_cubes[frameIdx];
//				conjunct_reach.push_back(_ve_model);
//				conjunct_reach.push_back(_ve_prop_eq_1);
//				for (auto& sigNext : Inst::_relevantCones[frameIdx]) {
//					conjunct_reach.push_back(Inst::fetch_trelation(sigNext));
//				}
//				conjunct_reach.push_back(_ve_model_next);
//				for (InstL::iterator it3 = _negated_refs.begin(); it3 != _negated_refs.end(); ++it3)
//					conjunct_reach.push_back(*it3);
//				Inst* ve_reach = OpInst::create(OpInst::LogAnd, conjunct_reach);
//				m5_API tmp_solver(_abstract_mapper, AVR_EXTRA_IDX, false, regular);
//				tmp_solver.s_assert(ve_reach);
//			#ifdef ASSERT_DISTINCT_NUMBERS
//				tmp_solver.assert_distinct_constants();
//			#endif
//				tmp_solver.s_assert_retractable(assumptions);
//			  int tmp_result = tmp_solver.s_check_assume(AB_QUERY_TIMEOUT, false);
//			  cout << "m5 result for id " << tmp_solver.get_solver_id() << " is " << tmp_result << endl;
//			  assert(tmp_result == AVR_QSAT);
//			}

			retrieve_ab_sol(y_solver.solver1, true);

//			print_abstract_min_term_compact(cout, _min_term);

			y_solver.solver1->s_retract_assertions();

//      if (frameIdx > 1)
//			  y_solver.solver1->s_retract_assertions();


			AVR_LOG(6, 2, "Tracing backwards" << endl);
#ifdef INTERACTIVE_CUBE
			cerr << "frame " << frameIdx << endl;
#endif
			trace_back(y_solver.solver1, ve_reach, assumptions, cube_next_v, cube_next_p, (frameIdx == 0)?AB_REACH_INIT:AB_REACH);

	    if (!solvePartition(_abViol, "trans. from F[" + to_string(frameIdx) + "] to dest")) {
	      AVR_LOG(15, 0, "\t(flushing due to global info)" << endl);
        TIME_E(start_time_full, end_time, Solver::time_ccext);
	      return 3;
	    }

	    if (!solveCube(_abViol.mainSubConstraints, _abViol.mainConstraints, "cube in F[" + to_string(frameIdx) + "]")) {
	      AVR_LOG(15, 0, "\t(flushing due to global info)" << endl);
        TIME_E(start_time_full, end_time, Solver::time_ccext);
	      return 3;
	    }

#ifdef PRINT_ALL_ABSTRACT_TRANSITIONS
      string tid = "#" + to_string(ve_reach->get_id());
      AVR_LOG(15, 0, "\t(" << tid << ")" << endl);
      print_states_transitions("fsm_c" + tid + ".txt", _abViol.mainConstraints, conjunct_cube, true, true);
      print_states_transitions("fsm_a" + tid + ".txt", _abViol.mainConstraints, conjunct_cube);
#endif

			if (idx == 1) {
//				/// Add F[0] to cube
//				collect_cubes(_ve_init, true);
//				for (auto& v: _collected_cubes)
//					_abViol.concreteConstraints.push_back(v);


				Inst* gcube_next_tb;
				if (_abViol.mainConstraints.empty())
					gcube_next_tb = NumInst::create(1, 1, SORT());
				else
					gcube_next_tb = OpInst::create(OpInst::LogAnd, _abViol.mainConstraints);

				AVR_LOG(6, 3, "<---" << endl);

				PQElement* temp = _tb_queue.PQ_push(priority--, 0, _abViol, PQ_next);
				AVR_LOG(15, 2, "\n\tC: " << *gcube_next_tb << " in F[" << 0 << "] (fl: " << gcube_next_tb->fcLevel << ")" << endl);
				if (!_abViol.nextStateConstraints.empty())
				{
					AVR_LOG(15, 0, "\t\t(Next: " << *(OpInst::create(OpInst::LogAnd, _abViol.nextStateConstraints)) << ")" << endl);
				}

				AVR_LOG(6, 4, "Pushed " << temp->abViol << " at F[" << temp->frame << "] " << " with prio: " << temp->prio << endl);
				TIME_E(start_time_full, end_time, Solver::time_ccext);
				return 1; // We've got the CCEXT
			}

			AVR_LOG(6, 1, "@@	QUEUE PUSH " << idx << endl);

			Inst* cube_next_tb;
			if (_abViol.mainConstraints.empty())
				cube_next_tb = NumInst::create(1, 1, SORT());
			else
				cube_next_tb = OpInst::create(OpInst::LogAnd, _abViol.mainConstraints);

			AVR_LOG(6, 3, "<---" << endl);
			AVR_LOG(6, 4, "Got C: " << *cube_next_tb << endl);

			Inst *gcube_next_tb = cube_next_tb;
			PQElement* temp = _tb_queue.PQ_push(priority--, idx - 1, _abViol, PQ_next);

			AVR_LOG(6, 3, "cube:" << *gcube_next_tb << endl);
			AVR_LOG(6, 4, "Pushed " << temp->abViol << " at F[" << temp->frame << "] " << " with prio: " << temp->prio << endl);
			AVR_LOG(6, 1, "@@	QUEUE PUSH " << idx-1 << endl);

      TIME_E(start_time_full, end_time, Solver::time_ccext);
			continue;
		} else {
			_nObligsU++;
	    oldFrameIdx = _frame_idx + 1;
		}

//		y_solver.solver1->print_query(0, ERROR, "br_unsat");

//		// correctness check
//		{
//			InstL assumptions2 = assumptions;
//			InstL core;
//			int result = y_solver.solver2->get_unsat_core(AB_QUERY_TIMEOUT, assumptions2, core, num_scalls_sat_correctness, num_scalls_unsat_correctness);
//			if (result != AVR_QUSAT) {
//				cout << "result check: " << result << endl;
//				y_solver.solver1->print_query(0, ERROR, "error_br");
//				assert(0);
//			}
//		}

		Inst *ve_gcube = cube; // generalized cube
		int g_idx = idx;

		InstLL muses;
		InstL gcubes;

		if (assumptions.size() > 1)
		{
			TIME_S(start_time);
			int conj_cube_next_size = assumptions.size();
			AVR_LOG(13, 7, "Query: " << conjunct_reach << endl);
			AVR_LOG(13, 5, "Trying expanding " << assumptions << endl);

			int res = 0;
			assumptions.clear();

//			Solver* mus_solver  = y_solver.solver1;
//			Solver* core_solver = y_solver.solver1;

			Solver* mus_solver  = y_solver.solver_main;
			Solver* core_solver = y_solver.solver_main;

#ifdef BACKEND_Z3
			core_solver = mus_solver;
#endif

//			generalize_unsat_query(brQuery, muses);
      generalize_unsat_query(brQuery, muses, core_solver, mus_solver);
			res = 1;

			if ((res == 0) && !abViol.t1Constraints.empty())
			{
				assumptions.insert(assumptions.end(), abViol.t1Constraints.begin(), abViol.t1Constraints.end());
				res = mus_solver->get_muses_2(AB_QUERY_TIMEOUT, assumptions, muses, num_scalls_sat_muses_reach, num_scalls_unsat_muses_reach, core_solver);

				if (res == 1)
					_nT1++;
			}

			if ((res == 0) && !abViol.t2Constraints.empty())
			{
				assumptions.insert(assumptions.end(), abViol.t2Constraints.begin(), abViol.t2Constraints.end());
				res = mus_solver->get_muses_2(AB_QUERY_TIMEOUT, assumptions, muses, num_scalls_sat_muses_reach, num_scalls_unsat_muses_reach, core_solver);

				if (res == 1)
					_nT2++;
			}

			if ((res == 0) && !abViol.t3Constraints.empty())
			{
				assumptions.insert(assumptions.end(), abViol.t3Constraints.begin(), abViol.t3Constraints.end());
				res = mus_solver->get_muses_2(AB_QUERY_TIMEOUT, assumptions, muses, num_scalls_sat_muses_reach, num_scalls_unsat_muses_reach, core_solver);

				if (res == 1)
					_nT3++;
			}

			if ((res == 0) && !abViol.t4Constraints.empty())
			{
				assumptions.insert(assumptions.end(), abViol.t4Constraints.begin(), abViol.t4Constraints.end());
				res = mus_solver->get_muses_2(AB_QUERY_TIMEOUT, assumptions, muses, num_scalls_sat_muses_reach, num_scalls_unsat_muses_reach, core_solver);

				if (res == 1)
					_nT4++;
			}
			if (res != 1)
			{
				cout << "core: #" << assumptions.size() << "\t" << assumptions << endl;
				cout << "t1  : #" << abViol.t1Constraints.size() << "\t" << abViol.t1Constraints << endl;
				cout << "t2  : #" << abViol.t2Constraints.size() << "\t" << abViol.t2Constraints << endl;
				cout << "t3  : #" << abViol.t3Constraints.size() << "\t" << abViol.t3Constraints << endl;
				cout << "t4  : #" << abViol.t4Constraints.size() << "\t" << abViol.t4Constraints << endl;
			}

			assert(res == 1);

			int num_muses_terms = 0;
			for (InstLL::iterator it_muses2 = muses.begin(); it_muses2 != muses.end(); ++it_muses2)
			{
				num_muses_terms += it_muses2->size();
				_mus_cls++;
			}
			AVR_LOG(6, 1, "$$ block(), solver.get_muses_2: " << conj_cube_next_size << " => "
							<< muses.size() << ", " << num_muses_terms << " : res = " << res << endl);

			_mus_before += conj_cube_next_size;
			_mus_lit+= num_muses_terms;
			_mus_cnt++;
			int muses_idx = 0;
			for (InstLL::iterator it_muses2 = muses.begin(); it_muses2 != muses.end(); ++it_muses2)
			{
				AVR_LOG(6, 4, "idx: " << muses_idx << ", mus: " << *it_muses2 << endl);
				muses_idx++;
			}

			AVR_LOG(6, 2, "bp get_muses_2, idx: " << (idx - 1) << ", runtime: " << double(time_diff)/1000000 << endl);

			if (res == 1 && muses.size() != 0)
			{
				for (InstLL::iterator it_muses = muses.begin(); it_muses != muses.end(); it_muses++)
				{
					Inst* ve_gcube_next = OpInst::create(OpInst::LogAnd, *it_muses);
					if(!ve_gcube_next){
						cout << "(*it_muses.size()): " << (*it_muses).size() << endl;
						AVR_LOG(6, 0, "abViol: " << abViol << endl);
						AVR_LOG(6, 0, "cube: " << *cube << endl);
						AVR_LOG(6, 0, "*it_muses: " << *it_muses << endl);
						assert(0);
					}

					ve_gcube = Inst::all_next2pre(ve_gcube_next);
					AVR_LOG(6, 6, "bp ve_gcube_next: " << *ve_gcube_next << endl << " -> ve_gcube: " << *ve_gcube << endl);

					gcubes.push_back(ve_gcube);
				}
			}
			TIME_E(start_time, end_time, _tb_UNSAT_camus_time);

		}

		if (gcubes.size() == 0) {
			gcubes.push_back(cube);
		}

		int maxBlockIdx = -1;

		AVR_LOG(15, 0, "\n\t\t[MUS(s)]:" << endl);
		int count = 0;
		for (InstL::iterator it_mus = gcubes.begin(); it_mus != gcubes.end(); it_mus++) {
			itCount++;
			AVR_LOG(15, 0, endl);
			ve_gcube = *it_mus;

			TIME_S(start_time);

#ifdef AVR_ADD_INITS_ENABLE
			Inst *ve_gcube_before = ve_gcube;
			AVR_LOG(6, 1, "## call add_inits_to_gcube in ccext_block !" << endl);
//			cout << "Cube: " << *cube << endl;
//			cout << "Gcube: " << *ve_gcube << endl;
//			cout << "Gcubes: " << gcubes << endl;
//			cout << "Gcubes$: " << gcubes_next << endl;

			InstL conjunct_ve_gcube;
			collect_cubes(ve_gcube, true);
			_collected_cubes.swap(conjunct_ve_gcube);
			int resultInit = (cube_contain_inits(ve_gcube) == false) ? 0 : 1;

//			if (resultInit == 1) {
//				{
//					ostringstream tmp;
//					tmp << *ve_gcube_before;
//					tmp.flush();
//					string tmp_s = tmp.str();
//					if (tmp_s == "(_s65_gen_fifos[0].f.entry_gen[0].ff_entry_inst.Q == 16'd0)") {
//						print_frames();
//						{
//							Inst* dest = Inst::all_pre2next(ve_gcube_before);
//							InstL conjunct_src;
//							negated_cubes(frameIdx, conjunct_src);
//
//							Inst* dest_full = Inst::all_pre2next(cube);
//
//							Solver* int_solver = new SOLVER_BV(_abstract_mapper, AVR_EXTRA_IDX, true, regular);
//							int_solver->assert_all_wire_constraints();
//
//							int_solver->s_assert(_ve_model);
//							int res = int_solver->s_check(0, false);
//							cout << "P is: " << res << endl;
//
//							int_solver->s_assert(_ve_prop_eq_1);
//							res = int_solver->s_check(0, false);
//							cout << "P is: " << res << endl;
//
//							int_solver->s_assert(_ve_model_nsf);
//							res = int_solver->s_check(0, false);
//							cout << "P & T is: " << res << endl;
//
//							int_solver->s_assert(_ve_model_next);
//							res = int_solver->s_check(0, false);
//							cout << "P & T is: " << res << endl;
//
//							int_solver->s_assert(dest);
//							res = int_solver->s_check(0, false);
//							cout << "P & T & Dest+ is: " << res << endl;
//
//							int_solver->s_assert(_negated_refs);
//							res = int_solver->s_check(0, false);
//							cout << "P & T & Dest+ & Refs is: " << res << endl;
//
//							InstLL tmp_muses;
//							res = int_solver->get_muses_2(0, conjunct_src, tmp_muses, num_scalls_sat_correctness, num_scalls_unsat_correctness, int_solver);
//							cout << "F" << frameIdx << " & P & T & Dest+ & Refs is: " << res << endl;
//
//							if (!tmp_muses.empty())
//								cout << "Mus: " << tmp_muses.front() << endl;
//
//							int_solver->s_assert(conjunct_src);
//							res = int_solver->s_check(0, false);
//							cout << "F" << frameIdx << " & P & T & Dest+ & Refs is: " << res << endl;
//
////							int_solver->s_assert(dest_full);
//
//							collect_cubes(dest_full, true);
//							res = int_solver->get_muses_2(0, _collected_cubes, tmp_muses, num_scalls_sat_correctness, num_scalls_unsat_correctness, int_solver);
//							cout << "F" << frameIdx << " & P & T & Dest+ & DestFull+ & Refs is: " << res << endl;
//
//							if (!tmp_muses.empty())
//								cout << "Mus: " << tmp_muses.front() << endl;
//
//							assert(0);
//						}
//
//						assert(0);
//					}
//				}
//			}

//			if (resultInit == 1)
//			{
//				restrict_cube(cube, ve_gcube);
//				resultInit = (cube_contain_inits(ve_gcube, true) == false) ? 0 : 1;
//			}


//			resultInit = add_inits_to_gcube(cube, ve_gcube, true);
//			AVR_LOG(15, 0, "")

			/// Aman
//			if(ve_gcube_before != ve_gcube)
//			{
//				AVR_LOG(15, 0, "\t\t   (eliminating initial states from original mus)" << endl);
//			}
			if (resultInit == 1)
			{
				/// !I
				conjunct_ve_gcube.push_back(_ve_initNeg);

				/// ve_gcube <-- ve_gcube && !I
				ve_gcube = OpInst::create(OpInst::LogAnd, conjunct_ve_gcube);
				AVR_LOG(15, 0, "\t\t   (forcing elimination of initial states from original mus)" << endl);
				AVR_LOG(15, 0, "\t\t[" << count << "] (orig) " << *ve_gcube_before << "\n");

#ifdef DO_CORRECTNESS_CHECKS
				TIME_E(start_time, end_time, _tb_ct_time);
				TIME_S(start_time);
				int tmpResult = (cube_contain_inits(ve_gcube, true) == false) ? 0 : 1;
				assert(tmpResult == 0);
				TIME_E(start_time, end_time, _cc_extra_tb_time);
				TIME_S(start_time);
#endif
			}
			/// END
#endif
			ve_gcube = OpInst::create(OpInst::LogAnd, conjunct_ve_gcube);
			count++;
			AVR_LOG(15, 0, "\t\t[" << count << "] w" << ve_gcube->maxSize << "\t" << *ve_gcube << "\n");

			CLAUSE gcube(conjunct_ve_gcube);
			int resultCc = containment_check(g_idx, gcube, itCount);
			AVR_LOG(6, 1, "containment_check result: " << resultCc << endl);

			if (resultCc == 0)
			{
				AVR_LOG(15, 0, "\n\t\t(redundant in F[" << g_idx << "])" << endl);
//				assert(0);
				if (itCount == 1)
				{
					cout << "Complete cube: " << *cube << endl;
					ostringstream ostr;
					ostr << "error/" << *cube;
					draw_graph(1, cube, ostr.str(), 0, false);

					cout << "Derived from: " << endl;
					collect_cubes(ve_gcube, true);
					for (auto& c: _collected_cubes)
					{
						cout << "-> " << *c << endl;
						ostringstream ostr;
						ostr << "error/" << *c;
						draw_graph(1, c, ostr.str(), 0, false);
					}
				}

				if(itCount == 1)
				{
					resultCc = 0;

					Inst::num_warnings++;
					cout << "(Warning: exception in reachability - unable to block cube in F[" << g_idx << "]" << endl;
					cout << "\t(giveup)" << endl;
#ifdef TRACE_SOLVER
					_cti_solver->print_trace("error", false);
#endif
					assert(0);
				}
//				assert(itCount != 1);

			}
			else if (resultCc == 4)
			{
				Inst* tve = OpInst::create(OpInst::LogNot, ve_gcube);
				AVR_LOG(15, 0, "\n\t\t(global info " << *tve << ")" << endl);
				g_idx = _frame_idx;
				add_refinement(tve, "ab");
			}

#ifdef AVR_ADD_INITS_ENABLE
			if(resultInit == 1)
			{
				AVR_LOG(15, 2, "\t\t\t(original mus: " << *ve_gcube_before << ")" << endl);
			}
#endif

			if ((resultCc != 0) && (resultCc != 4))
			{
				Inst* tve = OpInst::create(OpInst::LogNot, ve_gcube);

				/// Get the blocked cube in next state version
				///
				InstL conjunct_blockedCubeNext;
				collect_cubes(ve_gcube, true);
				Inst::init_visit2();
				int musSz = _collected_cubes.size();
				for (auto& c: _collected_cubes)
				{
					conjunct_blockedCubeNext.push_back(Inst::all_pre2next(c));

					Inst* cNeg = OpInst::create(OpInst::LogNot, c);

					if (c->is_t1())
						_selT1++;
					else if (c->is_t2())
						_selT2++;
					else if (c->is_t3())
						_selT3++;
					else if (c->is_t4())
						_selT4++;

					c->upgrade_tier();
					cNeg->upgrade_tier();

					if (abViol.subsAbSet.find(c) != abViol.subsAbSet.end())
					{
						_selSubsAbCube++;
						cout << "\t(2step- " << *c << ")" << endl;
					}
					else if (abViol.projAbSet.find(c) != abViol.projAbSet.end())
					{
						cout << "\n\t\t(missing: " << *c << ")" << endl;
						_selProjAbCube++;
						if (c->childrenInfo[NUM])
						{
							if (OpInst::as(c)->get_op() == OpInst::Eq)
								_selProjNumEqAbCube++;
							else
								_selProjNumNeqAbCube++;
						}
						else
						{
							if (OpInst::as(c)->get_op() == OpInst::Eq)
								_selProjSigEqAbCube++;
							else
								_selProjSigNeqAbCube++;
						}

#ifdef STRUCTURAL_PROJECTION
						Inst* lhs = c->get_children()->front();
						Inst* rhs = c->get_children()->back();
						sa.add_relevant(lhs, rhs);
#endif
					}
					else if (abViol.fprojAbSet.find(c) != abViol.fprojAbSet.end())
					{
						_selfProjAbCube++;
						if (c->childrenInfo[NUM])
						{
							if (OpInst::as(c)->get_op() == OpInst::Eq)
								_selfProjNumEqAbCube++;
							else
								_selfProjNumNeqAbCube++;
						}
						else
						{
							if (OpInst::as(c)->get_op() == OpInst::Eq)
								_selfProjSigEqAbCube++;
							else
								_selfProjSigNeqAbCube++;
						}
					}
					else if (abViol.predAbSet.find(c) != abViol.predAbSet.end())
					{
						_selPredAbCube++;
					}
					else
					{
						_selCoiAbCube++;
            OpInst* op = OpInst::as(c);
            if (op)
            {
              if (op->get_op() == OpInst::Eq)
              {
                Inst* lhs = op->get_children()->front();
                Inst* rhs = op->get_children()->back();

                if (lhs->get_type() == Num || rhs->get_type() == Num)
                  _selCoiNumEqAbCube++;
                else if (lhs->get_type() == Sig || rhs->get_type() == Sig)
                  _selCoiSigEqAbCube++;
                else
                  _selCoiOtherAbCube++;
              }
              else if (op->get_op() == OpInst::NotEq)
              {
                Inst* lhs = op->get_children()->front();
                Inst* rhs = op->get_children()->back();

                if (lhs->get_type() == Num || rhs->get_type() == Num)
                  _selCoiNumNeqAbCube++;
                else if (lhs->get_type() == Sig || rhs->get_type() == Sig)
                  _selCoiSigNeqAbCube++;
                else
                  _selCoiOtherAbCube++;
              }
              else
                _selCoiOtherAbCube++;
            }
            else
              _selCoiOtherAbCube++;
          }

          Inst* cP = c->get_port();
          OpInst* op = OpInst::as(cP);
          if (op)
          {
            if (op->get_op() == OpInst::Eq)
            {
              Inst* lhs = op->get_children()->front();
              Inst* rhs = op->get_children()->back();

              if (lhs->get_type() == Sig) {
                if (rhs->get_type() == Sig)
                  _cube_ab_SigEqSig_sel++;
                else if (rhs->get_type() == Num)
                  _cube_ab_SigEqNum_sel++;
                else
                  _cube_ab_SigEqOther_sel++;
              }
              else if (lhs->get_type() == Num) {
                if (rhs->get_type() == Sig)
                  _cube_ab_SigEqNum_sel++;
                else if (rhs->get_type() == Num)
                  assert(0);
                else
                  _cube_ab_NumEqOther_sel++;
              }
              else {
                if (rhs->get_type() == Sig)
                  _cube_ab_SigEqOther_sel++;
                else if (rhs->get_type() == Num)
                  _cube_ab_NumEqOther_sel++;
                else
                  _cube_ab_OtherEqOther_sel++;
              }
            }
            else if (op->get_op() == OpInst::NotEq)
            {
              Inst* lhs = op->get_children()->front();
              Inst* rhs = op->get_children()->back();

              if (lhs->get_type() == Sig) {
                if (rhs->get_type() == Sig)
                  _cube_ab_SigNeqSig_sel++;
                else if (rhs->get_type() == Num)
                  _cube_ab_SigNeqNum_sel++;
                else
                  _cube_ab_SigNeqOther_sel++;
              }
              else if (lhs->get_type() == Num) {
                if (rhs->get_type() == Sig)
                  _cube_ab_SigNeqNum_sel++;
                else if (rhs->get_type() == Num)
                  assert(0);
                else
                  _cube_ab_NumNeqOther_sel++;
              }
              else {
                if (rhs->get_type() == Sig)
                  _cube_ab_SigNeqOther_sel++;
                else if (rhs->get_type() == Num)
                  _cube_ab_NumNeqOther_sel++;
                else
                  _cube_ab_OtherNeqOther_sel++;
              }
            }
            else if (op->get_op() == OpInst::LogNot) {
              Inst* child = op->get_children()->front()->get_port();
              if (child->get_type() == Sig)
                _cube_ab_SigBool_sel++;
              else if (OpInst::as(child))
                _cube_ab_Up_sel++;
              else {
                _cube_ab_Other_sel++;
                cout << "error1 in sel: " << *op << endl;
                assert(0);
              }
            }
            else
              _cube_ab_Up_sel++;
          }
          else if (cP->get_type() == Sig)
            _cube_ab_SigBool_sel++;
          else {
            _cube_ab_Other_sel++;
            cout << "error2 in sel: " << *cP << endl;
            assert(0);
          }
        }

				_numFrameRes++;
				_sumFrameRes += musSz;
				if (_maxFrameRes < musSz)
					_maxFrameRes = musSz;

				int blockIdx = g_idx;
				if (Config::g_forward_check == FORWARDCHECK_FAST) {
					TIME_E(start_time, end_time, _tb_ct_time);
					TIME_S(start_time);

					InstS relevantNext;
					Inst::collect_next_reg(OpInst::create(OpInst::LogAnd, conjunct_blockedCubeNext), relevantNext, true);

	#ifdef ADD_CUBE_IN_SRC
					conjunct_coneT.push_back(OpInst::create(OpInst::LogNot, cube));
	#endif


		#ifdef DO_CORRECTNESS_CHECKS
					int blockIdx = -1;
					for (int i = (g_idx - 1); i < _frame_idx; i++)
		#else
					blockIdx = g_idx;
					for (int i = g_idx; i < _frame_idx; i++)
		#endif
					{
						InstL conjunct_coneT;

						for (auto& sigNext: relevantNext) {
							if (Inst::_relevantCones[i].find(sigNext) == Inst::_relevantCones[i].end()) {
								Inst* coneT = Inst::fetch_trelation(sigNext);
								conjunct_coneT.push_back(coneT);
							}
						}

						if (check_blocked_using_solver(i, conjunct_blockedCubeNext, conjunct_coneT, -1))
							blockIdx = i + 1;
						else
							break;
					}
					assert(blockIdx >= g_idx);

					if (blockIdx != g_idx)
					{
						AVR_LOG(15, 0, "\n\t\t(forwarding to F[" << blockIdx << "] from F[" << g_idx << "])" << endl);
						forward_frame_clause(g_idx, blockIdx, gcube);
					}

					TIME_E(start_time, end_time, _tb_ct_forwardfast_time);
					_tb_ct_time += time_diff;
					TIME_S(start_time);
				}

				if (Config::g_forward_check == FORWARDCHECK_ONESTEP)
					maxBlockIdx = (blockIdx > maxBlockIdx) ? blockIdx : maxBlockIdx;

				AVR_LOG(15, 2, "\n\t\t(conjoining " << *tve << " to F[" << blockIdx << "])" << endl);
//				Inst* simTve = simplify_expr(tve);
//				if (simTve != tve)
//				{
//					AVR_LOG(15, 2, "\n\t\t(i.e. " << *simTve << " to F[" << blockIdx << "])" << endl);
//				}

				update_inc_solvers(blockIdx, ve_gcube);
			}

			{
				int literals = 0;
				const InstL* ch = ve_gcube->get_children();
				if (ch) {
					literals += ch->size();
				}else{
					literals ++;
				}
				_nLiterals += literals;
			}
			_nCubes++;
			TIME_E(start_time, end_time, _tb_ct_time);

			AVR_LOG(6, 2, "ccext_ct, res: " << resultCc << ", idx: " << g_idx << ", runtime: " << double(time_diff)/1000000 << endl);
#ifdef CHECK_TERMINAL_CONDITION_DURING_CONTAINMENT_CHECK
			if (resultCc == 1){
				AVR_LOG(15, 0, "\t\tProperty holds (proved during containment check)" << endl);
        TIME_E(start_time_full, end_time, Solver::time_ccext);
				return 2; //property holds
			}
#endif
			if (resultCc == 0){
				AVR_LOG(15, 0, "\t(flushing due to redundancy)" << endl);
        TIME_E(start_time_full, end_time, Solver::time_ccext);
				return 3;
			}
			else if (resultCc == 4){
				AVR_LOG(15, 0, "\t(flushing due to global info)" << endl);
        TIME_E(start_time_full, end_time, Solver::time_ccext);
				return 3;
			}
//      else if (resultInit == 1){
//        AVR_LOG(15, 0, "\t(flushing due to intersection of blocking cube with frame 0)" << endl);
//        TIME_E(start_time_full, end_time, Solver::time_tmp);
//        return 3;
//      }
		}
		if (Config::g_forward_check == FORWARDCHECK_ONESTEP) {
			assert(maxBlockIdx >= g_idx);
			if (_frame_idx > maxBlockIdx) {
//				if ((_frame_idx % 3) == 0)
				{
					PQElement* temp = _tb_queue.PQ_push(priority*1.2, maxBlockIdx + 1, abViol, PQ_next);
					AVR_LOG(15, 0, "\n(forward check) in F[" << (maxBlockIdx + 1) << "]" << endl);

					AVR_LOG(6, 4, "Pushed " << temp->abViol << " at F[" << temp->frame << "] " << " with prio: " << temp->prio << endl);
					AVR_LOG(6, 1, "@@	QUEUE PUSH " << maxBlockIdx+1 << endl);
				}
			}
		}

		TIME_E(start_time_full, end_time, Solver::time_ccext);
	}
	return 0;
}

void Reach::reset_cti_solver() {
  // Do nothing

//  _cti_solver = NULL;
//  cout << "Resetting CTI solver" << endl;
  struct rusage usage;
  struct timeval start_time, end_time;
  long long time_diff;

  TIME_S(start_time);
  if (_cti_solver) {
    delete _cti_solver;
    _cti_solver = NULL;
  }
  TIME_E(start_time, end_time, _cti_i_time);
}

void Reach::reset_frame_solvers() {
//	cout << "Resetting" << endl;
	struct rusage usage;
	struct timeval start_time, end_time;
	long long time_diff;

	TIME_S(start_time);
	{
		int rs_size = _reach_solvers.size();
		for (int i = 0; i < rs_size; i++) {
//			cout << "\t\t(resetting solver for F[" << i << "])" << endl;
			_reach_solvers[i].reset();
		}
	}
	TIME_E(start_time, end_time, _solver_set_time);
}

void Reach::reset_frame_solver(int i) {
//	cout << "Resetting" << endl;
	struct rusage usage;
	struct timeval start_time, end_time;
	long long time_diff;

	TIME_S(start_time);
	{
		assert(i < _reach_solvers.size());
		_reach_solvers[i].reset();
	}
	TIME_E(start_time, end_time, _solver_set_time);
}

void Reach::set_cti_solver() {
//  _cti_solver = _reach_solvers[_frame_idx].solver1;
  struct rusage usage;
  struct timeval start_time, end_time;
  long long time_diff;

  TIME_S(start_time);
  if (_cti_solver == NULL) {
    _cti_solver = new SOLVER_CTI(_abstract_mapper, AVR_CTI_IDX, false, cti);
    InstL conjunct_prop;
    Inst* ve_prop;
    conjunct_prop.push_back(_ve_model);
    conjunct_prop.push_back(_ve_prop_eq_1);

//    conjunct_prop.push_back(_ve_model_nsf);
    conjunct_prop.push_back(_ve_model_nextT);

    conjunct_prop.push_back(_ve_model_next);
    conjunct_prop.push_back(_ve_prop_next_eq_0);
    for (InstL::iterator it3 = _negated_refs.begin(); it3 != _negated_refs.end(); ++it3)
      conjunct_prop.push_back(*it3);
    negated_cubes(_frame_idx, conjunct_prop);
    ve_prop = OpInst::create(OpInst::LogAnd, conjunct_prop);
    AVR_LOG(1, 6, "P && T && !P+:" << conjunct_prop);
    _cti_solver->s_assert(ve_prop);
  }
#ifdef ASSERT_DISTINCT_NUMBERS
  _cti_solver->assert_distinct_constants();
#endif

  TIME_E(start_time, end_time, _cti_i_time);
}

void Reach::set_frame_solvers() {
//	cout << "Setting" << endl;
	struct rusage usage;
	struct timeval start_time, end_time;
	long long time_diff;

	TIME_S(start_time);
	int rs_size = _frame_idx + 1;
//			int rs_size = (_frame_idx >= _num_reach_solvers) ? _num_reach_solvers : _frame_idx;
//			AVR_LOG(13, 4, "# reach solvers: " << _num_reach_solvers << endl);
	AVR_LOG(13, 4, "# relevant reach solvers: " << rs_size << endl);

//	assert(rs_size == Inst::_relevantCones.size());

//	InstS relevantNext;
//	collect_next_reg(_ve_model_next, relevantNext, true);
//	for (auto& sigNext: relevantNext)
//	{
//		int topIdx = (rs_size - 1);
//		Inst::_relevantCones[topIdx].insert(sigNext);
//	}

	InstL negatedCubes;
	for (int s_cnt = (rs_size - 1); s_cnt >= 0; s_cnt--) {
//		cout << "\t\t(setting solver for F[" << s_cnt << "])" << endl;

		InstL conjunct_reach;
#ifdef FP_EXPAND_FRAME
		if (s_cnt != 0)
		{
			for (auto& c: _cubes[s_cnt])
			{
				for (InstL::iterator nit = negatedCubes.begin(); nit != negatedCubes.end();)
				{
					Inst* nc = (*nit);
					Inst* presentCube = OpInst::create(OpInst::LogNot, nc);
					if (set_contains(presentCube, c))
						nit = negatedCubes.erase(nit);
					else
						nit++;
				}
				negatedCubes.push_back(OpInst::create(OpInst::LogNot, c));
			}
			_negated_cubes[s_cnt] = negatedCubes;
		}
#endif
    negated_cubes(s_cnt, conjunct_reach);

		//if (s_cnt != 0)
		{
			conjunct_reach.push_back(_ve_model);
			conjunct_reach.push_back(_ve_prop_eq_1);
		}

		for (auto& sigNext : Inst::_relevantCones[s_cnt])
		{
			conjunct_reach.push_back(Inst::fetch_trelation(sigNext));
		}

//		conjunct_reach.push_back(_ve_model_nsf);

		conjunct_reach.push_back(_ve_model_next);
//		conjunct_reach.push_back(_ve_prop_next_eq_1);

		for (InstL::iterator it3 = _negated_refs.begin(); it3 != _negated_refs.end(); ++it3)
			conjunct_reach.push_back(*it3);
		Inst* ve_reach = OpInst::create(OpInst::LogAnd, conjunct_reach);
		int ba_idx = AVR_FRAME_BASE_IDX + s_cnt;

//		cout << "Asserting F[" << s_cnt << "]: " << conjunct_reach << endl;

#ifdef FRAME_SOLVER_MULTI
		_reach_solvers[s_cnt].solver_main = new SOLVER_CORE(_abstract_mapper, ba_idx, true, regular);
		_reach_solvers[s_cnt].solver1 = new SOLVER_REACH(_abstract_mapper, ba_idx, true, br);

		_reach_solvers[s_cnt].solver_main->s_assert(ve_reach);
		_reach_solvers[s_cnt].solver1->s_assert(ve_reach);
	#ifdef ASSERT_DISTINCT_NUMBERS
		_reach_solvers[s_cnt].solver_main->assert_distinct_constants();
		_reach_solvers[s_cnt].solver1->assert_distinct_constants();
	#endif
#else
		_reach_solvers[s_cnt].solver_main = new SOLVER_CORE(_abstract_mapper, ba_idx, true, br);
		_reach_solvers[s_cnt].solver1 = _reach_solvers[s_cnt].solver_main;

		_reach_solvers[s_cnt].solver_main->s_assert(ve_reach);
	#ifdef ASSERT_DISTINCT_NUMBERS
		_reach_solvers[s_cnt].solver_main->assert_distinct_constants();
	#endif
#endif

	}
	TIME_E(start_time, end_time, _solver_set_time);
}

void Reach::set_frame_solver(int s_cnt) {
//	cout << "Setting" << endl;
	struct rusage usage;
	struct timeval start_time, end_time;
	long long time_diff;

	TIME_S(start_time);
	InstL conjunct_reach;
	negated_cubes(s_cnt, conjunct_reach);

	//if (s_cnt != 0)
	{
		conjunct_reach.push_back(_ve_model);
		conjunct_reach.push_back(_ve_prop_eq_1);
	}

	for (auto& sigNext : Inst::_relevantCones[s_cnt])
	{
		conjunct_reach.push_back(Inst::fetch_trelation(sigNext));
	}

//		conjunct_reach.push_back(_ve_model_nsf);

	conjunct_reach.push_back(_ve_model_next);
//		conjunct_reach.push_back(_ve_prop_next_eq_1);

	for (InstL::iterator it3 = _negated_refs.begin(); it3 != _negated_refs.end(); ++it3)
		conjunct_reach.push_back(*it3);
	Inst* ve_reach = OpInst::create(OpInst::LogAnd, conjunct_reach);
	int ba_idx = AVR_FRAME_BASE_IDX + s_cnt;

//		cout << "Asserting F[" << s_cnt << "]: " << conjunct_reach << endl;

#ifdef FRAME_SOLVER_MULTI
	_reach_solvers[s_cnt].solver_main = new SOLVER_CORE(_abstract_mapper, ba_idx, true, regular);
	_reach_solvers[s_cnt].solver1 = new SOLVER_REACH(_abstract_mapper, ba_idx, true, br);

	_reach_solvers[s_cnt].solver_main->s_assert(ve_reach);
	_reach_solvers[s_cnt].solver1->s_assert(ve_reach);
	#ifdef ASSERT_DISTINCT_NUMBERS
	_reach_solvers[s_cnt].solver_main->assert_distinct_constants();
	_reach_solvers[s_cnt].solver1->assert_distinct_constants();
	#endif
#else
	_reach_solvers[s_cnt].solver_main = new SOLVER_CORE(_abstract_mapper, ba_idx, true, br);
	_reach_solvers[s_cnt].solver1 = _reach_solvers[s_cnt].solver_main;

	_reach_solvers[s_cnt].solver_main->s_assert(ve_reach);
	#ifdef ASSERT_DISTINCT_NUMBERS
	_reach_solvers[s_cnt].solver_main->assert_distinct_constants();
	#endif
#endif

	TIME_E(start_time, end_time, _solver_set_time);
}

void Reach::add_frame_solver() {
  _reach_solvers.push_back(FRAME_SOLVER());
  Inst::_relevantCones.push_back(InstS());
//  Inst::_relevantCones.push_back(_assume_regNext);
  vector<CLAUSE> tmpL;
  _cubes.push_back(tmpL);

//	cout << "Setting" << endl;
	struct rusage usage;
	struct timeval start_time, end_time;
	long long time_diff;

	TIME_S(start_time);
	int rs_size = _reach_solvers.size();
//	int rs_size = _frame_idx + 1;

//			int rs_size = (_frame_idx >= _num_reach_solvers) ? _num_reach_solvers : _frame_idx;
//			AVR_LOG(13, 4, "# reach solvers: " << _num_reach_solvers << endl);
	AVR_LOG(13, 4, "# relevant reach solvers: " << rs_size << endl);

//	assert(rs_size == Inst::_relevantCones.size());

//	InstS relevantNext;
//	collect_next_reg(_ve_model_next, relevantNext, true);
//	for (auto& sigNext: relevantNext)
//	{
//		int topIdx = (rs_size - 1);
//		Inst::_relevantCones[topIdx].insert(sigNext);
//	}

	InstL negatedCubes;
	int s_cnt = (rs_size - 1);
//	cout << "\t\t(adding solver for F[" << s_cnt << "])" << endl;

  InstL conjunct_reach;
#ifdef FP_EXPAND_FRAME
  if (s_cnt != 0)
  {
    for (auto& c: _cubes[s_cnt])
    {
      for (InstL::iterator nit = negatedCubes.begin(); nit != negatedCubes.end();)
      {
        Inst* nc = (*nit);
        Inst* presentCube = OpInst::create(OpInst::LogNot, nc);
        if (set_contains(presentCube, c))
          nit = negatedCubes.erase(nit);
        else
          nit++;
      }
      negatedCubes.push_back(OpInst::create(OpInst::LogNot, c));
    }
    _negated_cubes[s_cnt] = negatedCubes;
  }
#endif
	negated_cubes(s_cnt, conjunct_reach);

  //if (s_cnt != 0)
  {
    conjunct_reach.push_back(_ve_model);
    conjunct_reach.push_back(_ve_prop_eq_1);
  }

  for (auto& sigNext : Inst::_relevantCones[s_cnt])
  {
    conjunct_reach.push_back(Inst::fetch_trelation(sigNext));
  }

//		conjunct_reach.push_back(_ve_model_nsf);

  conjunct_reach.push_back(_ve_model_next);
//		conjunct_reach.push_back(_ve_prop_next_eq_1);

  for (InstL::iterator it3 = _negated_refs.begin(); it3 != _negated_refs.end(); ++it3)
    conjunct_reach.push_back(*it3);
  Inst* ve_reach = OpInst::create(OpInst::LogAnd, conjunct_reach);
  int ba_idx = AVR_FRAME_BASE_IDX + s_cnt;

//		cout << "Asserting F[" << s_cnt << "]: " << conjunct_reach << endl;

#ifdef FRAME_SOLVER_MULTI
  _reach_solvers[s_cnt].solver_main = new SOLVER_CORE(_abstract_mapper, ba_idx, true, regular);
  _reach_solvers[s_cnt].solver1 = new SOLVER_REACH(_abstract_mapper, ba_idx, true, br);

  _reach_solvers[s_cnt].solver_main->s_assert(ve_reach);
  _reach_solvers[s_cnt].solver1->s_assert(ve_reach);
	#ifdef ASSERT_DISTINCT_NUMBERS
  _reach_solvers[s_cnt].solver_main->assert_distinct_constants();
  _reach_solvers[s_cnt].solver1->assert_distinct_constants();
	#endif
#else
  _reach_solvers[s_cnt].solver_main = new SOLVER_CORE(_abstract_mapper, ba_idx, true, br);
  _reach_solvers[s_cnt].solver1 = _reach_solvers[s_cnt].solver_main;

  _reach_solvers[s_cnt].solver_main->s_assert(ve_reach);
	#ifdef ASSERT_DISTINCT_NUMBERS
  _reach_solvers[s_cnt].solver_main->assert_distinct_constants();
	#endif
#endif

	TIME_E(start_time, end_time, _solver_set_time);
}

//void Reach::refine_flush()
//{
//#ifdef TEST_REFINE_FP
//		reset_frame_solvers();
//
//		ostringstream str;
//		str << "   " << _negated_refs.size() << "\t: " << _frame_idx << "\t: 0";
//		int sum_cubes = 0;
//
//		for (int i = 1; i <= _frame_idx; i++) {
//			sum_cubes += (_cubes[i]).size();
//			str << " " << (_cubes[i]).size();
//		}
//		str << " s: " << sum_cubes;
//		AVR_LOG(8, 1, str.str() << endl);
//
//		ostringstream str2;
//		str2 << "L  " << _frame_idx << " : 0";
//		int sum_literals = 0;
//		for (int i = 1; i <= _frame_idx; i++) {
//			int literals = 0;
//			for(InstL::iterator pc_it = _cubes[i].begin(); pc_it != _cubes[i].end(); pc_it++){
//				Inst *tve = *pc_it;
//				const InstL* ch = tve->get_children();
//				if (ch) {
//					literals += ch->size();
//				}else{
//					literals ++;
//				}
//			}
//			sum_literals += literals;
//			str2 << " " << literals;
//		}
//
//		//cout << "memUsed(): " << memUsed() << endl;
//		AVR_LOG(8, 2, str2.str());
//		#ifdef PRINT_FRAME_SUMMARY
//		cerr << "\r" << str.str() << "                  " << endl;
//		#endif
//
//		AVR_LOG(13, 6, "F[" << _frame_idx << "]: (sz: " << _negated_cubes[_frame_idx].size() << ")" << endl);
//		AVR_LOG(13, 6, _negated_cubes[_frame_idx] << endl);
//
//		AVR_LOG(13, 7, "B4_cubes :" << ((_cubes.size() == 0) ? " Empty":"") << endl);
//		for (int i = 0; i < _cubes.size(); i++)
//		AVR_LOG(13, 7, "\n[" << i << "]" << _cubes[i] << endl);
//
//		AVR_LOG(13, 7, "_negated_cubes :" << ((_negated_cubes.size() == 0) ? " Empty":"") << endl);
//		for (int i = 0; i < _negated_cubes.size(); i++)
//		AVR_LOG(13, 7, "\n[" << i << "]" << "\t" << _negated_cubes[i] << endl);
//
//		AVR_LOG(13, 7, "_negated_refs :" << ((_negated_refs.size() == 0) ? " Empty":"") << _negated_refs << endl);
//
//		AVR_LOG(15, 0, "\t[Forward propagation]:" << endl);
//		for (int i = 1; i <= _frame_idx; i++) {
//			InstL conjunct_fp = _negated_cubes[i]; //forward propagation
//			AVR_LOG(3, 6, "FP negated_cubes[" << i << "]: :" << (_negated_cubes[i]));
//			conjunct_fp.push_back(_ve_model);
//			conjunct_fp.push_back(_ve_prop_eq_1);
//
//			//		conjunct_fp.push_back(_ve_model_nsf);
//
//			conjunct_fp.push_back(_ve_model_next);
//			conjunct_fp.push_back(_ve_prop_next_eq_1);
//
//			for (InstL::iterator it3 = _negated_refs.begin(); it3 != _negated_refs.end(); ++it3)
//				conjunct_fp.push_back(*it3);
//			AVR_LOG(3, 6, "conjunct_fp (i = " << i << "): " << conjunct_fp << endl);
//			Inst *ve_fp = OpInst::create(OpInst::LogAnd, conjunct_fp);
//
//			z3_API int_solver(&_abstract_mapper, 0, false, false);
//
//			int_solver.forward_propagation(0, i, ve_fp, _negated_cubes, _cubes, &forward_all_next2pre, &forward_all_pre2next, &forward_set_contains, _m_corr_regs, this);
//			AVR_LOG(3, 1, "%% (FP) frame_idx: " << i << ", sat: " << Solver::num_scalls_sat_fp_non_accum << ", unsat: "
//										<< Solver::num_scalls_unsat_fp_non_accum << ", contained: " << Solver::num_scalls_contained_fp_non_accum << endl);
//			if (Solver::num_scalls_unsat_fp_non_accum > 0)
//				i--;
//		}
//
//		AVR_LOG(13, 7, "AF_cubes :" << ((_cubes.size() == 0) ? " Empty":"") << endl);
//		for (int i = 0; i < _cubes.size(); i++)
//		AVR_LOG(13, 7, "\n[" << i << "]" << _cubes[i] << endl);
//
//		AVR_LOG(13, 7, "_negated_cubes :" << ((_negated_cubes.size() == 0) ? " Empty":"") << endl);
//		for (int i = 0; i < _negated_cubes.size(); i++)
//		AVR_LOG(13, 7, "\n[" << i << "]" << "\t" << _negated_cubes[i] << endl);
//
//		AVR_LOG(13, 7, "_negated_refs :" << ((_negated_refs.size() == 0) ? " Empty":"") << _negated_refs << endl);
//
//		{
//			ostringstream str;
//			str << "   " << _negated_refs.size() << "\t: " << _frame_idx << "\t: 0";
//			int sum_cubes = 0;
//			for (int i = 1; i <= _frame_idx; i++) {
//				sum_cubes += (_cubes[i]).size();
//				str << " " << (_cubes[i]).size();
//			}
//			str << " s: " << sum_cubes;
//			AVR_LOG(8, 1, str.str() << endl);
//
//			ostringstream str2;
//			str2 << "L  " << _frame_idx << " : 0";
//			int sum_literals = 0;
//			for (int i = 1; i <= _frame_idx; i++) {
//			int literals = 0;
//			for(InstL::iterator pc_it = _cubes[i].begin(); pc_it != _cubes[i].end(); pc_it++){
//				Inst *tve = *pc_it;
//				const InstL* ch = tve->get_children();
//				if (ch) {
//					literals += ch->size();
//				}else{
//					literals ++;
//				}
//			}
//				sum_literals += literals;
//				str2 << " " << literals;
//			}
//			//cout << "memUsed(): " << memUsed() << endl;
//			AVR_LOG(8, 0, str2.str());
//
//			#ifdef PRINT_FRAME_SUMMARY
//			cerr << "\r" << str.str() << "                  ";
//			#endif
//		}
//
//		set_frame_solvers();
//	return;
//#endif
//
//	refine_flush_len_acext += _rcext_orig.size();
//	refine_flush_count++;
//
//	/// Step 1: reset all frames
//	reset_cti_solver();
//	reset_frame_solvers();
//
//	/// Step 2: Based on flush mode, reset appropriate frames
//	int maxFrame = 0;
//#ifdef TEST_REFINE_PARTIAL_FLUSH
//	maxFrame = _refine_exit_frame;
//	if (maxFrame == 0)
//		maxFrame = 1;
//	else if (maxFrame == BAD_CUBE_INDEX)
//		maxFrame = _frame_idx;
//#endif
//#ifdef TEST_REFINE_FULL_FLUSH
//	maxFrame = 1;
//#endif
//
//	assert(maxFrame > 0);
//
//	refine_flush_level += maxFrame;
//	cout << "\t(resetting frames " << maxFrame << " to " << _frame_idx << ")" << endl;
//
//	/// Flush all frames above and equal to maxFrame
//	for (int i = maxFrame; i <= _frame_idx; i++)
//	{
//		refine_flush_frames++;
//		refine_flush_clauses += _cubes[i].size();
//
//		_cubes.erase(i);
//		_negated_cubes.erase(i);
////		cout << "\t\t(F[" << i << "] erased)" << endl;
//
//		if (i > maxFrame)
//		{
//			_reach_solvers.erase(i);
//		}
//	}
//
//	InstL negatedCubes;
//	for (int i = maxFrame; i > 0; i--)
//	{
//		for (auto& c: _cubes[i])
//			negatedCubes.push_back(OpInst::create(OpInst::LogNot, c));
//
////		cout << "\t\t(F[" << i << "] recomputed)" << endl;
//		_negated_cubes[i] = negatedCubes;
//	}
//
////	cout << "F[0]: " << _negated_cubes[0] << endl;
//
//	_frame_idx = maxFrame;
//	if (_reach_solvers.size() != (_frame_idx + 1))
//	{
//		for (auto& s: _reach_solvers)
//			cout << "solver for frame " << s.first << endl;
//
//		cout << "#solvers: " << _reach_solvers.size() << endl;
//		cout << "new top frame: " << _frame_idx << endl;
//	}
//
//	assert(_reach_solvers.size() == (_frame_idx + 1));
//
//	set_cti_solver();
//	set_frame_solvers();
//}

// return 0 if holds, 1 if violated, -1 others
int Reach::verify() {
  cout.setf(ios::fixed, ios::floatfield);
  cout.precision(6);
	struct rusage usage;
	struct timeval start_time, end_time;
	long long time_diff;

	TIME_S(start_time);
	global_init();
	print_config();

	reduce_system();

	if (_ve_model == _ve_prop_eq_1) {
		AVR_LOG(15, 0, "\t(property trivially holds)" << endl);
		_converged_frame = 0;
		return EXIT_HOLD_TRIV;
	}

	collect_cones();
	collect_inputs();
	collect_struct_info();
	draw_system();

#ifndef PERFORMANCE_NOPRINT
	print_system_stats();
	//	print_backward_coi_matrix();
	print_backward_coi_list();
  print_states_transitions("fsm_cc.txt", NULL, true, true);
	print_states_transitions("fsm_ab.txt");
  dump_hm_sizes();
#endif
	print_config2();

  print_design_smt2();
//  print_design_btor2();

	TIME_E(start_time, end_time, _pre_time);
	AVR_LOG(0, 2, "pre-preprocess, runtime: " << double(time_diff)/1000000 << endl);

  int verify_ret_value = -1;


#ifdef EN_BMC
  if (Config::g_kind_en) {
  	Config::g_bmc_en = true;
  	verify_ret_value = kind_run(Config::g_bmc_max_bound);
		return verify_ret_value;
  }
  else if (Config::g_bmc_en) {
  	verify_ret_value = bmc_run(Config::g_bmc_max_bound);
		return verify_ret_value;
  }
#endif

  InstL conjunct_prop;
  InstL conjunct_hard;
  Inst *ve_prop;
	bool i_not_p_unsat = false;
	bool i_t_not_pp_unsat = false;

	AVR_LOG(15, 0, endl);
	AVR_LOG(15, 0, "---------------------------------------------------------------------------------------------" << endl);
	AVR_LOG(15, 0, " Reachability Analysis Begins" << endl);
	AVR_LOG(15, 0, "---------------------------------------------------------------------------------------------" << endl);
	AVR_LOG(15, 0, "Loop_FrameNumber_#ReachabilityIterations_#RefinementIterations" << endl);

//#ifdef BMC
//	_frame_idx = BMC_DEFAULT_LENGTH;
//	i_not_p_unsat = true;
//	i_t_not_pp_unsat = true;
//#endif

	for (int i = 0; i <= _frame_idx; i++) {
		_reach_solvers.push_back(FRAME_SOLVER());
		Inst::_relevantCones.push_back(InstS());
//		Inst::_relevantCones.push_back(_assume_regNext);
		if (i != 0) {
			vector<CLAUSE> tmpL;
			_cubes.push_back(tmpL);
		}
	}
	if (_frame_idx > 0) {
		set_frame_solvers();
		set_cti_solver();
	}

	while (1) {// refinement loop
		bool SAT_terminated = false;
		//TODO R0 && !P should be checked before the while loop
#ifdef ASSERT_DISTINCT_NUMBERS
    for (vector<FRAME_SOLVER>::iterator rs_it = _reach_solvers.begin(); rs_it != _reach_solvers.end(); rs_it++)
    {
      if (rs_it->solver_main) {
        (rs_it->solver_main)->assert_distinct_constants();
      }
#ifdef FRAME_SOLVER_MULTI
      if (rs_it->solver1) {
        (rs_it->solver1)->assert_distinct_constants();
      }
#endif
    }
    if (_cti_solver)
      _cti_solver->assert_distinct_constants();
#endif

		while (1) {// increments Frame
			_loop_idx = 0;
			while (1) { // Within the same frame, check a prop repeatedly

				AVR_LOG(15, 0, "---------------------------------------------------------------------------------------------" << endl);
				AVR_LOG(15, 0, "Loop_" << _frame_idx << "_" << _loop_idx << "_" << _num_dp_refine << endl);
				AVR_LOG(15, 0, "---------------------------------------------------------------------------------------------" << endl);

//				print_frames();
//				print_frame_summary(_frame_idx);

				if (_frame_idx == 0) {
					if(i_not_p_unsat == false){
						TIME_S(start_time);
						// QUERY: I && !P
						conjunct_prop = _conjunct_init;
						conjunct_prop.push_back(_ve_prop_eq_0);
						conjunct_prop.push_back(_ve_model);
						InstL conjunct_prop_wo_ref = conjunct_prop;
						for (InstL::iterator it3 = _negated_refs.begin(); it3 != _negated_refs.end(); ++it3)
							conjunct_prop.push_back(*it3);
						if (Config::g_lazy_assume >= LAZY_ASSUME_L2)
							conjunct_prop.push_back(_ve_assume);
						if (Config::g_lazy_assume >= LAZY_ASSUME_L1) {
							for (auto& v: _assume_T)
								conjunct_prop.push_back(v.first);
						}

						ve_prop = OpInst::create(OpInst::LogAnd, conjunct_prop);
						AVR_LOG(15, 0, "[Basis Step]:" << endl);
						if(_num_dp_refine == 0)
						{
							AVR_LOG(15, 0, "\t" << "F[0] = I" << endl);
						}
						if (_euf_solver){
							delete static_cast<SOLVER_AB*>(_euf_solver);
							_euf_solver = NULL;
						}
						_euf_solver = new SOLVER_AB(_abstract_mapper, AVR_BASIS_IDX, false, mdl);
						_sat_res = _euf_solver->check_sat(ve_prop, AB_QUERY_TIMEOUT, true);
						TIME_E(start_time, end_time, _cti_time);

						AVR_LOG(15, 0, "\t" << "SAT_a ? [ F[0] && !P ]: " << (_sat_res ? "SAT" : "UNSAT") << endl);
						AVR_LOG(1, 2, "(I && !P) solve, res: " << (_sat_res ? "SAT" : "UNSAT") << ", runtime: " << double(time_diff)/1000000 << endl);

						if (_sat_res) {
							print_all_abstract_min_term(conjunct_prop, _euf_solver);
//							retrieve_cex_val(ve_prop, _euf_solver, true, true, false);
              retrieve_ab_sol(_euf_solver, true);
//							print_abstract_min_term_compact(cout, _min_term);

							InstToInstM dummyMap;
							InstS relevantPresent;
							InstS relevantPresentInp;
							InstS relevantConst;
							set< string > relevantUFtype;

							_abViol.clear();
							EVAL tb(_abViol, dummyMap, relevantPresent, relevantPresent, relevantPresentInp, relevantPresentInp, relevantConst, relevantUFtype, _euf_solver);

							KEY_COI_VALUE::inc_coi_key();
#ifndef PERFORMANCE_NODRAW
							if (Config::g_print_dot[DRAW_TRANSITION] != '0')
								Inst::inc_drkey();
#endif

							Inst::init_visit();
							for (auto& c: conjunct_prop_wo_ref)
								COI_prune_relation(c, tb, 1);
//							  COI_generalize(c, tb);
							tb.print_all();

#ifndef PERFORMANCE_NODRAW
							if (Config::g_print_dot[DRAW_TRANSITION] != '0') {
								Inst* v = _ve_model;
								v->set_drVal(1);

								AVR_LOG(15, 0, "\t(key) #" << Inst::get_drkey() << "\t(#" << v->get_id() << ")" << endl);
								{
									ostringstream ostr;
							//    ostr << "ab/" << Inst::get_drkey() << "_v#" << v->get_id();
									ostr << "ab/" << Inst::get_drkey() << "_v";
									draw_graph(2, v, ostr.str(), 0, false);
								}
							}
#endif

							/// Minterm solution contains boolean predicates and partitions involving state variables, constants, wires (or their negation)
//							print_solution(_min_term.s, "solver solution");

							/// Merge relevant present and next state variables
							InstS relevantStates;
							relevantStates.insert(relevantPresent.begin(), relevantPresent.end());
							relevantStates.insert(relevantPresentInp.begin(), relevantPresentInp.end());

						  if (true)
						  {
						  	_abViol.print_cubes();

								simplify_solution2();

								/// Generalize solution to include relevant terms only (by dropping terms from minterm solution)
								model_generalize2(_euf_solver, conjunct_prop, _min_term, relevantStates, relevantConst, relevantUFtype, AB_REACH_INIT);

								/// Project generalized solution on present, next and input variables (mixed constains cases where inputs and present variables are mixed)
								SOLUTION pre_c, inp_c, next_c, mixed_c;
								model_abstract2(_min_term.s, pre_c, inp_c, next_c, mixed_c, false);

								add_pred_from_solution(pre_c, _abViol.mainConstraints, "adding pred. from pre_c to ab. cube");
								add_pred_from_solution(mixed_c, _abViol.mainConstraints, "adding pred. from mixed_c to ab. cube");
								add_pred_from_solution(inp_c, _abViol.mainConstraints, "adding pred. from inp_c to ab. cube");

								/// Add concrete constraints from generalized solution
								add_pred_from_solution(pre_c, _abViol.concreteConstraints, "adding pred. from pre_c to cc. cube");
								add_pred_from_solution(mixed_c, _abViol.concreteConstraints, "adding pred. from mixed_c to cc. cube");
								add_pred_from_solution(inp_c, _abViol.concreteConstraints, "adding pred. from inp_c to cc. cube");

								/// Add relevant wires from partition
								add_wires_from_list(_abViol.concreteConstraints, _abViol.relevantWires);

//						  	_abViol.print_cubes();
						  }
#ifdef	FIND_SUB_EXPRESSION
						  else
						  {
								/// Substitute wires with their respective evaluations (each evaluation expression stores a list of original wire expressions)
								InstToListM opMap;
								simplify_solution(_min_term.s, opMap);

								/// Generalize solution to include relevant terms only (by dropping terms from minterm solution)
								model_generalize(_min_term.s, relevantStates, relevantConst, relevantUFtype);


								/// Project generalized solution on present, next and input variables (mixed constains cases where inputs and present variables are mixed)
								SOLUTION pre, inp, next, mixed;
								model_abstract(_min_term.s, pre, inp, next, mixed, true);

								/// Undo simplification (done for abstraction and generalization) of UPs/UFs
								_abViol.generalized_s = _min_term.s;
								SOLUTION pre_c, inp_c, next_c, mixed_c;
								InstToInstM subMap, subMapR;
								resimplify_solution(_min_term.s, opMap, subMap, subMapR);

								model_abstract(_min_term.s, pre_c, inp_c, next_c, mixed_c, subMapR, false);

								add_from_solution(_euf_solver, pre, _abViol.mainSubConstraints, "adding to pre_sub");

								add_from_solution(_euf_solver, pre_c, _abViol.mainConstraints, "adding to pre_c");

	//							/// Undo simplification (done for abstraction and generalization) of UPs/UFs
	//							SOLUTION pre_c, inp_c, next_c, mixed_c;
	//							resimplify_solution(_min_term.s, opMap);
	//							model_abstract(_min_term.s, pre_c, inp_c, next_c, mixed_c, true);

	#ifdef CORRECT_GENERALIZATION
								/// Add concrete constraints from generalized solution
								/// Add relevant wires from partition
								add_wires_from_solution(pre_c, _abViol.relevantWires, _abViol.relevantWiresNext);

								/// Add concrete constraints from generalized solution
								add_from_solution(_euf_solver, pre_c, _abViol.concreteConstraints, "adding to concrete pre");
	#endif
						  }
#endif

#ifdef CORRECT_GENERALIZATION
              interpret_distinct_constant(_abViol.concreteConstraints);
#endif

#ifdef DEFAULT_PROJECTION
							/// Projection (pre)
							///
							{
								AVR_LOG(15, 0, "\t(projection pre)" << endl);

								/// Present
								AVR_LOG(15, 0, "\t\t#sv: " << relevantPresent.size() << endl);
								InstL fprojectionConstraints;
								InstL projectionConstraints;
								project_abstract_min_term(1, fprojectionConstraints, projectionConstraints, relevantPresent, relevantConst, _min_term);
								for (auto& c: fprojectionConstraints)
								{
									_abViol.mainConstraints.push_front(c);

#ifndef RESTRICT_ALL_PROJECTION_CONSTRAINTS_IN_CONCRETE_CUBE
#ifdef RESTRICT_PROJECTION_NUMBERS_IN_CONCRETE_CUBE
									if (c->childrenInfo[NUM])
										continue;
#endif
									_abViol.concreteConstraints.push_front(c);
#endif
								}
								for (auto& c: projectionConstraints)
								{
									_abViol.mainConstraints.push_front(c);

#ifndef RESTRICT_ALL_PROJECTION_CONSTRAINTS_IN_CONCRETE_CUBE
#ifdef RESTRICT_PROJECTION_NUMBERS_IN_CONCRETE_CUBE
									if (c->childrenInfo[NUM])
										continue;
#endif
									_abViol.concreteConstraints.push_front(c);
#endif
								}
							}

							/// Collect important wires
							InstS importantWires;
							for (auto& c: _abViol.concreteConstraints)
							{
								Inst* tve = c;
								if (tve->childrenInfo[WIRE])
								{
									OpInst* opC = OpInst::as(c);
									if (opC && opC->get_op() == OpInst::LogNot)
										tve = c->get_children()->front();
									if (tve->get_type() == Wire)
										importantWires.insert(tve);
									else
									{
										const InstL* children = tve->get_children();
										if (children)
										{
											for (auto& ch: (*children))
											{
												if (ch->get_type() == Wire)
													importantWires.insert(ch);
											}
										}
									}
								}
							}
//							cout << "\t(important wires)" << endl;
//							for (auto& r: importantWires)
//								cout << "\t\t" << *r << endl;

							/// Projection (important wires)
							///
							{
								AVR_LOG(15, 0, "\t(projection wires)" << endl);

								/// Wires
								AVR_LOG(15, 0, "\t\t#wires: " << importantWires.size() << endl);

#ifndef RESTRICT_ALL_PROJECTION_CONSTRAINTS_IN_CONCRETE_CUBE
								project_abstract_min_term(1, _abViol.concreteConstraints, _abViol.concreteConstraints, importantWires, relevantConst, _min_term, Wire, false);
#endif
							}
							/// END
#endif

							InstS violSet;
							for (auto& v: _abViol.mainConstraints)
								violSet.insert(v);

							InstS concreteSet;
							for (auto& v: _abViol.concreteConstraints)
								concreteSet.insert(v);

//							/// Print COI constraints
//							AVR_LOG(15, 0, "\t(abstract)" << endl);
//							for (auto& v: _abViol.mainConstraints)
//							{
//								if (concreteSet.find(v) != concreteSet.end())
//								{
//									AVR_LOG(15, 0, "\t\t" << *v << endl);
//								}
//								else
//								{
//									AVR_LOG(15, 0, "\t\t" << *v << "\t[s]" << endl);
//								}
//							}
//
//							/// Print COI constraints
//							AVR_LOG(15, 0, "\t(concrete)" << endl);
//							for (auto& v: _abViol.concreteConstraints)
//							{
//								if (violSet.find(v) == violSet.end())
//								{
//									AVR_LOG(15, 0, "\t\t" << *v << endl);
//								}
//							}

              bool isSat = solvePartition(_abViol, "trans. from F[" + to_string(_frame_idx) + "] to !P+");

              if (!isSat) {
                if (!solveCube(_abViol.mainSubConstraints, _abViol.mainConstraints, "cube in F[" + to_string(_frame_idx) + "]")) {
                  isSat = false;
                }
              }

              if (isSat) {
                _tb_queue.PQ_clear();
                PQElement* temp = _tb_queue.PQ_push(0, _frame_idx, _abViol, NULL);
                AVR_LOG(6, 4, "Pushed " << temp->abViol << " at F[" << temp->frame << "] " << " with prio: " << temp->prio << endl);

                AVR_LOG(1, 1, "Averroes Termination Condition!!!	Property is violated ~~" << endl);
                SAT_terminated = true;
                break;
              }
              else {
                AVR_LOG(15, 0, "\t(flushing due to global info)" << endl);
                continue;
              }
						}
						i_not_p_unsat = true;
						AVR_LOG(15, 0, endl);
					}
					if(i_t_not_pp_unsat == false){
						TIME_S(start_time);
						// QUERY: I && T && !P+
						conjunct_prop = _conjunct_init;
//						conjunct_prop.push_back(_ve_model_nsf);
						conjunct_prop.push_back(_ve_model_nextT);
						conjunct_prop.push_back(_ve_model_next);
						conjunct_prop.push_back(_ve_prop_next_eq_0);
						for (InstL::iterator it3 = _negated_refs.begin(); it3 != _negated_refs.end(); ++it3)
							conjunct_prop.push_back(*it3);
						if (Config::g_lazy_assume >= LAZY_ASSUME_L2)
							conjunct_prop.push_back(_ve_assume);
						if (Config::g_lazy_assume >= LAZY_ASSUME_L1) {
							for (auto& v: _assume_T)
								conjunct_prop.push_back(v.first);
						}

						ve_prop = OpInst::create(OpInst::LogAnd, conjunct_prop);
						AVR_LOG(15, 0, "[First Step]:" << endl);
						AVR_LOG(1, 5, "I && T && !P+:" << conjunct_prop);

						if (_euf_solver){
							delete static_cast<SOLVER_AB*>(_euf_solver);
							_euf_solver = NULL;
						}
						_euf_solver = new SOLVER_AB(_abstract_mapper, AVR_BASIS_IDX, false, mdl);
						_sat_res = _euf_solver->check_sat(ve_prop, AB_QUERY_TIMEOUT, true);
						TIME_E(start_time, end_time, _cti_time);

						AVR_LOG(15, 0, "\t" << "SAT_a ? [ F[0] & T & !P ]: " << (_sat_res ? "SAT" : "UNSAT") << endl);
						AVR_LOG(1, 2, "prop_solve, res: " << (_sat_res ? "SAT" : "UNSAT") << ", idx: 0, runtime: " << double(time_diff)/1000000 << endl);

						if (_sat_res) {
							print_all_abstract_min_term(conjunct_prop, _euf_solver);
							retrieve_ab_sol(_euf_solver, true);
//							print_abstract_min_term_compact(cout, _min_term);

//#ifdef CHECK_BAD_CUBE
////							cout << _s_conditions_next << endl;
//							expand_next_from_abstract_minterm(_min_term);
//							if (!_abViol.mainConstraints.empty())
//							{
//								Inst* badCubeNext = OpInst::create(OpInst::LogAnd, _abViol.mainConstraints);
//								_bad_cube = all_next2pre(badCubeNext, true);
//							}
//							else
//							{
//								_bad_cube = NumInst::create(1, 1);
//							}
////							cout << "Bad cube: " << *_bad_cube << endl;
//#endif

							InstL tmp;
							trace_back(_euf_solver, ve_prop, tmp, _ve_model_next, NumInst::create(1, 1, SORT()), AB_REACH_TOP);

	            bool isSat = solvePartition(_abViol, "trans. from F[" + to_string(_frame_idx) + "] to !P+");


              if (!isSat) {
                if (!solveCube(_abViol.mainSubConstraints, _abViol.mainConstraints, "cube in F[" + to_string(_frame_idx) + "]")) {
                  isSat = false;
                }
              }

	            if (isSat)
	              isSat = solveBadDest();

	            if (isSat) {

#ifdef PRINT_ALL_ABSTRACT_TRANSITIONS
                string tid = "#" + to_string(ve_prop->get_id());
                AVR_LOG(15, 0, "\t(" << tid << ")" << endl);
                print_states_transitions("fsm_c" + tid + ".txt", _abViol.mainConstraints, _ve_prop_eq_0, true, true);
                print_states_transitions("fsm_a" + tid + ".txt", _abViol.mainConstraints, _ve_prop_eq_0);
#endif

                _tb_queue.PQ_clear();
                PQElement* temp = _tb_queue.PQ_push(0, _frame_idx, _abViol, NULL);
                AVR_LOG(6, 4, "Pushed " << temp->abViol << " at F[" << temp->frame << "] " << " with prio: " << temp->prio << endl);

                AVR_LOG(1, 1, "Averroes Termination Condition!!!	Property is violated ~~" << endl);
                SAT_terminated = true;
                break;
	            }
	            else {
                AVR_LOG(15, 0, "\t(flushing due to global info)" << endl);
	              continue;
	            }
						}
						i_t_not_pp_unsat = true;
						AVR_LOG(15, 0, endl);
					}
				} else {
					if(_cubes[_frame_idx].size() == 0)
					{
						AVR_LOG(15, 0, "\t" << "F[" << _frame_idx << "] = P" << endl);
					}
					TIME_S(start_time);

					// QUERY: Ri && P && T && !P+
					// there's no further frame than _frame_idx, so we don't need to
					// add upper frame's cubes
					_loop_idx++;

					AVR_LOG(15, 0, "\t" << "SAT_a ? [ F[" << _frame_idx << "] & T & !P+ ]: ");

//					InstL conjunct_cube_next;
//					conjunct_cube_next.push_back(_ve_model_next);
//					conjunct_cube_next.push_back(_ve_prop_next_eq_0);
//					int s_check_result = solveRelative(_frame_idx, _negated_cubes[_frame_idx], cti);

					int s_check_result = _cti_solver->s_check(AB_QUERY_TIMEOUT, true);
					_sat_res = (s_check_result == AVR_QUSAT) ? false : true;
					TIME_E(start_time, end_time, _cti_time);
          AVR_LOG(15, 0, (_sat_res ? "SAT" : "UNSAT") << endl);

					AVR_LOG(1, 1, "R" << _frame_idx << " && P && T && !P+ : " << (_sat_res ? "SAT" : "UNSAT") << endl);
					AVR_LOG(1, 2, "prop_solve, res: " << (_sat_res ? "SAT" : "UNSAT") << ", idx: " << _frame_idx << ", runtime: " << double(time_diff)/1000000 << endl);

					if (_sat_res) {
						_nBlocksS++;
            conjunct_prop.clear();
            conjunct_prop.push_back(_ve_model);
            conjunct_prop.push_back(_ve_prop_eq_1);
//            conjunct_prop.push_back(_ve_model_nsf);
						conjunct_prop.push_back(_ve_model_nextT);
            conjunct_prop.push_back(_ve_model_next);
            conjunct_prop.push_back(_ve_prop_next_eq_0);
            for (InstL::iterator it3 = _negated_refs.begin(); it3 != _negated_refs.end(); ++it3)
              conjunct_prop.push_back(*it3);
            negated_cubes(_frame_idx, conjunct_prop);
            ve_prop = OpInst::create(OpInst::LogAnd, conjunct_prop);
            AVR_LOG(1, 5, "P && T && !P+:" << conjunct_prop);

            print_all_abstract_min_term(conjunct_prop, _cti_solver);
            retrieve_ab_sol(_cti_solver, true);
//            print_abstract_min_term_compact(cout, _min_term);

//#ifdef CHECK_BAD_CUBE
////							cout << _s_conditions_next << endl;
//							expand_next_from_abstract_minterm(_min_term);
//							if (!_abViol.mainConstraints.empty())
//							{
//								Inst* badCubeNext = OpInst::create(OpInst::LogAnd, _abViol.mainConstraints);
//								_bad_cube = all_next2pre(badCubeNext, true);
//							}
//							else
//							{
//								_bad_cube = NumInst::create(1, 1);
//							}
////							cout << "Bad cube: " << *_bad_cube << endl;
//#endif

            AVR_LOG(13, 2, "Tracing backwards" << endl);
            InstL tmp;
            trace_back(_cti_solver, ve_prop, tmp, _ve_model_next, NumInst::create(1, 1, SORT()), AB_REACH_TOP);

							/// Aman - Test
#ifdef EXTRA_CHECKS
							TIME_E(start_time, end_time, _tb_time);
							TIME_S(start_time);
							z3_API* tmpSolver = new z3_API(&_abstract_mapper, AVR_EXTRA_IDX, false, true);
							tmpSolver->disable_ex_cc_interpret();
							InstL conjunctTmp;
							conjunctTmp.push_back(_ve_model);
							conjunctTmp.push_back(_ve_prop_eq_1);
							conjunctTmp.push_back(_ve_model_next);
							conjunctTmp.push_back(_ve_prop_next_eq_0);
//							cout << "prop is " << conjunct_prop << endl;
							for (InstL::iterator it3 = _negated_refs.begin(); it3 != _negated_refs.end(); ++it3)
								conjunctTmp.push_back(*it3);
							for(InstL::iterator nc_it = (_negated_cubes[_frame_idx]).begin();
								nc_it != (_negated_cubes[_frame_idx]).end(); nc_it++){
								conjunctTmp.push_back(*nc_it);
//								cout << "prop is " << conjunct_prop << endl;
							}
							InstL conjunct_mus = conjunctTmp;
//							conjunctTmp.push_back(_ve_model_nsf);
							tmpSolver->s_assert(_ve_model_nsf);

//							tmpSolver->s_assert_retractable(conjunctTmp);
							tmpSolver->s_assert(OpInst::create(OpInst::LogAnd, conjunctTmp));

							if (!_abViol.mainConstraints.empty())
								tmpSolver->s_assert(OpInst::create(OpInst::LogAnd, _abViol.mainConstraints));
#ifdef REACH_ADD_PATH_CONSTRAINTS
							if (!_abViol.pathConstraints.empty())
								tmpSolver->s_assert(OpInst::create(OpInst::LogAnd, _abViol.pathConstraints));
#endif
//							if (!_abViol.restrictedConstraints.empty())
//								tmpSolver->s_assert(OpInst::create(OpInst::LogAnd, _abViol.restrictedConstraints));
//							if (!_abViol.restrictedPathConstraints.empty())
//								tmpSolver->s_assert(OpInst::create(OpInst::LogAnd, _abViol.restrictedPathConstraints));

							int tmpRes = tmpSolver->s_check(AB_QUERY_TIMEOUT);
							delete tmpSolver;
							if(tmpRes != 1)
							{
								cout << tmpRes << endl;
								z3_API* tmpSolver = new z3_API(&_abstract_mapper, AVR_EXTRA_IDX, false, true);
								tmpSolver->s_assert(_ve_model_nsf);
								for (InstL::iterator vit = _abViol.mainConstraints.begin(); vit != _abViol.mainConstraints.end(); vit++)
									conjunct_mus.push_back(*vit);
#ifdef REACH_ADD_PATH_CONSTRAINTS
								for (InstL::iterator vit = _abViol.pathConstraints.begin(); vit != _abViol.pathConstraints.end(); vit++)
									conjunct_mus.push_back(*vit);
#endif
#ifdef ABSTRACTION_COURSE
								for (InstL::iterator vit = _abViol.restrictedConstraints.begin(); vit != _abViol.restrictedConstraints.end(); vit++)
									conjunct_mus.push_back(*vit);
	#ifdef REACH_ADD_PATH_CONSTRAINTS
								for (InstL::iterator vit = _abViol.restrictedPathConstraints.begin(); vit != _abViol.restrictedPathConstraints.end(); vit++)
									conjunct_mus.push_back(*vit);
	#endif
#endif

								InstLL muses;
								int res = tmpSolver->get_muses_2(0, conjunct_mus, muses, num_scalls_sat_correctness, num_scalls_unsat_correctness);

								int count = 0;
								for (InstLL::iterator it_muses2 = muses.begin(); it_muses2 != muses.end(); ++it_muses2)
								{
									count++;
									cout << "[" << count << "]: " << *it_muses2 << endl;
									for (auto& m: (*it_muses2))
									{
										ostringstream ostr;
										ostr << "error/" << *m;
										draw_graph(m, ostr.str(), 0, false);
									}

//									for (InstL::iterator it = (*it_muses2).begin(); it != (*it_muses2).end(); ++it)
//									{
//										Inst* tve = *it;
//										cout << *tve << " : " << tve->cex_mpz << tve->cex_val << endl;
//										OpInst* op = OpInst::as(tve);
//										if (op)
//										{
//											if (op->get_op() == OpInst::NotEq)
//											{
//												tve = OpInst::create(OpInst::LogNot, op);
//												cout << "\tc- " << *tve << " : " << tve->cex_mpz << tve->cex_val << endl;
//											}
//											for (InstL::const_iterator cit = tve->get_children()->begin(); cit != tve->get_children()->end(); cit++)
//											{
//												cout << "\t\tcc- " << *(*cit) << " : " << (*cit)->cex_mpz << endl;
//											}
//										}
//									}
								}
//								retrieve_cex_val(OpInst::create(OpInst::LogAnd, _viol), _cti_solver, true, true);
//								cout << "AF: " << endl;
//								count = 0;
//								for (InstLL::iterator it_muses2 = muses.begin(); it_muses2 != muses.end(); ++it_muses2)
//								{
//									count++;
//									cout << "[" << count << "]: " << endl;
//									for (InstL::iterator it = (*it_muses2).begin(); it != (*it_muses2).end(); ++it)
//									{
//										Inst* tve = *it;
//										cout << *tve << " : " << tve->cex_mpz << tve->cex_val << endl;
//										OpInst* op = OpInst::as(tve);
//										if (op)
//										{
//											if (op->get_op() == OpInst::NotEq)
//											{
//												tve = OpInst::create(OpInst::LogNot, op);
//												cout << "\tc- " << *tve << " : " << tve->cex_mpz << tve->cex_val << endl;
//											}
//											for (InstL::const_iterator cit = tve->get_children()->begin(); cit != tve->get_children()->end(); cit++)
//											{
//												cout << "\t\tcc- " << *(*cit) << " : " << (*cit)->cex_mpz << endl;
//											}
//										}
//									}
//								}
								delete tmpSolver;
								assert(0);
							}
							TIME_E(start_time, end_time, _cc_extra_tb_time);
							_tb_time += time_diff;
							TIME_S(start_time);
#endif
							/// END

						bool isSat = solveBadDest();


			      if (isSat)
			        isSat = solvePartition(_abViol, "trans. from F[" + to_string(_frame_idx) + "] to !P+");

			      if (isSat)
			        isSat = solveCube(_abViol.mainSubConstraints, _abViol.mainConstraints, "cube in F[" + to_string(_frame_idx) + "]");

						int tb_ret = 3;
						if (isSat) {

#ifdef PRINT_ALL_ABSTRACT_TRANSITIONS
            string tid = "#" + to_string(ve_prop->get_id());
            AVR_LOG(15, 0, "\t(" << tid << ")" << endl);
            print_states_transitions("fsm_c" + tid + ".txt", _abViol.mainConstraints, _ve_prop_eq_0, true, true);
            print_states_transitions("fsm_a" + tid + ".txt", _abViol.mainConstraints, _ve_prop_eq_0);
#endif

              AVR_LOG(13, 3, "<---" << endl);
              _tb_queue.PQ_clear();
              AVR_LOG(13, 2, "CCEXT_block: " << endl);
              tb_ret = ccext_block();
              AVR_LOG(13, 2, "<---" << endl);
						}

            TIME_E(start_time, end_time, _tb_time);

            AVR_LOG(6, 1, "ccext_block() returns " << tb_ret << endl);
            AVR_LOG(6, 2, "ccext_block(), runtime: " << double(time_diff)/1000000 << endl);

            if(tb_ret == 1) {
              SAT_terminated = true;
              break;
            } else if (tb_ret == 2) {
              AVR_LOG(6, 1, "Averroes Termination Condition from ccext_block()!!!	Property holds !!!" << endl);
              return EXIT_HOLD;
            }

            print_frame_summary(_frame_idx);
						continue;
					}
					_nBlocksU++;
				}
				AVR_LOG(1, 1, "GOOD!!!	( R" << _frame_idx << " && P && T && !P+ ) is UNSAT ~~" << endl);
				break;
			}// while(1){ // Within the same frame, check a prop repeatedly

			if (SAT_terminated == true) {
				break;
			}

//			reset_frame_solvers();
//      reset_cti_solver();

      print_frame_summary(_frame_idx);
#ifdef PRINT_FRAME_SUMMARY
       cerr << "\r" << endl;
#endif

       add_frame_solver();

			if (_frame_idx != 0) {//forward propagation

#ifdef FP_EXPAND_FRAME
	TIME_S(start_time);
	InstL conjunct_reach; //forward propagation
	conjunct_reach.push_back(_ve_model);
	conjunct_reach.push_back(_ve_prop_eq_1);
	conjunct_reach.push_back(_ve_model_nsf);
	conjunct_reach.push_back(_ve_model_next);
	conjunct_reach.push_back(_ve_prop_next_eq_0);

	for (InstL::iterator it3 = _negated_refs.begin(); it3 != _negated_refs.end(); ++it3)
		conjunct_reach.push_back(*it3);

	Inst* ve_reach = OpInst::create(OpInst::LogAnd, conjunct_reach);
	z3_API int_solver(&_abstract_mapper, 0, true, false);
	int_solver.s_assert(ve_reach);
	int res = int_solver.s_check(AB_QUERY_TIMEOUT);

	if (res == 1)
	{
		InstLL muses;
		InstS sourceSet;
		assert(_negated_cubes[_frame_idx].size() == _cubes[_frame_idx].size());
		for (auto& nc: _negated_cubes[_frame_idx])
			sourceSet.insert(nc);
		unsigned origSz = _negated_cubes[_frame_idx].size();

		int res = int_solver.get_muses_2(AB_QUERY_TIMEOUT, _negated_cubes[_frame_idx], muses, num_scalls_sat_muses_reach, num_scalls_unsat_muses_reach);
		assert(res == 1);
		InstL& mus = muses.front();
		unsigned newSz = mus.size();
		if (newSz < origSz)
		{
			_cubes[_frame_idx].clear();
			_negated_cubes[_frame_idx].clear();
			for (auto& nc: mus)
			{
				_negated_cubes[_frame_idx].push_back(nc);
				_cubes[_frame_idx].push_back(OpInst::create(OpInst::LogNot, nc));
				sourceSet.erase(nc);
			}
			for (auto& s: sourceSet)
			{
				for (int i = 1; i < _frame_idx; i++)
				{
					for (InstL::iterator it = _negated_cubes[i].begin(); it != _negated_cubes[i].end();)
					{
						if ((*it) == s)
							it = _negated_cubes[i].erase(it);
						else
							it++;
					}
				}
			}

			AVR_LOG(15, 0, "Reducing F[" << _frame_idx << "]" << " from " << origSz << " to " << newSz << endl);
//			AVR_LOG(15, 0, "MUS: " << mus << endl);
		}
	}
	else if (res == 0)
	{
//		_cubes[_frame_idx].clear();
//		_negated_cubes[_frame_idx].clear();
//		AVR_LOG(15, 0, "Reducing F[" << _frame_idx << "]" << " to empty" << endl);
		AVR_LOG(15, 0, "P & T & !P+ & Refinements is now UNSAT" << endl);
	}
	else
		assert(0);

	TIME_E(start_time, end_time, _cc_extra_fp_time);
	_fp_time += time_diff;
#endif

//	print_frames("before fp");

	TIME_S(start_time);
	AVR_LOG(15, 0, "\t[Forward propagation]:" << endl);
	for (int i = 1; i <= _frame_idx; i++) {

//    InstL conjunct_fp = _negated_cubes[i]; //forward propagation
//    AVR_LOG(3, 6, "FP negated_cubes[" << i << "]: :" << (_negated_cubes[i]));
//    conjunct_fp.push_back(_ve_model);
//    conjunct_fp.push_back(_ve_prop_eq_1);
//
////    conjunct_fp.push_back(_ve_model_nsf);
//
//    conjunct_fp.push_back(_ve_model_next);
//    conjunct_fp.push_back(_ve_prop_next_eq_1);
//    for (InstL::iterator it3 = _negated_refs.begin(); it3 != _negated_refs.end(); ++it3)
//      conjunct_fp.push_back(*it3);
//    AVR_LOG(3, 6, "conjunct_fp (i = " << i << "): " << conjunct_fp << endl);
////    Inst *ve_fp = OpInst::create(OpInst::LogAnd, conjunct_fp);
////
////    SOLVER_AB int_solver(_abstract_mapper, AVR_EXTRA_IDX, false, fp);
////    int_solver.s_assert(ve_fp);
////
//#ifdef DO_CORRECTNESS_CHECKS
//    TIME_E(start_time, end_time, _fp_time);
//    TIME_S(start_time);
//    InstLL muses;
//    y2_API int_solver2(_abstract_mapper, AVR_EXTRA_IDX, true, regular);
//    int_solver2.get_muses_2(AB_QUERY_TIMEOUT, conjunct_fp, muses, num_scalls_sat_correctness, num_scalls_unsat_correctness, &int_solver2);
//    if (!muses.empty())
//    {
//      for (InstLL::iterator lit = muses.begin(); lit != muses.end(); lit++)
//      {
//        cout << "Mus: " << *lit << endl;
//      }
//      z3_API int_solver3(_abstract_mapper, AVR_EXTRA_IDX, true, regular);
////      int_solver3.stop_ex_cc_interpret();
//      int_solver3.s_assert(muses.front());
//      int res = int_solver3.s_check(AB_QUERY_TIMEOUT);
//      cout << "Result: " << res << endl;
//      int_solver3.print_query(0, ERROR, "error");
//      assert(0);
//    }
//    TIME_E(start_time, end_time, _cc_extra_fp_time);
//    _fp_time += time_diff;
//    TIME_S(start_time);
//#endif
////
////    int_solver.forward_propagation(0, i, _negated_cubes, _cubes, &forward_all_next2pre, &forward_all_pre2next, &forward_set_contains, this);

    solveRelative(i, NULL, fp, false, false);
		AVR_LOG(3, 1, "%% (FP) frame_idx: " << i << ", sat: " << Solver::num_scalls_sat_fp_non_accum << ", unsat: "
									<< Solver::num_scalls_unsat_fp_non_accum << ", contained: " << Solver::num_scalls_contained_fp_non_accum << endl);
#ifdef FP_EARLY_EXIT
//		if (i < _cubes.size())
		assert (i < _cubes.size());
		{
			if (_cubes[i].empty())
			{
				AVR_LOG(15, 0, "\t\tProperty holds" << endl);
			  TIME_E(start_time, end_time, _fp_time);
				return EXIT_HOLD;
			}
		}
#endif

#ifdef FP_RECURSIVE
		if (Solver::num_scalls_unsat_fp_non_accum > 0)
			i--;
#endif
	}

	print_frames("after fp");

	TIME_E(start_time, end_time, _fp_time);
	AVR_LOG(3, 2, "forward_propagation, runtime: " << double(time_diff)/1000000 << endl);

//	for (int i = 1; i < _cubes.size(); i++)
	for (int i = 1; i <= _frame_idx; i++)
	{
		if ((i < _cubes.size()) && _cubes[i].empty()) {
			AVR_LOG(15, 0, "\t\tProperty holds" << endl);
			return EXIT_HOLD;
		}
	}
	}

  reset_cti_solver();

  bool reset_frames = false;
  bool reset_context = false;

#ifdef REFRESH_CONTEXT
  if (Inst::numContextCalls > Inst::maxContextCalls) {
    reset_context = true;
    reset_frames = true;
    Inst::numContextCalls = 0;
  }
#else
#ifdef RESET_CONTEXT_AFTER_FP
  reset_context = true;
  reset_frames = true;
#endif
#endif

#ifdef RESET_FRAME_SOLVERS_AFTER_FP
  reset_frames = (_frame_idx % 5 == 0);
#endif

	if (reset_frames)
		reset_frame_solvers();

	if (reset_context) {
		unsigned memory_usage = usage.ru_maxrss/1024;	// accurate memory usage in Mbytes
		if (memory_usage > 512) {
			delete_solvers();
			reset_solv();
			numResetContext++;
		}
	}

	if (!reset_frames && (_frame_idx == 0))
		set_frame_solver(0);

  _frame_idx++;
  print_frame_summary(_frame_idx);

  if (reset_frames)
  	set_frame_solvers();

  set_cti_solver();
  _loop_idx = 0;

	}// while(1){// increments Frame

		// Assume CEXT : c0, c1, ... , ck
		// Check ck -> !P
		if (SAT_terminated == true)
		{
			TIME_S(start_time);

			AVR_LOG_NO_TAG(4, 1, endl);
			AVR_LOG(4, 1, "##############################################" << endl);
			AVR_LOG(4, 1, "########		DATAPATH REFINEMENT BEGINS, refine_idx: " << _num_dp_refine << endl);

			AVR_LOG(15, 0, "\n\t[Concrete check]:" << endl);

			// the first proof_oblig should have the smallest priority
			// derive CEXT in reverse order from the elements in tb_queue
			_rcext_orig.clear();
			ABSTRACT_CUBE _badCube;
			deque < ABSTRACT_REACH_VIOL* > queue_rev;

			for(PQElement* pq_elem = _tb_queue.PQ_head(); pq_elem != NULL; pq_elem = pq_elem->pNext)
			{
				ABSTRACT_REACH_VIOL& abViol = pq_elem->abViol;
#ifndef AB_SUBSTITUTE
				InstL cubeConstraints = abViol.mainConstraints;
#else
				InstL cubeConstraints = abViol.concreteConstraints;
#endif
//					for (auto& v: abViol.pathConstraints)
//						cubeConstraints.push_back(v);
				ABSTRACT_CUBE tmp;
				if (cubeConstraints.empty())
					tmp.cube = NumInst::create(1, 1, SORT());
				else
				{
					tmp.cube = OpInst::create(OpInst::LogAnd, cubeConstraints);
					tmp.cube = OpInst::create(OpInst::LogAnd, cubeConstraints);
				}

				if (abViol.nextStateConstraints.empty())
					tmp.next = NumInst::create(1, 1, SORT());
				else
					tmp.next = OpInst::create(OpInst::LogAnd, abViol.nextStateConstraints);

				tmp.frame = pq_elem->frame;
				tmp.relevantWires = &(abViol.relevantWires);
				tmp.relevantWiresNext = &(abViol.relevantWiresNext);

				_rcext_orig.push_front(tmp);
				queue_rev.push_front(&abViol);
//					AVR_LOG(4, 4, "F[" << rcext_orig[0].frame << "]  " << *(rcext_orig[0].cube)  << " Next: " << *(rcext_orig[0].next) << endl);
//					AVR_LOG(15, 0, "A[" << pq_elem->frame << "]  " << *(pq_elem->cube)  << " Next: " << *(pq_elem->nextState) << endl);
			}
			if (i_not_p_unsat != false)
			{
				_badCube.cube = OpInst::create(OpInst::LogAnd, _bad_cube.nextStateConstraints);
//				_badCube.frame = NULL;
//				_badCube.next = NULL;
				_badCube.relevantWires = &(_bad_cube.relevantWires);
				_badCube.relevantWiresNext = &(_bad_cube.relevantWiresNext);
			}

			deque< ABSTRACT_CUBE >& rcext = _rcext_orig;

			int count = 0;
			AVR_LOG(15, 0, "\n[ ACEXT ]: (Length: " << rcext.size() << ")" << endl);
			if (i_not_p_unsat != false)
			{
				Inst* bad_cube = _badCube.cube;
				AVR_LOG(15, 1, "\tA[" << "End" << "] in !P : " << *bad_cube << endl);
			}
			for(deque< ABSTRACT_CUBE >::iterator it = rcext.begin(); it != rcext.end(); it++)
			{
				AVR_LOG(15, 1, endl << "\tA[" << count << "] in F[" << (*it).frame << "]: " << *((*it).cube) <<
						" ( n" << (*it).cube->childrenInfo[NUM] <<
						" s" << (*it).cube->childrenInfo[SIG] <<
						" c" << (*it).cube->childrenInfo[CONST] <<
						" fc" << (*it).cube->childrenInfo[FC] <<
						((*it).cube->fcLevel > 1 ? (" fl:" + to_string((*it).cube->fcLevel)) : "") <<
						" )" << endl);
				AVR_LOG(15, 1, "\tT[" << count << "]: " << *((*it).next) << endl);
				count++;
			}
			AVR_LOG(15, 1, endl);

			InstToBoolM dp_lemmas;
			if (_frame_idx == 0)
			{
				if (i_not_p_unsat == false)
				{
					_nLegnthsCEXTL.push_back(0);
					assert(rcext.size() == 1);

					ABSTRACT_CUBE& abCube = rcext.front();
					// I && !P
					conjunct_prop.clear();
					conjunct_hard.clear();
					conjunct_prop.push_back(abCube.cube);
					conjunct_prop.push_back(_ve_model);

					Inst *ve_prop_wo_ref = OpInst::create(OpInst::LogAnd, conjunct_prop);
//					for (InstL::iterator it3 = _negated_refs.begin(); it3 != _negated_refs.end(); ++it3)
//					{
////						add_intermediate_constraints(*it3, conjunct_prop);
//						conjunct_prop.push_back(*it3);
//						//++it3;
//					}
//					ve_prop = OpInst::create(OpInst::LogAnd, conjunct_prop);
					AVR_LOG(4, 5, "I && !P:" << conjunct_prop);

#ifdef EXTRA_CHECKS
					if (_euf_solver)
					{
						delete _euf_solver;
						_euf_solver = NULL;
					}
					_euf_solver = new z3_API(&_abstract_mapper, AVR_BASIS_IDX, false, false);

					_sat_res = _euf_solver->check_sat(ve_prop);
					//TIME_E(start_time, end_time, _cti_time);
					//AVR_LOG(4, 2, "DP-R abst-level-solve, I && !P, runtime: " << double(time_diff)/1000000 << endl);

					if (_sat_res)
#endif
					{
						AVR_LOG(4, 1, "(I && !P) : datapath refinement" << endl);

						_new_refs.clear();

						AVR_LOG(15, 0, "\t\tSAT_c ? [ F[0] & !P ]: " );
						refine(conjunct_hard, abCube, ve_prop_wo_ref, false);

						if (!_new_refs.empty())
						{
							for (auto& v: _new_refs)
								dp_lemmas[v] = true;
							add_lazy_assumes(dp_lemmas);

							AVR_LOG(15, 0, "\n\t" << "[Lemmas]: " << endl);
							int count = 0;
							bool added = false;
							for(auto& v: dp_lemmas)
							{
								Inst *ref = v.first;
								Inst *tve = OpInst::create(OpInst::LogNot, ref);
								count++;
								AVR_LOG(15, 0, "\t\t[" << count << "] " << *tve << endl);
								added |= add_refinement(tve);
							}
							if (!added) {
								AVR_LOG(15, 0, "(error: no new lemma learnt)" << endl);
								cout << _negated_refs << endl;
								assert(0);
							}
						}
						if (!_feas_sat_res)
						{
							_refine_exit_frame = 0;

							TIME_E(start_time, end_time, _dpr_time);
							AVR_LOG(4, 2, "datapath refinement, I && !P, runtime: " << double(time_diff)/1000000 << endl);
							dp_refinement_cleanup();
							continue;
						}
						else
						{
							for (auto& v: Inst::_s_reg) {
								cext.add(-1, v, v, false);
							}
							for (auto& v: Inst::_s_inp) {
								if (v != _ve_prop_eq_1)
									cext.add(-1, v, v, true);
							}
							//cout << endl << "===  VIOLATED  === !!! CEX is feasible !!! : length 1" << endl;
//							print_cex();
							verify_ret_value = EXIT_VIOL;
							TIME_E(start_time, end_time, _dpr_time);
							break;
						}
					}
#ifdef EXTRA_CHECKS
					else
					{
						AVR_LOG(4, 1, "I && !P is UNSAT ? (It was SAT in the previous SMT call)" << endl);
						assert(0);
					}
#endif
				}

				// I && T && !P+
				_nLegnthsCEXTL.push_back(1);

				Inst *ve_prop_wo_ref;
				/// Aman
#ifdef CHECK_BAD_CUBE
					conjunct_prop.clear();
					conjunct_hard.clear();
					conjunct_prop.push_back(_badCube.cube);
					conjunct_prop.push_back(_ve_model_next);

					AVR_LOG(4, 2, "Checking C_bad " << endl);
					AVR_LOG(4, 5, "C_bad " << conjunct_prop);

					ve_prop_wo_ref = OpInst::create(OpInst::LogAnd, conjunct_prop);
//					for (InstL::iterator it3 = _negated_refs.begin(); it3 != _negated_refs.end(); ++it3)
//					{
//						conjunct_prop.push_back(*it3);
//					}
//
//					ve_prop = OpInst::create(OpInst::LogAnd, conjunct_prop);
					_feas_sat_res = false;
					AVR_LOG(4, 1, "C_bad is " << (_sat_res ? "SAT" : "UNSAT") << endl);

#ifdef EXTRA_CHECKS
					if (_euf_solver){
						delete _euf_solver;
						_euf_solver = NULL;
					}
					_euf_solver = new z3_API(&_abstract_mapper, AVR_BASIS_IDX, false, false);

					_sat_res = _euf_solver->check_sat(ve_prop);
					//AVR_LOG(4, 2, "DP-R abst-level-solve, idx: " << idx << ", runtime: " << double(time_diff)/1000000 << endl);

					if (_sat_res)
#endif
					{
						_new_refs.clear();
						AVR_LOG(15, 0, "\t\tSAT_c ? [ A[End] ]:              " );
						refine(conjunct_hard, _badCube, ve_prop_wo_ref, false);
						if(!_feas_sat_res)
						{
							_refine_exit_frame = BAD_CUBE_INDEX;

							for (auto& v: _new_refs)
								dp_lemmas[v] = true;
							add_lazy_assumes(dp_lemmas);

							AVR_LOG(15, 0, "\n\t" << "[Lemmas]: " << endl);
							int count = 0;
							bool added = false;
							for(auto& v: dp_lemmas)
							{
								Inst *ref = v.first;
								Inst *tve = OpInst::create(OpInst::LogNot, ref);
								count++;
								AVR_LOG(15, 0, "\t\t[" << count << "] " << *tve << endl);
								added |= add_refinement(tve);
							}
							if (!added) {
								AVR_LOG(15, 0, "(error: no new lemma learnt)" << endl);
								cout << _negated_refs << endl;
								assert(0);
							}
							dp_refinement_cleanup();
							TIME_E(start_time, end_time, _dpr_time);
							continue;
						}
					}
#ifdef EXTRA_CHECKS
					else
					{
						AVR_LOG(4, 1, "C_bad is UNSAT ? (C is a violating cube)" << endl);
						dp_refinement_cleanup();
						/// Aman
				//		continue;
						// due to the DP lemmas from the (one-seg) feasibility check, this can be unsat.
						assert(0);
						/// END
					}
#endif
#endif
				/// END

				ABSTRACT_CUBE& abCube = rcext.front();
				assert(rcext.size() == 1);

				conjunct_prop.clear();
				conjunct_hard.clear();
				conjunct_prop = _conjunct_init;

				conjunct_prop.push_back(_badCube.cube);

				conjunct_prop.push_back(abCube.cube);
				conjunct_prop.push_back(abCube.next);

//				conjunct_prop.push_back(_ve_model);
				conjunct_prop.push_back(_ve_model_next);

//				conjunct_prop.push_back(_ve_prop_next_eq_0);
//
//				InstS relevantNext;
//				Inst::collect_next_reg(_ve_model_next, relevantNext, true);
//				Inst::init_visit();
//				for (auto& s: relevantNext)
//				{
//					conjunct_prop.push_back(OpInst::create(OpInst::Eq, s, Inst::_m_sn[s]));
//					add_all_wires(Inst::_m_sn[s], _tb_queue.PQ_head()->abViol.relevantWires);
//				}
//				add_all_wires(_ve_model_next, _bad_cube.relevantWiresNext);

				ve_prop_wo_ref = OpInst::create(OpInst::LogAnd, conjunct_prop);

//				for (InstL::iterator it3 = _negated_refs.begin(); it3 != _negated_refs.end(); ++it3)
//				{
//					conjunct_prop.push_back(*it3);
//				}
//				ve_prop = OpInst::create(OpInst::LogAnd, conjunct_prop);

				AVR_LOG(4, 5, "I && T && !P+:" << conjunct_prop);

#ifdef EXTRA_CHECKS
				if (_euf_solver){
					delete _euf_solver;
					_euf_solver = NULL;
				}
				_euf_solver = new z3_API(&_abstract_mapper, AVR_BASIS_IDX, false, false);

				_sat_res = _euf_solver->check_sat(ve_prop);
				//TIME_E(start_time, end_time, _cti_time);
				//AVR_LOG(4, 2, "DP-R abst-level-solve, idx: 0, runtime: " << double(time_diff)/1000000 << endl);

				if (_sat_res)
#endif
				{
					AVR_LOG(4, 1, "(I && T && !P+) : datapath refinement" << endl);
					_new_refs.clear();
					AVR_LOG(15, 0, "\t\tSAT_c ? [ F[0] & T & !P+ ]: " );
					refine(conjunct_hard, abCube, ve_prop_wo_ref, false);

					if (!_new_refs.empty())
					{
						for (auto& v: _new_refs)
							dp_lemmas[v] = true;
						add_lazy_assumes(dp_lemmas);

						AVR_LOG(15, 0, "\n\t" << "[Lemmas]: " << endl);
						int count = 0;
						bool added = false;
						for(auto& v: dp_lemmas)
						{
							Inst *ref = v.first;
							Inst *tve = OpInst::create(OpInst::LogNot, ref);
							count++;
							AVR_LOG(15, 0, "\t\t[" << count << "] " << *tve << endl);
							added |= add_refinement(tve);
						}
						if (!added) {
							AVR_LOG(15, 0, "(error: no new lemma learnt)" << endl);
							cout << _negated_refs << endl;
							assert(0);
						}
					}
					if (!_feas_sat_res)
					{
						_refine_exit_frame = 0;

						AVR_LOG(4, 2, "datapath refinement, I && T && !P, runtime: " << double(time_diff)/1000000 << endl);
						dp_refinement_cleanup();
						TIME_E(start_time, end_time, _dpr_time);
						continue;
					}
					else
					{
						simulation_check(rcext, _badCube);

						//cout << endl << "===  VIOLATED  === !!! CEX is feasible !!! : length 2" << endl;
						/// Aman
						print_concrete_min_term();
						InstL conjunct_c;
						for(InstToMpzM::iterator it = _min_term_c.begin(); it != _min_term_c.end(); it++)
						{
							Inst* tve = (*it).first;
							if (SigInst::as(tve) && (tve->get_sort_type() != arraytype))
							{
								Inst* num = NumInst::create((*it).second, tve->get_size(), tve->get_sort());
								NumInst* val = NumInst::as(num);
								if (tve->get_size() == 1)
								{
									if (val->get_num() == 0)
										conjunct_c.push_back(OpInst::create(OpInst::LogNot, tve));
									else
										conjunct_c.push_back(tve);
								}
								else
									conjunct_c.push_back(OpInst::create(OpInst::Eq, tve, val));
							}
						}

						ABSTRACT_CUBE tmp;
						tmp.frame = 0;
						tmp.cube = OpInst::create(OpInst::LogAnd, conjunct_c);
						tmp.next = NULL;
						_rcext_orig.push_back(tmp);
						/// END
//						print_cex();
						verify_ret_value = EXIT_VIOL;
						TIME_E(start_time, end_time, _dpr_time);
						break;
					}
				}
#ifdef EXTRA_CHECKS
				else
				{
					AVR_LOG(4, 1, "I && T && !P is UNSAT ? (It was SAT in the previous SMT call)" << endl);
					assert(0);
				}
#endif
			}
			else
			{
				_nLegnthsCEXTL.push_back(rcext.size());

				AVR_LOG(15, 0, "[Concrete check]:" << endl);

				bool all_feasible = true;
				int dp_refinement_status = -1;
				int dp_refinement_idx = 0;
				_loop_idx++;

#ifdef ABSTRACT_CHECK_ACEXT
				{
					deque< ABSTRACT_CUBE >::iterator q_it_ab = rcext.begin();
					Inst *cube = q_it_ab->cube;
					Inst* next = q_it_ab->next;
					int idx = q_it_ab->frame;
#ifndef AVR_DP_REFINEMENT_ON_ALL_CEXT_SEGMENTS
					if(dp_refinement_status == -1)
#endif
					{
						ABSTRACT_CUBE& abCube = (*q_it_ab);
						conjunct_prop.clear();
						conjunct_prop.push_back(cube);
						conjunct_prop.push_back(_ve_model_next);
						conjunct_prop.push_back(next);
						conjunct_prop.push_back(_badCube.cube);

						Inst *ve_prop_wo_ref = OpInst::create(OpInst::LogAnd, conjunct_prop);
						for (InstL::iterator it3 = _negated_refs.begin(); it3 != _negated_refs.end(); ++it3) {
							conjunct_prop.push_back(*it3);
						}

						ve_prop = OpInst::create(OpInst::LogAnd, conjunct_prop);
						_feas_sat_res = false;
						_new_refs.clear();
						AVR_LOG(15, 0, "\t\tSAT_a ? [ A[0] & T[0] & A[End]+ ]: " );

						refine(ve_prop, abCube, true, ve_prop_wo_ref, true);
						for (InstL::iterator sit = _new_refs.begin(); sit != _new_refs.end(); sit++)
						{
							dp_lemmas[*sit] = true;
						}
						dp_refinement_idx++;
						if (!_feas_sat_res)
						{
							_refine_exit_frame = idx;
							dp_refinement_status = dp_refinement_idx;
							all_feasible = false;
						}
					}

#ifndef AVR_DP_REFINEMENT_ON_ALL_CEXT_SEGMENTS
					if(dp_refinement_status == -1)
#endif
					{
						int rcextIdxAb = 0;
						Inst* cubeNext;
						for (int qc = rcext.size(); qc > 1; qc--) {
							if (qc > 1) {
								cubeNext = all_pre2next(q_it_ab->cube);
								++q_it_ab;
								rcextIdxAb++;
								_refine_seq_idx = idx;
							}
							idx  = q_it_ab->frame;
							cube = q_it_ab->cube;
							next = q_it_ab->next;
							ABSTRACT_CUBE& abCube = (*q_it_ab);
							InstL conjunct_reach;

							Inst::init_visit();
							if (qc == 2) {
								_refine_seq_idx = 0;
								assert(idx == 0);
								conjunct_reach = _negated_cubes[0];
								conjunct_reach.push_back(cube);
							} else {
								conjunct_reach.push_back(cube);
							}
							conjunct_reach.push_back(next);
							conjunct_reach.push_back(cubeNext);
							Inst *ve_reach_wo_ref = OpInst::create(OpInst::LogAnd, conjunct_reach);
							for (InstL::iterator it3 = _negated_refs.begin(); it3 != _negated_refs.end(); ++it3) {
								conjunct_reach.push_back(*it3);
							}
							Inst *ve_reach = OpInst::create(OpInst::LogAnd, conjunct_reach);
							_feas_sat_res = false;
							_new_refs.clear();
							AVR_LOG(15, 0, "\t\tSAT_a ? [ A[" << rcextIdxAb << "] & T[" << rcextIdxAb << "] & A[" << (rcextIdxAb - 1) << "]+ ]: " );
							refine(ve_reach, abCube, true, ve_reach_wo_ref, true);

							for (InstL::iterator sit = _new_refs.begin(); sit != _new_refs.end(); sit++)
								dp_lemmas[*sit] = true;

							dp_refinement_idx++;
							if (!_feas_sat_res)
							{
								_refine_exit_frame = idx;
								all_feasible = false;
								if(dp_refinement_status == -1)
								{
									dp_refinement_status = dp_refinement_idx;
								}
#ifndef AVR_DP_REFINEMENT_ON_ALL_CEXT_SEGMENTS
								break;
#endif
							}
						}
					}
				}
#endif


#ifdef CHECK_BAD_CUBE
#ifndef AVR_DP_REFINEMENT_ON_ALL_CEXT_SEGMENTS
      if(dp_refinement_status == -1)
#endif
      {
				conjunct_prop.clear();
				conjunct_hard.clear();
				conjunct_prop.push_back(_badCube.cube);
				conjunct_prop.push_back(_ve_model_next);

				AVR_LOG(4, 2, "Checking C_bad " << endl);
				AVR_LOG(4, 5, "C_bad " << conjunct_prop);

				Inst *ve_prop_wo_ref = OpInst::create(OpInst::LogAnd, conjunct_prop);
//				for (InstL::iterator it3 = _negated_refs.begin(); it3 != _negated_refs.end(); ++it3)
//					conjunct_prop.push_back(*it3);
//
//				ve_prop = OpInst::create(OpInst::LogAnd, conjunct_prop);
				_feas_sat_res = false;
				AVR_LOG(4, 1, "C_bad is " << (_sat_res ? "SAT" : "UNSAT") << endl);

#ifdef EXTRA_CHECKS
				if (_euf_solver){
					delete _euf_solver;
					_euf_solver = NULL;
				}
				_euf_solver = new z3_API(&_abstract_mapper, AVR_BASIS_IDX, false, false);

				_sat_res = _euf_solver->check_sat(ve_prop);
				//AVR_LOG(4, 2, "DP-R abst-level-solve, idx: " << idx << ", runtime: " << double(time_diff)/1000000 << endl);

				if (_sat_res)
#endif
				{
					AVR_LOG(15, 0, "\t\tSAT_c ? [ A[End] ]:              " );
					_new_refs.clear();
//					add_all_wires(ve_prop_wo_ref, dummyCube.relevantWires, true);
					refine(conjunct_hard, _badCube, ve_prop_wo_ref, false);

//					dp_lemmas.push_back(_new_refs);
					for (InstL::iterator sit = _new_refs.begin(); sit != _new_refs.end(); sit++)
					{
						dp_lemmas[*sit] = true;
					}

					dp_refinement_idx++;

					AVR_LOG(4, 2, "datapath refinement, C_bad " << ", runtime: " << double(time_diff)/1000000 << endl);

					if (!_feas_sat_res)
					{
						_refine_exit_frame = BAD_CUBE_INDEX;

						dp_refinement_status = dp_refinement_idx;
						all_feasible = false;
					}
				}
#ifdef EXTRA_CHECKS
				else
				{
					AVR_LOG(4, 1, "C_bad is UNSAT ? (C is a violating cube)" << endl);
					dp_refinement_cleanup();
					/// Aman
			//		continue;
					// due to the DP lemmas from the (one-seg) feasibility check, this can be unsat.
					assert(0);
					/// END
				}
#endif
      }
#endif
/// END

#ifdef CHECK_ALL_CUBES
    deque< ABSTRACT_CUBE >::iterator cit = rcext.begin();
    int cIdx = 0;
    while (cit != rcext.end())
    {
#ifndef AVR_DP_REFINEMENT_ON_ALL_CEXT_SEGMENTS
      if(dp_refinement_status == -1)
#endif
      {
				refineCube((*cit), cIdx++);
				for (InstL::iterator sit = _new_refs.begin(); sit != _new_refs.end(); sit++)
		    {
		      dp_lemmas[*sit] = true;
		    }

		    dp_refinement_idx++;

		    if (!_feas_sat_res)
		    {
		      _refine_exit_frame = (*cit).frame;

		      dp_refinement_status = dp_refinement_idx;
		      all_feasible = false;
		    }
      }
      else
        break;
      cit++;
    }
#endif

			deque< ABSTRACT_CUBE >::iterator q_it = rcext.begin();

			/// Aman
			int rcextIdx = 0;
			/// END

			int idx = q_it->frame;
			_refine_seq_idx = idx;
//				cout << "_refine_seq_idx: "  << _refine_seq_idx << endl;
			Inst *cube = q_it->cube;
			Inst* next = q_it->next;

// 				for (int i = 1; i <= _frame_idx; i++) {
// 					AVR_LOG(4, 4, "frame number : " << i << endl);
// 					AVR_LOG(4, 4, "&(_negated_cubes[i]):" << (_negated_cubes[i]));
// 				}
//				 Ri && P && T && !P+
//				 			if(_negated_cubes[_frame_idx].empty()){
//				 				conjunct_prop.clear();
//				 			}else{
//				 				conjunct_prop = _negated_cubes[_frame_idx];
//				 			}
//				 			conjunct_prop.push_back(_ve_model);
//				 			conjunct_prop.push_back(_ve_prop_eq_1);

#ifndef AVR_DP_REFINEMENT_ON_ALL_CEXT_SEGMENTS
			if(dp_refinement_status == -1)
#endif
			{
#if 1
// checking the feasibility of a cube
// (i.e. whether the abstract cube contains any concrete state or not)
///////////////////////////////////////////////////////////////////////////////////////
				ABSTRACT_CUBE& abCube = (*q_it);
				conjunct_prop.clear();
				conjunct_hard.clear();
//				add_all_wires(_ve_model, abCube.relevantWires, true);
//				conjunct_prop.push_back(_ve_prop_eq_1);
				conjunct_prop.push_back(cube);
//				conjunct_prop.push_back(_ve_model);
				conjunct_prop.push_back(_ve_model_next);

				/// Aman
//				next = slice_transition(abCube);
				conjunct_prop.push_back(next);

//	#ifndef INTERPRET_EX_CC
//				conjunct_prop.push_back(next);
//	#else
//				conjunct_prop.push_back(_ve_model_nsf);
//	#endif
				/// END

				conjunct_prop.push_back(_badCube.cube);
//				abCube.relevantWires.insert(abCube.relevantWires.end(), _badCube.relevantWires.begin(), _badCube.relevantWires.end());
				/// END

				AVR_LOG(4, 5, "Cend & P & T & !P+ " << conjunct_prop);

				Inst *ve_prop_wo_ref = OpInst::create(OpInst::LogAnd, conjunct_prop);
//				for (InstL::iterator it3 = _negated_refs.begin(); it3 != _negated_refs.end(); ++it3) {
////					add_intermediate_constraints(*it3, conjunct_prop);
//					conjunct_prop.push_back(*it3);
//					//++it3;
//				}
//
//				ve_prop = OpInst::create(OpInst::LogAnd, conjunct_prop);
				_feas_sat_res = false;

#ifdef EXTRA_CHECKS
				if (_euf_solver){
					delete _euf_solver;
					_euf_solver = NULL;
				}
				_euf_solver = new z3_API(&_abstract_mapper, AVR_BASIS_IDX, false, false);

				_sat_res = _euf_solver->check_sat(ve_prop);
				AVR_LOG(4, 1, "cube && dp_lemmas is " << (_sat_res ? "SAT" : "UNSAT") << endl);
				//AVR_LOG(4, 2, "DP-R abst-level-solve, idx: " << idx << ", runtime: " << double(time_diff)/1000000 << endl);

				if (_sat_res)
#endif
				{
					_new_refs.clear();
					AVR_LOG(15, 0, "\t\tSAT_c ? [ A[0] & T[0] & A[End]+ ]: " );

//          AVR_LOG(15, 0, "\n\t\tA[0]: " << endl);
//					collect_cubes(cube, true);
//					for (auto& v: _collected_cubes) {
//					  AVR_LOG(15, 0, "\t\t\t" << *v << endl);
//					}
//
//          AVR_LOG(15, 0, "\t\tT[0]: " << endl);
//          collect_cubes(next, true);
//          for (auto& v: _collected_cubes) {
//            AVR_LOG(15, 0, "\t\t\t" << *v << endl);
//          }
//
//          AVR_LOG(15, 0, "\t\tA[End]+: " << endl);
//          collect_cubes(_badCube.cube, true);
//          for (auto& v: _collected_cubes) {
//            AVR_LOG(15, 0, "\t\t\t" << *v << endl);
//          }

//          AVR_LOG(15, 0, "\t\t(wires) " << endl);
//          for (auto& v: *abCube.relevantWires) {
//            AVR_LOG(15, 0, "\t\t\t" << *v << endl);
//          }
//
//          AVR_LOG(15, 0, "\t\t(wires+) " << endl);
//          for (auto& v: *abCube.relevantWiresNext) {
//            AVR_LOG(15, 0, "\t\t\t" << *v << endl);
//          }

					refine(conjunct_hard, abCube, ve_prop_wo_ref, false);

					for (InstL::iterator sit = _new_refs.begin(); sit != _new_refs.end(); sit++)
					{
						dp_lemmas[*sit] = true;
					}

					dp_refinement_idx++;

					AVR_LOG(4, 2, "datapath refinement, C && P && T && !P+, idx: " << idx << ", runtime: " << double(time_diff)/1000000 << endl);

					if (!_feas_sat_res) {
						_refine_exit_frame = idx;

						dp_refinement_status = dp_refinement_idx;
						all_feasible = false;
					}
				}
#ifdef EXTRA_CHECKS
				else
				{
					AVR_LOG(4, 1, "C && P && T && !P+ is UNSAT ? (C is a violating cube)" << endl);
//					dp_refinement_cleanup();
					/// Aman
//					continue;
					// due to the DP lemmas from the (one-seg) feasibility check, this can be unsat.

					InstL conjunct_T;
					InstLL muses;
					collect_cubes(ve_prop, true);
					z3_API* tmpSolver = new z3_API(&_abstract_mapper, AVR_EXTRA_IDX, true, false);

					Inst::inc_dckey();
					int res = tmpSolver->identify_dont_cares(AB_QUERY_TIMEOUT, _collected_cubes, num_scalls_sat_correctness, num_scalls_unsat_correctness);
					tmpSolver->get_muses_2(0, _collected_cubes, muses, Reach::num_scalls_sat_correctness, Reach::num_scalls_unsat_correctness);
//					fetch_failure_condition(next, _collected_cubes, true, conjunct_T, muses);

					{
						cout << "full: " << *ve_prop << endl;
						ostringstream ostr;
						ostr << "error/" << *ve_prop;
						draw_graph(ve_prop, "", 0, true);
					}

					{
						cout << "\tCube: " << *cube << endl;
						ostringstream ostr;
						ostr << "error/" << *cube;
						draw_graph(cube, ostr.str(), 0, false);
					}
					{
						cout << "\tNext: " << *next << endl;
						ostringstream ostr;
						ostr << "error/" << *next;
						draw_graph(next, ostr.str(), 0, false);
					}

					int musIdx = 0;
					AVR_LOG(15, 0, "\n\t\t[MUS(s)]:" << endl);
					for (InstLL::iterator it_muses2 = muses.begin(); it_muses2 != muses.end(); ++it_muses2)
					{
						musIdx++;
						AVR_LOG(15, 0, "\t\t[" << musIdx << "]:" << endl);
						for (auto& m : (*it_muses2))
						{
							cout << "\t" << *m << endl;
							ostringstream ostr;
							ostr << "error/" << *m;
							draw_graph(m, ostr.str(), 0, false);

							OpInst* op = OpInst::as(m);
							if (op && op->get_op() == OpInst::Eq)
							{
								ExInst* exRhs = ExInst::as(op->get_children()->back());
								if (exRhs)
								{
									cout << "\n\tsimplified: " << *(exRhs->t_simple) << endl;
									{
										ostringstream ostr;
										ostr << "error/" << *(exRhs->t_simple);
										draw_graph((exRhs->t_simple), ostr.str(), 0, false);
									}

									SigInst* sigLhs = SigInst::as(op->get_children()->front());
									if (sigLhs)
									{
										Inst* expT = Inst::_m_sn[sigLhs];
										if (expT)
										{
											Inst* simpleT = simplify_expr(expT);
											cout << "\n\tsimplified T: " << *simpleT << endl;
											{
												ostringstream ostr;
												ostr << "error/" << *simpleT;
												draw_graph(simpleT, ostr.str(), 0, false);
											}
											assert(0);
										}
									}
								}
							}
							cout << endl;
						}
						AVR_LOG(15, 0, endl);
					}
					assert(0);
					/// END
				}
#endif
///////////////////////////////////////////////////////////////////////////////////////
#endif
			}

				int temp_idx = 0;

				int n_idx = idx;
				Inst *n_cube = cube;

				deque< ABSTRACT_CUBE >::iterator q_itTmp;
				Inst* cubeNext;

#ifndef AVR_DP_REFINEMENT_ON_ALL_CEXT_SEGMENTS
				if(dp_refinement_status == -1)
#endif
				{
//					all_feasible = true;
					// Assume CEXT : c0, c1, ... , ck
					// Check c(k-1) & T -> c(k) , ... , c0 & T -> c1 , R0 & T -> c0

					AVR_LOG(4, 6, "n_cube: " << *n_cube << endl);
					//for(; q_it != _tb_queue.end(); q_it++){
					for (int qc = rcext.size(); qc > 1; qc--) {
//						all_feasible = false;
						AVR_LOG(4, 1, "#$	refine sub loop idx: " <<temp_idx++ << endl);
						if (qc > 1) {
							/// Aman
							cubeNext = Inst::all_pre2next(q_it->cube);
							/// END

							++q_it;
							rcextIdx++;
							_refine_seq_idx = idx;
	//						cout << "_refine_seq_idx: "  << _refine_seq_idx << endl;
						}
						idx = q_it->frame;
						cube = q_it->cube;
						next = q_it->next;
						/// Aman
						AVR_LOG(4, 4, "@ F[" << idx << "]  " << *cube  << " Next: " << *next << endl);
						/// END

			//			AVR_LOG(4, 3, "## " << n_idx << " : " << *n_cube << endl);

	// 					Inst *cube_next = all_pre2next(n_cube, true);
	// 					AVR_LOG(4, 3, "cube_next: " << *cube_next << endl);
						ABSTRACT_CUBE& abCube = (*q_it);
						InstL conjunct_reach;
						conjunct_hard.clear();

						Inst::init_visit();
						if (qc == 2) {
							_refine_seq_idx = 0;
	//						cout << "_refine_seq_idx: 0" << endl;
							//				conjunct_reach = _negated_cubes[idx - 1];
							if (idx != 0) {
								AVR_LOG(4, 1, "idx: " << idx << endl);
							}
//							assert(idx == 0);
							conjunct_reach.clear();
							conjunct_hard.clear();
//							conjunct_reach = _negated_cubes[0];

	// 						conjunct_reach.push_back(_ve_model_nsf);
	// 						collect_cubes(cube_next, true);
							conjunct_reach.push_back(cube);
							q_itTmp = q_it;

	// 						for (InstL::iterator it3 = _collected_cubes.begin(); it3 != _collected_cubes.end(); ++it3) {
	// 							conjunct_reach.push_back(*it3);
	// 							//conjunct_cube_next.push_back(*it3);
	// 						}
						} else {
							conjunct_reach.push_back(cube);

//							conjunct_reach.push_back(_ve_model);
//							InstL propertyWires
//							add_all_wires(_ve_model_next, propertyWires, true);
//							conjunct_reach.push_back(_ve_prop_eq_1);
						}

						/// Aman
//						next = slice_transition(abCube);
						conjunct_reach.push_back(next);

//			#ifndef INTERPRET_EX_CC
//						conjunct_prop.push_back(next);
//			#else
//						conjunct_prop.push_back(_ve_model_nsf);
//			#endif

						conjunct_reach.push_back(cubeNext);
						/// END

//						AVR_LOG(4, 5, "conjunct_reach:" << conjunct_reach);
						//InstL conjunct_cube_next;

#if 1
						//conjunct_reach.push_back(_ve_model_nsf);
#else
						//cube_next = OpInst::create(OpInst::LogAnd, conjunct_cube_next);
						//analyzes coi of regs
						collect_nsfs(cube_next, true);
						AVR_LOG(4, 1, "##	collect_nsfs result: " << _m_sn.size() << " -> " << _collected_nsfs.size() << endl);
						for (InstS::iterator it3 = _collected_nsfs.begin(); it3 != _collected_nsfs.end(); ++it3) {
							conjunct_reach.push_back(*it3);
							//conjunct_cube_next.push_back(*it3);
						}
#endif

						Inst *ve_reach_wo_ref = OpInst::create(OpInst::LogAnd, conjunct_reach);
//						for (InstL::iterator it3 = _negated_refs.begin(); it3 != _negated_refs.end(); ++it3) {
////							add_intermediate_constraints(*it3, conjunct_reach);
//							conjunct_reach.push_back(*it3);
//							//++it3;
//						}
//
//						AVR_LOG(4, 5, "Ri && T && C+:" << conjunct_reach);
//
//						Inst *ve_reach = OpInst::create(OpInst::LogAnd, conjunct_reach);
						_prop = _ve_model_nsf; //TODO check and delete
						_feas_sat_res = false;

#ifdef EXTRA_CHECKS
						if (_euf_solver){
							delete _euf_solver;
							_euf_solver = NULL;
						}
						_euf_solver = new z3_API(&_abstract_mapper, AVR_BASIS_IDX, false, false);
						_sat_res = _euf_solver->check_sat(ve_reach);
						if (_sat_res)
#endif
						{
							AVR_LOG(4, 1, "SAT, so run refine" << endl);
							//DEBUG_EXPR7(ve_reach);
							_new_refs.clear();
							AVR_LOG(15, 0, "\t\tSAT_c ? [ A[" << rcextIdx << "] & T[" << rcextIdx << "] & A[" << (rcextIdx - 1) << "]+ ]: " );
							refine(conjunct_hard, abCube, ve_reach_wo_ref, false);

							for (InstL::iterator sit = _new_refs.begin(); sit != _new_refs.end(); sit++)
								dp_lemmas[*sit] = true;

							dp_refinement_idx++;
							if (!_feas_sat_res)
							{
								_refine_exit_frame = idx;

								all_feasible = false;
								if(dp_refinement_status == -1)
								{
									dp_refinement_status = dp_refinement_idx;
								}
#ifndef AVR_DP_REFINEMENT_ON_ALL_CEXT_SEGMENTS
								break;
#endif
							}
//							else
//							{
//								all_feasible = true;
//							}
						}
#ifdef EXTRA_CHECKS
						else
						{
							AVR_LOG(15, 0, "\tFail: SAT_c ? [ A[" << rcextIdx << "] & T[" << rcextIdx << "] & A[" << (rcextIdx - 1) << "]+ ]: UNSAT" << endl);
							collect_cubes(ve_reach, true);
							cout << "\nQuery: " << _collected_cubes << endl;
							collect_cubes(cube, true);
							cout << "\nCube: " << _collected_cubes << endl;
							collect_cubes(next, true);
							cout << "\nNext: " << _collected_cubes << endl;
							collect_cubes(cubeNext, true);
							cout << "\nCube+: " << _collected_cubes << endl;
							/// Aman - Test
							z3_API* tmpSolver = new z3_API(&_abstract_mapper, AVR_EXTRA_IDX, false, false);
//							InstL conjunctTmp;
//							for (InstL::iterator it3 = _negated_refs.begin(); it3 != _negated_refs.end(); ++it3) {
//								conjunctTmp.push_back(*it3);
//							}
//							tmpSolver->s_assert(OpInst::create(OpInst::LogAnd, conjunctTmp));
							collect_cubes(ve_reach, true);
							tmpSolver->s_assert_retractable(_collected_cubes);
							int tmpRes = tmpSolver->s_check(AB_QUERY_TIMEOUT);
							tmpSolver->s_retract_assertions();
							assert (tmpRes != 1);
							InstLL muses;
							int res = tmpSolver->get_muses_2(0, _collected_cubes, muses, num_scalls_sat_correctness, num_scalls_unsat_correctness);

							int count = 0;
							for (InstLL::iterator it_muses2 = muses.begin(); it_muses2 != muses.end(); ++it_muses2)
							{
								count++;
								cout << "[" << count << "]: " << *it_muses2 << endl;
//								for (auto& m: *it_muses2)
//									draw_graph(*it_muses2, "", 0);
							}
							delete tmpSolver;
							/// END
							assert(0);
						}
#endif
						n_idx = idx;
						n_cube = cube;
					}
				}

				bool simStage = false;
				/// Aman
				if (all_feasible)
				{
					simStage = true;
					_feas_sat_res = false;
					bool res_sim = simulation_check(rcext, _badCube);


					if (!res_sim)
					{
//						dp_lemmas.push_back(_new_refs);
						for (InstL::iterator sit = _new_refs.begin(); sit != _new_refs.end(); sit++)
						{
							dp_lemmas[*sit] = false;
						}

						dp_refinement_idx++;
						assert (!_feas_sat_res);
						if(dp_refinement_status == -1)
						{
							dp_refinement_status = dp_refinement_idx;
						}
						all_feasible = false;

					}
//					cout << "==============================================" << endl;
//					cout << "TODO: Implement simulation check" << endl;
//					cout << "==============================================" << endl;
//					return 2;
				}
				/// END

				//cout << "###	dp_refinement_status: " << dp_refinement_status << ", dp_refinement_idx: " << dp_refinement_idx << endl;
				//cout << "$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$" << endl;
				#ifdef AVR_DUMP_ACCUM_REFF
					accum_reff << "###	dp_refinement_status: " << dp_refinement_status << ", dp_refinement_idx: " << dp_refinement_idx << endl;
					accum_reff << "$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$" << endl;
				#endif
				//assert(0);

//				deque< ABSTRACT_CUBE >::iterator temp_q_it = rcext.begin();
//				for(; temp_q_it != rcext.end(); ++temp_q_it){
//					Inst* later_cube = temp_q_it->cube;
//					init_invalid_state_field(later_cube, true);
//					derive_euf_func_list_debug(_func_list, later_cube, true);
//					check_invalid_state_term(later_cube);
//				}

				AVR_LOG(4, 2, "datapath refinement, others, runtime: " << double(time_diff)/1000000 << endl);
				if (all_feasible == true)
				{
					//cout << endl << "===  VIOLATED  === !!! CEX Trace is feasible !!!" << endl;
//					print_cex();
					verify_ret_value = EXIT_VIOL;
					TIME_E(start_time, end_time, _dpr_time);
					break;
				}
				else
				{
					AVR_LOG(15, 0, "\n\t" << "[Lemmas]: " << endl);
					int count = 0;
          int trueCount = 0;

					/// Test
//#ifdef INTERPRET_EX_CC
//					InstL lemmaList;
//					InstS simpleRefs;
//					for(InstS::iterator ref_it = dp_lemmas.begin(); ref_it != dp_lemmas.end(); ++ref_it)
//					{
//						Inst *ref = *ref_it;
//						Inst* simpleRef = simplify_expr(ref);
//						if (simpleRef != ref)
//						{
//							if (simpleRefs.find(simpleRef) == simpleRefs.end())
//							{
//								simpleRefs.insert(simpleRef);
//								lemmaList.push_back(simpleRef);
//							}
//						}
//						lemmaList.push_back(ref);
//					}
//#endif

          add_lazy_assumes(dp_lemmas);

					for(InstToBoolM::iterator ref_it = dp_lemmas.begin(); ref_it != dp_lemmas.end(); ++ref_it)
//					for(InstL::iterator ref_it = lemmaList.begin(); ref_it != lemmaList.end(); ++ref_it)
					{
						Inst *ref = (*ref_it).first;
						Inst *tve = OpInst::create(OpInst::LogNot, ref);

						SOLVER_AB tmpSolver(_abstract_mapper, AVR_EXTRA_IDX, false, regular);
//						tmpSolver->disable_ex_cc_interpret();

						InstL conjunctTmp;
						conjunctTmp.push_back(ref);
						for (InstL::iterator it3 = _negated_refs.begin(); it3 != _negated_refs.end(); ++it3) {
							conjunctTmp.push_back(*it3);
						}
						tmpSolver.s_assert(OpInst::create(OpInst::LogAnd, conjunctTmp));
						int tmpRes = tmpSolver.s_check(AB_QUERY_TIMEOUT, false);

						count++;
						AVR_LOG(15, 0, "\t\t[" << count << "] " << *tve << endl);
						if(tmpRes == AVR_QUSAT)
						{
							bool added = add_refinement(tve, "ab", (*ref_it).second);
							if (added) {
							  trueCount++;
								AVR_LOG(15, 0, "\t\t(redundant lemma)" << endl);
							}
							else {
								AVR_LOG(15, 0, "\t\t(syntactic. redundant lemma)" << endl);
							}
						}
						else {
						  trueCount++;
							add_refinement(tve, "", (*ref_it).second);
						}
					}
					/// END

					if (trueCount == 0)
					{
						if (simStage)
						{
							AVR_LOG(15, 0, "(no new lemma learnt)" << endl);
						}
						else
						{
								if (Config::g_ab_granularity < AB_GRANULARITY_MAX) {
//								if (false && Config::g_allow_inputs < MAX_AB_FINENESS) {
//									Config::g_ab_granularity++;
									Config::g_ab_granularity = AB_GRANULARITY_MAX;
									AVR_LOG(15, 0, "(no new lemma learnt, incrementing abstraction granularity to level " << Config::g_ab_granularity << ")" << endl);
//									assert(0);
								}
								else {
									AVR_LOG(15, 0, "(error: no new lemma learnt)" << endl);
									cout << _negated_refs << endl;
									assert(0);
								}

//	//						cout << dp_lemmas.size() << endl;
//							for(InstToBoolM::iterator ref_it = dp_lemmas.begin(); ref_it != dp_lemmas.end(); ++ref_it)
//							{
//								Inst *ref = (*ref_it).first;
//								Inst *tve = OpInst::create(OpInst::LogNot, ref);
//								cout << "\t(redundant lemma:" << endl;
//								cout << "\t\t" << *tve << " )" << endl;
//
//								SOLVER_AB tmpSolver(_abstract_mapper, AVR_EXTRA_IDX, false, regular);
////								tmpSolver->disable_ex_cc_interpret();
//
//								tmpSolver.s_assert(ref);
//								tmpSolver.s_assert_retractable(_negated_refs);
//								int tmpRes = tmpSolver.s_check_assume(AB_QUERY_TIMEOUT, false);
//								tmpSolver.s_retract_assertions();
//								assert (tmpRes != AVR_QSAT);
//
//								InstLL muses;
////								tmpSolver->get_muses_2(AB_QUERY_TIMEOUT, _negated_refs, muses, num_scalls_sat_correctness, num_scalls_unsat_correctness);
//
//								int numMus = 0;
//								cout << "MUSs: " << endl;
//								for (InstLL::iterator it_muses2 = muses.begin(); it_muses2 != muses.end(); ++it_muses2)
//								{
//									cout << "[" << ++numMus << "]: " << (*it_muses2) << endl;
//								}
//							}
//							assert(0);
						}
					}
					else
					{
						AVR_LOG(15, 0, "#Lemmas = " << _negated_refs.size() << endl);
					}
//						dp_lemmas.pop_front();
//					}
					TIME_E(start_time, end_time, _dpr_time);

#ifdef TEST_REFINE_FLUSH
					refine_flush();
#endif
				}
				dp_refinement_cleanup();

//#endif	//ONE_SEG_FEASIBILITY_CHECK
//}
			}
		}
		else
		{
			//cout << endl << "===     HOLD     === !!!	Property holds !!!" << endl;
			verify_ret_value = EXIT_HOLD;
			break;
		}
	}
	// 	if(tempf0) tempf0.close();
	// 	if(tempf1) tempf1.close();
	// 	if(tempf2) tempf2.close();
	#ifdef AVR_DUMP_ACCUM_REFF
		accum_reff.close();
	#endif
	return verify_ret_value;
}

}
