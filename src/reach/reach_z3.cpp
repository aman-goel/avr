/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


#include "reach_z3.h"

#ifdef _Z3

#include <cstdlib>
#include <fstream>
#include <cmath>
#include <csignal>
#include <pthread.h>
#include <functional>

using namespace std;

namespace _z3 {

z3_IntBvM z3_API::m_sz_to_bv;
z3_IntUtM z3_API::m_sz_to_ut;
z3_StringToFunctM z3_API::m_funct;

z3_StringToDecl z3_API::m_var_decs;
z3_InstToFuncDecl z3_API::m_func_decs;
z3_MpzToNum z3_API::m_num_to_const;

z3_config  z3_API::g_config   = NULL;
z3_context z3_API::g_ctx   = NULL;
z3_param  z3_API::g_param   = NULL;

#ifdef ASSERT_DISTINCT_NUMBERS
	pair < int, z3_expr_vec > z3_API::m_distinct_constraints = make_pair(-1, z3_expr_vec());
#endif


/// Timeouts in milliseconds
#ifndef MICRO_ALARM
	unsigned z3_API::query_timeout_ab           = AB_QUERY_TIMEOUT * 1000;
	unsigned z3_API::query_timeout_core_ab      = AB_QUERY_TIMEOUT * 1000;
	unsigned z3_API::query_timeout_bv           = BV_QUERY_TIMEOUT * 1000;
	unsigned z3_API::query_timeout_core_bv      = BV_QUERY_TIMEOUT * 1000;
#else
	unsigned z3_API::query_timeout_ab           = AB_QUERY_TIMEOUT / 1000;
	unsigned z3_API::query_timeout_core_ab      = AB_QUERY_TIMEOUT / 1000;
	unsigned z3_API::query_timeout_bv           = BV_QUERY_TIMEOUT / 1000;
	unsigned z3_API::query_timeout_core_bv      = BV_QUERY_TIMEOUT / 1000;
#endif

z3_expr_ptr z3_API::m_v0 = NULL;
z3_expr_ptr z3_API::m_v1 = NULL;

z3_expr_ptr z3_API::m_b0 = NULL;
z3_expr_ptr z3_API::m_b1 = NULL;

//solv_expr SolverAPI::m_v0(g_ctx);
//solv_expr SolverAPI::m_v1(g_ctx);
//solv_expr SolverAPI::m_b0(g_ctx);
//solv_expr SolverAPI::m_b1(g_ctx);

list < z3_expr_ptr > z3_API::g_exps;
list < z3_type_ptr > z3_API::g_typs;
list < z3_ftype_ptr > z3_API::g_ftyps;

//static z3::params  m_params(g_ctx);
//static z3::solver  global_solver(g_ctx);
//static z3::model   global_model(global_solver.get_model());


z3_expr& term(z3_expr_ptr y)
{
//	return "";
	return *y;
}

z3_type& type(z3_type_ptr y)
{
//	return "";
	return *y;
}

ostream& operator<<(ostream& out, z3_expr_vec& assertions)
{
	out << endl;
	for (auto& v: assertions)
		out << "\t" << term(v) << endl;
	return out;
}

void z3_API::debug() {

}

SolverType z3_API::fetch_solv_name(void)
{
	return SMT_Z3;
}

void z3_API::z3_exit()
{
	delete_ptrs();
	delete g_param;
	delete g_ctx;
	delete g_config;
}

void z3_API::z3_init()
{
	g_config = new z3::config();
	g_config->set("proof", false);
	g_ctx = new context(*g_config);
	g_param = new params(*g_ctx);

//	g_config->set("verbose", static_cast<int>(999999));
//	g_ctx->set("verbose", static_cast<int>(999999));
//	g_ctx->set("dack", static_cast<int>(0));

#ifndef TEST_Z3
	g_param->set("solver2_timeout", (unsigned) Z3_SOLVER2_TIMEOUT);
	g_param->set("bit2bool", true);
#endif

//	g_config_i = new z3::config();
//	g_config_i->set("proof", false);
//	g_ctx_i = new context(*g_config_i);
//	g_param_i = new params(*g_ctx_i);

#ifndef MICRO_ALARM
	_resFile << "q-to-ab:\t" << AB_QUERY_TIMEOUT << endl;
	_resFile << "q-to-bv:\t" << BV_QUERY_TIMEOUT << endl;
#else
	_resFile << "q-to-ab:\t" << AB_QUERY_TIMEOUT/1000000.0 << endl;
	_resFile << "q-to-bv:\t" << BV_QUERY_TIMEOUT/1000000.0 << endl;
#endif

	_resFile << "z3-soft-q-to-ab-msec:\t" << z3_API::query_timeout_ab << endl;
	_resFile << "z3-soft-q-to-bv-msec:\t" << z3_API::query_timeout_bv << endl;
	_resFile << "z3-soft-q-to-ab-core-msec:\t" << z3_API::query_timeout_core_ab << endl;
	_resFile << "z3-soft-q-to-bv-core-msec:\t" << z3_API::query_timeout_core_bv << endl;

	_resFile << "z3-solver2_timeout-msec:\t" << Z3_SOLVER2_TIMEOUT << endl;

	z3_API::m_v0 = new z3_expr(*g_ctx);
	z3_API::m_v1 = new z3_expr(*g_ctx);
	z3_API::m_b0 = new z3_expr(*g_ctx);
	z3_API::m_b1 = new z3_expr(*g_ctx);
	add_ptr(z3_API::m_v0);
	add_ptr(z3_API::m_v1);
	add_ptr(z3_API::m_b0);
	add_ptr(z3_API::m_b1);

	*(z3_API::m_v0) = g_ctx->bv_val(0, 1);
	*(z3_API::m_v1) = g_ctx->bv_val(1, 1);

	*(z3_API::m_b0) = g_ctx->bool_val(false);
	*(z3_API::m_b1) = g_ctx->bool_val(true);

//	m_params.set("blast_distinct", true);
//	m_params.set("hoist_mul", true);
//	m_params.set("hoist_cmul", true);
//	m_params.set("mul2concat", true);
//	m_params.set("ite_extra_rules", true);
//	m_params.set("ite_extra_rules", true);
//	m_params.set("bv_not_simpl", true);
//	g_param->set("bv_ite2id", true);
//	m_params.set("bv_le_extra", true);
//	m_params.set("cache_all", true);
//	cout << m_params << endl;

//	param_descrs p = param_descrs::simplify_param_descrs(*g_ctx);
//	for (int i = 0; i < p.size(); i++)
//	{
//		cout << p.name(i) << " -> " << p.documentation(p.name(i)) << endl;
//	}
//	exit(1);
}

void z3_API::z3_interrupt(int signum)
{
	if(g_ctx)
	{
		g_ctx->interrupt();
		s_check_timed_out = true;
	}
}

void z3_API::s_change_timeout(unsigned to, z3_solver solver)
{
//	m_param->set("timeout", to);
	solver->set(*m_param);
}

#ifdef TEST_Z3
void z3_API::shift_to_tactic_solver(z3_solver& solv)
{
		delete solv;
		z3_param param_tmp = new z3::params(*g_ctx);

//		param_tmp->set("auto_config", false);
//		param_tmp->set("blast_distinct", true);
//		param_tmp->set("cache_all", true);
//		param_tmp->set("dack.eq", true);
//		param_tmp->set("ite_extra_rules", true);

//		param_tmp->set("pull_cheap_ite", true);
//		param_tmp->set("local_ctx", true);
//		param_tmp->set("local_ctx_limit", (unsigned) 10000000);

//		param_tmp->set("auto_config", true);
//		param_tmp->set("dack", static_cast<unsigned>(2));
//		param_tmp->set("relevancy", static_cast<unsigned>(0));
//		param_tmp->set("restart_strategy", static_cast<unsigned>(0));
//		param_tmp->set("restart_factor", static_cast<double>(1.4));
//		param_tmp->set("mbqi", false);

		z3_param param_tmp1 = new z3::params(*g_ctx);
		z3_param param_tmp2 = new z3::params(*g_ctx);

		*param_tmp1 = *param_tmp;
		*param_tmp2 = *param_tmp;

		param_tmp1->set("random_seed", static_cast<unsigned>(2));
		param_tmp2->set("random_seed", static_cast<unsigned>(9));

//		unsigned rNum = 0;
//		unsigned rNum = rand();
//		param_tmp->set("random_seed", static_cast<unsigned>(rNum));

		try {
			tactic solv_smt [2] = {
									with(tactic(*g_ctx, "smt"), *param_tmp1),
									with(tactic(*g_ctx, "smt"), *param_tmp2)
								  };

			tactic t =
//					tactic(*g_ctx, "simplify") &
//					tactic(*g_ctx, "propagate-values") &
					tactic(*g_ctx, "solve-eqs") &
//					with(tactic(*g_ctx, "simplify"), *param_tmp) &
//					tactic(*g_ctx, "symmetry-reduce") &
					par_or(2, solv_smt);
//					tactic(*g_ctx, "smt");
//					with(tactic(*g_ctx, "smt"), *param_tmp);

			solv = new solver(*g_ctx);
			*solv = t.mk_solver();
		}
		catch (const z3::exception& e) {
			cout << e.msg() << endl;
			assert(0);
		}
		delete param_tmp;
		delete param_tmp1;
		delete param_tmp2;
}
#endif

void z3_API::set_logic(void)
{
	set_logic(m_solver);
	if (m_abstract)
	{
		s_change_timeout(z3_API::query_timeout_ab);

//		param_descrs p = m_solver->get_param_descrs();
//		for (int i = 0; i < p.size(); i++)
//		{
//			cout << p.name(i) << " -> " << p.documentation(p.name(i)) << endl;
//		}
//		assert(0);
	}
	else
	{
		s_change_timeout(z3_API::query_timeout_bv);
//		z3::params s_params = *m_param;
//		s_params.set("relevancy", (unsigned) 0);
//		m_solver->set(s_params);
	}
}

void z3_API::set_logic_core(z3_solver& zsolver, z3_param s_params)
{
	set_logic(zsolver);
	if (m_abstract)
	{
//		s_params->set("timeout", z3_API::query_timeout_core_ab);
	}
	else
	{
//		s_params->set("relevancy", (unsigned) 0);
//		s_params->set("timeout", z3_API::query_timeout_core_bv);
	}
}

void z3_API::set_logic(z3_solver& zsolver)
{
	if (m_abstract)
	{

		if (m_mapper->fetch_logic() == TheoryMapper::QF_UF)
			if (Inst::en_array)
//				zsolver = new solver(*g_ctx);
				zsolver = new solver(*g_ctx, "QF_AUFBV");
			else if (Inst::en_integer)
//				zsolver = new solver(*g_ctx);
				zsolver = new solver(*g_ctx, "QF_UFLIA");
			else
				zsolver = new solver(*g_ctx, "QF_UF");
		else
		{
			assert (m_mapper->fetch_logic() == TheoryMapper::QF_UFBV);
			if (Inst::en_array)
				zsolver = new solver(*g_ctx, "QF_AUFBV");
			else if (Inst::en_integer)
				zsolver = new solver(*g_ctx, "QF_UFBVLIA");
			else
				zsolver = new solver(*g_ctx, "QF_UFBV");
		}
#ifdef TEST_Z3
		shift_to_tactic_solver(zsolver);
#endif
	}
	else
	{
		assert (m_mapper->fetch_logic() == TheoryMapper::QF_BV);
		if (Inst::en_array)
//			zsolver = new solver(*g_ctx, "QF_AUFBV");
			zsolver = new solver(*g_ctx);
		else if (Inst::en_integer)
//			zsolver = new solver(*g_ctx, "QF_BVLIA");
			zsolver = new solver(*g_ctx);
		else
			zsolver = new solver(*g_ctx, "QF_BV");
	}
}

z3_API::z3_API(Solver::TheoryMapper* m, unsigned ba_idx, bool is_inc, int type) :
	Solver(m, ba_idx, type), is_i(is_inc) {

//  cout << "Error: Z3 disabled (for testing)" << endl;
//  assert(0);

	assert(m);

	m_param = new z3::params(*g_param);

	/// Random seed
  unsigned seed = 1;
	if (Config::g_random)
		seed = rand();
	m_param->set("random_seed", seed);

//	/// Automatic conversion of single bit vector to bool
//	m_param->set("bit2bool", false);

//	m_param->set("blast_eq_value", false);

//	m_param->set("auto_config", false);

//	m_param->set("phase_selection", static_cast<unsigned>(4));
//	m_param->set("restart_strategy", static_cast<unsigned>(2));

	AVR_LOG(11, 1, "Creating new Z3 instance for BA[" << m_ba_idx << "] with solver_id [" << m_solver_id << "]" << endl);

	set_logic();
	q_solver = m_solver;

	m_model = new z3::model(*g_ctx, Z3_model());

	m_constraints.clear();

	m_assumptions = new z3_expr_vector(*g_ctx);
	q_assumptions = m_assumptions;

	z3_expr_vec tmp;
	m_cList.push_back(make_pair(m_cList.size() + 1, tmp));

#ifdef ASSERT_DISTINCT_NUMBERS
	if (m_abstract)
	{
		assert_distinct_constants();
	}
#endif

}

z3_API::~z3_API()
{
	AVR_LOG(11, 1, "Deleting Yices instance for BA[" << m_ba_idx << "] with solver_id [" << m_solver_id << "]" << endl);

	m_constraints.clear();

	if (m_model)
		delete m_model;
	if (m_solver)
		delete m_solver;
	if (m_param)
		delete m_param;
	m_cList.clear();

	while(!m_assumptions->empty())
		m_assumptions->pop_back();

	delete m_assumptions;
}

#ifdef ASSERT_DISTINCT_NUMBERS
void z3_API::assert_distinct_constants(z3_solver& solver)
{
	if (m_mapper->fetch_logic() == TheoryMapper::QF_BV)
		return;
  if (Config::g_ab_interpret) {
  	if ((Config::g_ab_interpret_excc >= LEVEL_EXCC_ALL) || (Config::g_ab_interpret_limit == 0))
  		return;
  }

//	cout << "\t(asserting distinct constants)" << endl;

	m_constraints.clear();
	int idx = z3_API::m_distinct_constraints.first;
	if (idx != -1)
	{
		z3_expr_vec& dV = z3_API::m_distinct_constraints.second;
		for (auto& dis_ptr : dV)
		{
			add_constraint(dis_ptr, "forcing distinct constant: ");
//			cout << "SID: " << m_solver_id << "\t" << print_term(dis) << endl;
		}
	}
	else
	{
		z3_expr_vec dV;
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
				z3_expr_vector* yV = new z3_expr_vector(*g_ctx);
				for (auto& e : consts)
				{
					if (e->z3_node.z3_vset[get_vIdx()] == false)
					{
						string name = get_z3_name(e);
						z3_expr_ptr y = create_int_var(name, sz);

						e->z3_node.z3_var[get_vIdx()] = y;
						e->z3_node.z3_vset[get_vIdx()] = true;
						yV->push_back(*y);
					}
					else
					{
						yV->push_back(*(e->z3_node.z3_var[get_vIdx()]));
					}
				}
				unsigned vSz = yV->size();
				if (vSz > 1)
				{
					z3_expr_ptr dis = new z3_expr(*g_ctx);
					add_ptr(dis);
			    try {
	          *dis = distinct(*yV);
			    }
			    catch(z3::exception& e) {
			      cout << e.msg() << endl;
			      assert(0);
			    }
					dV.push_back(dis);
					add_constraint(dis, "forcing distinct constant: ");
//					cout << "SID: " << m_solver_id << "\t" << print_term(dis) << endl;
//					cout << "\t(asserting distinct constants for sz: " << sz << " -> " << term(dis) << ")" << endl;
				}
				delete (yV);
			}
		}
		m_distinct_constraints = make_pair(1, dV);
	}
	if (!m_constraints.empty())
	{
		s_assert_constraints(solver);
	}
}
#endif

string z3_API::get_z3_name(Inst*e)
{
	string prefix = "z$";
	string suffix = "";

	switch(get_vIdx())
	{
	case UFBV_V: suffix = "_ufbv"; break;
	case BV_V:   suffix = "_bv";   break;
	}

	string output = "";

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

//	replace(output.begin(), output.end(), '[', '$');
//	replace(output.begin(), output.end(), ']', '$');
//	replace(output.begin(), output.end(), ':', '_');

	Solver::m_nameToInst[output] = e;
	return output;
}

std::string z3_API::get_z3_temp_name(Inst*e, int count) {
//	return to_string(count);
	return to_string(e->get_id()) + (m_abstract?"":"_bv");
//	return to_string(e->get_id()) + "$" + to_string(count);
}

z3_type_ptr z3_API::create_bv_sort(pair< unsigned, SORT > sz) {
	z3_type_ptr bv;
	z3_IntBvM::iterator it = m_sz_to_bv.find(sz);
	if (it == m_sz_to_bv.end())
	{
		bv = new z3_type(*g_ctx);
		add_ptr(bv);
		if (sz.second.type == bvtype)
			if (sz.first == 1)
				*bv = g_ctx->bool_sort();
			else {
				assert(sz.first > 1);
				*bv = g_ctx->bv_sort(sz.first);
			}
		else if (sz.second.type == arraytype) {
			SORT& d = sz.second.args.front();
			SORT& r = sz.second.args.back();
			*bv = g_ctx->array_sort(type(create_bv_sort(make_pair(d.sz, d))),
															type(create_bv_sort(make_pair(r.sz, r))));
			AVR_LOG(11, 3, "inserting conc var type: " << (*bv) << " (sz = " << sz.first << ", " << sz.second << ")" << endl);
		}
		else if (sz.second.type == inttype)
			*bv = g_ctx->int_sort();
		else {
			AVR_LOG(11, 0, "unsupported sort: " << sz.second.type << endl);
			assert(0);
		}
		m_sz_to_bv.insert(make_pair(sz, bv));
		AVR_LOG(11, 3, "inserting conc var type: " << (*bv) << " (sz = " << sz.first << ", " << sz.second << ")" << endl);
	}
	else
		bv = (*it).second;
	return bv;
}

z3_type_ptr z3_API::create_int_sort(pair< unsigned, SORT > sz)
{
	z3_type_ptr ut;
	z3_IntUtM::iterator it = m_sz_to_ut.find(sz);
	if (it == m_sz_to_ut.end())
	{
		ut = new z3_type(*g_ctx);
		add_ptr(ut);
		if (sz.second.type == bvtype || sz.second.type == inttype) {
			if (sz.first == 1)
				*ut = g_ctx->bool_sort();
			else {
				string typeName = "utt$";
				if (sz.second.type != bvtype) {
					typeName += sz.second.sort2str();
				}
				else {
					typeName += to_string(sz.first);
				}

				char* n = const_cast<char*> (typeName.c_str());
				*ut = g_ctx->uninterpreted_sort(n);
			}
		}
		else if (sz.second.type == arraytype) {
			SORT& d = sz.second.args.front();
			SORT& r = sz.second.args.back();
			*ut = g_ctx->array_sort(type(create_int_sort(make_pair(d.sz, d))),
															type(create_int_sort(make_pair(r.sz, r))));
		}
		else {
			AVR_LOG(11, 0, "unsupported sort: " << sz.second.type << endl);
			assert(0);
		}

		m_sz_to_ut.insert(make_pair(sz, ut));
		AVR_LOG(11, 3, "inserting ut var type: " << (*ut) << " (sz = " << sz.first << ", " << sz.second << ")" << endl);
	}
	else
		ut = (*it).second;
	return ut;
}

z3_expr_ptr z3_API::create_bv_var(std::string name, pair< unsigned, SORT > sz)
{
	z3_expr_ptr d;
	z3_StringToDecl::iterator tit = m_var_decs.find(name);
	if (tit == m_var_decs.end())
	{
		char* n = const_cast<char*> (name.c_str());
		d = new z3_expr(*g_ctx);
		add_ptr(d);
//		if (sz.second.type == arraytype) {
//			z3_type range = g_ctx->bv_sort(sz.second.size);
//			z3_type domain = g_ctx->bv_sort(sz.second.width);
//
//			z3_ftype_ptr funct = new z3_ftype(*g_ctx);
//			add_ptr(funct);
//			*funct = z3::function("array", domain, range);
//			*d = as_array(*funct);
//			AVR_LOG(11, 0, "creating bv var: " << term(d) << " (sz = " << sz.first << ", " << sz.second << ")" << endl);
//		}
//		else {
//		}
		z3_type_ptr bv = create_bv_sort(sz);
		*d = g_ctx->constant(n, type(bv));
		m_var_decs[name] = d;
		AVR_LOG(11, 3, "creating bv var: " << term(d) << " (sz = " << sz.first << ", " << sz.second << ")" << endl);
	}
	else
	{
		d = (*tit).second;
	}
	return d;
}

z3_expr_ptr z3_API::create_int_var(std::string name, pair< unsigned, SORT > sz)
{
	z3_expr_ptr d;
	z3_StringToDecl::iterator tit = m_var_decs.find(name);
	if (tit == m_var_decs.end())
	{
		z3_type_ptr ut = create_int_sort(sz);
		char* n = const_cast<char*> (name.c_str());
		d = new z3_expr(*g_ctx);
		add_ptr(d);
		*d = g_ctx->constant(n, type(ut));
		m_var_decs[name] = d;
		AVR_LOG(11, 3, "creating ut var: " << term(d) << " i.e. " << d << "(sz = " << sz.first << ", " << sz.second << ")" << endl);
	}
	else
	{
		d = (*tit).second;
	}
	return d;
}

z3_expr_ptr z3_API::create_bool_var(std::string name)
{
	z3_expr_ptr d;
	z3_StringToDecl::iterator tit = m_var_decs.find(name);
	if (tit == m_var_decs.end())
	{
		char* n = const_cast<char*> (name.c_str());
		d = new z3_expr(*g_ctx);
		add_ptr(d);
		*d = g_ctx->bool_const(n);
		m_var_decs[name] = d;
		AVR_LOG(11, 3, "creating bool var: " << term(d) << endl);
	}
	else
	{
		d = (*tit).second;
	}
	return d;
}

void z3_API::print_constraints(int loc, int level)
{
#ifndef PERFORMANCE_NOPRINT
	AVR_LOG(loc, level, "\nAssumptions:" << m_assumptions->size() << endl);
	AVR_LOG(loc, level, "\nConstraints:" << endl);

//	cout << get_assumptions() << endl;
//	cout << m_solver->assertions() << endl;
//	return;

	for (auto& cit : m_cList)
	{
		int idx = cit.first;
		AVR_LOG(loc, level, "[" << idx << "]" << endl);
		for (auto& y : cit.second)
		{
			string name = y->to_string();
			if (Solver::m_nameToInst.find(name) != Solver::m_nameToInst.end())
			{
				AVR_LOG(loc, level, name << "\t\t(i.e. " << *(Solver::m_nameToInst[name]) << ")" << endl);
			}
			else
			{
				AVR_LOG(loc, level, term(y) << endl);
			}
		}
		AVR_LOG(loc, level, endl);
	}
	AVR_LOG(loc, level, endl);
#endif
}


void z3_API::print_smt2(string fname, string header)
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

	f << q_solver->to_smt2();

  z3_expr_vector& assumptions = (*q_assumptions);
	if (assumptions && !assumptions.empty())
	{
	  unsigned sz = assumptions.size();
	  for (int i = 0; i < sz; i++)
	    f << "(assert " << assumptions[i] << ")" << endl;
	  f << "(check-sat)" << endl;
  }
	f.close();
}

void z3_API::add_yices_func(z3_expr_ptr& var, string op, bool pred, z3_expr_list& ch, Ints& sz, Inst* e)
{
	assert(m_abstract);

	z3_expr_ptr func;
	pair <Inst*, string> typeKey = make_pair(e, op);
	z3_InstToFuncDecl::iterator tit = m_func_decs.find(typeKey);
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

		z3_ftype_ptr funct;
		z3_StringToFunctM::iterator it = m_funct.find(op);
		if (it == m_funct.end())
		{
			z3_type target = var->get_sort();

//			bool extract = op.find("Extract") != string::npos;

			vector< z3_type > domain;
			{
				for (z3_expr_list::iterator it = ch.begin(), end_it = ch.end(); it != end_it; ++it)
				{
					z3_expr_ptr tmp = *it;
					domain.push_back(tmp->get_sort());
				}
			}
			funct = new z3_ftype(*g_ctx);
			add_ptr(funct);
			*funct = z3::function(op.c_str(), ch.size(), &(domain.front()), target);

			m_funct.insert(make_pair(op, funct));
			AVR_LOG(11, 3, "inserting function template: " << "" << " of type " << *funct << endl);
		}
		else
			funct = (*it).second;

		InstL::const_iterator cit = e->get_children()->begin();
		z3_expr_vector* args = new z3_expr_vector(*g_ctx);
		for (z3_expr_list::iterator it = ch.begin(), end_it = ch.end(); it != end_it; ++it)
		{
			z3_expr_ptr tmp = *it;
			args->push_back(*tmp);
		}
		func = new z3_expr(*g_ctx);
		add_ptr(func);
		z3_ftype& functt = *funct;
		*func = functt(*args);
		delete args;
		m_func_decs[typeKey] = func;
		if (func == Z3_INVALID_EXPR)
		{
			cout << *e << endl;
		}
		assert(func != Z3_INVALID_EXPR);
		AVR_LOG(11, 3, "creating function application: " << term(func) << " of type " << *funct << endl);
	}
	else
	{
		func = (*tit).second;
	}
	if (func == Z3_INVALID_EXPR)
	{
		cout << *e << endl;
	}
	assert(var);
	assert(func);

	if (!allow_flatten) {
		var = func;
	}
	else {
		z3_expr_ptr tmp = new z3_expr(*g_ctx);
		add_ptr(tmp);
		*tmp = (term(var) == term(func));
		if (!tmp)
		{
			cout << "var: " << var << " for " << *e << endl;
			cout << "var sort: " << var->get_sort() << endl;

			cout << "func: " << term(func) << " for " << *e << endl;
			cout << "func sort: " << func->get_sort() << endl;
		}
		assert(tmp);
		add_constraint(tmp, "func link", e);
	}
}

void z3_API::add_constraint(z3_expr_ptr y, string comment, Inst*e, bool storeC)
{
	if (y == Z3_INVALID_EXPR)
	{
		cout << *e << endl;
		cout << e->get_size() << endl;
		cout << m_abstract << endl;
		assert(0);
	}

	if (!(y->is_bool()))
	{
//		assert(y->is_bv());
		cout << "Asserting non-bool" << term(y) << endl;
		if (e)
			cout << *e << endl;
		assert(0);
	}

#ifdef SIMPLIFY_Z3_CONSTRAINTS
//	if (storeC && !m_abstract)
//	if (storeC)
//	if (false)
	{
		z3_expr_ptr yOld = new z3_expr(*g_ctx);
		*yOld = term(y);
		try {
			*y = y->simplify(*m_param);
		}
		catch(z3::exception& e) {
			cout << e.msg() << endl;
			assert(0);
		}

		if (!(y->is_bool()))
		{
			cout << "Asserting non-bool, orig: " << term(yOld) << endl;
			cout << "Asserting non-bool, simp: " << term(y) << endl;
			if (e)
				cout << *e << endl;
			assert(0);
		}
		delete yOld;
	}
#endif

	if (e != 0)
	{
		if (storeC)
		{
//			solv_expr_ptr indVar = e->y_var[m_abstract ? ABSTRACT : CONCRETE];
//			solv_expr_ptr sExpr = new solv_expr(g_ctx);
//			*sExpr = implies(term(indVar), term(y));
//			add_ptr(sExpr);

			m_constraints.push_back(y);

			unsigned cIdx = get_cIdx();
			e->z3_node.z3_constraints[cIdx].push_back(y);
			AVR_LOG(11, 2, "     storing & adding (" << comment << "): " << term(y) << " i.e. " << y << " for " << *e << endl);
		}
		else
		{
			m_constraints.push_back(y);
			AVR_LOG(11, 3, "     adding constraints (" << comment << "): " << term(y) << " i.e. " << y << " for " << *e << endl);
		}
	}
	else
	{
		m_constraints.push_back(y);
		AVR_LOG(11, 3, "     adding constraints (" << comment << "): " << term(y) << " i.e. " << y << endl);
	}
}

bool z3_API::check_sat(Inst* e, long timeout_value, bool getModel)
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
//		yices_assert_formula(g_ctx, *it);
//	}

	AVR_LOG(11, 3, "calling Z3" << endl);
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

void z3_API::force(Inst* e)
{
	if (m_mapper->fetch_var(e) == TheoryMapper::BV_VAR)
	{
		add_constraint(e->z3_node.solv_var(get_vIdx()), "forcing for BOOL", e, false);
	}
	else if (m_mapper->fetch_var(e) == TheoryMapper::BOOL_VAR)
	{
		add_constraint(e->z3_node.solv_var(get_vIdx()), "forcing for BOOL", e, false);
	}
	else if (m_mapper->fetch_var(e) == TheoryMapper::EUF_VAR)
	{
		assert(0);
	}
	else
		assert(0);
}

bool z3_API::s_another_solution(void)
{
	return false;
}

z3_expr_ptr z3_API::force_wo_add(Inst* e)
{
	if (m_mapper->fetch_var(e) == TheoryMapper::BV_VAR)
	{
		return e->z3_node.solv_var(get_vIdx());
	}
	else if (m_mapper->fetch_var(e) == TheoryMapper::BOOL_VAR)
	{
		return e->z3_node.solv_var(get_vIdx());
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

bool z3_API::get_relation(Inst* lhs, Inst* rhs, bool expected)
{
  return true;
}

bool z3_API::get_assignment(Inst*e, int& val)
{
	assert(m_model != NULL);
//	assert(m_abstract);

	z3_expr_ptr decl = e->z3_node.solv_var(get_vIdx());
	assert(decl != Z3_INVALID_EXPR);

	assert(e->get_size() == 1);
//	assert (m_mapper->fetch_var(e) == TheoryMapper::BOOL_VAR);

	val = INVALID_SVAL;
//	z3_expr result = m_model->eval(*decl);
	z3_expr result = m_model->eval(*decl, true);
//	cout << "result: " << *e << " is " << result << endl;

	bool done = false;
//	if (result == *decl) {
//		cout << "Don't care: " << *e << "\t" << m_model->has_interp((*decl).decl()) << endl;
//		result = m_model->eval(*decl, true);
//	}

	if (m_mapper->fetch_var(e) == TheoryMapper::BOOL_VAR) {
		string sval = result.to_string();
		if (sval == "true") {
			e->set_bval(1);
			val = 1;
		}
		else {
			if (sval != "false") {
				assert(0);
			}
			else {
				e->set_bval(0);
				val = 0;
			}
		}
		done = true;
	}
	else if (m_mapper->fetch_var(e) == TheoryMapper::BV_VAR) {
		if (result.is_bool()) {
			string sval = result.to_string();
			if (sval == "true") {
				e->set_bval(1);
				val = 1;
				done = true;
			}
			else {
				if (sval != "false") {
					done = false;
				}
				else {
					e->set_bval(0);
					val = 0;
					done = true;
				}
			}
		}
		else if (result.is_numeral()) {
			string zval = result.get_decimal_string(0);
			if (zval == "1") {
				e->set_bval(1);
				val = 1;
			}
			else {
				if (zval != "0") {
					assert(0);
				}
				else {
					e->set_bval(0);
					val = 0;
				}
			}
			done = true;
		}
	}

	if (!done) {
		Inst* e_new = e->get_port();
		OpInst* op = OpInst::as(e_new);
		if (op) {
			if (op->get_op() == OpInst::Eq || op->get_op() == OpInst::NotEq) {
				Inst* lhs = e_new->get_children()->front();
				Inst* rhs = e_new->get_children()->back();

				bool eq = false;
				if (lhs->get_size() == 1) {
					int valL = lhs->get_bval();
					assert(valL != INVALID_SVAL);

					int valR = rhs->get_bval();
					assert(valR != INVALID_SVAL);

					eq = (valL == valR);
				}
				else {
					mpz_class* valL = lhs->get_ival();
					assert (valL != INVALID_SMPZ);

					mpz_class* valR = rhs->get_ival();
					assert (valR != INVALID_SMPZ);

					eq = (*valL == *valR);
				}
				if (op->get_op() == OpInst::NotEq)
					eq = !eq;

				if (eq) {
					e->set_bval(1);
					val = 1;
				}
				else {
					e->set_bval(0);
					val = 0;
				}
			}
			else if (op->get_op() == OpInst::LogAnd || op->get_op() == OpInst::LogOr || op->get_op() == OpInst::LogNot) {
				for (InstL::const_iterator cit = e_new->get_children()->begin(); cit != e_new->get_children()->end(); cit++) {
					Inst* child = *cit;
					int valL = child->get_bval();
					assert(valL != INVALID_SVAL);
					switch(op->get_op()) {
					case OpInst::LogAnd:
						if (valL == 0) {
							e->set_bval(0);
							val = 0;
						}
						break;
					case OpInst::LogOr:
						if (valL == 1) {
							e->set_bval(1);
							val = 1;
						}
						break;
					case OpInst::LogNot:
						e->set_bval(!valL);
						val = !valL;
						break;
					default:
						assert(0);
					}
				}
				if (val == INVALID_SVAL) {
					if (op->get_op() == OpInst::LogAnd) {
						e->set_bval(1);
						val = 1;
					}
					else if (op->get_op() == OpInst::LogOr) {
						e->set_bval(0);
						val = 0;
					}
					else
						assert(0);
				}
			}
			else {
				cout << "Unexpected model value: " << result << " for " << *e << endl;
				assert(0);
			}
		}
		else {
			cout << "Unexpected model value: " << result << " for " << *e << endl;
			assert(0);
		}
	}

	z3_expr result2 = m_model->eval(*decl);
	AVR_LOG(11, 3, "[VALB] " << *e << "\t" << term(decl) << " (" << decl->get_sort() << ") \t" << val << "\t" << result2 << endl);
	assert(val != INVALID_SVAL);

	{
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
				cout << "expr  : " << *tve << " " << " (aka " << term(decl) << ") " << e->get_bval() << endl;
				cout << "expr  : " << *tve << " " << " (aka " << term(decl) << ") " << val << endl;

				assert(lhs->z3_node.solv_var(get_vIdx()));
				assert(rhs->z3_node.solv_var(get_vIdx()));
				z3_expr& decl_l = *(lhs->z3_node.solv_var(get_vIdx()));
				z3_expr& decl_r = *(rhs->z3_node.solv_var(get_vIdx()));

				if (lhs->get_size() == 1)
				{
					int val_l = lhs->get_bval();
					int val_r = rhs->get_bval();
					assert(val_l != INVALID_SVAL);
					assert(val_r != INVALID_SVAL);
					cout << "lhs  : " << *lhs << " " << " (aka " << (decl_l) << ") " << val_l << endl;
					cout << "rhs  : " << *rhs << " " << " (aka " << (decl_r) << ") " << val_r << endl;
				}
				else
				{
					mpz_class* val_l = lhs->get_ival();
					mpz_class* val_r = rhs->get_ival();
					assert(val_l != INVALID_SMPZ);
					assert(val_r != INVALID_SMPZ);
					cout << "lhs  : " << *lhs << " " << " (aka " << (decl_l) << ") " << *val_l << endl;
					cout << "rhs  : " << *rhs << " " << " (aka " << (decl_r) << ") " << *val_r << endl;
				}
				cout << "SID: " << m_solver_id << " BA: " << m_ba_idx << endl;

//				print_constraints();

				cout << "key: " << Inst::get_rkey() << "  idx: " << Inst::get_bIdx() << endl;
				cout << "model: " << *m_model << endl;
				assert(0);
			}
		}
		else
		{
			if (op && op->get_op() == OpInst::LogNot)
			{
				tve = e->get_children()->front();
				assert(tve->get_size() == 1);

				z3_expr_ptr decl_t = tve->z3_node.solv_var(get_vIdx());
				assert(decl_t);

				int val_t = tve->get_bval();
				if (val_t == INVALID_SVAL)
					return true;

				if (val_t == e->get_bval())
				{
					cout << endl << "Error in (not) in SID: " << m_solver_id << " BA: " << m_ba_idx << endl;
					cout << "expr  : " << *e << " " << " (aka " << term(decl) << ") " << val << endl;
					cout << "!expr : " << *tve << " " << " (aka " << term(decl_t) << ") " << val_t << endl;

					cout << "result: " << result << endl;

//					print_constraints();

					assert(0);
				}
			}
		}
	}
	return true;
}

void z3_API::get_value_bv(unsigned sz, z3_expr_ptr decl, string& sval) {
	assert(sz > 0);
	z3_expr result = m_model->eval(*decl, true);
	if (sz == 1) {
		string val = result.to_string();
		if (val == "true")
			sval = "1";
		else {
			if (val != "false") {
				assert(0);
			}
			else
				sval = "0";
		}
	}
	else {
		string val = result.get_decimal_string(0);
		mpz_class tmp = mpz_class(val, 10);
		sval = tmp.get_str(2);
		while (sval.length() < sz)
			sval = "0" + sval;
	}
//	cout << term(decl) << " of sz " << sz << " to " << sval << endl;
	assert(sval.size() == sz);
}
void z3_API::get_value_int(unsigned sz, z3_expr_ptr decl, string& sval) {
	assert(sz == INT_SZ);
	z3_expr result = m_model->eval(*decl, true);
	sval = result.get_decimal_string(0);
}
void z3_API::get_value_utt(unsigned sz, z3_expr_ptr decl, string& sval) {
	z3_expr result = m_model->eval(*decl,true);
	if (sz == 1) {
		string val = result.to_string();
		if (val == "true")
			sval = "1";
		else {
			if (val != "false") {
				assert(0);
			}
			else
				sval = "0";
		}
	}
	else
		sval = result.to_string();
}
void z3_API::get_value(bool abstract, SORT& sort, z3_expr_ptr decl, string& sval) {
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

#define TRACE_VALUE 0

void z3_API::get_value_arr(bool abstract, SORT& sort, z3_expr_ptr decl, string& sval) {
	assert(sort.type == arraytype);
	assert(sort.args.size() == 2);

	SORT& d = sort.args.front();
	SORT& r = sort.args.back();

	string defstr = "";
	map < string, string > vMap;

	bool isfunc = false;
#if TRACE_VALUE
	cout << "decl top: " << term(decl) << endl;
#endif

	z3_ftype f(*g_ctx);
	z3_expr me(*g_ctx);

	if (decl->is_app()) {
		f = decl->decl();
		if (m_model->has_interp(f)) {
			if (decl->is_const()) {
				me = m_model->get_const_interp(f);
			}
			else {
				isfunc = true;
			}
		}
		else {
			if (Z3_get_decl_kind(*g_ctx, f) == Z3_OP_AS_ARRAY) {
				isfunc = true;
				assert(Z3_get_decl_num_parameters(*g_ctx, f) == 1);
				assert(Z3_get_decl_parameter_kind(*g_ctx, f, 0) == Z3_PARAMETER_FUNC_DECL);
				f = func_decl(*g_ctx, Z3_get_decl_func_decl_parameter(*g_ctx, f, 0));
			}
			else
				me = term(decl);
		}
	}
	else
		me = term(decl);

	if (!isfunc) {
		bool skipDef = false;
		bool negated = false;

#if TRACE_VALUE
		cout << "me top: " << me << endl;
#endif
		while(!me.is_numeral()) {
#if TRACE_VALUE
			cout << "me: " << me << endl;
#endif
			z3_expr address(*g_ctx), value(*g_ctx);
			isfunc = false;

			z3_expr me_old(*g_ctx);
			me_old = me;

			// is_lambda() unavailable in z3 4.7.1
#ifndef Z3_INTERPOLATION
			if (Z3_get_ast_kind(*g_ctx, me) == Z3_QUANTIFIER_AST) {
#else
			if (false) {
#endif
//			cout << "me: is lambda" << endl;
				me = me.body();
				continue;
			}
			else if (me.is_app()) {
				f = me.decl();
				switch(f.decl_kind()) {
				case Z3_OP_ITE: {
#if TRACE_VALUE
					cout << "me: is ite" << endl;
#endif

					if (me.arg(0).decl().decl_kind() != Z3_OP_EQ) {
						cout << me << endl;
					}
					assert(me.arg(0).decl().decl_kind() == Z3_OP_EQ);
					assert(me.arg(0).arg(0).is_var());
					assert(Z3_get_index_value(*g_ctx, me.arg(0).arg(0)) == 0);

					address = me.arg(0).arg(1);
					value = me.arg(1);
					me = me.arg(2);
				} break;
				case Z3_OP_CONST_ARRAY: {
#if TRACE_VALUE
					cout << "me: is constarray" << endl;
#endif
					me = me.arg(0);
					continue;
				} break;
				case Z3_OP_AS_ARRAY: {
#if TRACE_VALUE
					cout << "me: is asarray" << endl;
#endif
					me = m_model->eval(me);
					if (Z3_get_decl_kind(*g_ctx, f) == Z3_OP_AS_ARRAY) {
						isfunc = true;
						assert(Z3_get_decl_num_parameters(*g_ctx, f) == 1);
						assert(Z3_get_decl_parameter_kind(*g_ctx, f, 0) == Z3_PARAMETER_FUNC_DECL);
						f = func_decl(*g_ctx, Z3_get_decl_func_decl_parameter(*g_ctx, f, 0));
				    skipDef = true;
				    break;
					}

					if (me == me_old)
						assert(0);
					continue;
				} break;
				case Z3_OP_STORE: {
#if TRACE_VALUE
					cout << "me: is store" << endl;
#endif
					address = me.arg(1);
					value = me.arg(2);
					me = me.arg(0);
				} break;
				case Z3_OP_NOT: {
#if TRACE_VALUE
					cout << "me: is not" << endl;
#endif
					assert(me.arg(0).is_var());
					assert(Z3_get_index_value(*g_ctx, me.arg(0)) == 0);
					me = me.arg(0);
					negated = true;
					continue;
				} break;
				case Z3_OP_TRUE: {
#if TRACE_VALUE
					cout << "me: is true" << endl;
#endif
					assert(d.type == bvtype);
			    for (int i = pow(2, d.sz) - 1; i >= 0; i--) {
			    	string addrstr = val_to_str(i, d.sz, false);
			    	if (vMap.find(addrstr) == vMap.end()) {
			    		vMap[addrstr] = negated ? "0" : "1";
			    	}
			    }
			    negated = false;
			    defstr = "";
			    skipDef = true;
				} break;
				case Z3_OP_FALSE: {
#if TRACE_VALUE
					cout << "me: is false" << endl;
#endif
					assert(d.type == bvtype);
			    for (int i = pow(2, d.sz) - 1; i >= 0; i--) {
			    	string addrstr = val_to_str(i, d.sz, false);
			    	if (vMap.find(addrstr) == vMap.end()) {
			    		vMap[addrstr] = negated ? "1" : "0";
			    	}
			    }
			    negated = false;
			    defstr = "";
			    skipDef = true;
				} break;
				case Z3_OP_EQ: {
#if TRACE_VALUE
					cout << "me: is eq" << endl;
#endif
					assert(d.type == bvtype);
					assert(r.type == bvtype && r.sz == 1);

					assert(me.arg(0).is_var());
					string rhsstr;
					value = me.arg(1);
					get_value(abstract, d, &value, rhsstr);

					for (int i = 0; i < rhsstr.size(); i++)
						assert(isdigit(rhsstr[i]));

			    for (int i = pow(2, d.sz) - 1; i >= 0; i--) {
			    	string addrstr = val_to_str(i, d.sz, false);
			    	if (vMap.find(addrstr) == vMap.end()) {
			    		vMap[addrstr] = (addrstr == rhsstr) ? (negated ? "0" : "1") : (negated ? "1" : "0");
			    	}
			    }
			    negated = false;
			    defstr = "";
			    skipDef = true;
				} break;
				default:
					cout << "unexpected type: " << me << endl;
					cout << "decl: " << term(decl) << endl;
					cout << "val: " << m_model->eval(term(decl)) << endl;
					assert(0);
				}
				if (skipDef)
					break;
			}
			else if (me.is_var()) {
#if TRACE_VALUE
				cout << "me: is var" << endl;
#endif
				assert(Z3_get_index_value(*g_ctx, me) == 0);
				assert(d.type == bvtype);

		    for (int i = pow(2, d.sz) - 1; i >= 0; i--) {
		    	string addrstr = val_to_str(i, d.sz, false);
		    	if (vMap.find(addrstr) == vMap.end()) {
		    		vMap[addrstr] = val_to_str((negated ? !i : i), r.sz, false);
		    	}
		    }
		    negated = false;
		    defstr = "";
		    skipDef = true;
		    break;
			}
			else {
				cout << "unexpected type: " << me << endl;
				cout << "decl: " << term(decl) << endl;
				cout << "val: " << m_model->eval(term(decl)) << endl;
				assert(0);
			}

//				cout << "address: " << address << endl;
//				cout << "value: " << value << endl;
//				cout << "me: " << me << endl;

			string addrstr;
			get_value(abstract, d, &address, addrstr);

			string valstr;
			get_value(abstract, r, &value, valstr);

			if (vMap.find(addrstr) == vMap.end())
				vMap[addrstr] = valstr;
//				cout << "storing: " << addrstr << " -> " << valstr << endl;
			assert(me != me_old);
		}
		if (!skipDef && defstr == "") {
			 assert(me.is_numeral());
			 get_value(abstract, r, &me, defstr);
		}
	}
	if (isfunc) {
#if TRACE_VALUE
		cout << "f top: " << f << endl;
#endif
		if (Z3_get_decl_kind(*g_ctx, f) == Z3_OP_UNINTERPRETED) {
			defstr = "?";
		}
		else {
			z3_func_interp m = m_model->get_func_interp(f);
			assert(m != NULL);

			for (int i = 0; i < m.num_entries(); i++) {
				z3_expr address = m.entry(i).arg(0);

				string addrstr;
				get_value(abstract, d, &address, addrstr);

				z3_expr valbv = m.entry(i).value();
				string valstr;
				get_value(abstract, r, &valbv, valstr);

				if (vMap.find(addrstr) == vMap.end())
					vMap[addrstr] = valstr;
	//			cout << addrstr << " -> " << valstr << endl;
			}
			if (defstr == "") {
				z3_expr defvalue = m.else_value();
				if (defvalue.is_numeral())
					get_value(abstract, r, &defvalue, defstr);
				else if (defvalue.is_var()) {
					assert(Z3_get_index_value(*g_ctx, defvalue) == 0);
					assert(r.type == bvtype);
					for (int i = pow(2, d.sz) - 1; i >= 0; i--) {
						string addrstr = val_to_str(i, d.sz, false);
						if (vMap.find(addrstr) == vMap.end()) {
							vMap[addrstr] = addrstr;
	//						cout << addrstr << " -> " << addrstr << endl;
						}
					}
				}
			}
		}
	}

#if TRACE_VALUE
	cout << term(decl) << " has value: \n\t(default: " << defstr << ")" << endl;
	for (auto& v: vMap)
		cout << "\t" << v.first << " -> " << v.second << endl;
#endif

//	if (false && !abstract && d.type == bvtype) {
	if (!abstract && d.type == bvtype && r.type == bvtype) {
		sval = "";
		bool isuninterpreted = false;
		for (int i = pow(2, d.sz) - 1; i >= 0; i--) {
			map < string, string >::iterator mit = vMap.find(val_to_str(i, d.sz, false));
			if (mit != vMap.end()) {
				sval += (*mit).second;
				if (!isdigit((*mit).second[0]))
					isuninterpreted = true;
			}
			else {
				sval += defstr;
				if (!isdigit(defstr[0]))
					isuninterpreted = true;
			}
		}
		if (isuninterpreted)
			sval = "a?" + sval;
	}
	else {
		sval = "a" + defstr + "b";
		for (auto& v: vMap)
			sval += v.first + "c" + v.second + "d";
	}
  assert(sval != "");

//  assert(0);
}

bool z3_API::get_assignment(Inst*e, mpz_class* val)
{
	assert(m_model != NULL);

//	assert(m_abstract);
	z3_expr_ptr decl = e->z3_node.solv_var(get_vIdx());
	assert(decl != Z3_INVALID_EXPR);

	assert(e->get_size() != 1);

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
	    SORT sort = e->get_sort();
//			cout << *e << " getting bv array value" << endl;
	    get_value_arr(false, sort, decl, sval);
//			cout << *e << " bv has value: " << sval << endl;
//			assert(0);
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
	    SORT sort = e->get_sort();
			cout << *e << " getting ab array value" << endl;
	    get_value_arr(true, sort, decl, sval);
			cout << *e << " ab has value: " << sval << endl;
			assert(0);
		}
		else {
			assert(0);
		}
  }

	auto mit = solv_values.find(sval);
	mpz_class* pval = INVALID_SMPZ;
	if (mit != solv_values.end())
		pval = &(*mit).second;
	else
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
    	}
		}
		else
		{
			int dval = solv_values.size() + 2;
			dval *= -1;
			zval = mpz_class(dval);
		}
		solv_values.insert(make_pair(sval, zval));
		AVR_LOG(11, 1, "inserting ut value: " << sval << " with key " << zval << endl);

	  mit = solv_values.find(sval);
	  assert (mit != solv_values.end());
    pval = &(*mit).second;
	}

	e->set_ival(pval);
	val = pval;

//	if (Inst::get_rkey() == 13)
	z3_expr result2 = m_model->eval(*decl);
  AVR_LOG(11, 3, "[VALE] " << *e << "\t" << term(decl) << " (" << decl->get_sort() << ") \t" << *pval << "\t" << sval << "\t" << result2 << endl);

//	if (e->get_sort_type() == arraytype)
//		AVR_LOG(11, 0, "[VALE] " << *e << "\t" << sval << "\t" << *pval << endl);

//	if (e->get_type() == Op && OpInst::as(e)->get_op() == OpInst::Ternary) {
//		InstL::const_iterator it = e->get_children()->begin();
//		Inst* cond = (*it);
//		it++;
//		Inst* the = (*it);
//		it++;
//		Inst* els = (*it);
//
//		if (cond->get_bval() == 1) {
//			if (*e->get_ival() != *the->get_ival()) {
//				cout << *e << " has incorrect value: " << *e->get_ival() << endl;
//				for (auto& v: e->z3_node.z3_constraints[get_cIdx()])
//					cout << "\t" << term(v) << endl;
//
//				cout << "cond: " << *cond << " has value: " << cond->get_bval() << endl;
//				for (auto& v: cond->z3_node.z3_constraints[get_cIdx()])
//					cout << "\t" << term(v) << endl;
//
//				cout << "the: " << *the << " has value: " << *the->get_ival() << endl;
//				for (auto& v: the->z3_node.z3_constraints[get_cIdx()])
//					cout << "\t" << term(v) << endl;
//
//				cout << "els: " << *els << " has value: " << *els->get_ival() << endl;
//				for (auto& v: els->z3_node.z3_constraints[get_cIdx()])
//					cout << "\t" << term(v) << endl;
//
//				cout << endl;
//				print_query(0, ERROR, "error");
//				cout << endl;
//				cout << m_solver->assertions() << endl;
//				cout << *m_model << endl;
//				assert(0);
//			}
//		}
//		else {
//			if (*e->get_ival() != *els->get_ival()) {
//				cout << *e << " has incorrect value: " << *e->get_ival() << endl;
//				cout << "cond: " << *cond << " has value: " << cond->get_bval() << endl;
//				cout << "the: " << *the << " has value: " << *the->get_ival() << endl;
//				cout << "els: " << *els << " has value: " << *els->get_ival() << endl;
//				assert(0);
//			}
//		}
//	}

	return true;
}

// if check_containment returns "true", termination condition is met, i.e. "Property holds"
//TODO force_wo_add
//TODO remove the use of function pointer
int z3_API::forward_propagation(long timeout_value, int frame_idx, InstL& forwarded,
		vector<vector<CLAUSE>>& cubes, void *inst) {
	//clock_t ref_time = clock();
	int next_frame_idx = frame_idx + 1;
	num_scalls_sat_fp_non_accum = 0;
	num_scalls_unsat_fp_non_accum = 0;
	num_scalls_contained_fp_non_accum = 0;

	long timeout_value_original = timeout_value;

	vector<CLAUSE>::iterator it_c = cubes[frame_idx].begin();
	while (it_c != cubes[frame_idx].end())
	{
//				cout << "FP: " << *(*it_c) << endl;
		Inst* cube = (*it_c).cube;
		Inst *ve_next_c = Inst::all_pre2next(cube);

		InstL conjunct_query;
		InstS relevantNext;
		Inst::collect_next_reg(ve_next_c, relevantNext, true);
		for (auto& sigNext : relevantNext)
		{
			conjunct_query.push_back(Inst::fetch_trelation(sigNext));
		}

		conjunct_query.push_back(ve_next_c);
		s_assert_retractable(conjunct_query);
		int res = s_check_assume(AB_QUERY_TIMEOUT, false);
		s_retract_assertions();

//		InstL conjunct_dest;
//		conjunct_dest.push_back(ve_next_c);
//		s_assert_retractable(conjunct_dest);
//		int res = s_check(AB_QUERY_TIMEOUT);
//		s_retract_assertions();

//		if (res == AVR_QSAT)
//		{
//			solv_result os_res = s_check_oneshot(AB_QUERY_TIMEOUT);
//			assert(os_res == z3::sat);
//		}

//		if (res == z3::sat)
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

/// Obsolete
/// Identifying don't cares using solver
//int SolverAPI::identify_dont_cares(long timeout_value, InstL& mus, int& numSat, int& numUnsat)
//{
//	int level = 5;
//
//	AVR_LOG(17, level, "\tEntering identify don't cares using Z3" << endl);
//	AVR_LOG(17, level, "\t[Input]: " << mus << endl);
//	assert(!mus.empty());
//
//	int res;
//
//	/// Create non-incremental solver
//
//	solv_solver ni_solver;
//	z3::params s_params = *m_param;
//	s_params.set("core.minimize", true);
//	bool minimizedCore = true;
////	bool minimizedCore = false;
//
//	if (m_abstract)
//	{
//		ni_solver = new solver(*g_ctx, "QF_UFBV");
//		s_params.set("timeout", SolverAPI::query_timeout_core_ab);
//	}
//	else
//	{
//		ni_solver = new solver(*g_ctx, "QF_BV");
//		s_params.set("relevancy", (unsigned) 0);
//		s_params.set("timeout", SolverAPI::query_timeout_core_bv);
//	}
//	ni_solver->set(s_params);
//
//	int count = 0;
//	map<string, pair <Inst*, bool> > indVar2exprFull;
//	solv_expr_vector assumptions(*g_ctx);
//
//	for (auto& v: mus)
//	{
//		Inst::init_visit2();
//		singleInst2yices(ni_solver, v, count, indVar2exprFull, assumptions, true);
//	}
//
//	if (assumptions.empty())
//		return AVR_QUSAT;
//
////#ifdef DO_CORRECTNESS_CHECKS
//	int pre_initial_res = s_check_inc(ni_solver, timeout_value);
//	AVR_LOG(17, level, "\t\t(pre-initial-check) " << pre_initial_res << endl);
//	if (pre_initial_res == AVR_QUSAT)
//	{
//		numUnsat++;
//
//		for (auto& m: indVar2exprFull)
//		{
//			m.second.first->set_dcVal(true);
//		}
//
//		return AVR_QUSAT;
//	}
//	assert (pre_initial_res == AVR_QSAT);
//	numSat++;
////#endif
//
//	solv_result initial_res = s_check_mus(ni_solver, timeout_value, assumptions);
//	AVR_LOG(17, level, "\t\t(total-check) " << initial_res << endl);
//
//	if (initial_res == z3::unsat)
//	{
//		solv_expr_vector uCore = ni_solver->unsat_core();
//		unsigned uSz = uCore.size();
//		AVR_LOG(17, level, "\t\t(core, sz: " << uSz << ")" << uCore << endl);
//		assert(uSz > 0);
//		collect_stats_mus(uSz);
//
//		for (int i = 0; i < uSz; i++)
//		{
//			string iName = uCore[i].to_string();
//			map<string, pair <Inst*, bool> >::iterator mit = indVar2exprFull.find(iName);
//			assert(mit != indVar2exprFull.end());
//
//			Inst* tve = (*mit).second.first;
//			assert(tve);
//			(*mit).second.second = false;
//			AVR_LOG(17, level, "\t\t\t\t" << i << " " << uCore[i] << endl);
//		}
//
//		for (auto& m: indVar2exprFull)
//		{
//			m.second.first->set_dcVal(m.second.second);
//		}
//
//		if (uSz < count)
//		{
//			AVR_LOG(17, 0, "\t\t\t\t(" << count << " -> " << uSz << ")" << endl);
////			assert(0);
//		}
//		res = AVR_QUSAT;
//
////		while(!stack.empty())
////		{
////			solv_expr_ptr curr = new solv_expr(*g_ctx);
////			*curr = stack.back();
////			stack.pop_back();
////			AVR_LOG(17, 6, "\t\t(deleting " << term(curr) << ", stack: " << stack.size() << ")" << endl);
////			AVR_LOG(17, 7, "\t\tstack: " << stack << endl);
////
////			solv_result result;
////			if (!minimizedCore)
////			{
////				if (stack.empty())
////					result = s_check_inc(ni_solver, timeout_value);
////				else
////					result = s_check_mus(ni_solver, timeout_value, stack);
////			}
////			else
////			{
////				result = z3::sat;
////			}
////
////			AVR_LOG(17, 6, "\t\t(result) " << result << endl);
////
////			if (result == z3::unsat)
////			{
////				numUnsat++;
////			}
////			else if (result == z3::sat)
////			{
////				numSat++;
////				Inst *tve = indVar2inst[curr->to_string()];
////				assert(tve);
////				mus.push_back(tve);
////				s_assert_constraint_mus(ni_solver, curr);
////				AVR_LOG(17, 5, "\t\t(adding to mus) " << *tve << endl);
////			}
////			else
////			{
////				AVR_LOG(17, 5, "\t\t(clearing mus)" << endl);
////				mus.clear();
////				delete curr;
////				break;
////			}
////			delete curr;
////		}
//
////		if (mus.empty())
////		{
////			AVR_LOG(17, 6, "\t\t(mus empty)" << endl);
////			res = AVR_QTO;//the given formula is UNDEF
////		}
////		else
////		{
////			res = 1;
////		}
//	}
//	else if (initial_res == z3::sat)
//	{
////		cout << "mus: " << mus << endl;
//		res = AVR_QSAT;
//		*m_model = ni_solver->get_model();
//		s_print_model();
//		string fname = "error/" + _benchmark;
//		print_smt2(fname, -1, ni_solver);
//	}
//	else
//	{
//		res = AVR_QTO;//the given formula is UNDEF
//		*m_model = ni_solver->get_model();
//		s_print_model();
//		string fname = "error/" + _benchmark;
//		print_smt2(fname, -1, ni_solver);
//	}
//	delete ni_solver;
//	return res;
//}

int z3_API::check_half(int start, int size, std::unordered_map<string, string>& indVarHash, long timeout_value, z3_solver& ni_solver, vector < pair <Inst*, string> >& instCore, int& numSat, int& numUnsat, bool recordTime)
{
  struct rusage usage;
  struct timeval start_time, end_time;
  long long time_diff;
  long long time_res = 0;

	int res;

	assert(start >= 0);
	assert((start + size) <= instCore.size());

//	s_push(ni_solver);
	z3_expr_vector assumptions(*g_ctx);

	list< z3_expr_ptr > garbageList;
	for (int i = 0; i < size; i++)
	{
		Inst* inst = instCore[start + i].first;
		string iName = instCore[start + i].second;
		iName = indVarHash[iName];
		z3_expr_ptr indVar = new z3_expr(*g_ctx);
		*indVar = g_ctx->bool_const(iName.c_str());
		AVR_LOG(17, 5, "\t\t\t(inst: " << *inst << ", indicator: " << term(indVar) << ")" << endl);
//		s_assert_constraint(ni_solver, indVar);
//		garbageList.push_back(indVar);
		assumptions.push_back(term(indVar));
		add_assume(inst);
		delete indVar;
	}

  TIME_S(start_time);
	z3_result resSolv = s_check_mus(ni_solver, timeout_value, assumptions, false);
  TIME_E(start_time, end_time, time_res);
	clear_assume();

//	solv_result resSolv = s_check_oneshot(ni_solver, timeout_value);
//	solv_result resSolv = s_check_inc(ni_solver, timeout_value);
//	s_pop(ni_solver);

	if (resSolv == z3::unsat)
	{
		numUnsat++;
    if (recordTime)
    {
      time_unsat_min_muses_reach += time_diff;
      if (time_diff > time_max_unsat_min_muses_reach)
        time_max_unsat_min_muses_reach = time_diff;
    }

		int count = 0;
		for (vector < pair <Inst*, string> >::iterator vit = instCore.begin(); vit != instCore.end();)
		{
			if (count < start || count >= (start + size))
				vit = instCore.erase(vit);
			else
				vit++;

			count ++;
		}
		res = AVR_QUSAT;
	}
	else if (resSolv == z3::sat)
	{
		numSat++;
    if (recordTime)
    {
      time_sat_min_muses_reach += time_diff;
      if (time_diff > time_max_sat_min_muses_reach)
        time_max_sat_min_muses_reach = time_diff;
    }
		res = AVR_QSAT;
	}
	else
	{
		res = AVR_QTO;//the given formula is UNDEF
	}
	for (auto& ptr: garbageList)
		if (ptr)
			delete ptr;
	return res;
}

int z3_API::check_linear(std::unordered_map<string, string>& indVarHash, long timeout_value, z3_solver& ni_solver, vector < pair <Inst*, string> >& instCore, int& numSat, int& numUnsat, bool recordTime)
{
  struct rusage usage;
  struct timeval start_time, end_time;
  long long time_diff;
  long long time_res = 0;

	int res;
	z3_expr_vector assumptions(*g_ctx);
	std::unordered_map<string, Inst*> indVarToInst;
	vector < z3_expr_ptr> stack;
	list< z3_expr_ptr > garbageList;
	for (int i = 0; i < instCore.size(); i++)
	{
		Inst* inst = instCore[i].first;
		string iName = instCore[i].second;
		iName = indVarHash[iName];
		z3_expr_ptr indVar = new z3_expr(*g_ctx);
		*indVar = g_ctx->bool_const(iName.c_str());
		AVR_LOG(17, 5, "\t\t\t(inst: " << *inst << ", indicator: " << term(indVar) << ")" << endl);
		assumptions.push_back(term(indVar));
		indVarToInst[iName] = inst;
		add_assume(inst);
		stack.push_back(indVar);
		garbageList.push_back(indVar);
	}

	set<string> coreSet;

	bool timedOut = false;
	vector < z3_expr_ptr > satBucket;
	while(!stack.empty())
	{
		z3_expr_ptr curr = stack.back();
		stack.pop_back();
		assumptions.pop_back();
		Inst* currInst = m_asserts.assumptions.back();
		pop_assume();

		AVR_LOG(17, 6, "stack: " << stack << endl);

		z3_result result;

		int count = 0;
		for (auto& s: satBucket) {
			assumptions.push_back(term(s));
			count++;
		}

    TIME_S(start_time);
		if (!assumptions.empty())
			result = s_check_mus(ni_solver, timeout_value, assumptions, false);
		else
			result = z3::sat;
    TIME_E(start_time, end_time, time_res);

		for (int i = 0; i < count; i++)
			assumptions.pop_back();

		if (result == z3::unsat)
		{
			numUnsat++;
      if (recordTime)
      {
        time_unsat_min_muses_reach += time_diff;
        if (time_diff > time_max_unsat_min_muses_reach)
          time_max_unsat_min_muses_reach = time_diff;
      }
		}
		else if (result == z3::sat)
		{
			numSat++;
      if (recordTime)
      {
        time_sat_min_muses_reach += time_diff;
        if (time_diff > time_max_sat_min_muses_reach)
          time_max_sat_min_muses_reach = time_diff;
      }
			coreSet.insert(curr->to_string());
			satBucket.push_back(curr);
			add_assume_front(currInst);
		}
		else
		{
			coreSet.insert(curr->to_string());
			for (auto& c: stack)
				coreSet.insert(c->to_string());
			timedOut = true;
			break;
		}
	}

	for (auto& ptr: garbageList)
		if (ptr)
			delete ptr;

	for (vector < pair <Inst*, string> >::iterator vit = instCore.begin(); vit != instCore.end();)
	{
		if (coreSet.find((*vit).second) == coreSet.end())
			vit = instCore.erase(vit);
		else
			vit++;
	}

	if (timedOut)
		res = AVR_QTO;
	else
		res = AVR_QUSAT;

	clear_assume();
	return res;
}


z3_result z3_API::find_mus(std::unordered_map<string, string>& indVarHash, long timeout_value, z3_solver& ni_solver, vector < pair <Inst*, string> >& instCore, InstL& mus, int& numSat, int& numUnsat, bool recordTime)
{
//	cout << "Core: " << endl;
//	for (int i = 0; i < instCore.size(); i++)
//		cout << "\t[" << i << "]\t" << *(instCore[i].first) << endl;

//	std::sort(instCore.begin(), instCore.end(), CompareCoreByChildInfo);
//	if (instCore.size() > 5)
//	{
//		int lhs = instCore.size() / 2;
//		int rhs = instCore.size() - lhs;
//
////		cout << "lhs: " << lhs << endl;
////		cout << "rhs: " << rhs << endl;
//
//		cout << "\t(mus: " << instCore.size() << " -> " << lhs << " ? ";
//		int resL = check_half(0, lhs, indVarHash, timeout_value, ni_solver, instCore, numSat, numUnsat);
//		cout << (resL == AVR_QUSAT ? "s)" : "f)") << endl;
//		if (resL == AVR_QUSAT)
//		{
//			if (instCore.size() == 1)
//			{
//				mus.push_back(instCore.front().first);
//				return z3::unsat;
//			}
//			else
//				return find_mus(indVarHash, timeout_value, ni_solver, instCore, mus, numSat, numUnsat);
//		}
//
//		cout << "\t(mus: " << instCore.size() << " -> " << rhs << " ? ";
//		int resR = check_half(lhs, rhs, indVarHash, timeout_value, ni_solver, instCore, numSat, numUnsat);
//		cout << (resR == AVR_QUSAT ? "s)" : "f)") << endl;
//		if (resR == AVR_QUSAT)
//		{
//			if (instCore.size() == 1)
//			{
//				mus.push_back(instCore.front().first);
//				return z3::unsat;
//			}
//			else
//				return find_mus(indVarHash, timeout_value, ni_solver, instCore, mus, numSat, numUnsat);
//		}
//	}

	cout << "\t(mus: l " << instCore.size() << " -> ";
	int resLi = check_linear(indVarHash, timeout_value, ni_solver, instCore, numSat, numUnsat, recordTime);
	if (resLi == AVR_QUSAT)
	{
		cout << instCore.size() << ")" << endl;
		assert(resLi == AVR_QUSAT);
		for (auto& i: instCore)
		{
//			cout << *i.first << endl;
			mus.push_back(i.first);
		}
		return z3::unsat;
	}
	else if (resLi == AVR_QSAT)
	{
		cout << "sat)" << endl;
		return z3::sat;
	}
	else
	{
		cout << "TO)" << endl;
		return z3::unknown;
	}
}

/// MUS extraction by using z3 unsat_core
int z3_API::get_mus(long timeout_value, InstL& vel, InstL& mus, int& numSat, int& numUnsat, bool recordTime)
{
  struct rusage usage;
  struct timeval start_time, end_time;
  long long time_diff;
  long long time_res = 0;

	unsigned sz = vel.size();
	AVR_LOG(17, 5, "\tEntering MUS core extraction from Z3" << endl);
	AVR_LOG(17, 5, "\t[Input]: " << vel << " (sz: " << sz << ")" << endl);
	assert(!vel.empty());

	int res;

	/// Create non-incremental solver

	z3_solver ni_solver;
	z3::params s_params = *m_param;
	s_params.set("unsat_core", true);
	if (m_abstract)
	  s_params.set("core.minimize", true);

	set_logic_core(ni_solver, &s_params);
	q_solver = ni_solver;

//	s_params.set("auto_config", false);
//	s_params.set("elim_vars", false);
//	s_params.set("resolution", false);
//	s_params.set("scc", false);

	q_solver->set(s_params);

	m_query_sz = 0;
	/// Add all assertions from m_cList
	for (auto& v: m_cList)
	{
		for (auto& c: v.second)
		{
			q_solver->add(term(c));
		}
		m_query_sz += v.second.size();
	}

	int count = 0;
	unordered_map<string, Inst*> indVar2instFull;
	unordered_map<string, string> indVarHash;
	z3_expr_vector assumptions(*g_ctx);
	for (InstL::iterator it = vel.begin(); it != vel.end(); it++)
	{
		Inst* tve = *it;
		init_inst2yices();
		inst2yices(tve);
		force(tve);
		add_assume(tve);

		string iName = "_q_$" + get_z3_temp_name(tve, count);
		z3_expr_ptr indVar = new z3_expr(*g_ctx);
		*indVar = g_ctx->bool_const(iName.c_str());
		AVR_LOG(17, 5, "\t\t\t(inst: " << *(*it) << ", indicator: " << term(indVar) << ")" << endl);
		if (!m_constraints.empty())
		{
			AVR_LOG(17, 7, "\t\t\t\t(assertions " << term(indVar) << " => " << m_constraints << endl);
			s_assert_constraints_mus(q_solver, indVar);
		}
		string iNameZ3 = indVar->to_string();
		assumptions.push_back(term(indVar));
		indVar2instFull[iNameZ3] = (*it);
		indVarHash[iNameZ3] = iName;
		count++;
		delete indVar;
	}

#ifdef DO_CORRECTNESS_CHECKS
	int pre_initial_res = s_check(timeout_value);
	AVR_LOG(17, 6, "\t\t(pre-initial-check) " << pre_initial_res << endl);
	assert(pre_initial_res == AVR_QSAT);
	numSat++;
#endif

  TIME_S(start_time);
	z3_result initial_res = s_check_mus(q_solver, timeout_value, assumptions, false);
  TIME_E(start_time, end_time, time_res);
	clear_assume();
	AVR_LOG(17, 5, "\t\t(total-check) " << initial_res << endl);

	if (initial_res == z3::unsat)
	{
		numUnsat++;
    if (recordTime)
    {
      time_unsat_min_muses_reach += time_diff;
      if (time_diff > time_max_unsat_min_muses_reach)
        time_max_unsat_min_muses_reach = time_diff;
    }

		z3_expr_vector uCore = q_solver->unsat_core();
		unsigned uSz = uCore.size();
		AVR_LOG(17, 4, "\t\t(core, sz: " << uSz << ")" << uCore << endl);
		assert(uSz > 0);
		collect_stats_mus(uSz);

		vector < pair <Inst*, string> > instCore;

		for (int i = 0; i < uSz; i++)
		{
			string iName = uCore[i].to_string();
			Inst* tve = indVar2instFull[iName];
			assert(tve);
			instCore.push_back(make_pair(tve, iName));
		}

//		for (auto& i: instCore)
//			mus.push_back(i.first);
//		solv_result mus_res = z3::unsat;

		z3_result mus_res = find_mus(indVarHash, timeout_value, q_solver, instCore, mus, numSat, numUnsat, recordTime);
		if (mus_res == z3::unknown)
		{
			InstL instCoreList;
			for (auto& i: instCore)
				instCoreList.push_back(i.first);

			cout << "\t(mus: l " << instCoreList.size() << " -> ";
			int resAlt = get_mus_avr(timeout_value, instCoreList, mus, numSat, numUnsat, recordTime);
			assert(resAlt == 1);
			assert(!mus.empty());
			cout << mus.size() << ")";
		}
		else
			assert(mus_res == z3::unsat);

		if (mus.empty())
		{
			AVR_LOG(17, 6, "\t\t(mus empty)" << endl);
			res = AVR_QTO;//the given formula is UNDEF
		}
		else
		{
			res = AVR_QUSAT;
		}
	}
	else if (initial_res == z3::sat)
	{
		numSat++;
    if (recordTime)
    {
      time_sat_min_muses_reach += time_diff;
      if (time_diff > time_max_sat_min_muses_reach)
        time_max_sat_min_muses_reach = time_diff;
    }
		res = AVR_QSAT;//the given formula is SAT, i.e. there's no MUS
	}
	else
	{
		res = AVR_QTO;//the given formula is UNDEF
	}
	delete q_solver;
	q_solver = m_solver;

	return res;
}

/// MUS extraction by using complete set as unsat_core
int z3_API::get_mus_avr(long timeout_value, InstL& vel, InstL& mus, int& numSat, int& numUnsat, bool recordTime)
{
  struct rusage usage;
  struct timeval start_time, end_time;
  long long time_diff;
  long long time_res = 0;

	bool fastMode = true;

	unsigned sz = vel.size();
	AVR_LOG(17, 4, "\tEntering avr core extraction " << endl);
	AVR_LOG(17, 4, "\t[Input]: " << vel << " (sz: " << sz << ")" << endl);
	assert(sz > 0);

	int res;

	/// Switch to separate solver
	z3_solver inc_solver;
	z3::params s_params = *m_param;
//	s_params.set("core.minimize", true);
//	bool minimizedCore = true;

	set_logic_core(inc_solver, &s_params);
	q_solver = inc_solver;

	q_solver->set(s_params);

	m_query_sz = 0;
	/// Add all assertions from m_cList
	for (auto& v: m_cList)
	{
		for (auto& c: v.second)
		{
			q_solver->add(term(c));
		}
		m_query_sz += v.second.size();
	}

	map<string, pair< Inst*, z3_expr_vec > > indVar2inst;
	list< z3_expr_ptr > garbageList;
	vector < z3_expr_ptr > stack;
	int count = 0;

	s_push(q_solver, true);

	unordered_map<string, string> indVarHash;
	vector < pair <Inst*, string> > instCore;
	for (InstL::iterator it = vel.begin(); it != vel.end(); it++)
	{
		Inst* tve = *it;
		init_inst2yices();
		inst2yices(tve);
		force(tve);

		string iName = "_q_$" + get_z3_temp_name(tve, count);
		z3_expr_ptr indVar = new z3_expr(*g_ctx);
		*indVar = g_ctx->bool_const(iName.c_str());

		AVR_LOG(17, 5, "\t\t\t(inst: " << *(*it) << ", indicator: " << term(indVar) << ")" << endl);
		if (!m_constraints.empty())
		{
			AVR_LOG(17, 7, "\t\t\t\t(assertions " << term(indVar) << " => " << m_constraints << endl);
		}

		string iNameZ3 = indVar->to_string();
		if(fastMode)
		{
			indVarHash[iNameZ3] = iName;
			instCore.push_back(make_pair(tve, iNameZ3));
		}

		stack.push_back(indVar);
		indVar2inst[iNameZ3] = make_pair((*it), m_constraints);

		s_assert_constraints(q_solver, true, indVar);
		garbageList.push_back(indVar);
		count++;
	}

#ifdef DO_CORRECTNESS_CHECKS
	int pre_initial_res = s_check_inc(q_solver, timeout_value);
	if (pre_initial_res != AVR_QSAT)
	{
		cout << "pre-initial res: " << pre_initial_res << endl;
	}
	assert(pre_initial_res == AVR_QSAT);
	numSat++;
#endif


	z3_result initial_res;

	if(fastMode)
	{
		initial_res = find_mus(indVarHash, timeout_value, q_solver, instCore, mus, numSat, numUnsat, recordTime);
	}

	if (!fastMode || (initial_res == z3::unknown))
	{
		s_push(q_solver);
		s_assert_constraints_inc(q_solver, stack);
		for (auto& tve: vel)
			add_assert(tve);

    TIME_S(start_time);
		initial_res = s_check_inc(q_solver, timeout_value, false);
    TIME_E(start_time, end_time, time_res);
		s_pop(q_solver);

		if (initial_res == z3::unsat)
		{
			collect_stats_mus(sz);
      if (recordTime)
      {
        time_unsat_min_muses_reach += time_diff;
        if (time_diff > time_max_unsat_min_muses_reach)
          time_max_unsat_min_muses_reach = time_diff;
      }
	//#ifdef DO_CORRECTNESS_CHECKS
	//		SolvAPIBAV tmp;
	//		m_cList.push_back(make_pair(m_cList.size() + 1, tmp));
	//#endif
			while(!stack.empty())
			{
				z3_expr_ptr curr = stack.back();
				stack.pop_back();

				AVR_LOG(17, 6, "stack: " << stack << endl);

				z3_result result;
				s_push(q_solver);
				s_assert_constraints_inc(q_solver, stack);
				for (auto& indVar: stack)
					add_assert(indVar2inst[indVar->to_string()].first);

	      TIME_S(start_time);
				result = s_check_inc(q_solver, timeout_value, false);
	      TIME_E(start_time, end_time, time_res);
				s_pop(q_solver);

				if (result == z3::unsat)
				{
					numUnsat++;
	        if (recordTime)
	        {
	          time_unsat_min_muses_reach += time_diff;
	          if (time_diff > time_max_unsat_min_muses_reach)
	            time_max_unsat_min_muses_reach = time_diff;
	        }
				}
				else if (result == z3::sat)
				{
					numSat++;
	        if (recordTime)
	        {
	          time_sat_min_muses_reach += time_diff;
	          if (time_diff > time_max_sat_min_muses_reach)
	            time_max_sat_min_muses_reach = time_diff;
	        }
					pair< Inst*, z3_expr_vec >& inst = indVar2inst[curr->to_string()];
					assert(inst.first);
					mus.push_back(inst.first);
					assert(curr != Z3_INVALID_EXPR);
	//				if (!inst.second.empty())
	//					s_assert_constraints_inc(q_solver, inst.second);
					s_assert_constraint(q_solver, curr);

	//				cout << "Adding " << *(inst.first) << " to mus" << endl;
				}
				else
				{
					mus.clear();
					break;
				}
			}
	//#ifdef DO_CORRECTNESS_CHECKS
	//		m_cList.pop_back();
	//#endif
			m_constraints.clear();
		}
	}

	if (initial_res == z3::unsat)
	{
    if (recordTime)
    {
      time_sat_min_muses_reach += time_diff;
      if (time_diff > time_max_sat_min_muses_reach)
        time_max_sat_min_muses_reach = time_diff;
    }
		if (mus.empty())
		{
			res = AVR_QTO;//the given formula is UNDEF
		}
		else
			res = AVR_QUSAT;
	}
	else if (initial_res == z3::sat)
	{
//		cout << "\tSAT" << endl;
		numSat++;
		res = AVR_QSAT;//the given formula is SAT, i.e. there's no MUS
	}
	else
	{
//		cout << "\tUNDEF" << endl;
		res = AVR_QTO;//the given formula is UNDEF
	}
	s_pop(q_solver, true);

#ifdef DO_CORRECTNESS_CHECKS
	#ifndef ALLOW_MULTIPLE_LEVELS
		assert(m_numpush == m_numpop);
	#endif
#endif
	for (auto& ptr: garbageList)
		if (ptr)
			delete ptr;

	delete q_solver;
	q_solver = m_solver;

	return res;
}

/// UNSAT core extraction using Z3
int z3_API::get_unsat_core(long timeout_value, InstL& vel, InstL& core, int& numSat, int& numUnsat)
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

	struct rusage usage;
	struct timeval start_time, end_time;
	long long time_diff;
	long long time_res = 0;

	unsigned sz = vel.size();
	AVR_LOG(17, 5, "\tEntering core extraction from Z3" << endl);
	AVR_LOG(17, 5, "\t[Input]: " << vel << " (sz: " << sz << ")" << endl);
	assert(!vel.empty());

	int res;

	/// Create non-incremental solver

	z3_solver ni_solver;
	z3::params s_params = *m_param;
	s_params.set("unsat_core", true);
  if (m_abstract)
    s_params.set("core.minimize", true);

	set_logic_core(ni_solver, &s_params);
	q_solver = ni_solver;

	q_solver->set(s_params);

	m_query_sz = 0;
	/// Add all assertions from m_cList
	for (auto& v: m_cList)
	{
		for (auto& c: v.second)
		{
			q_solver->add(term(c));
		}
		m_query_sz += v.second.size();
	}

#ifdef Z3_MUS_M1
#else
	init_inst2yices();
	for (InstL::iterator it = vel.begin(); it != vel.end(); it++)
	{
		inst2yices(*it);
	}
	if (!m_constraints.empty())
	{
		s_assert_constraints(q_solver);
	}
#endif

	int count = 0;
	unordered_map<string, Inst*> indVar2instFull;
	unordered_map<string, string> indVarHash;
	z3_expr_vector assumptions(*g_ctx);
	z3_expr_vector constraints(*g_ctx);
	z3_expr_vector constraints2(*g_ctx);
  InstL induct_clause;
	for (InstL::iterator it = vel.begin(); it != vel.end(); it++)
	{
		Inst* tve = *it;

#ifdef Z3_MUS_M1
		init_inst2yices();
		inst2yices(tve);
		force(tve);
#else
		force(tve);
#endif

		string iName = "_p_$" + get_z3_temp_name(tve, count);
		z3_expr_ptr indVar = new z3_expr(*g_ctx);
		*indVar = g_ctx->bool_const(iName.c_str());
		AVR_LOG(17, 5, "\t\t\t(inst: " << *(*it) << ", indicator: " << term(indVar) << ")" << endl);
		assert (!m_constraints.empty());
		AVR_LOG(17, 7, "\t\t\t\t(assertions " << term(indVar) << " => " << m_constraints << endl);
		for (auto& c: m_constraints)
			constraints.push_back(implies(term(indVar), term(c)));
		m_constraints.clear();

		string iNameZ3 = indVar->to_string();
		assumptions.push_back(term(indVar));
		add_assume(tve);
		indVar2instFull[iNameZ3] = (*it);
		indVarHash[iNameZ3] = iName;

    if (uType != no_induct) {
    	Inst* ve2;
      if (uType == pre_to_next)
      	ve2 = Inst::all_pre2next(*it);
      else {
      	assert (uType == next_to_pre);
      	ve2 = Inst::all_next2pre(*it);
      }
      inst2yices(ve2);
      z3_expr_ptr c2 = force_wo_add(ve2);
      induct_clause.push_back(OpInst::create(OpInst::LogNot, ve2));

      string iName = "_pi_$" + get_z3_temp_name(*it, count);
  		z3_expr_ptr indVar2 = new z3_expr(*g_ctx);
  		*indVar2 = g_ctx->bool_const(iName.c_str());
      AVR_LOG(17, 5, "\t\t\t(induct inst: " << *ve2 << ", indicator: " << term(indVar2) << ")" << endl);

      if (!m_constraints.empty()) {
				AVR_LOG(17, 7, "\t\t\t\t(induct assertions " << term(indVar2) << " => " << m_constraints << endl);
				for (auto& c: m_constraints)
					constraints.push_back(implies(term(indVar), term(c)));
				m_constraints.clear();
      }
			constraints.push_back((term(indVar2) == term(c2)));
			constraints2.push_back(!term(indVar2));

			delete indVar2;
    }

		count++;
		delete indVar;
	}

  if (uType != no_induct) {
  	assert(!constraints2.empty());
//		AVR_LOG(17, 7, "\t\t\t(induct assertions " << print_terms(constraints2) << endl);

  	Inst* clause = OpInst::create(OpInst::LogOr, induct_clause);

		string iName = "_pi_$" + get_z3_temp_name(clause, count);
    z3_expr_ptr a = create_bool_var(iName);
    AVR_LOG(17, 5, "\t\t\t(induct indicator: " << term(a) << ")" << endl);

    constraints2.push_back(!term(a));
  	z3_expr cInd = mk_or(constraints2);
  	constraints.push_back(cInd);

  	assumptions.push_back(term(a));
  }
  for (int i = 0; i < constraints.size(); i++)
  	q_solver->add(constraints[i]);


#ifdef DO_CORRECTNESS_CHECKS
	int pre_initial_res = s_check(timeout_value);
	AVR_LOG(17, 6, "\t\t(pre-initial-check) " << pre_initial_res << endl);
	assert(pre_initial_res == AVR_QSAT);
	numSat++;
#endif

	TIME_S(start_time);
	z3_result initial_res = s_check_mus(q_solver, timeout_value, assumptions, true);
	TIME_E(start_time, end_time, time_res);
	clear_assume();
	AVR_LOG(17, 5, "\t\t(total-check) " << initial_res << endl);

	if (initial_res == z3::unsat)
	{
		numUnsat++;

		z3_expr_vector uCore = q_solver->unsat_core();
		unsigned uSz = uCore.size();
		AVR_LOG(17, 4, "\t\t(core, sz: " << uSz << ")" << uCore << endl);
		assert(uSz > 0);
		collect_stats_mus(uSz);

		for (int i = 0; i < uSz; i++)
		{
			string iName = uCore[i].to_string();
			Inst* tve = indVar2instFull[iName];
      if (tve != NULL) {
				core.push_back(tve);
				AVR_LOG(17, 4, "adding to mus: " << *tve << endl);
      }
		}
		res = AVR_QUSAT;
	}
	else if (initial_res == z3::sat)
	{
		numSat++;

//		cout << "Error: Z3 unsat core extraction query gave SAT" << endl;
		res = AVR_QSAT;
	}
	else
	{
		core = vel;
		res = AVR_QTO;
	}
	delete q_solver;
	q_solver = m_solver;

	return res;
}

/// UNSAT core extraction using Z3
int z3_API::find_unsat_core(long timeout_value, InstL& hardQ, InstL& vel, InstL& mus, int& numSat, int& numUnsat)
{
#ifdef DISABLE_Z3_CORE
  mus = vel;
  return AVR_QUSAT;
#endif

	struct rusage usage;
	struct timeval start_time, end_time;
	long long time_diff;
	long long time_res = 0;

	assert(m_abstract);

	unsigned sz = vel.size();
	AVR_LOG(17, 5, "\tEntering core extraction from Z3" << endl);
	AVR_LOG(17, 5, "\t[Input]: " << vel << " (sz: " << sz << ")" << endl);
	assert(!vel.empty());

	int res;

	/// Create non-incremental solver

	z3::params s_params = *m_param;
	s_params.set("unsat_core", true);
  if (m_abstract)
    s_params.set("core.minimize", true);

	set_logic_core(q_solver, &s_params);

	q_solver->set(s_params);

  m_query_sz = 0;
  /// Add all assertions from m_cList
  for (auto& v: m_cList)
  {
    for (auto& c: v.second)
    {
      q_solver->add(term(c));
    }
    m_query_sz += v.second.size();
  }

	/// Add all hard assertions
  init_inst2yices();
  m_constraints.clear();
  for (auto& e: hardQ)
  {
    inst2yices(e);
    force(e);
    add_assert(e);
  }
  s_assert_constraints(q_solver);

#ifdef Z3_MUS_M1
#else
	init_inst2yices();
	for (InstL::iterator it = vel.begin(); it != vel.end(); it++)
	{
		inst2yices(*it);
	}
	if (!m_constraints.empty())
	{
		s_assert_constraints(q_solver);
	}
#endif

	int count = 0;
	unordered_map<string, Inst*> indVar2instFull;
	unordered_map<string, string> indVarHash;
	z3_expr_vector assumptions(*g_ctx);
	for (InstL::iterator it = vel.begin(); it != vel.end(); it++)
	{
		Inst* tve = *it;

#ifdef Z3_MUS_M1
		init_inst2yices();
		inst2yices(tve);
		force(tve);
#else
		force(tve);
#endif

		string iName = "_p_$" + get_z3_temp_name(tve, count);
		z3_expr_ptr indVar = new z3_expr(*g_ctx);
		*indVar = g_ctx->bool_const(iName.c_str());
		AVR_LOG(17, 5, "\t\t\t(inst: " << *(*it) << ", indicator: " << term(indVar) << ")" << endl);
		if (!m_constraints.empty())
		{
			AVR_LOG(17, 7, "\t\t\t\t(assertions " << term(indVar) << " => " << m_constraints << endl);
			s_assert_constraints_mus(q_solver, indVar);
		}

		string iNameZ3 = indVar->to_string();
		assumptions.push_back(term(indVar));
		add_assume(tve);
		indVar2instFull[iNameZ3] = (*it);
		indVarHash[iNameZ3] = iName;
		count++;
		delete indVar;
	}


#ifdef DO_CORRECTNESS_CHECKS
	int pre_initial_res = s_check(timeout_value, false);
	AVR_LOG(17, 6, "\t\t(pre-initial-check) " << pre_initial_res << endl);
	assert(pre_initial_res == AVR_QSAT);
	numSat++;
#endif

	TIME_S(start_time);
	z3_result initial_res = s_check_mus(q_solver, timeout_value, assumptions, false);
	TIME_E(start_time, end_time, time_res);
	clear_assume();
	AVR_LOG(17, 5, "\t\t(total-check) " << initial_res << endl);

	if (initial_res == z3::unsat)
	{
		numUnsat++;
		time_unsat_core_muses_reach += time_res;
		if (time_res > time_max_unsat_core_muses_reach)
			time_max_unsat_core_muses_reach = time_res;

		z3_expr_vector uCore = q_solver->unsat_core();
		unsigned uSz = uCore.size();
		AVR_LOG(17, 4, "\t\t(core, sz: " << uSz << ")" << uCore << endl);
		assert(uSz > 0);
		collect_stats_mus(uSz);

		for (int i = 0; i < uSz; i++)
		{
			string iName = uCore[i].to_string();
			Inst* tve = indVar2instFull[iName];
			assert(tve);
			mus.push_back(tve);
		}

		res = AVR_QUSAT;
	}
	else if (initial_res == z3::sat)
	{
		numSat++;
		time_sat_core_muses_reach += time_res;
		if (time_res > time_max_sat_core_muses_reach)
			time_max_sat_core_muses_reach = time_res;

		res = AVR_QSAT;

    cout << "Error: Z3 unsat core extraction query gave SAT" << endl;
    print_query(time_res, ERROR, "error");
//    assert(0);
	}
	else
	{
		mus = vel;
		res = AVR_QTO;
	}
	delete q_solver;
  clear_assume();
	q_solver = m_solver;

	return res;
}


void z3_API::minimize_core(long timeout_value, InstL& vel, InstLL& muses, int& numSat, int& numUnsat, bool recordTime)
{
	collect_stats_muses(vel.size());

#ifdef DO_CORRECTNESS_CHECKS
	#ifndef ALLOW_MULTIPLE_LEVELS
		assert(m_numpush == m_numpop);
		assert(m_cList.size() == 1);
	#endif
#endif

//	vel.sort(CompareInstByPriority);
	vel.sort(Inst::CompareInstByChildInfoTier);
//	for (InstL::iterator lit = vel.begin(); lit != vel.end(); lit++)
//	{
//		cout << "\t" << (*lit)->priority << "\t" << *(*lit) << endl;
//	}

	InstL remainingList = vel;

	/// Flag for triggering avr core extraction
	bool fallbackActive = false;
//	if (m_abstract)
//		fallbackActive = true;

	/// Iteration count
	int itCount = 0;
	while(!remainingList.empty())
	{
		itCount++;
		AVR_LOG(17, 4, "\t#" << itCount << endl);
		int res;
		InstL mus;

		if (!fallbackActive)
		{
			res = get_mus(timeout_value, remainingList, mus, numSat, numUnsat, recordTime);
			if (res == AVR_QTO)
			{
				fallbackActive = true;
				AVR_LOG(17, 4, "\t(fallback) " << res << endl);
			}
		}
		if (fallbackActive)
		{
			if (m_abstract)
			{
				AVR_LOG(15, 0, "\n\t(fallback to avr core extraction, ab, sz: " << remainingList.size() << ")" << endl);
			}
			else
			{
				AVR_LOG(15, 0, "\n\t(fallback to avr core extraction, bv, sz: " << remainingList.size() << ")" << endl);
			}
			res = get_mus_avr(timeout_value, remainingList, mus, numSat, numUnsat, recordTime);
		}

		if (res == AVR_QSAT)
			break;
		else
		{
			assert(res == AVR_QUSAT);
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
//				for (InstL::iterator it = remainingList.begin(); it != remainingList.end();)
//				{
//					if ((*it)->childrenInfo[NUM])
//					{
//						if (musSet.find(*it) != musSet.end())
//						{
//							changed = true;
//							it = remainingList.erase(it);
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
//			for (InstL::iterator it = remainingList.begin(); it != remainingList.end();)
//			{
//				if (musSet.find(*it) != musSet.end())
//					it = remainingList.erase(it);
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
//		return 1;
//	}
//	else
//	{
//		AVR_LOG(17, 4, "\t(no mus, exit)" << endl);
//		return 0;
//	}
//	//	cout << "status: " << status << endl;
//	return status;
}

int z3_API::get_muses_2(long timeout_value, InstL& vel, InstLL& muses, int& numSat, int& numUnsat, Solver* core_solver)
{
#ifdef DISABLE_UNSAT_CORE_MINIMIZATION
	InstL core;
	core_solver->get_unsat_core(timeout_value, vel, core, numSat, numUnsat);
	if (!core.empty())
		muses.push_back(core);
#else
//	if (core_solver->fetch_solv_name() == SMT_Z3)
//		minimize_core(timeout_value, vel, muses, numSat, numUnsat);
//	else
	{
		InstL core;
		int status = core_solver->get_unsat_core(timeout_value, vel, core, numSat, numUnsat);
		if (status == AVR_QSAT)
			return 0;
		minimize_core(timeout_value, core, muses, numSat, numUnsat);
		assert(!muses.empty());
	}
#endif

	if (!muses.empty())
	{
		AVR_LOG(17, 4, "\t(#muses: " << muses.size() << ", exit)" << endl);
		return 1;
	}
	else
	{
		AVR_LOG(17, 4, "\t(no mus, exit)" << endl);
		return 0;
	}
	//	cout << "status: " << status << endl;
}

int z3_API::get_muses(long timeout_value, InstL& vel_1, InstL& vel_2, InstLL& muses, int& numSat, int& numUnsat, Solver* core_solver)
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

	AVR_LOG(17, 4, "\t(i.e.)" << m_constraints << endl);
	s_assert_constraints(true);
	
	int status = get_muses_2(timeout_value, vel_2, muses, numSat, numUnsat, core_solver);
	return status;
}

#ifdef Z3_INTERPOLATION
/**
   \brief Create a variable using the given name and type.
*/
Z3_ast mk_var(Z3_context ctx, const char * name, Z3_sort ty)
{
    Z3_symbol   s  = Z3_mk_string_symbol(ctx, name);
    return Z3_mk_const(ctx, s, ty);
}

/**
   \brief Create a boolean variable using the given name.
*/
z3_expr mk_bool_var(Z3_context ctx, const char * name)
{
    Z3_sort ty = Z3_mk_bool_sort(ctx);
    return expr(*z3_API::g_ctx, mk_var(ctx, name, ty));
}

void interpolation_example(z3_expr expA, z3_expr expB) {
    Z3_ast args3[2] = {Z3_mk_interpolant(Z3_context(*z3_API::g_ctx),expA),expB};
    Z3_ast f = Z3_mk_and(Z3_context(*z3_API::g_ctx),2,args3);
    Z3_ast_vector interpolant = 0;
    Z3_model m = 0;
    Z3_lbool result = Z3_L_UNDEF;

    cout << "\ninterpolation_example for " << expA << " and " << expB << endl;

    result = Z3_compute_interpolant(Z3_context(*z3_API::g_ctx),f,0,&interpolant,&m);

    switch (result) {
    case Z3_L_FALSE:
        printf("unsat\n");
        printf("interpolant: %s\n", Z3_ast_to_string(Z3_context(*z3_API::g_ctx), Z3_ast_vector_get(Z3_context(*z3_API::g_ctx), interpolant, 0)));
        printf("\n");
        break;
    case Z3_L_UNDEF:
        printf("unknown\n");
        printf("potential model:\n");
//	if (m) Z3_model_inc_ref(Z3_context(*g_ctx), m);
//        display_model(ctx, stdout, m);
        break;
    case Z3_L_TRUE:
        printf("sat\n");
//	if (m) Z3_model_inc_ref(Z3_context(*g_ctx), m);
//        display_model(ctx, stdout, m);
        break;
    }
}

int z3_API::get_interpolant(long timeout_value, InstL& velA, InstL& velB, InstL& interpolant, int& numSat, int& numUnsat)
{
#ifndef RANDOM_SHUFFLE_CORE
	if (Config::g_random)
#endif
	{
		vector< Inst* > velVec;
		for (auto& v: velA)
			velVec.push_back(v);
		random_shuffle(velVec.begin(), velVec.end());
		velA.clear();
		for (auto& v: velVec)
			velA.push_back(v);
	}

	AVR_LOG(17, 0, "\tEntering interpolant extraction from Z3" << endl);
	AVR_LOG(17, 0, "\t[InputA]: " << velA << " (sz: " << velA.size() << ")" << endl);
	AVR_LOG(17, 0, "\t[InputB]: " << velB << " (sz: " << velB.size() << ")" << endl);
	assert(!velA.empty());
	assert(!velB.empty());
	m_constraints.clear();

	int res;

	z3_expr_ptr expA = new z3_expr(*g_ctx);
	{
		Inst* veA = OpInst::create(OpInst::LogAnd, velA);
		init_inst2yices();
		inst2yices(veA);
		force(veA);
		z3_expr_vector argumentsA(*g_ctx);
		for (auto v: m_constraints)
			argumentsA.push_back(term(v));
		*expA = mk_and(argumentsA);
//		*expA = expr(*g_ctx, Z3_mk_interpolant(*g_ctx, mk_and(argumentsA)));
		m_constraints.clear();
	}

	z3_expr_ptr expB = new z3_expr(*g_ctx);
	{
		Inst* veB = OpInst::create(OpInst::LogAnd, velB);
		init_inst2yices();
		inst2yices(veB);
		force(veB);
		z3_expr_vector argumentsB(*g_ctx);
		for (auto v: m_constraints)
			argumentsB.push_back(term(v));
		*expB = mk_and(argumentsB);
		m_constraints.clear();
	}

	z3_expr_ptr expAB = new z3_expr(*g_ctx);
	*expAB = term(expA) && term(expB);

//	cout << "itp expAB: " << term(expAB) << endl;

	{
    z3_expr pa = mk_bool_var(Z3_context(*g_ctx), "PredA");
    z3_expr pb = mk_bool_var(Z3_context(*g_ctx), "PredB");
    z3_expr pc = mk_bool_var(Z3_context(*g_ctx), "PredC");
    z3_expr args1[2] = {pa,pb}, args2[2] = {(!pb),pc};
		interpolation_example((pa && pb), ((!pb) && pc));
	}
	interpolation_example(term(expA), term(expB));

	z3::params s_params = *m_param;
	z3_expr_vector interp(*g_ctx);

	try {
	  check_result itp_res = g_ctx->compute_interpolant(term(expAB), s_params, interp, *m_model);
	  cout << "itp result: " << itp_res << endl;
	  cout << "itp interp: " << "\t" << interp << " (sz: " << interp.size() << ")" << endl;
	  if (!interp.empty())
	  	assert(0);
	}
	catch (const z3::exception& e) {
		cout << e.msg() << endl;
		assert(0);
	}

  delete expA;
  delete expB;
  delete expAB;

	return res;
}
#endif


bool z3_API::s_assert(Inst* e)
{
	AVR_LOG(11, 1, "[SID:" << m_solver_id << ", SBA:" << m_ba_idx << "]----------" << endl);
 	init_inst2yices();
	m_constraints.clear();
	inst2yices(e);
	force(e);
	add_assert(e);

	s_assert_constraints();
//	// add the constraints to YICES
//	for (YicesAPIBAV::iterator it = m_constraints.begin(), end_it = m_constraints.end(); it != end_it; ++it)
//	{
//		yices_assert_formula(g_ctx, *it);
//	}

	return true;
}

bool z3_API::s_assert(InstL& vel)
{
 	init_inst2yices();
	m_constraints.clear();

	for (auto& e: vel)
	{
		inst2yices(e);
		force(e);
		add_assert(e);
	}

	s_assert_constraints();

	return true;
}



void z3_API::s_push(z3_solver& solver, bool fake)
{
	if (!fake)
	{
	  AVR_LOG(17, 5, "(push)" << endl);
	  solver->push();
	}
#ifdef DO_CORRECTNESS_CHECKS
	assert(m_numpush >= m_numpop);
#endif

	m_numpush++;

	z3_expr_vec tmp;
	m_cList.push_back(make_pair(m_cList.size() + 1, tmp));
	push_assert();
}

void z3_API::s_pop(z3_solver& solver, bool fake)
{
	if (!fake)
	{
    AVR_LOG(17, 5, "(pop)" << endl);
	  solver->pop();
	}
	m_numpop++;

#ifdef DO_CORRECTNESS_CHECKS
	assert(m_numpush >= m_numpop);
#endif

	m_query_sz -= m_cList.back().second.size();
	m_cList.pop_back();
	pop_assert();
}

void z3_API::s_print_model(void)
{
	cout << "Model: " << *m_model << endl;
}

void z3_API::s_assert_constraint(z3_solver& solver, z3_expr_ptr ye, z3_expr_ptr indVar)
{
#ifdef DO_CORRECTNESS_CHECKS
		assert(m_cList.size() >= 1);
#endif
		pair< int, z3_expr_vec>& tmp = m_cList.back();

	if (indVar)
	{
		z3_expr_ptr sExpr = new z3_expr(*g_ctx);
		add_ptr(sExpr);
		*sExpr = implies(term(indVar), term(ye));
		solver->add(term(sExpr));

		tmp.second.push_back(sExpr);
	}
	else
	{
		solver->add(term(ye));

		tmp.second.push_back(ye);
	}
	m_query_sz += 1;
}

void z3_API::s_assert_constraints(z3_solver& solver, bool reset, z3_expr_ptr indVar)
{
#ifdef DO_CORRECTNESS_CHECKS
	assert(m_cList.size() >= 1);
#endif
	pair< int, z3_expr_vec>& tmp = m_cList.back();

	/// Assumed std::vector guarantees continuous memory allocation
	for (auto& c : m_constraints)
	{
		if (indVar)
		{
			z3_expr_ptr sExpr = new z3_expr(*g_ctx);
			add_ptr(sExpr);
			*sExpr = implies(term(indVar), term(c));
			solver->add(term(sExpr));

			tmp.second.push_back(sExpr);
		}
		else
		{
			try {
				solver->add(term(c));
			}
			catch (const z3::exception& e) {
				cout << e.msg() << endl;
				assert(0);
			}

			tmp.second.push_back(c);
		}
	}

	int sz = m_constraints.size();
	m_query_sz += sz;

	if (reset)
		m_constraints.clear();
}

void z3_API::s_assert_constraint_mus(z3_solver& solver, z3_expr_ptr ye)
{
	solver->add(term(ye));
}

void z3_API::s_assert_constraints_mus(z3_solver& solver, z3_expr_ptr indVar)
{
	for (auto& c : m_constraints)
	{
		if (indVar)
		{
			z3_expr_ptr sExpr = new z3_expr(*g_ctx);
//			add_ptr(sExpr);
			*sExpr = implies(term(indVar), term(c));
			solver->add(term(sExpr));
			delete sExpr;
		}
		else
			solver->add(term(c));
	}
	m_query_sz += m_constraints.size();
	m_constraints.clear();
}

void z3_API::s_assert_constraints_inc(z3_solver& solver, vector < z3_expr_ptr >& assumptions)
{
#ifdef DO_CORRECTNESS_CHECKS
	assert(m_cList.size() >= 1);
#endif
	pair< int, z3_expr_vec>& tmp = m_cList.back();

	/// Assumed std::vector guarantees continuous memory allocation
	for (auto& c : assumptions)
	{
		solver->add(term(c));
		tmp.second.push_back(c);
	}

	int sz = assumptions.size();
	m_query_sz += sz;
}

void z3_API::print_timeout_query(string fname, long long time_res)
{
  string header = "";
  if (time_res != -1)
    header += "(set-info :time " + to_string(((double) time_res / 1000.0)) + " milli-seconds)\n";
  if (m_abstract)
    header += "(set-info :query_class abstract)\n";
  else
    header += "(set-info :query_class concrete)\n";
  header += "(set-info :status unknown)\n";
  print_smt2(fname, header);
}

z3_result z3_API::shift_to_noninc(long timeout_value, long long time_res, bool getModel)
{
	AVR_LOG(17, 0, "\n\t(fallback to non-inc solver, " << (m_abstract?"ab":"bv")
			<< ", depth: " << m_cList.size() << ", t:" << time_res << " usec)" << endl);
	print_query(time_res, TIME_TO, "to");
	return s_check_oneshot(timeout_value, getModel);
}

bool z3_API::s_check_model(bool allowDontCares)
{
#ifdef SIMPLIFY_Z3_CONSTRAINTS
//	return true;
#endif

#ifdef DO_CORRECTNESS_CHECKS
	for (auto& cit : m_cList)
	{
		for (auto& y : cit.second)
		{
			z3_expr_ptr valExpr = new z3_expr(*g_ctx);
			*valExpr = m_model->eval(*y, true);
			Z3_lbool ans = valExpr->bool_value();
//				cout << term(y) << endl;

			if (ans != Z3_L_TRUE)
			{
				int idx = cit.first;
				cout << "\n[" << idx << "]:\t" << term(y) << " -> " << ans << endl;
				cout << "\nm_cList: " << endl;
				for (auto& cit : m_cList)
				{
					int idx = cit.first;
					cout << "[" << idx << "]" << endl;
					for (auto& y : cit.second)
					{
						z3_expr_ptr valExpr = new z3_expr(*g_ctx);
						*valExpr = m_model->eval(*y);
						Z3_lbool ans = valExpr->bool_value();

						z3_expr_ptr valExprComplete = new z3_expr(*g_ctx);
						*valExprComplete = m_model->eval(*y, true);
						Z3_lbool ansComplete = valExprComplete->bool_value();

						cout << term(y) << " -> " << ans << " (" << ansComplete << ")" << endl;
					}
					cout << endl;
				}
				cout << endl;
				return false;
			}
			delete (valExpr);
		}
	}
#endif
	return true;
}

// 0 : UNSAT
// 1 : SAT
//-1 : T.O. (assert fail)
int z3_API::s_check(long timeout_value, bool getModel)
{
	update_query_sz();
	struct rusage usage;
	struct timeval start_time, end_time;
	long long time_diff;
	long long time_res = 0;

	Z3_SET_TIMEOUT;
	TIME_S(start_time);
	z3_result res = z3::unknown;

	try {
		res = m_solver->check();

//		string comment = "regular ";
//		comment += m_abstract ? "ab" : "bv";
//		comment += ": ans- " + to_string(res);
//		print_asserts(comment);
	}
	catch (const z3::exception& e) {
		cout << e.msg() << endl;
	}

	Z3_CHECK_TIMEOUT;
	TIME_E(start_time, end_time, time_res);

//	if (m_abstract)
//	{
//		z3_stats st = m_solver->statistics();
//		for (unsigned i = 0; i < st.size(); i++)
//		{
//			string key = st.key(i);
//			unsigned rhsN;
//			double rhsD;
//
//			if (st.is_uint(i))
//			{
//				rhsN = st.uint_value(i);
//				cout << key << "\t:\t" << rhsN << endl;
//			}
//			else if (st.is_double(i))
//			{
//				rhsD = st.double_value(i);
//				cout << key << "\t:\t" << rhsD << endl;
//			}
//		}
//	}
//	assert(0);

	if (res == z3::sat)
	{
		if (m_numpush == 0)
			collect_stats_query(time_res, ONESHOT_SAT);
		else
			collect_stats_query(time_res, INC_SAT);
		if (getModel)
		{
			*m_model = m_solver->get_model();
			bool mres = s_check_model();
			if (!mres)
			{
		    print_query(time_res, ERROR, "error");
			}
			assert(mres);
		}
		return AVR_QSAT;
	}
	else if (res == z3::unsat)
	{
		if (m_numpush == 0)
			collect_stats_query(time_res, ONESHOT_UNSAT);
		else
			collect_stats_query(time_res, INC_UNSAT);
		return AVR_QUSAT;
	}
	else
	{
		collect_stats_query(time_res, TIME_TO);
		z3_result newRes = shift_to_noninc(timeout_value, time_res, getModel);
		if (newRes == z3::sat)
			return AVR_QSAT;
		else if (newRes == z3::unsat)
			return AVR_QUSAT;
		else
			assert(0);
	}
}

z3_result z3_API::s_check_inc(z3_solver& solver, long timeout_value, bool getModel)
{
	update_query_sz();
	struct rusage usage;
	struct timeval start_time, end_time;
	long long time_diff;
	long long time_res = 0;

	Z3_SET_TIMEOUT;
	TIME_S(start_time);
	z3_result res = z3::unknown;

	try {
		res = solver->check();

//		string comment = "inc ";
//		comment += m_abstract ? "ab" : "bv";
//		comment += ": ans- " + to_string(res);
//		print_asserts(comment);
	}
	catch (const z3::exception& e) {
		cout << e.msg() << endl;
	}

	Z3_CHECK_TIMEOUT;
	TIME_E(start_time, end_time, time_res);

	if (res == z3::sat)
	{
		collect_stats_query(time_res, INC_SAT);
		if (getModel)
		{
			*m_model = solver->get_model();
			bool mres = s_check_model();
			if (!mres)
			{
			  print_query(time_res, ERROR, "error");
			}
			assert(mres);
		}
	}
	else if (res == z3::unsat)
	{
		collect_stats_query(time_res, INC_UNSAT);
	}
	else
	{
		collect_stats_query(time_res, TIME_TO);
		z3_result newRes = shift_to_noninc(timeout_value, time_res, getModel);
		if (newRes == z3::unknown)
			assert(0);
		res = newRes;
	}
	return res;
}

z3_result z3_API::s_check_oneshot(long timeout_value, bool getModel)
{
	update_query_sz();
	struct rusage usage;
	struct timeval start_time, end_time;
	long long time_diff;
	long long time_res = 0;

	/// Create non-incremental solver
	z3_solver ni_solver;
//	ni_solver = new solver(*g_ctx);
	set_logic(ni_solver);
	q_solver = ni_solver;

//	param_descrs p = q_solver->get_param_descrs();
//	for (int i = 0; i < p.size(); i++)
//	{
//		cout << p.name(i) << " -> " << p.documentation(p.name(i)) << endl;
//	}
//	assert(0);

	z3::params s_params(*g_ctx);
	s_params.set("unsat_core", false);
//	s_params.set("relevancy", static_cast< unsigned > (0));
//	s_params.set("phase_selection", static_cast< unsigned > (4));

//	unsigned timeoutVal = timeout_value * 500;
//	s_params.set("timeout", timeoutVal);
//	cout << s_params << endl;
	q_solver->set(s_params);

	/// Add all assertions from m_cList
	for (auto& v: m_cList)
		for (auto& c: v.second)
			q_solver->add(term(c));

//	/// Add all assertions from m_solver
//	expr_vector assertions = m_solver->assertions();
//	assert(assertions.size() == m_query_sz);
//	for (int i = 0; i < assertions.size(); i++)
//		q_solver->add(assertions[i]);

	/// Now query
	Z3_SET_TIMEOUT;
	TIME_S(start_time);
	z3_result res = z3::unknown;

	try {
		res = q_solver->check();

//		string comment = "oneshot ";
//		comment += m_abstract ? "ab" : "bv";
//		comment += ": ans- " + to_string(res);
//		print_asserts(comment);
	}
	catch (const z3::exception& e) {
		cout << e.msg() << endl;
	}

	TIME_E(start_time, end_time, time_res);
	Z3_CHECK_TIMEOUT_OS;

	if (res == z3::sat)
	{
		collect_stats_query(time_res, ONESHOT_SAT);
		if (getModel)
		{
			*m_model = q_solver->get_model();
			bool mres = s_check_model();
			if (!mres)
			{
        print_query(time_res, ERROR, "error");
			}
			assert(mres);
		}
	}
	else if (res == z3::unsat)
	{
		collect_stats_query(time_res, ONESHOT_UNSAT);
	}
	else
	{
		collect_stats_query(time_res, TIME_TO);
    print_query(time_res, TIME_TO, "error");
		AVR_LOG(15, 0, "Z3 oneshot Query TIMEOUT (" << timeout_value << "), query type: " << queryType << ", getModel: " << getModel << endl);
		Inst::g_result = f_to_query;

		cout << q_solver->statistics() << endl;
		cout << q_solver->reason_unknown() << endl;
		cout << s_params << endl;

    z3_API* tmpSolver = new z3_API(m_mapper, m_ba_idx, is_i, queryType);
    for (auto& assertions: m_asserts.assertions)
      for (auto& v: assertions)
      	tmpSolver->s_assert(v);

  	long long time_res2 = 0;
  	TIME_S(start_time);
    z3_result res2 = tmpSolver->s_check_oneshot(0, false);
  	TIME_E(start_time, end_time, time_res2);
    AVR_LOG(17, 0, "\t(result: " << ((res2 == z3::sat) ? "sat" : (res2 == z3::unsat) ? "unsat" : "??")
    		<< ", t: " << time_res2 << " usec)" << endl);
		assert(0);
	}
	delete q_solver;
	q_solver = m_solver;

	return res;
}


int z3_API::s_check_assume(long timeout_value, bool getModel)
{
	update_query_sz();
	struct rusage usage;
	struct timeval start_time, end_time;
	long long time_diff;
	long long time_res = 0;

	z3_expr_vector& assumptions = get_assumptions();
	unsigned sz = assumptions.size();
//	assert(sz > 0);

//	cout << solver->to_smt2() << endl;
//	string fname = "to/" + _benchmark + "_test";
//	print_smt2(fname, ((double) time_res / 100000));

	Z3_SET_TIMEOUT;
	TIME_S(start_time);
	z3_result res = z3::unknown;

	try {
		if (sz == 0)
			res = m_solver->check();
		else
			res = m_solver->check(assumptions);

//		string comment = "assume ";
//		comment += m_abstract ? "ab" : "bv";
//		comment += ": ans- " + to_string(res);
//		print_asserts(comment);
	}
	catch (const z3::exception& e) {
		cout << e.msg() << endl;
	}

	Z3_CHECK_TIMEOUT;
	TIME_E(start_time, end_time, time_res);

	if (res == z3::sat)
	{
		collect_stats_query(time_res, MUS_SAT);
		if (getModel)
		{
			*m_model = m_solver->get_model();
			bool mres = s_check_model();
			if (!mres)
			{
        print_query(time_res, ERROR, "error");
			}
			assert(mres);
		}
		return AVR_QSAT;
	}
	else if (res == z3::unsat)
	{
		collect_stats_query(time_res, MUS_UNSAT);
		return AVR_QUSAT;
	}
	else
	{
		collect_stats_query(time_res, TIME_TO);
		z3_result newRes = shift_to_noninc(timeout_value, time_res, getModel);
		if (newRes == z3::sat)
			return AVR_QSAT;
		else if (newRes == z3::unsat)
			return AVR_QUSAT;
		else
			assert(0);
	}
}

z3_result z3_API::s_check_mus(z3_solver& solver, long timeout_value, z3_expr_vector& assumptions, bool getModel)
{
	update_query_sz();
	struct rusage usage;
	struct timeval start_time, end_time;
	long long time_diff;
	long long time_res = 0;


	q_assumptions = &assumptions;
	unsigned sz = assumptions.size();
	assert(sz > 0);
//	cout << solver->assertions() << endl;
//	cout << assumptions << endl;
//	print_query(0, ERROR, "error");

	Z3_SET_TIMEOUT;
	TIME_S(start_time);
	z3_result res = z3::unknown;

	try {
		res = solver->check(assumptions);

//		string comment = "mus ";
//		comment += m_abstract ? "ab" : "bv";
//		comment += ": ans- " + to_string(res);
//		print_asserts(comment);
	}
	catch (const z3::exception& e) {
		cout << e.msg() << endl;
	}

	Z3_CHECK_TIMEOUT;
	TIME_E(start_time, end_time, time_res);

	if (res == z3::sat)
	{
		collect_stats_query(time_res, MUS_SAT);
		if (getModel)
			*m_model = solver->get_model();
	}
	else if (res == z3::unsat)
	{
		collect_stats_query(time_res, MUS_UNSAT);
	}
	else
	{
		collect_stats_query(time_res, TIME_TO);
    print_query(time_res, TIME_TO, "error");
    AVR_LOG(15, 0, "Z3 mus Query TIMEOUT (" << timeout_value << "), query type: " << queryType << endl);
    AVR_LOG(15, 0, "result: " << res << endl);
		Inst::g_result = f_to_query;

		cout << solver->statistics() << endl;
		cout << solver->reason_unknown() << endl;

    z3_API* tmpSolver = new z3_API(m_mapper, m_ba_idx, is_i, queryType);
    for (auto& assertions: m_asserts.assertions)
      for (auto& v: assertions)
      	tmpSolver->s_assert(v);

    for (auto& v: m_asserts.assumptions)
    	tmpSolver->s_assert(v);

  	long long time_res2 = 0;
  	TIME_S(start_time);
    z3_result res2 = tmpSolver->s_check_oneshot(0, false);
  	TIME_E(start_time, end_time, time_res2);
    AVR_LOG(17, 0, "\t(result: " << ((res2 == z3::sat) ? "sat" : (res2 == z3::unsat) ? "unsat" : "??")
    		<< ", t: " << time_res2 << " usec)" << endl);
    assert(0);
	}
	return res;
}

bool z3_API::s_assert_retractable(InstL vel)
{
//	cout << "Assume: " << vel << endl;

	init_inst2yices();
	m_constraints.clear();
	s_push();
//	s_push(true);

//	Solver::incremental_count++;
//	string iName = "pr#" + to_string(Solver::incremental_count);
//	z3_expr_ptr indVar = new z3_expr(*g_ctx);
//	*indVar = g_ctx->bool_const(iName.c_str());
//	m_assumptions->push_back(term(indVar));
//	stack.push_back(indVar);


	for (InstL::iterator it = vel.begin(); it != vel.end(); it++)
	{
		inst2yices(*it);
	}
	for (InstL::iterator it = vel.begin(); it != vel.end(); it++)
	{
		z3_expr_ptr ye = force_wo_add(*it);
		m_constraints.push_back(ye);
		add_assert(*it);
	}
	s_assert_constraints();

#ifdef Y2_USE_RETRACTABLE_ASSUMPTIONS
	m_assumptions.clear();
	m_unsatCore.clear();

	Solver::incremental_count++;
	Inst* ve = OpInst::create(OpInst::LogAnd, vel);
	string iName = "_a_$" + get_z3_temp_name(ve, Solver::incremental_count);
	z3_expr_ptr indVar = create_bool_var(iName);
	m_assumptions.push_back(indVar);
	s_assert_constraints(indVar);
#else
	s_assert_constraints();
#endif
  q_assumptions = m_assumptions;
	return true;
}

bool z3_API::s_retract_all_assertions()
{
	assert(0);
}

bool z3_API::s_retract_assertions()
{
	s_pop();
	assert(m_numpush == m_numpop);
	while(!m_assumptions->empty())
	{
		m_assumptions->pop_back();
	}
	return true;
}

z3_expr_ptr z3_API::create_z3_number(NumInst* num) {
	if (num->get_sort_type() == bvtype) {
		unsigned sz = num->get_size();

		if (sz == 1) {
			if (num->get_num() == 1) {
				z3_expr_ptr c = new z3_expr(*g_ctx);
				*c = term(m_b1);
				return c;
			}
			else {
				assert (num->get_num() == 0);
				z3_expr_ptr c = new z3_expr(*g_ctx);
				add_ptr(c);
				*c = term(m_b0);
				return c;
			}
		}

		string str_num = num->get_mpz()->get_str(10);
		z3_expr_ptr c = new z3_expr(*g_ctx);
		*c = g_ctx->bv_val(str_num.c_str(), sz);
		return c;
	}
	else if (num->get_sort_type() == inttype) {
		string str_num = num->get_mpz()->get_str(10);
		z3_expr_ptr c = new z3_expr(*g_ctx);
		*c = g_ctx->int_val(str_num.c_str());
		return c;
	}
	else
		assert(0);
}

void z3_API::inst2z3(Inst*e, bool bvAllConstraints)
{
	assert(0);

	inst2z3(e, bvAllConstraints);
}

void z3_API::inst2yices(Inst*e, bool bvAllConstraints)
{
//  	cout<< endl << "--en--> " << *e << endl;
	assert(e != 0);
	assert(m_mapper);
//	cout << "m_ba_idx: " << m_ba_idx << "  e->yvar_sz: " << e->yvar.size() << endl;

	if (e->get_visit())
	{
//	  	cout<< endl << "--gex--> " << *e << "\t" << print_term(e->yvar[m_ba_idx]) << endl;

		assert (e->z3_node.get_z3_key() == Z3_INFO::st_z3_key);
		return;
	}
	e->set_visit();

	// do the children first.
	z3_expr_list y_ch;
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
//			y_ch.push_back(v->z3_node.solv_var[yIdx]);
//			s_sz.push_back(v->get_size());
//			assert(y_ch.back());
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
//		assert(m_abstract);
	}
	else
	{
		assert(0);
	}

	e->z3_node.set_key();
	z3_expr_ptr& yvar = e->z3_node.z3_var[yIdx];

	if (!(e->z3_node.solv_vset(yIdx)))
	{
		string name = get_z3_name(e);

		// first, what type of variable should we allocate
		if (m_mapper->fetch_var(e) == TheoryMapper::BV_VAR)
		{
			yvar = create_bv_var(name, make_pair(e->get_size(), e->get_sort()));
		}
		else if (m_mapper->fetch_var(e) == TheoryMapper::EUF_VAR)
		{
			yvar = create_int_var(name, make_pair(e->get_size(), e->get_sort()));
		}
		else if (m_mapper->fetch_var(e) == TheoryMapper::BOOL_VAR)
		{
			yvar = create_bool_var(name);
		}
		else
		{
			assert(0);
		}
		assert(yvar != Z3_INVALID_EXPR);
		e->z3_node.z3_vset[yIdx] = true;
	}

	if (ch)
	{
		for (auto& v: *ch)
		{
			inst2yices(v);
			y_ch.push_back(v->z3_node.solv_var(yIdx));
			s_sz.push_back(v->get_size());
			assert(y_ch.back());
			assert(v->z3_node.solv_vset(yIdx));
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
#endif

	if (reuseAllowed && e->z3_node.solv_vset(yIdx))
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

		if (e->z3_node.solv_cset(cIdx))
		{
			/// Constraints already set, use stored constraints.
	//		cout << "reusing stored constraints " << *e << " nC: " << e->y_constraints[yIdx].size() << endl;

			for (auto& c : e->z3_node.solv_constraints(cIdx))
			{
				add_constraint(c, "reusing stored constraints", e, false);
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

	e->z3_node.z3_cset[cIdx] = true;

	//	cout << "yname: " << name << " (for " << *e << ")" << endl;
	//	assert(name == print_term(yvar));

	// now link this node with the children's yices expressions

	switch (e->get_type())
	{
	case Num: {
		NumInst* num = NumInst::as(e);
		assert(num != 0);

		if (m_mapper->fetch_var(e) == TheoryMapper::BV_VAR) {
// 			if(num->get_mpz() == 3 && num->get_size() == 2){
// 				cout << "debug" << endl;
// 			}
//			link_bv_const(yvar, num->get_mpz(), num->get_size(), e);
			z3_expr_ptr c = create_z3_number(num);
			if (!allow_flatten) {
				yvar = c;
				add_ptr(yvar);
			}
			else {
				z3_expr_ptr ptr = new z3_expr(*g_ctx);
				add_ptr(ptr);
				*ptr = (term(yvar) == term(c));
				add_constraint(ptr, "constant link", e);
			}
			// required to remain in QF_LIA
			if (e->get_sort_type() == inttype) {
				yvar = c;
				add_ptr(yvar);
			}
			else
				delete (c);
		}
		else if (m_mapper->fetch_var(e) == TheoryMapper::BOOL_VAR) {

			yvar = ((*(num->get_mpz()) == 0) ? m_b0 : m_b1);

//			z3_expr_ptr ptr = new z3_expr(*g_ctx);
//			add_ptr(ptr);
//			*ptr = (term(yvar) == ((*(num->get_mpz()) == 0) ? term(m_b0) : term(m_b1)));
//			add_constraint(ptr, "num to boolean conversion", e);
		}
		else {
			// Do nothing
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
        assert(y_ch.size() == 1);
       z3_expr_ptr res = y_ch.front();

//				if (!allow_flatten)
//					yvar = res;
//				else
				{
					z3_expr_ptr ptr = new z3_expr(*g_ctx);
					add_ptr(ptr);
					*ptr = (term(yvar) == term(res));
					add_constraint(ptr, "port connection", e);
				}
			}
			// nothing!
		}
		else if (m_mapper->fetch_op(e) == TheoryMapper::EUF_OP || m_mapper->fetch_op(e) == TheoryMapper::CLU_OP) {
      assert(y_ch.size() == 1);
      z3_expr_ptr res = y_ch.front();

			if (!allow_flatten)
				yvar = res;
      else {
  			z3_expr_ptr ptr = new z3_expr(*g_ctx);
  			add_ptr(ptr);
  			*ptr = (term(yvar) == term(res));
  			add_constraint(ptr, "port connection", e);
      }

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
		z3_expr_ptr res;
		string opstr = "";
		bool interpreted = false;

		z3_expr_list::iterator it = y_ch.begin(), it2 = y_ch.begin(), end_it = y_ch.end();
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
			z3_expr_ptr log;

			z3_expr_ptr a = (*it);
			z3_expr_ptr b = (*it2);

			switch (o) {

			case OpInst::LogNot: {
				if (m_mapper->fetch_var(e) == TheoryMapper::BV_VAR) {
					z3_expr_ptr sExpr = new z3_expr(*g_ctx);
					*sExpr = !(term(*it));
					log = sExpr;
				}
				else if (m_mapper->fetch_var(e) == TheoryMapper::BOOL_VAR) {
					z3_expr_ptr sExpr = new z3_expr(*g_ctx);
					*sExpr = !(term(*it));
					log = sExpr;
				}
				else {
					assert(0);
				}
				interpreted = true;
			}
				break;
			case OpInst::LogNand:
			case OpInst::LogNor:
			case OpInst::LogAnd:
			case OpInst::LogOr: {
				z3_expr_vector* arguments = new z3_expr_vector(*g_ctx);
				z3_expr_list::iterator cit = y_ch.begin();
				InstL::const_iterator ch = e->get_children()->begin();
				for (unsigned j = 0; j < y_ch.size(); j++)
				{
					if (m_mapper->fetch_var(*ch) == TheoryMapper::BV_VAR)
					{
						arguments->push_back(term(*cit));
					}
					else if (m_mapper->fetch_var(*ch) == TheoryMapper::BOOL_VAR)
					{
						arguments->push_back(term(*cit));
					}
					else
						assert(0);
					cit++;
					ch++;
				}

				z3_expr_ptr sExpr = new z3_expr(*g_ctx);
				*sExpr = ((o == OpInst::LogAnd) || (o == OpInst::LogNand)) ? mk_and(*arguments) : mk_or(*arguments);
				if((o == OpInst::LogNor) || (o == OpInst::LogNand)){
					*sExpr = !(term(sExpr));
				}
				delete arguments;

				log = sExpr;
				interpreted = true;
			}
				break;
			case OpInst::LogXor: { // ab' + a'b
				assert(y_ch.size() == 2);
				z3_expr_ptr an = new z3_expr(*g_ctx);
				z3_expr_ptr bn = new z3_expr(*g_ctx);
				*an = !term(a);
				*bn = !term(b);
				z3_expr_ptr sExpr = new z3_expr(*g_ctx);
				*sExpr = (term(a) && term(bn)) || (term(an) && term(b));
				log = sExpr;
				delete (an);
				delete (bn);
				interpreted = true;
			}
				break;
			case OpInst::LogXNor: { // ab + a'b'
				assert(y_ch.size() == 2);
				z3_expr_ptr an = new z3_expr(*g_ctx);
				z3_expr_ptr bn = new z3_expr(*g_ctx);
				*an = !term(a);
				*bn = !term(b);
				z3_expr_ptr sExpr = new z3_expr(*g_ctx);
				*sExpr = (term(a) && term(b)) || (term(an) && term(bn));
				log = sExpr;
				interpreted = true;
				delete (an);
				delete (bn);
			}
				break;
			case OpInst::Eq:{
				assert(y_ch.size() == 2);
				z3_expr_ptr sExpr = new z3_expr(*g_ctx);
				*sExpr = (term(a) == term(b));
				log = sExpr;
				interpreted = true;

//#ifdef INTERPRET_EX_CC
//        if (m_allow_ex_cc)
//        {
//          OpInst* op_t = OpInst::as(e);
//          assert(op_t);
//
//          Inst* simplified = op_t->t_simple;
//          if (e != simplified)
//          {
//            z3_expr& a = *(simplified->z3_node.solv_var[get_vIdx()]);
//            z3_expr_ptr ptr = new z3_expr(*g_ctx);
//            add_ptr(ptr);
//            *ptr = (term(log) == a);
//            add_constraint(ptr, "partial interpretation of == with Ex/Cc", e);
//  //            cout << "Asserting " << *e << " == " << *simplified << endl;
//          }
//        }
//#endif
			}
				break;
			case OpInst::NotEq: {
				assert(y_ch.size() == 2);
				z3_expr_ptr sExpr = new z3_expr(*g_ctx);
				*sExpr = (term(a) != term(b));
				log = sExpr;
				interpreted = true;

//#ifdef INTERPRET_EX_CC
//        if (m_allow_ex_cc)
//        {
//          OpInst* op_t = OpInst::as(e);
//          assert(op_t);
//
//          Inst* simplified = op_t->t_simple;
//          if (e != simplified)
//          {
//            z3_expr& a = *(simplified->z3_node.solv_var[get_vIdx()]);
//            z3_expr_ptr ptr = new z3_expr(*g_ctx);
//            add_ptr(ptr);
//            *ptr = (term(log) == a);
//            add_constraint(ptr, "partial interpretation of != with Ex/Cc", e);
//  //            cout << "Asserting " << *e << " == " << *simplified << endl;
//          }
//        }
//#endif
			}
				break;
			case OpInst::ArrayConst: {
				if (m_mapper->fetch_var(e) == TheoryMapper::BV_VAR) {
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
							z3_expr_ptr b = create_z3_number(NumInst::as(data));
							z3_type_ptr domt = create_bv_sort(make_pair(width, SORT()));
							z3_expr_ptr sExpr = new z3_expr(*g_ctx);
							*sExpr = const_array(type(domt), term(b));
							log = sExpr;
//							cout << "constarray: " << term(log) << " of type " << log->get_sort() << endl;
						}
						else if (data != defval){
							Inst* address = NumInst::create(maxaddress - i, width, SORT());
							z3_expr_ptr a = create_z3_number(NumInst::as(address));
							z3_expr_ptr b = create_z3_number(NumInst::as(data));
							*log = store(term(log), term(a), term(b));
						}
//						cout << "final constarray: " << term(log) << endl;
					}
				} else if (m_mapper->fetch_var(e) == TheoryMapper::EUF_VAR) {
					SORT* d = e->get_sort_domain();
					SORT* r = e->get_sort_range();
					assert(d->type == bvtype);
					assert(r->type == bvtype);
					int width = d->sz;
					int size = r->sz;
					z3_ftype_ptr funct = new z3_ftype(*g_ctx);
					add_ptr(funct);
					*funct = z3::function("constarray", type(create_int_sort(make_pair(width, SORT()))),
																						 type(create_int_sort(make_pair(size, SORT()))));

					z3_expr_ptr sExpr = new z3_expr(*g_ctx);
					*sExpr = z3::as_array(*funct);
					log = sExpr;
					cout << "constarray: " << term(log) << " of type " << log->get_sort() << endl;

//					Inst* init_val = e->get_children()->back();
//					assert(init_val->get_type() == Num);
//					string value = NumInst::as(init_val)->get_mpz()->get_str(2);
//					while (value.length() < e->get_size())
//						value = "0" + value;
//					int maxaddress = pow(2, width) - 1;
//					Inst* defval;
//					for (int i = 0; i <= maxaddress; i++) {
//						string v = value.substr(i*size, size);
//						Inst* data = NumInst::create(v, size, 2);
//						if (i == 0) {
//							defval = data;
//							inst2yices(data);
//							z3_expr_ptr b = data->z3_node.solv_var(yIdx);
//							z3_type_ptr domt = create_int_sort(make_pair(width, SORT()));
//							z3_expr_ptr sExpr = new z3_expr(*g_ctx);
//							*sExpr = const_array(type(domt), term(b));
//							log = sExpr;
////							cout << "constarray: " << term(log) << endl;
//						}
//						else if (data != defval){
//							Inst* address = NumInst::create(maxaddress - i, width);
//							Inst* data = NumInst::create(v, size, 2);
//							inst2yices(address);
//							inst2yices(data);
//							z3_expr_ptr a = address->z3_node.solv_var(yIdx);
//							z3_expr_ptr b = data->z3_node.solv_var(yIdx);
//							*log = store(term(log), term(a), term(b));
////							cout << "update constarray: " << term(log) << endl;
//						}
//					}
				} else {
					assert(0);
				}
				assert(log);
				interpreted = true;
			}
				break;
			case OpInst::ArraySelect: {
				z3_expr_ptr a = *it;
				z3_expr_ptr b = *it2;
				z3_expr_ptr sExpr = new z3_expr(*g_ctx);
				*sExpr = select(term(a), term(b));
				log = sExpr;
				assert(log);
				interpreted = true;
//				cout << "selectarray: " << term(log) << " of type " << log->get_sort() << endl;
//				cout << "  arg a: " << term(a) << " of type " << a->get_sort() << endl;
//				cout << "  arg b: " << term(b) << " of type " << b->get_sort() << endl;
			}
				break;
			case OpInst::ArrayStore: {
				z3_expr_ptr a = *it;
				z3_expr_ptr b = *it2;
				it2++;
				z3_expr_ptr c = *it2;
				z3_expr_ptr sExpr = new z3_expr(*g_ctx);
				*sExpr = store(term(a), term(b), term(c));
				log = sExpr;
				assert(log);
				interpreted = true;
//				cout << "storearray: " << term(log) << " of type " << log->get_sort() << endl;
//				cout << "  arg a: " << term(a) << " of type " << a->get_sort() << endl;
//				cout << "  arg b: " << term(b) << " of type " << b->get_sort() << endl;
//				cout << "  arg c: " << term(c) << " of type " << c->get_sort() << endl;
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
#ifdef USE_INTERPRETED_GREQ
						log = yices_mk_ge(g_ctx, *it, *it2);
						interpreted = true;
#else
						opstr = "GrEq";
#endif
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
				}
				else if (m_mapper->fetch_op(e) == TheoryMapper::CLU_OP) {
					assert(0);
				}
				else if (m_mapper->fetch_op(e) == TheoryMapper::BV_OP) {
					list<z3_expr_ptr> garbage;
					if (e->get_sort_type() == bvtype) {
						Inst* c1 = e->get_children()->front();
						Inst* c2 = e->get_children()->back();
						int c1Sz = c1->get_size();
						int c2Sz = c2->get_size();

						if (a->is_bool()) {
							z3_expr_ptr tmp = new z3_expr(*g_ctx);
								garbage.push_back(tmp);
							*tmp = ite(term(a), term(m_v1), term(m_v0));
							a = tmp;
						}
						if (b->is_bool()) {
							z3_expr_ptr tmp = new z3_expr(*g_ctx);
								garbage.push_back(tmp);
							*tmp = ite(term(b), term(m_v1), term(m_v0));
							b = tmp;
						}

						if (c1Sz < c2Sz)
						{
							z3_expr_ptr tmp = new z3_expr(*g_ctx);
								garbage.push_back(tmp);
							*tmp = zext(term(a), (c2Sz - c1Sz));
							a = tmp;
						}
						if (c2Sz < c1Sz)
						{
							z3_expr_ptr tmp = new z3_expr(*g_ctx);
								garbage.push_back(tmp);
							*tmp = zext(term(b), (c1Sz - c2Sz));
							b = tmp;
						}
					}

					switch (o) {
					case OpInst::Gr: {
						z3_expr_ptr sExpr = new z3_expr(*g_ctx);
						*sExpr = ugt(term(a), term(b));
						log = sExpr;
					}
						break;
					case OpInst::Le: {
						z3_expr_ptr sExpr = new z3_expr(*g_ctx);
						*sExpr = ult(term(a), term(b));
						log = sExpr;
					}
						break;
					case OpInst::GrEq: {
						z3_expr_ptr sExpr = new z3_expr(*g_ctx);
						*sExpr = uge(term(a), term(b));
						log = sExpr;
					}
						break;
					case OpInst::LeEq: {
						z3_expr_ptr sExpr = new z3_expr(*g_ctx);
						*sExpr = ule(term(a), term(b));
						log = sExpr;
					}
						break;
					case OpInst::SLe:
					case OpInst::IntLe:
					{
						z3_expr_ptr sExpr = new z3_expr(*g_ctx);
						*sExpr = (term(a) < term(b));
						log = sExpr;
					}
						break;
					case OpInst::SLeEq:
					case OpInst::IntLeEq:
					{
						z3_expr_ptr sExpr = new z3_expr(*g_ctx);
						*sExpr = (term(a) <= term(b));
						log = sExpr;
					}
						break;
					case OpInst::SGr:
					case OpInst::IntGr:
					{
						z3_expr_ptr sExpr = new z3_expr(*g_ctx);
						*sExpr = (term(a) > term(b));
						log = sExpr;
					}
						break;
					case OpInst::SGrEq:
					case OpInst::IntGrEq:
					{
						z3_expr_ptr sExpr = new z3_expr(*g_ctx);
						*sExpr = (term(a) >= term(b));
						log = sExpr;
					}
						break;
					default:
						assert(0);
					}
					for (auto& ptr: garbage)
						if (ptr)
							delete ptr;
					interpreted = true;
				}
			}
				break;
			default:
				assert(0);
			}

			if (opstr != "") {
//				add_yices_func(yvar, opstr, e->get_size() == 1, y_ch, s_sz, e, (m_mapper->fetch_var(e) == TheoryMapper::BV_VAR) ? e->get_size() : 0);
			}
			else if (m_mapper->fetch_var(e) == TheoryMapper::BV_VAR) {
				res = log;
//				z3_expr_ptr sExpr = new z3_expr(*g_ctx);
//				*sExpr = ite(term(log), term(m_v1), term(m_v0));
//				res = sExpr;
//				delete (log);
			}
			else if (interpreted) {
				res = log;
			}
			else
			{
				cout << *e << endl;
				cout << e->ab_interpret.is_concrete() << endl;
				cout << e->ab_interpret.output_concrete() << endl;
				assert(0);
			}
		}
			break;
		case OpInst::Concat: {
			if (m_mapper->fetch_op(e) == TheoryMapper::BV_OP) {
				assert(m_mapper->fetch_var(e) == TheoryMapper::BV_VAR);
				if (y_ch.size() == 1) {
					res = *it;
				}
				else {
					z3_expr_vector* arguments = new z3_expr_vector(*g_ctx);
					z3_expr_list::reverse_iterator cit = y_ch.rbegin();
					for (unsigned j = 0; j < y_ch.size(); j++)
					{
						if (term(*cit).is_bool())
							arguments->push_back(ite(term(*cit), term(m_v1), term(m_v0)));
						else
							arguments->push_back(term(*cit));
						cit++;
					}

					z3_expr_ptr sExpr = new z3_expr(*g_ctx);
					*sExpr = concat(*arguments);
					res = sExpr;
					delete (arguments);
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
				// bv op on an int var?????????????
				assert(m_mapper->fetch_var(e) == TheoryMapper::BV_VAR);

				list<z3_expr_ptr> garbage;
				z3_expr_ptr a = *it;
				Inst* c1 = e->get_children()->front();
				int outSz = e->get_size();
				int c1Sz = c1->get_size();

				if (e->get_sort_type() == bvtype) {
					if (a->is_bool()) {
						z3_expr_ptr tmp = new z3_expr(*g_ctx);
							garbage.push_back(tmp);
						*tmp = ite(term(a), term(m_v1), term(m_v0));
						a = tmp;
					}

					if (c1Sz < outSz)
					{
						z3_expr_ptr tmp = new z3_expr(*g_ctx);
						garbage.push_back(tmp);
						*tmp = zext(term(a), (outSz - c1Sz));
						a = tmp;
					}
				}

				switch (o) {
				case OpInst::Minus:
				case OpInst::IntMinus:
				{
					assert(y_ch.size() == 1);
					z3_expr_ptr sExpr = new z3_expr(*g_ctx);
					*sExpr = -term(a);
					res = sExpr;
				}
					break;
				case OpInst::BitWiseNot: {
					assert(y_ch.size() == 1);
					z3_expr_ptr sExpr = new z3_expr(*g_ctx);
					*sExpr = ~term(a);
					res = sExpr;
				}
					break;
				case OpInst::IntFloor:
				{
					assert(y_ch.size() == 1);
					string n =  "k" + to_string(e->get_id());
					z3_expr_ptr sExpr = new z3_expr(*g_ctx);
					*sExpr = g_ctx->int_const(n.c_str());
					res = sExpr;

					z3_expr_ptr ptr = new z3_expr(*g_ctx);
					add_ptr(ptr);
					*ptr = to_real(term(res)) <= term(a) < to_real(term(res)) + 1;
					add_constraint(ptr, "floor conversion", e);

					cout << "found floor operation with z3, asserting to identify this case" << endl;
					assert(0);
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
					z3_expr_ptr b = *it2;
					int maxSz = outSz;

					if (e->get_sort_type() == bvtype) {

						if (b->is_bool()) {
							z3_expr_ptr tmp = new z3_expr(*g_ctx);
								garbage.push_back(tmp);
							*tmp = ite(term(b), term(m_v1), term(m_v0));
							b = tmp;
						}

						Inst* c2 = e->get_children()->back();
						int c2Sz = c2->get_size();
						if (maxSz < c1Sz)
							maxSz = c1Sz;
						if (maxSz < c2Sz)
							maxSz = c2Sz;

						if (outSz < maxSz)
						{
							z3_expr_ptr tmp = new z3_expr(*g_ctx);
							garbage.push_back(tmp);
							*tmp = zext(term(a), (maxSz - outSz));
							a = tmp;
						}
						if (c2Sz < maxSz)
						{
							z3_expr_ptr tmp = new z3_expr(*g_ctx);
							garbage.push_back(tmp);
							*tmp = zext(term(b), (maxSz - c2Sz));
							b = tmp;
						}
					}
					switch (o) {
					case OpInst::Add:
					case OpInst::IntAdd:
					{
						if(y_ch.size() == 2) {
							z3_expr_ptr sExpr = new z3_expr(*g_ctx);
							*sExpr = (term(a) + term(b));
							res = sExpr;
						}
						else {
							assert(0);
						}
					}
						break;
					case OpInst::Sub:
					case OpInst::IntSub:
					{
						assert(y_ch.size() == 2);
						z3_expr_ptr sExpr = new z3_expr(*g_ctx);
						*sExpr = (term(a) - term(b));
						res = sExpr;
					}
						break;
					case OpInst::Mult:
					case OpInst::IntMult:
					{
						assert(y_ch.size() == 2);
						z3_expr_ptr sExpr = new z3_expr(*g_ctx);
						*sExpr = (term(a) * term(b));
						res = sExpr;
					}
						break;
					case OpInst::Div: {
						assert(y_ch.size() == 2);
						z3_expr_ptr sExpr = new z3_expr(*g_ctx);
						*sExpr = udiv(term(a), term(b));
						res = sExpr;
					}
						break;
					case OpInst::SDiv:
					case OpInst::IntDiv:
					{
						assert(y_ch.size() == 2);
						z3_expr_ptr sExpr = new z3_expr(*g_ctx);
						*sExpr = (term(a) / term(b));
						res = sExpr;
					}
						break;
					case OpInst::Rem: {
						assert(y_ch.size() == 2);
						z3_expr_ptr sExpr = new z3_expr(*g_ctx);
						*sExpr = urem(term(a), term(b));
						res = sExpr;
					}
						break;
					case OpInst::SRem: {
						assert(y_ch.size() == 2);
						z3_expr_ptr sExpr = new z3_expr(*g_ctx);
						*sExpr = srem(term(a), term(b));
						res = sExpr;
					}
						break;
					case OpInst::SMod: {
						assert(y_ch.size() == 2);
						z3_expr_ptr sExpr = new z3_expr(*g_ctx);
						*sExpr = smod(term(a), term(b));
						res = sExpr;
					}
						break;
					case OpInst::IntMod: {
						assert(y_ch.size() == 2);
						z3_expr_ptr sExpr = new z3_expr(*g_ctx);
						*sExpr = mod(term(a), term(b));
						res = sExpr;
					}
						break;
					case OpInst::BitWiseAnd: {
						assert(y_ch.size() == 2);
						z3_expr_ptr sExpr = new z3_expr(*g_ctx);
						*sExpr = (term(a) & term(b));
						res = sExpr;
					}
						break;
					case OpInst::BitWiseNand: {
						assert(y_ch.size() == 2);
						z3_expr_ptr sExpr = new z3_expr(*g_ctx);
						*sExpr = nand(term(a), term(b));
						res = sExpr;
					}
						break;
					case OpInst::BitWiseOr: {
						assert(y_ch.size() == 2);
						z3_expr_ptr sExpr = new z3_expr(*g_ctx);
						*sExpr = (term(a) | term(b));
						res = sExpr;
					}
						break;
					case OpInst::BitWiseNor: {
						assert(y_ch.size() == 2);
						z3_expr_ptr sExpr = new z3_expr(*g_ctx);
						*sExpr = nor(term(a), term(b));
						res = sExpr;
					}
						break;
					case OpInst::BitWiseXor: {
						assert(y_ch.size() == 2);
						z3_expr_ptr sExpr = new z3_expr(*g_ctx);
						*sExpr = (term(a) ^ term(b));
						res = sExpr;
					}
						break;
					case OpInst::BitWiseXNor: {
						assert(y_ch.size() == 2);
						z3_expr_ptr sExpr = new z3_expr(*g_ctx);
						*sExpr = xnor(term(a), term(b));
						res = sExpr;
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
								z3_expr_ptr sExpr = new z3_expr(*g_ctx);
								*sExpr = shl(term(a), num->get_mpz()->get_si());
								res = sExpr;
							}
							else {
								z3_expr_ptr sExpr = new z3_expr(*g_ctx);
								*sExpr = lshr(term(a), num->get_mpz()->get_si());
								res = sExpr;
							}
						}
						else {
							if (o == OpInst::ShiftR)
							{
								z3_expr_ptr sExpr = new z3_expr(*g_ctx);
								*sExpr = lshr(term(a), term(b));
								res = sExpr;
							}
							else if (o == OpInst::ShiftL)
							{
								z3_expr_ptr sExpr = new z3_expr(*g_ctx);
								*sExpr = shl(term(a), term(b));
								res = sExpr;
							}
							else
								assert(0);
						}
						break;
					}
					case OpInst::AShiftR: {
						assert(y_ch.size() == 2);
						InstL::const_iterator ve_it = ch->begin(), ve_it2 = ch->begin();
						ve_it2++;
						NumInst* num = NumInst::as(*ve_it2);
						if (num != 0)
						{
							z3_expr_ptr sExpr = new z3_expr(*g_ctx);
							*sExpr = ashr(term(a), num->get_mpz()->get_si());
							res = sExpr;
						}
						else
						{
							z3_expr_ptr sExpr = new z3_expr(*g_ctx);
							*sExpr = ashr(term(a), term(b));
							res = sExpr;
						}
					}
						break;
					case OpInst::Sext:
					case OpInst::Zext: {
						assert(y_ch.size() == 2);
						z3_expr_ptr a2 = *it;
						if (a2->is_bool()) {
							z3_expr_ptr tmp = new z3_expr(*g_ctx);
								garbage.push_back(tmp);
							*tmp = ite(term(a2), term(m_v1), term(m_v0));
							a2 = tmp;
						}
						InstL::const_iterator ve_it = ch->begin();
						int amount = e->get_size() - (*ve_it)->get_size();
						assert(amount >= 0);
						z3_expr_ptr sExpr = new z3_expr(*g_ctx);
						if (o == OpInst::Sext)
							*sExpr = sext(term(a2), amount);
						else
							*sExpr = zext(term(a2), amount);
						res = sExpr;
					}
						break;
					default:
						assert(0);
					}
					if (e->get_sort_type() == bvtype) {
						if (outSz < maxSz)
							*res = res->extract((outSz - 1), 0);
					}
				}
					break;

				case OpInst::AddC:
				case OpInst::AShiftL:
					assert(0); // for now.

				case OpInst::ReductionAnd:
				case OpInst::ReductionNand: {
					assert(y_ch.size() == 1);
					Z3_ast r = Z3_mk_bvredand(*g_ctx, term(a));
					z3_expr_ptr sExpr = new z3_expr(*g_ctx);
					*sExpr = expr(*g_ctx, r);
					if (o == OpInst::ReductionNand)		*sExpr = ~(term(sExpr));
					res = sExpr;
				}
					break;
				case OpInst::ReductionOr:
				case OpInst::ReductionNor: {
					assert(y_ch.size() == 1);
					Z3_ast r = Z3_mk_bvredor(*g_ctx, term(a));
					z3_expr_ptr sExpr = new z3_expr(*g_ctx);
					*sExpr = expr(*g_ctx, r);
					if (o == OpInst::ReductionNor)		*sExpr = ~(term(sExpr));
					res = sExpr;
				}
					break;
				case OpInst::ReductionXor:
				case OpInst::ReductionXNor: {
					assert(y_ch.size() == 1);
					z3_expr& ych = term(a);
					unsigned sz = (*(ch->begin()))->get_size();
					if (sz == 1) {
						res = &ych;
					}
					else {
						z3_expr_ptr bit = new z3_expr(*g_ctx);
						z3_expr_ptr bit2 = new z3_expr(*g_ctx);
						*bit = ych.extract(0, 0);
						*bit2 = ych.extract(1, 1);
						*bit = term(bit) ^ term(bit2);
						for (unsigned i = 2; i < sz; i++)
						{
							*bit = term(bit) ^ (ych.extract(i, i));
						}
						z3_expr_ptr sExpr = new z3_expr(*g_ctx);
						*sExpr = term(bit);
						if (o == OpInst::ReductionXNor)		*sExpr = ~(term(sExpr));
						res = sExpr;
						delete (bit);
						delete (bit2);
					}
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
					if(simp_to_zero == true) {
						//cout << "(simp_to_zero == true): e: " << *e << endl;
						z3_expr_ptr sExpr = new z3_expr(*g_ctx);
						*sExpr = g_ctx->bv_val(0, out_size);
						res = sExpr;
					}
					else {
						//cout << "(simp_to_zero == false): e: " << *e << endl;
	//					int rotate_amount = 31;
						z3_expr& a = term(*it);
						z3_expr& b = term(*it2);
						z3_expr_ptr els = new z3_expr(*g_ctx);
						z3_expr_ptr thn = new z3_expr(*g_ctx);
						*els = concat(a.extract(rotate_amount-1, 0), a.extract(out_size-1, rotate_amount));	//right	31
						rotate_amount--;
						*thn = concat(a.extract(rotate_amount-1, 0), a.extract(out_size-1, rotate_amount));	//right	30

						z3_expr_ptr num = new z3_expr(*g_ctx);
						z3_expr_ptr cond = new z3_expr(*g_ctx);
						*num = g_ctx->bv_val(rotate_amount, amt_size);
						*cond = (b == term(num));
						z3_expr_ptr sExpr = new z3_expr(*g_ctx);
						*sExpr = ite(term(cond), term(thn), term(els));	// (sel == 30) ? rotate_30 : rotate_31

						for(; rotate_amount > 0; --rotate_amount) {
							*thn = concat(a.extract(rotate_amount-1, 0), a.extract(out_size-1, rotate_amount));
							*num = g_ctx->bv_val(rotate_amount, amt_size);
							*cond = (b == term(num));
							*sExpr = ite(term(cond), term(thn), term(sExpr));
						}
						*num = g_ctx->bv_val(0, amt_size);
						*cond = (b == term(num));
						*sExpr = ite(term(cond), a, term(sExpr));
						res = sExpr;

						delete (els);
						delete (thn);
						delete (num);
						delete (cond);
					}
					break;
					//yices_mk_bv_concat(g_ctx, yices_mk_bv_extract(g_ctx, out_size-1-rotate_amount, 0, *it), yices_mk_bv_extract(g_ctx, out_size-1, out_size-rotate_amount, *it))	//left
				}
				case OpInst::VRotateL: {
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
					if(simp_to_zero == true) {
						//cout << "(simp_to_zero == true): e: " << *e << endl;
						z3_expr_ptr sExpr = new z3_expr(*g_ctx);
						*sExpr = g_ctx->bv_val(0, out_size);
						res = sExpr;
					}
					else {
						//cout << "(simp_to_zero == false): e: " << *e << endl;
						//int rotate_amount = 31;
						z3_expr& a = term(*it);
						z3_expr& b = term(*it2);
						
						z3_expr_ptr els = new z3_expr(*g_ctx);
						z3_expr_ptr thn = new z3_expr(*g_ctx);
						*els = concat(a.extract(out_size-rotate_amount-1, 0), a.extract(out_size-1, out_size-rotate_amount));	//right	31
						rotate_amount--;
						*thn = concat(a.extract(out_size-rotate_amount-1, 0), a.extract(out_size-1, out_size-rotate_amount));	//right	30

						z3_expr_ptr num = new z3_expr(*g_ctx);
						z3_expr_ptr cond = new z3_expr(*g_ctx);
						*num = g_ctx->bv_val(rotate_amount, amt_size);
						*cond = (b == term(num));
						z3_expr_ptr sExpr = new z3_expr(*g_ctx);
						*sExpr = ite(term(cond), term(thn), term(els));	// (sel == 30) ? rotate_30 : rotate_31

						for(; rotate_amount > 0; --rotate_amount){
							*thn = concat(a.extract(out_size-rotate_amount-1, 0), a.extract(out_size-1, out_size-rotate_amount));
							*num = g_ctx->bv_val(rotate_amount, amt_size);
							*cond = (b == term(num));
							*sExpr = ite(term(cond), term(thn), term(sExpr));
						}
						*num = g_ctx->bv_val(0, amt_size);
						*cond = (b == term(num));
						*sExpr = ite(term(cond), a, term(sExpr));
						res = sExpr;

						delete (els);
						delete (thn);
						delete (num);
						delete (cond);
					}
					break;
				}
				case OpInst::VShiftL:	//TODO
				case OpInst::VShiftR: 
				case OpInst::VAShiftL:
				case OpInst::VAShiftR:
				case OpInst::VEx: {
					const InstL* ch = e->get_children();
					InstL::const_iterator ve_it = ch->begin();
					int ex_offset = (*ve_it)->get_size()-1;
					++ve_it;
					int idx_size = (*ve_it)->get_size();
					
// 					cout << "ex_offset: " << ex_offset << endl;
// 					cout << "idx_size: " << idx_size << endl;
					
					z3_expr& a = term(*it);
					z3_expr& b = term(*it2);

					z3_expr_ptr els = new z3_expr(*g_ctx);
					z3_expr_ptr thn = new z3_expr(*g_ctx);
					*els = a.extract(ex_offset, ex_offset);
					ex_offset--;
					*thn = a.extract(ex_offset, ex_offset);

					z3_expr_ptr num = new z3_expr(*g_ctx);
					z3_expr_ptr cond = new z3_expr(*g_ctx);
					*num = g_ctx->bv_val(ex_offset, idx_size);
					*cond = (b == term(num));
					z3_expr_ptr sExpr = new z3_expr(*g_ctx);
					*sExpr = ite(term(cond), term(thn), term(els));	// (sel == 30) ? rotate_30 : rotate_31

					for(; ex_offset >= 0; --ex_offset){
						*thn = a.extract(ex_offset, ex_offset);
						*num = g_ctx->bv_val(ex_offset, idx_size);
						*cond = (b == term(num));
						*sExpr = ite(term(cond), term(thn), term(sExpr));
					}
					res = sExpr;

					delete (els);
					delete (thn);
					delete (num);
					delete (cond);
				}
					break;
				default:
					assert(0);
				}
				for (auto& ptr: garbage)
					if (ptr)
						delete ptr;
			}
			else if (m_mapper->fetch_op(e) == TheoryMapper::EUF_OP || m_mapper->fetch_op(e) == TheoryMapper::CLU_OP) {
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
						res = yices_mk_sum(g_ctx, args, 2);
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
							res = yices_mk_sum(g_ctx, args, 2);
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
// 							res = yices_mk_sum(g_ctx, arguments, 2);
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
// 								arguments[1] = yices_mk_num(g_ctx, num->get_mpz());
// 								res = yices_mk_sum(g_ctx, arguments, 2);
// 								interpreted = true;
// 							} else if ((*cit)->get_type() == Num) {
// 								NumInst* num = NumInst::as(*cit);
// 								assert(num != 0);
// 								yices_expr arguments[2];
// 								arguments[1] = *it;
// 								arguments[0] = yices_mk_num(g_ctx, num->get_mpz());
// 								res = yices_mk_sum(g_ctx, arguments, 2);
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
						res = yices_mk_sub(g_ctx, args, 2);
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
							res = yices_mk_sub(g_ctx, args, 2);
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
//							arguments[1] = yices_mk_num(g_ctx, num->get_mpz()->get_si());
//							res = yices_mk_sub(g_ctx, arguments, 2);
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
			z3_expr_list::iterator it3 = it2;
			it3++;
			z3_expr& cond = term(*it);
			z3_expr& a = term(*it2);
			z3_expr& b = term(*it3);

			z3_expr_ptr sExpr = new z3_expr(*g_ctx);
			if (cond.is_bv())
				*sExpr = ite((cond == term(m_v1)), a, b);
			else
				*sExpr = ite(cond, a, b);

			res = sExpr;
			interpreted = true;

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
//					z3_expr& a = *(simplified->z3_node.solv_var[get_vIdx()]);
//					z3_expr_ptr ptr = new z3_expr(*g_ctx);
//					add_ptr(ptr);
//					*ptr = (term(res) == a);
//					add_constraint(ptr, "partial interpretation of ternary with Ex/Cc", e);
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

			if (res->is_bv() && yvar->is_bool())
				*res = (term(res) == term(m_v1));

			if (!allow_flatten) {
        yvar = res;
				add_ptr(res);
      }
      else {
  			z3_expr_ptr ptr = new z3_expr(*g_ctx);
  			add_ptr(ptr);
  			*ptr = (term(yvar) == term(res));
  			add_constraint(ptr, "result of a bv op", e);
  			delete (res);
      }
		}
		else if (m_mapper->fetch_op(e) == TheoryMapper::EUF_OP || m_mapper->fetch_op(e) == TheoryMapper::CLU_OP) {
			if (interpreted) {
				assert(res);

				if (!allow_flatten) {
	        yvar = res;
					add_ptr(res);
	      }
	      else {
					z3_expr_ptr ptr = new z3_expr(*g_ctx);
					add_ptr(ptr);
					*ptr = (term(yvar) == term(res));
					add_constraint(ptr, "interpreted operator constraint for EUF", e);
					delete (res);
	      }
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
//							z3_expr& a = *(simplified->z3_node.solv_var[get_vIdx()]);
//							z3_expr_ptr ptr = new z3_expr(*g_ctx);
//							add_ptr(ptr);
//							*ptr = (term(yvar) == a);
//							add_constraint(ptr, "partial interpretation of Cc", e);
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
			z3_expr& a = *(y_ch.front());
			assert(a);
			z3_expr_ptr res = new z3_expr(*g_ctx);
			add_ptr(res);
			*res = a.extract(ex->get_hi(), ex->get_lo());
			if (term(yvar).is_bool())
				*res = (term(res) == term(m_v1));

			if (!allow_flatten) {
        yvar = res;
      }
      else {
				z3_expr_ptr ptr = new z3_expr(*g_ctx);
				add_ptr(ptr);
				*ptr = (term(yvar) == term(res));
				add_constraint(ptr, "result of a bv EX", e);
				delete (res);
      }
		}
		else if (m_mapper->fetch_op(e) == TheoryMapper::EUF_OP || m_mapper->fetch_op(e) == TheoryMapper::CLU_OP) {
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
//	//				inst2yices(simplified);
//	//				yices_expr tmp = yices_eq(yvar, simplified->yvar[m_ba_idx]);
//	//				if (tmp == -1)
//	//				{
//	//					cout << "Asserting " << *e << " == " << *simplified << endl;
//	//					cout << yvar << "  " << print_term(yvar) << endl;
//	//					cout << simplified->yvar[m_ba_idx] << "  " << print_term(simplified->yvar[m_ba_idx]) << endl;
//	//					assert(0);
//	//				}
//					z3_expr& a = *(simplified->z3_node.solv_var[get_vIdx()]);
//					z3_expr_ptr ptr = new z3_expr(*g_ctx);
//					add_ptr(ptr);
//					*ptr = (term(yvar) == a);
//					add_constraint(ptr, "partial interpretation of Ex", e);
//	//				cout << "Asserting " << *e << " == " << *simplified << endl;
//				}
//			}
////			stringstream str;
////			str << *e;
////			if (str.str() == "msr_output_edge_7_52422[1:1]" || str.str() == "state_hsn0vb3f_rpfcore0_doRpf_dpk_thread_reg.q[1:1]")
////			{
////				OpInst* opTmp = OpInst::as(e);
////				assert(opTmp);
////				cout << *opTmp << " -s-> " << *(opTmp->t_simple) << endl;
////				for (auto& c : e->y_constraints[yIdx])
////				{
////					cout << "\t\t" << print_term(c) << endl;
////				}
////			}
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
		 domains[i] = yices_mk_bitvector_type(g_ctx,ch_sz);
		 yices_type domain = yices_mk_bitvector_type(g_ctx,uf->get_size());
		 yices_type funct = yices_mk_function_type(g_ctx,domains,ch->size(),domain);
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
	//			cout << "Asserting " << *e << " == " << *simplified << endl;

	#ifdef INTERPRET_UF_NUM
				NumInst* num = NumInst::as(e);
				if (num) {
					if (e->get_size() != 1) {

						OpInst* opS = OpInst::as(simplified);
						assert(opS);
						assert(opS->get_op() == OpInst::Concat);

						z3_expr_vec tmp_constraints;
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
	#endif

	#ifdef INTERPRET_UF_SIG
				SigInst* sig = SigInst::as(e);
				if (sig) {
					if (e->get_size() != 1) {

						OpInst* opS = OpInst::as(simplified);
						assert(opS);
						assert(opS->get_op() == OpInst::Concat);

						z3_expr_vec tmp_constraints;
						swap(tmp_constraints, m_constraints);

						inst2yices(simplified);
	//					for (int i = 0; i < sig->get_size(); i++) {
	//						Inst* ex = ExInst::create(sig, i, i);
	//						inst2yices(ex);
	//					}

						swap(tmp_constraints, m_constraints);
						for (auto& c: tmp_constraints)
							add_constraint(c, "(partial interpretation)", e);
					}
				}
	#endif

				{
					z3_expr& a = *(simplified->z3_node.solv_var(get_vIdx()));
					z3_expr_ptr ptr = new z3_expr(*g_ctx);
					add_ptr(ptr);
					*ptr = (term(yvar) == a);
					add_constraint(ptr, "(partial interpretation)", e);
				}
			}
		}
	}
#endif

//  	cout<< endl << "--gex--> " << *e << "\t" << print_term(yvar) << "\t" << print_term(e->yvar[m_ba_idx]) << endl;
}

};

#endif
