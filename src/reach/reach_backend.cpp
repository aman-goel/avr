/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


/*
 * reach_backend.cpp
 *
 *  Created on: Jun 26, 2017
 *      Author: rock
 */

/// Solver Backend (Shared constructs)
#include "reach_backend.h"

#ifdef _Y2
int Y2_INFO::st_y2_key = 1;
#endif
#ifdef _Z3
int Z3_INFO::st_z3_key = 1;
#endif
#ifdef _M5
int M5_INFO::st_m5_key = 1;
#endif
#ifdef _BT
int BT_INFO::st_bt_key = 1;
#endif

unordered_map<string, Inst*> Solver::m_nameToInst;
map< string, mpz_class > Solver::solv_values;
long long Solver::incremental_count = 0;

unsigned Solver::st_solver_id = 1;

bool Solver::s_check_timed_out = false;

int Solver::num_scalls_sat = 0;
int Solver::num_scalls_unsat = 0;
int Solver::num_scalls_timeout = 0;

int Solver::num_scalls_sat_fp = 0;
int Solver::num_scalls_unsat_fp = 0;
int Solver::num_scalls_sat_fp_non_accum = 0;
int Solver::num_scalls_unsat_fp_non_accum = 0;
int Solver::num_scalls_contained_fp_non_accum = 0;

/// Solver stats
int Solver::num_ab_sat_oneshot = 0;
int Solver::num_ab_unsat_oneshot = 0;
int Solver::num_ab_sat_inc = 0;
int Solver::num_ab_unsat_inc = 0;
int Solver::num_ab_sat_mus = 0;
int Solver::num_ab_unsat_mus = 0;

int Solver::num_bv_sat_oneshot = 0;
int Solver::num_bv_unsat_oneshot = 0;
int Solver::num_bv_sat_inc = 0;
int Solver::num_bv_unsat_inc = 0;
int Solver::num_bv_sat_mus = 0;
int Solver::num_bv_unsat_mus = 0;

int Solver::num_ab_timeout = 0;
int Solver::num_bv_timeout = 0;

int Solver::num_ab_muses_calls = 0;
int Solver::num_bv_muses_calls = 0;
unsigned long long Solver::total_sz_ab_muses_input = 0;
unsigned long long Solver::total_sz_bv_muses_input = 0;
int Solver::max_sz_ab_muses_input = 0;
int Solver::max_sz_bv_muses_input = 0;

int Solver::total_itr_ab_muses_input = 0;
int Solver::total_itr_bv_muses_input = 0;

int Solver::num_ab_mus_core = 0;
int Solver::num_bv_mus_core = 0;
unsigned long long Solver::total_sz_ab_core = 0;
unsigned long long Solver::total_sz_bv_core = 0;
int Solver::max_sz_ab_core = 0;
int Solver::max_sz_bv_core = 0;

int Solver::num_ab_query = 0;
int Solver::num_bv_query = 0;
unsigned long long Solver::total_sz_ab_query = 0;
unsigned long long Solver::total_sz_bv_query = 0;
int Solver::max_sz_ab_query = 0;
int Solver::max_sz_bv_query = 0;

long long Solver::time_ab_sat_oneshot = 0;
long long Solver::time_ab_unsat_oneshot = 0;
long long Solver::time_ab_sat_inc = 0;
long long Solver::time_ab_unsat_inc = 0;
long long Solver::time_ab_sat_mus = 0;
long long Solver::time_ab_unsat_mus = 0;
long long Solver::time_ab_timeout = 0;

long long Solver::time_bv_sat_oneshot = 0;
long long Solver::time_bv_unsat_oneshot = 0;
long long Solver::time_bv_sat_inc = 0;
long long Solver::time_bv_unsat_inc = 0;
long long Solver::time_bv_sat_mus = 0;
long long Solver::time_bv_unsat_mus = 0;
long long Solver::time_bv_timeout = 0;

long long Solver::time_max_ab_query = 0;
long long Solver::time_max_bv_query = 0;
long long Solver::time_max_ab_mus_query = 0;
long long Solver::time_max_bv_mus_query = 0;

long long Solver::time_sat_core_muses_reach = 0;
long long Solver::time_unsat_core_muses_reach = 0;
long long Solver::time_sat_core2_muses_reach = 0;
long long Solver::time_unsat_core2_muses_reach = 0;
long long Solver::time_sat_min_muses_reach = 0;
long long Solver::time_unsat_min_muses_reach = 0;

long long Solver::time_max_sat_core_muses_reach = 0;
long long Solver::time_max_unsat_core_muses_reach = 0;
long long Solver::time_max_sat_core2_muses_reach = 0;
long long Solver::time_max_unsat_core2_muses_reach = 0;
long long Solver::time_max_sat_min_muses_reach = 0;
long long Solver::time_max_unsat_min_muses_reach = 0;

int Solver::num_scalls_sat_core2_muses_reach = 0;
int Solver::num_scalls_unsat_core2_muses_reach = 0;
long long Solver::core1_size = 0;

long long Solver::time_ccext = 0;
long long Solver::time_tmp = 0;

map < string, SOLVER_STAT > Solver::g_solver_stats;

void Solver::add_var(string var, bool predicate, unsigned bv_sz) {
	Ints l;
	l.push_back(bv_sz);
	m_var_defs.insert(make_pair(var, make_pair(predicate, l)));
}

void Solver::add_bvop(string var, string op, bool is_bool, SMTBAL&ch, unsigned sz) {
	ostringstream str;
	if (is_bool)
		str << "f";
	str << "let (" << var << " (";
	if (op == "/=")
		str << "not (=";
	else if (op == "bvredor")
		str << "= (extract[" << sz - 1 << ":0] bv1)";
	else
		str << op;
	for (SMTBAL::iterator it = ch.begin(), end_it = ch.end(); it != end_it; ++it)
		str << " " << *it;
	str << "))";
	if (op == "/=")
		str << ")";
	m_smt_defs.push_back(str.str());
}

void Solver::add_func(string var, string op, bool interpreted, bool predicate, SMTBAL& ch, Ints& sz) {
	if (!interpreted) {
		ostringstream str;
		str << op;
		for (Ints::iterator it = sz.begin(), end_it = sz.end(); it != end_it; ++it) {
			str << "_" << *it;
		}
		op = str.str();
		m_var_defs.insert(make_pair(op, make_pair(predicate, sz)));
	}

	ostringstream str;
	if (predicate)
		str << "f";
	str << "let (" << var << " (" << op;
	for (SMTBAL::iterator it = ch.begin(), end_it = ch.end(); it != end_it; ++it)
		str << " " << *it;
	str << "))";
	m_smt_defs.push_back(str.str());
}

void Solver::add_const(string var, unsigned long long val, unsigned sz) {
	if (m_consts.find(var) != m_consts.end())
		return;
	ostringstream str;
	str << "let (" << var << " (extract[" << sz - 1 << ":0] bv" << val << "))";
	m_smt_defs.push_back(str.str());
	m_consts.insert(var);
}

string Solver::clean_str(string s) {
	string res;
	for (string::iterator it = s.begin(), end_it = s.end(); it != end_it; ++it)
		if (((*it) >= 'a' && (*it) <= 'z') || ((*it) >= 'A' && (*it) <= 'Z') || ((*it) >= '0' && (*it) <= '9') || (*it) == '_')
			res += *it;
		else
			res += "_";
	return res;
}

string Solver::val_to_str(unsigned long long val, unsigned sz, bool reversed) {
	string s;
	if (sz != 0) {
		for (unsigned i = 0; i < sz; i++) {
			if (reversed)
				s += (val % 2 == 0) ? "0" : "1";
			else
				s = string((val % 2 == 0) ? "0" : "1") + s;
			val /= 2;
		}
	} else {
		while (val > 0) {
			if (reversed)
				s += (val % 2 == 0) ? "0" : "1";
			else
				s = string((val % 2 == 0) ? "0" : "1") + s;
			val /= 2;
		}
	}
	return s;
}

string Solver::arr_to_str(int* val, unsigned sz) {
	string s;
// 	for (unsigned i = 0; i < sz; i++) {
// 		s += (val[i] == 0) ? "0" : "1";
// 	}
	for (unsigned i = 0; i < sz; i++) {
		s = ((val[i] == 0) ? "0" : "1") + s;
	}
	return s;
}

unsigned long long Solver::str_to_val(string s, bool reversed) {
	unsigned long long res = 0;
	if (reversed) {
		for (string::reverse_iterator it = s.rbegin(), end_it = s.rend(); it != end_it; ++it) {
			res = res * 2;
			res += (*it == '1') ? 1 : 0;
		}
	} else {
		for (string::iterator it = s.begin(), end_it = s.end(); it != end_it; ++it) {
			res = res * 2;
			res += (*it == '1') ? 1 : 0;
		}
	}
	return res;
}

void Solver::update_query_sz(void)
{
	if (m_abstract)
	{
		Solver::num_ab_query += 1;
		Solver::total_sz_ab_query += m_query_sz;
		if (m_query_sz > Solver::max_sz_ab_query)
			Solver::max_sz_ab_query = m_query_sz;
	}
	else
	{
		Solver::num_bv_query += 1;
		Solver::total_sz_bv_query += m_query_sz;
		if (m_query_sz > Solver::max_sz_bv_query)
			Solver::max_sz_bv_query = m_query_sz;
	}
}

void Solver::collect_stats_mus(unsigned uSz)
{
	if (m_abstract)
	{
		Solver::num_ab_mus_core += 1;
		Solver::total_sz_ab_core += uSz;
		if (uSz > Solver::max_sz_ab_core)
			Solver::max_sz_ab_core = uSz;
	}
	else
	{
		Solver::num_bv_mus_core += 1;
		Solver::total_sz_bv_core += uSz;
		if (uSz > Solver::max_sz_bv_core)
			Solver::max_sz_bv_core = uSz;
	}
}

void Solver::collect_stats_muses(unsigned sz)
{
	if (m_abstract)
	{
		Solver::num_ab_muses_calls += 1;
		Solver::total_sz_ab_muses_input += sz;
		if (sz > Solver::max_sz_ab_muses_input)
			Solver::max_sz_ab_muses_input = sz;
	}
	else
	{
		Solver::num_bv_muses_calls += 1;
		Solver::total_sz_bv_muses_input += sz;
		if (sz > Solver::max_sz_bv_muses_input)
			Solver::max_sz_bv_muses_input = sz;
	}
}

void Solver::print_query(long long time_diff, int mode, string suffix)
{
  string fname = m_mapper->get_theory_name() + "_";
  fname += (Config::g_ab_interpret?"ufbv_":"uf_") + _benchmark;

  string header = "";
#ifdef SMTCOMP
  header += "(set-info :smt-lib-version 2.6)\n";
#endif

  if (queryType == mus_core)
    header += "(set-option :produce-unsat-cores true)\n";

  header += "(set-logic " + m_mapper->get_theory_name() + ")\n";

  header += "(set-info :source |\n";
#ifdef SMTCOMP
  header += "Generated by: Aman Goel (amangoel@umich.edu), Karem A. Sakallah (karem@umich.edu)\n";
  header += "Generated on: 2018-04-06\n";
//  header += "Generator: Averroes 2\n";
//  header += "Application: Safety property verification of hardware systems\n";
  header += "\n";
  header += "Generated by the tool Averroes 2 (successor of [1]) which implements safety property\n";
  header += "verification on hardware systems.\n";
  header += "\n";
  header += "This SMT problem belongs to a set of SMT problems generated by applying Averroes 2\n";
  header += "to benchmarks derived from [2, 3, 4, 5].\n";
  header += "\n";
  header += "[1] Lee S., Sakallah K.A. (2014) Unbounded Scalable Verification Based on Approximate\n";
  header += "Property-Directed Reachability and Datapath Abstraction. In: Biere A., Bloem R. (eds)\n";
  header += "Computer Aided Verification. CAV 2014. Lecture Notes in Computer Science, vol 8559.\n";
  header += "Springer, Cham\n";
  header += "[2] Pelánek, Radek. \"BEEM: Benchmarks for explicit model checkers.\" International SPIN\n";
  header += "Workshop on Model Checking of Software. Springer, Berlin, Heidelberg, 2007.\n";
  header += "[3] http://www.cs.cmu.edu/~modelcheck/vcegar/\n";
  header += "[4] http://www.cprover.org/hardware/v2c/\n";
  header += "[5] http://github.com/aman-goel/verilogbench/\n";
#endif

  string avr_header = "\n";
  avr_header += "id: " + _benchmark + "\n";
  switch(fetch_solv_name())
  {
  case SMT_Yices2:
    avr_header += "query-maker: \"Yices 2\"\n";
    break;
  case SMT_Z3:
    avr_header += "query-maker: \"Z3\"\n";
    break;
  case SMT_MathSAT5:
    avr_header += "query-maker: \"MathSAT 5\"\n";
    break;
  }
  if (time_diff != -1)
    avr_header += "query-time: " + to_string(((double) time_diff) / 1000.0) + " ms\n";

  if (m_abstract)
  {
    fname += "_ab";
    avr_header += "query-class: abstract\n";
    switch (mode)
    {
      case(ONESHOT_SAT):
        avr_header += "query-category: oneshot\n";
      break;
      case(INC_SAT):
        avr_header += "query-category: incremental\n";
      break;
      case(MUS_SAT):
        avr_header += "query-category: assume\n";
      break;
      case(ONESHOT_UNSAT):
        avr_header += "query-category: oneshot\n";
      break;
      case(INC_UNSAT):
        avr_header += "query-category: incremental\n";
      break;
      case(MUS_UNSAT):
        avr_header += "query-category: assume\n";
      break;
      case(TIME_TO):
        avr_header += "query-category: timed_out\n";
      break;
      default:
        avr_header += "query-category: error\n";
    }
  }
  else
  {
    fname += "_cc";
    avr_header += "query-class: concrete\n";
    switch (mode)
    {
      case(ONESHOT_SAT):
        avr_header += "query-category: oneshot\n";
      break;
      case(INC_SAT):
        avr_header += "query-category: incremental\n";
      break;
      case(MUS_SAT):
        avr_header += "query-category: assume\n";
      break;
      case(ONESHOT_UNSAT):
        avr_header += "query-category: oneshot\n";
      break;
      case(INC_UNSAT):
        avr_header += "query-category: incremental\n";
      break;
      case(MUS_UNSAT):
        avr_header += "query-category: assume\n";
      break;
      case(TIME_TO):
        avr_header += "query-category: timed_out\n";
      break;
      default:
        avr_header += "query-category: error\n";
    }
  }
  switch (queryType)
  {
  case cti:
    avr_header += "query-type: cti\n";
    fname += "_cti";  break;
  case br:
    avr_header += "query-type: br\n";
    fname += "_br";  break;
  case fp:
    avr_header += "query-type: fp\n";
    fname += "_fp";  break;
  case mus_core:
    avr_header += "query-type: mus_core\n";
    fname += "_core";  break;
  case mus_min:
    avr_header += "query-type: mus_min\n";
    fname += "_min";  break;
  case conc:
    avr_header += "query-type: refine\n";
    fname += "_ref";  break;
  case regular:
    avr_header += "query-type: regular\n";
    fname += "_reg";  break;
  case mdl:
    avr_header += "query-type: mdl\n";
    fname += "_mdl";  break;
  }
  switch (mode)
  {
    case(ONESHOT_SAT):
    case(INC_SAT):
    case(MUS_SAT):
      avr_header += "status: sat\n";
    break;
    case(ONESHOT_UNSAT):
    case(INC_UNSAT):
    case(MUS_UNSAT):
      avr_header += "status: unsat\n";
    break;
    default:
      avr_header += "status: unknown\n";
  }
  avr_header += "mode: " + Config::g_abstraction_name + "\n";

  header += avr_header;
  header += "|)\n";

#ifdef SMTCOMP
  header += "(set-info :license \"https://creativecommons.org/licenses/by/4.0/\")\n";
  header += "(set-info :category \"industrial\")\n";
#endif
  header += "\n";

  if (suffix != "")
    fname += "_" + suffix;

  print_smt2(fname, header);
}

#ifdef TRACE_SOLVER
void Solver::print_trace(string suffix, bool iscore) {
  string fname = m_mapper->get_theory_name() + "_";
#ifdef TEST_ABSTRACT_BV
#ifdef TEST_ABSTRACT_BV_8
  fname += "bv8_";
#else
  fname += "bv_";
#endif
#endif
#ifdef TEST_ABSTRACT_BV
  fname += "bv_";
#endif
  fname += _benchmark;

  string header = "";
#ifdef SMTCOMP
  header += "(set-info :smt-lib-version 2.6)\n";
#endif

  if (iscore)
    header += "(set-option :produce-unsat-cores true)\n";

  header += "(set-logic " + m_mapper->get_theory_name() + ")\n";

  header += "(set-info :source |\n";
#ifdef SMTCOMP
  header += "Generated by: Aman Goel (amangoel@umich.edu), Karem A. Sakallah (karem@umich.edu)\n";
  header += "Generated on: 2018-04-06\n";
//  header += "Generator: Averroes 2\n";
//  header += "Application: Safety property verification of hardware systems\n";
  header += "\n";
  header += "Generated by the tool Averroes 2 (successor of [1]) which implements safety property\n";
  header += "verification on hardware systems.\n";
  header += "\n";
  header += "This SMT problem belongs to a set of SMT problems generated by applying Averroes 2\n";
  header += "to benchmarks derived from [2, 3, 4, 5].\n";
  header += "\n";
  header += "[1] Lee S., Sakallah K.A. (2014) Unbounded Scalable Verification Based on Approximate\n";
  header += "Property-Directed Reachability and Datapath Abstraction. In: Biere A., Bloem R. (eds)\n";
  header += "Computer Aided Verification. CAV 2014. Lecture Notes in Computer Science, vol 8559.\n";
  header += "Springer, Cham\n";
  header += "[2] Pelánek, Radek. \"BEEM: Benchmarks for explicit model checkers.\" International SPIN\n";
  header += "Workshop on Model Checking of Software. Springer, Berlin, Heidelberg, 2007.\n";
  header += "[3] http://www.cs.cmu.edu/~modelcheck/vcegar/\n";
  header += "[4] http://www.cprover.org/hardware/v2c/\n";
  header += "[5] http://github.com/aman-goel/verilogbench/\n";
#endif

  string avr_header = "\n";
  avr_header += "id: " + _benchmark + "\n";
  switch(fetch_solv_name())
  {
  case SMT_Yices2:
    avr_header += "query-maker: \"Yices 2\"\n";
    break;
  case SMT_Z3:
    avr_header += "query-maker: \"Z3\"\n";
    break;
  case SMT_MathSAT5:
    avr_header += "query-maker: \"MathSAT 5\"\n";
    break;
  }

  if (m_abstract)
  {
    fname += "_ab";
    avr_header += "query-class: abstract\n";
  }
  else
  {
    fname += "_cc";
    avr_header += "query-class: concrete\n";
  }
  switch (queryType)
  {
  case cti:
    avr_header += "query-type: cti\n";
    fname += "_cti";  break;
  case br:
    avr_header += "query-type: br\n";
    fname += "_br";  break;
  case fp:
    avr_header += "query-type: fp\n";
    fname += "_fp";  break;
  case mus_core:
    avr_header += "query-type: mus_core\n";
    fname += "_core";  break;
  case mus_min:
    avr_header += "query-type: mus_min\n";
    fname += "_min";  break;
  case conc:
    avr_header += "query-type: refine\n";
    fname += "_ref";  break;
  case regular:
    avr_header += "query-type: regular\n";
    fname += "_reg";  break;
  }
#ifdef TEST_ABSTRACT_BV
#ifdef TEST_ABSTRACT_BV_8
  avr_header += "mode: abstract_bv8\n";
#else
  avr_header += "mode: abstract_bv\n";
#endif
#endif

  header += avr_header;
  header += "|)\n";

#ifdef SMTCOMP
  header += "(set-info :license \"https://creativecommons.org/licenses/by/4.0/\")\n";
  header += "(set-info :category \"industrial\")\n";
#endif
  header += "\n";

  if (suffix != "")
    fname += "_" + suffix;

	fname = QUERY_PATH + m_mapper->get_theory_name() + "/" + fname + "_trace.smt2";
	ofstream f;
	f.open(fname.c_str());

  if (header != "")
    f << header;
  f << ";\n";
  f << "(set-info :status unknown)\n";

  process_trace(f);
  for (auto& i: m_trace)
  	f << i << "\n";

}
#endif

void Solver::update_query_time(double time_res, int mode)
{
  long long int* curr;
  if (m_abstract)
  {
    switch (mode)
    {
      case(ONESHOT_SAT):
      case(INC_SAT):
        curr = &Solver::time_max_ab_query;
      break;
      case(MUS_SAT):
        curr = &Solver::time_max_ab_mus_query;
      break;
      case(ONESHOT_UNSAT):
      case(INC_UNSAT):
        curr = &Solver::time_max_ab_query;
      break;
      case(MUS_UNSAT):
        curr = &Solver::time_max_ab_query;
      break;
      case(TIME_TO):
        curr = &Solver::time_max_ab_mus_query;
      break;
      default:
        assert(0);
    }
  }
  else
  {
    switch (mode)
    {
      case(ONESHOT_SAT):
      case(INC_SAT):
        curr = &Solver::time_max_bv_query;
      break;
      case(MUS_SAT):
        curr = &Solver::time_max_bv_mus_query;
      break;
      case(ONESHOT_UNSAT):
      case(INC_UNSAT):
        curr = &Solver::time_max_bv_query;
      break;
      case(MUS_UNSAT):
        curr = &Solver::time_max_bv_query;
      break;
      case(TIME_TO):
        curr = &Solver::time_max_bv_mus_query;
      break;
      default:
        assert(0);
    }
  }

//  if (m_abstract && (queryType == cti) && (Solver::num_ab_query < 5))
//    print_query(time_res, mode, to_string(Solver::num_ab_query));
  if (time_res > (*curr))
  {
    (*curr) = time_res;
#ifdef DUMP_LONGEST_QUERY
    if (mode == TIME_TO)
      print_query(time_res, mode, "to");
    else
      print_query(time_res, mode, "max");
#endif
//    cout << "max time " << time_res << endl;
  }
//  cout << "query time " << time_res << endl;

  collect_solver_stats();
}

void Solver::collect_stats_query(long long time_res, int mode)
{
  update_query_time(time_res, mode);

//	if (mode != TIME_TO)
//		update_query_sz();

	if (m_abstract)
	{
		switch (mode)
		{
			case(ONESHOT_SAT):
			{
				num_ab_sat_oneshot++;
				time_ab_sat_oneshot += time_res;
				num_scalls_sat++;
			}
			break;
			case(INC_SAT):
			{
				num_ab_sat_inc++;
				time_ab_sat_inc += time_res;
				num_scalls_sat++;
			}
			break;
			case(MUS_SAT):
			{
				num_ab_sat_mus++;
				time_ab_sat_mus += time_res;
				num_scalls_sat++;
			}
			break;
			case(ONESHOT_UNSAT):
			{
				num_ab_unsat_oneshot++;
				time_ab_unsat_oneshot += time_res;
				num_scalls_unsat++;
			}
			break;
			case(INC_UNSAT):
			{
				num_ab_unsat_inc++;
				time_ab_unsat_inc += time_res;
				num_scalls_unsat++;
			}
			break;
			case(MUS_UNSAT):
			{
				num_ab_unsat_mus++;
				time_ab_unsat_mus += time_res;
				num_scalls_unsat++;
			}
			break;
			case(TIME_TO):
			{
				num_ab_timeout++;
				time_ab_timeout += time_res;
				num_scalls_timeout++;
			}
			break;
			default:
				assert(0);
		}
	}
	else
	{
		switch (mode)
		{
			case(ONESHOT_SAT):
			{
				num_bv_sat_oneshot++;
				time_bv_sat_oneshot += time_res;
				num_scalls_sat++;
			}
			break;
			case(INC_SAT):
			{
				num_bv_sat_inc++;
				time_bv_sat_inc += time_res;
				num_scalls_sat++;
			}
			break;
			case(MUS_SAT):
			{
				num_bv_sat_mus++;
				time_bv_sat_mus += time_res;
				num_scalls_sat++;
			}
			break;
			case(ONESHOT_UNSAT):
			{
				num_bv_unsat_oneshot++;
				time_bv_unsat_oneshot += time_res;
				num_scalls_unsat++;
			}
			break;
			case(INC_UNSAT):
			{
				num_bv_unsat_inc++;
				time_bv_unsat_inc += time_res;
				num_scalls_unsat++;
			}
			break;
			case(MUS_UNSAT):
			{
				num_bv_unsat_mus++;
				time_bv_unsat_mus += time_res;
				num_scalls_unsat++;
			}
			break;
			case(TIME_TO):
			{
				num_bv_timeout++;
				time_bv_timeout += time_res;
				num_scalls_timeout++;
			}
			break;
			default:
				assert(0);
		}
	}
}

void Solver::print_asserts(string comment, int loc, int level)
{
	//	return;
#ifndef PERFORMANCE_NOPRINT

	AVR_LOG(loc, level, "\n\t(assert list: " << comment << ")" << endl);
	AVR_LOG(loc, level, "\t\t(# buckets)     " << m_asserts.assertions.size() << endl);

	if (!m_asserts.assumptions.empty())
	{
		AVR_LOG(loc, level, "\t\t(# assumptions) " << m_asserts.assumptions.size() << endl);
		for (auto& tve : m_asserts.assumptions)
		{
			AVR_LOG(loc, level, "\t\t\t" << *tve << endl);
		}
		AVR_LOG(loc, level, endl);
	}

	AVR_LOG(loc, level, "\t\t(assertions)" << endl);
	int idx = 0;
	for (auto& l : m_asserts.assertions)
	{
		idx++;
		AVR_LOG(loc, level, "\t\t#" << idx << endl);
		for (auto& tve : l)
		{
			if (OpInst::as(tve) && OpInst::as(tve)->get_op() == OpInst::LogAnd)
			{
				for (auto& chTve : *(tve->get_children()))
				{
					AVR_LOG(loc, level, "\t\t\t" << *chTve << endl);
				}
			}
			else
			{
				AVR_LOG(loc, level, "\t\t\t" << *tve << endl);
			}
		}
		AVR_LOG(loc, level, endl);
	}
	AVR_LOG(loc, level, endl);
#endif
}

void Solver::add_assert(Inst* e)
{
	m_asserts.assertions.back().push_back(e);
}

void Solver::add_assume(Inst* e)
{
	m_asserts.assumptions.push_back(e);
}
void Solver::add_assume_front(Inst* e)
{
	m_asserts.assumptions.push_front(e);
}

void Solver::push_assert(void)
{
	m_asserts.assertions.push_back(InstL());
}

void Solver::pop_assert(void)
{
	m_asserts.assertions.pop_back();
}

void Solver::clear_assume(void)
{
	m_asserts.assumptions.clear();
}

void Solver::pop_assume(void)
{
	m_asserts.assumptions.pop_back();
}

void Solver::copy_asserts(ASSERT_LIST& in)
{
	m_asserts.assertions = in.assertions;
	m_asserts.assumptions = in.assumptions;
}

