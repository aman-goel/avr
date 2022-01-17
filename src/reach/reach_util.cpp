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

bool CompareConstant (int i,int j) { return (i<j); }

bool CompareBySz (Inst *first, Inst *second) {
	if (first->get_size() == second->get_size())
	{
		return !(first->get_id() < second->get_id());
	}
	else
		return first->get_size() < second->get_size();
}

bool Reach::add_lazy_assumes(InstToBoolM& dp_lemmas) {
	bool modified = false;
	if (Config::g_lazy_assume > LAZY_ASSUME_NONE) {
		InstToBoolM new_dp_lemmas;
		for (auto& r: dp_lemmas) {
			Inst* ref = r.first;
			bool rhs = r.second;
			bool addedAssume = false;

			collect_cubes(ref, true);
			for (auto& v: _collected_cubes) {
				bool added = false;
				if (Config::g_lazy_assume >= LAZY_ASSUME_L1) {
					InstToBoolM::iterator ait2 = _assume_T.find(v);
					if (ait2 != _assume_T.end()) {
						if (!(*ait2).second) {
							(*ait2).second = true;
							new_dp_lemmas[OpInst::create(OpInst::LogNot, v)] = rhs;
							AVR_LOG(15, 0, "\t(adding assumption cone: " << *v << ")\n");
							added = true;
						}
					}
				}

				if (!added) {
					if (Config::g_lazy_assume >= LAZY_ASSUME_L2) {
						InstToBoolM::iterator ait = _all_assumptions.find(v);
						if (ait != _all_assumptions.end()) {
							if (!(*ait).second) {
								(*ait).second = true;
								new_dp_lemmas[OpInst::create(OpInst::LogNot, v)] = rhs;
								AVR_LOG(15, 0, "\t(adding assumption: " << *v << ")\n");
								added = true;
							}
						}
					}
				}

				addedAssume |= added;
			}
			if (!addedAssume)
				new_dp_lemmas[ref] = rhs;

			modified |= addedAssume;
		}
		if (modified)
			swap(dp_lemmas, new_dp_lemmas);
	}
	return modified;
}

bool Reach::add_refinement(Inst *tve, string comment, bool simplificationAllowed)
{
	bool status = false;
	Inst* ref = OpInst::create(OpInst::LogNot, tve);

//	collect_cubes(ref, true);
//	for (auto& v: _collected_cubes)
//		v->coi.set_req_pred();

	AVR_REF("(#" << _negated_refs.size() << ")\t\t" << *tve << "\n");

#ifndef SUBSTITUTE
	pair< Inst*, Inst* > new_ref = reduce_ref(ref);
	Inst* new_tve = OpInst::create(OpInst::LogNot, new_ref.first);
	Inst* new_subtve = OpInst::create(OpInst::LogNot, new_ref.second);

	if (new_subtve != new_tve)
	{
#ifndef PERFORMANCE_NODRAW
		if (Config::g_print_dot[DRAW_REFINEMENT] != '0') {
			{
				ostringstream ostr;
				if (comment != "")
					 ostr << comment << "_";
				ostr << "ref/" << _negated_refs.size() << "_#_orig_" << new_tve->get_id();
				draw_graph(1, tve, ostr.str(), 0, false);
			}
			if (new_tve != new_subtve)
			{
				ostringstream ostr;
				if (comment != "")
					 ostr << comment << "_";
				ostr << "ref/" << _negated_refs.size() << "_#_subs_" << new_tve->get_id();
				draw_graph(1, new_subtve, ostr.str(), 0, false);
			}
		}
#endif

#ifdef PRINT_SIMPLIFIED_LEMMAS
    AVR_LOG(15, 2, "\t\t\t(simplified: " << *new_subtve << ")" << endl);
    AVR_REF("\t(sub.)\t" << *new_subtve << "\n");
#endif

//		status |= add_single_refinement(new_subtve);
	}
	else
	  new_subtve = new_tve;

	tve = new_tve;
//	tve = new_subtve;

  cout << "#" << tve->get_id() << endl;

	AVR_REF("\t(id)\t" << tve->get_id() << "\n");
	if (comment != "")
	  AVR_REF("\t(comment)\t" << comment << "\n");
	int numConst = 0;
	int numCF = 0;
	int numUF = 0;
	int numMux = 0;
	int numCc = 0;
	int numEx = 0;
	map< string, int > ufType, ccType, exType;
	InstS constants;
	InstS regs, inps;
	collect_func_stat(new_subtve, numConst, numCF, numUF, numMux, numCc, numEx, ufType, ccType, exType, constants, regs, inps, true);

	AVR_REF("\t(#UF )\t" << numUF << endl);
	AVR_REF("\t(#UFt)\t" << ufType.size() << endl);
	for (map< string, int >::iterator it = ufType.begin(); it != ufType.end(); it++)
	{
		AVR_REF("\t      \t" << (*it).first << "\t#" << (*it).second << endl);
	}
	AVR_REF("\t(#K  )\t" << numConst << endl);
//	for (auto& k: constants)
//	{
//		AVR_REF("\t      \t" << *k << endl);
//	}
	AVR_REF("\t(#reg)\t" << regs.size() << endl);
	AVR_REF("\t(#inp)\t" << inps.size() << endl);
//	for (auto& k: sigs)
//	{
//		AVR_REF("\t      \t" << *k << endl);
//	}
	AVR_REF("\t(#ite)\t" << numMux << endl);
	AVR_REF("\t(#CF )\t" << numCF << endl);

	AVR_REF("\t(#Cc )\t" << numCc << endl);
	AVR_REF("\t(#Cct)\t" << ccType.size() << endl);
//	for (map< string, int >::iterator it = ccType.begin(); it != ccType.end(); it++)
//	{
//		AVR_REF("\t      \t" << (*it).first << "\t#" << (*it).second << endl);
//	}
	AVR_REF("\t(#Ex )\t" << numEx << endl);
	AVR_REF("\t(#Ext)\t" << exType.size() << endl);
//	for (map< string, int >::iterator it = exType.begin(); it != exType.end(); it++)
//	{
//		AVR_REF("\t      \t" << (*it).first << "\t#" << (*it).second << endl);
//	}

	AVR_REF(endl);

#ifndef PERFORMANCE_NODRAW
	if (Config::g_print_dot[DRAW_REFINEMENT] != '0') {
		Inst::inc_dckey();
		Inst* tveNeg = OpInst::create(OpInst::LogNot, tve);
		tveNeg->set_hlVal(true);
		collect_cubes(tveNeg, true);
		for (auto& parent: _collected_cubes)
		{
			parent->set_hlVal(true);
			const InstL* children = parent->get_children();
			if (children)
			{
				for (auto& child: (*children))
				{
					child->set_hlVal(true);
					WireInst* w = WireInst::as(child);
					if (w)
						w->get_port()->set_hlVal(true);
				}
			}
		}
		tve->set_hlVal(true);
	}
#endif

#endif

#ifndef PERFORMANCE_NODRAW
	if (Config::g_print_dot[DRAW_REFINEMENT] != '0') {
		ostringstream ostr;
		if (comment != "")
			 ostr << comment << "_";
		ostr << "ref/" << _negated_refs.size() << "_#" << tve->get_id();
	#ifndef SUBSTITUTE
		draw_graph(1, tve, ostr.str(), 0, true);
	#else
		draw_graph(1, tve, ostr.str(), 0, false);
	#endif
	}
#endif

//	if (comment != "ab" && ufType.size() == 0) {
//		cout << "\t(error: expected a UF in cc. refinement)" << endl;
//		assert(0);
//	}

	status |= add_single_refinement(tve);
	return status;
}

bool Reach::add_single_refinement(Inst *tve)
{
	if (find(_negated_refs.begin(), _negated_refs.end(), tve) != _negated_refs.end())
		return false;
	else
	{
		_numRefinements++;

//		{
//			InstL conjunct_check;
//			Inst* ref = OpInst::create(OpInst::LogNot, tve);
//			conjunct_check.push_back(ref);
//
//			SOLVER_BV bv_solver(_concrete_mapper, AVR_EXTRA_IDX, false, regular);
//			bv_solver.assert_all_wire_constraints();
//
//			AVR_LOG(8, 5, "Checking Q:" << conjunct_check);
//			Inst* ve_check = OpInst::create(OpInst::LogAnd, conjunct_check);
//			bool res = bv_solver.check_sat(ve_check, 0, false);
//
//			if(res)
//			{
//				AVR_LOG(8, 0, "There is a wrong refinement lemma!!!" << endl);
//				cout << "Ref: (id: " << tve->get_id() << ") " << *tve << endl;
//				cout << "Check Q: " << conjunct_check << endl;
//				assert(0);
//			}
//		}

		_negated_refs.push_back(tve);
		for (vector<FRAME_SOLVER>::iterator rs_it = _reach_solvers.begin(); rs_it != _reach_solvers.end(); rs_it++)
		{
			if (rs_it->solver_main) {
				(rs_it->solver_main)->s_assert(tve);
			}
#ifdef FRAME_SOLVER_MULTI
			if (rs_it->solver1) {
				(rs_it->solver1)->s_assert(tve);
			}
#endif
		}
		if (_cti_solver)
			_cti_solver->s_assert(tve);
		return true;
	}
}

void Reach::collect_sig(Inst *top, InstS& s, bool init_visit)
{
	if (init_visit) {
		Inst::init_visit2();
	}
	if (top->get_visit2()) {
		return;
	}
	top->set_visit2();

//	cout << "top: " << *top << endl;

	const InstL* ch = top->get_children();
	if (ch)
	{
		for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it)
		{
			Inst * tve = *it;
			collect_sig(tve, s, false);
		}
	}
	else
	{
		SigInst* sig = SigInst::as(top);
		if (sig)
		{
			s.insert(sig);
		}
	}
}

void Reach::collect_wire(Inst *top, InstS& s, bool init_visit)
{
	if (init_visit) {
		Inst::init_visit();
	}
	if (top->get_visit()) {
		return;
	}
	top->set_visit();

//	cout << "top: " << *top << endl;

//	if (!top->childrenInfo[WIRE])
//		return;

	const InstL* ch = top->get_children();
	if (ch)
	{
		for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it)
		{
			Inst * tve = *it;
			collect_wire(tve, s, false);
		}
	}

	WireInst* w = WireInst::as(top);
	if (w)
	{
		s.insert(w);
	}
}

void Reach::collect_const(Inst *top, InstS& s, bool init_visit)
{
	if (init_visit) {
		Inst::init_visit();
	}
	if (top->get_visit()) {
		return;
	}
	top->set_visit();

//	cout << "top: " << *top << endl;

  const InstL* ch = top->get_children();
  if (ch)
  {
    for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it)
    {
      Inst * tve = *it;
      collect_const(tve, s, false);
//      collect_sig(tve, s, false);
    }
  }
	else
	{
		ConstInst* c = ConstInst::as(top);
		if (c)
		{
			s.insert(c);
		}
	}
}

Inst* Reach::replace_constant_with_value(Inst *top) {
  Inst* topRet = top;

  const InstL* ch = top->get_children();
  if (ch)
  {
    InstL new_ch;
    bool need_new = false;

    for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it)
    {
      Inst* newCh = replace_constant_with_value((*it));
      if (newCh != (*it))
      {
        need_new = true;
      }
      new_ch.push_back(newCh);
    }
    if (need_new)
    {
      topRet = top->apply_children(new_ch);
    }
  }
  else
  {
    ConstInst* c = ConstInst::as(top);
    if (c)
    {
  		Inst* num;
    	if (c->get_sort_type() == arraytype) {
    		if (c->get_sort_domain()->type == bvtype && c->get_sort_range()->type == bvtype) {
					string value = top->get_ival()->get_str(2);
					while (value.length() < c->get_size())
						value = "0" + value;

					int width = c->get_sort_domain()->sz;
					int size = c->get_size();
					assert(size == c->get_sort_range()->sz);

					Inst* wI = NumInst::create(width, 32, SORT());
					Inst* dI = NumInst::create(value, size, 2, SORT());
					num = OpInst::create(OpInst::ArrayConst, wI, dI);
    		}
    		else {
    			num = c->get_parent();
    			AVR_LOG(15, 0, "\t\t\t\t\t(using parent " << *num << " to instantiate array: " << *top << ")" << endl);
//    			assert(0);
    		}
    	}
    	else {
        if (top->get_size() == 1)
          num = NumInst::create(top->get_bval(), 1, SORT());
        else
          num = NumInst::create(*top->get_ival(), top->get_size(), top->get_sort());
    	}
			topRet = num;
			AVR_LOG(15, 0, "\t\t\t\t(instantiating symbolic value)\t" << *top << "\t:=\t" << *num << endl);
//        if (top->get_size() > 4) {
//          AVR_LOG(15, 0, "\t\t\t(error: symbolic value too wide for instantiation)\t" << *top << endl);
//          assert(0);
//        }
    }
  }
//  cout << *top << " -> " << *topRet << endl;
  return topRet;
}

Inst* Reach::replace_constant_with_parent(Inst *top, InstToInstM& valMap, bool init_visit) {
  if (init_visit) {
	  Inst::init_visit3();
  }
  if (top->get_visit3()) {
	return top->acex_coi;
  }
  top->set_visit3();

  Inst* topRet = top;

  const InstL* ch = top->get_children();
  if (ch)
  {
    InstL new_ch;
    bool need_new = false;

    for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it)
    {
      Inst* newCh = replace_constant_with_parent((*it), valMap);
      if (newCh != (*it))
      {
        need_new = true;
      }
      new_ch.push_back(newCh);
    }
    if (need_new)
    {
      topRet = top->apply_children(new_ch);
      OpInst* opRet = OpInst::as(topRet);
      if (opRet) {
      	Inst* w = opRet->get_wire();
      	if (w)
      		topRet = w;
      }
    }
  }
  else
  {
    ConstInst* c = ConstInst::as(top);
    if (c)
    {
        topRet = c->get_parent();
        AVR_LOG(15, 0, "\t\t\t\t(symbolic value parent)\t" << *top << "\t:=\t" << *topRet << endl);
    }
    else if (top->get_type() == Num) {
    	InstToInstM::iterator mit = valMap.find(top);
    	if (mit != valMap.end()) {
  			topRet = (*mit).second;
  			AVR_LOG(15, 0, "\t\t\t\t(number value parent)\t" << *top << "\t:=\t" << *topRet << endl);
    	}
//    	else if (top->get_sort_type() == inttype){
//    		NumInst* n = NumInst::as(top);
//    		if (n->get_num() < 0) {
//  				string snum = NumInst::as(n)->get_mpz()->get_str(10);
//  				assert (snum[0] == '-');
//  				snum = snum.substr(1);
//  				Inst* new_n = NumInst::create(snum, n->get_size(), 10, n->get_sort());
//  		  	InstToInstM::iterator mit2 = valMap.find(new_n);
//  		  	if (mit2 != valMap.end()) {
//  					topRet = OpInst::create(OpInst::IntMinus, (*mit2).second);
//  					AVR_LOG(15, 0, "\t\t\t\t(number value parent)\t" << *top << "\t:=\t" << *topRet << endl);
//  		  	}
//    		}
//    	}
    }
  }
  assert(topRet);
//  cout << *top << " -> " << *topRet << endl;
  top->acex_coi = topRet;
  return topRet;
}

Inst* Reach::replace_constant_with_all_parent(Inst *top, int& idx, list< pair< Inst*, pair< int, Inst* > > >& l, InstToInstM& valMap, bool init_visit) {
  if (init_visit) {
    Inst::init_visit3();
  }
  if (top->get_visit3()) {
	return top->acex_coi;
  }
  top->set_visit3();

  Inst* topRet = top;

  const InstL* ch = top->get_children();
  if (ch)
  {
    InstL new_ch;
    bool need_new = false;

    for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it)
    {
      Inst* newCh = replace_constant_with_all_parent((*it), idx, l, valMap);
      if (newCh != (*it))
      {
        need_new = true;
      }
      new_ch.push_back(newCh);
    }
    if (need_new)
    {
      topRet = top->apply_children(new_ch);
      OpInst* opRet = OpInst::as(topRet);
      if (opRet) {
      	Inst* w = opRet->get_wire();
      	if (w)
      		topRet = w;
      }
    }
  }
//  else
//  {
//    ConstInst* c = ConstInst::as(top);
//    if (c)
//    {
//        pair< int, Inst* > p = c->pop_parent(idx);
//        idx = p.first;
//        topRet = p.second;
//        if (!topRet->childrenInfo[CONST]) {
//        	AVR_LOG(15, 0, "\t\t\t\t(symbolic value parent) @" << idx << "\t" << *top << "\t:=\t" << *topRet << endl);
//        }
//    }
//  }

  if (topRet->childrenInfo[CONST] && !topRet->find_sig()) {
    pair< int, Inst* > p = topRet->pop_parent(idx);
    idx = p.first;

    if (idx != -1 && topRet != p.second)
    	l.push_back(make_pair(topRet, p));

    topRet = p.second;
    if (!topRet->childrenInfo[CONST]) {
    	AVR_LOG(15, 0, "\t\t\t\t(symbolic value parent) @" << idx << "\t" << *top << "\t:=\t" << *topRet << endl);
    }
  }
  else if (topRet->get_type() == Num) {
  	InstToInstM::iterator mit = valMap.find(topRet);
  	if (mit != valMap.end()) {
			topRet = (*mit).second;
			AVR_LOG(15, 0, "\t\t\t\t(number value parent all)\t" << *top << "\t:=\t" << *topRet << endl);
  	}
//  	else if (topRet->get_sort_type() == inttype){
//  		NumInst* n = NumInst::as(topRet);
//  		if (n->get_num() < 0) {
//				string snum = NumInst::as(n)->get_mpz()->get_str(10);
//				assert (snum[0] == '-');
//				snum = snum.substr(1);
//				Inst* new_n = NumInst::create(snum, n->get_size(), 10, n->get_sort());
//		  	InstToInstM::iterator mit2 = valMap.find(new_n);
//		  	if (mit2 != valMap.end()) {
//					topRet = OpInst::create(OpInst::IntMinus, (*mit2).second);
//					AVR_LOG(15, 0, "\t\t\t\t(number value parent)\t" << *top << "\t:=\t" << *topRet << endl);
//		  	}
//  		}
//  	}
  }

//  cout << *top << " -> " << *topRet << endl;
  top->acex_coi = topRet;
  return topRet;
}


Inst* Reach::replace_with_constant(Inst *top, InstToInstM& sigMap, int pIdx)
{
//	cout << "top: " << *top << endl;

	Inst* topRet = top;

	const InstL* ch = top->get_children();
	if (ch)
	{
		InstL new_ch;
		bool need_new = false;

		for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it)
		{
			Inst* newCh = replace_with_constant((*it), sigMap, pIdx);
			if (newCh != (*it))
			{
				need_new = true;
			}
			new_ch.push_back(newCh);
		}
		if (need_new)
		{
			topRet = top->apply_children(new_ch);
		}
	}
	else
	{
		SigInst* sig = SigInst::as(top);
		if (sig)
		{
			assert (Inst::_s_inp.find(sig) != Inst::_s_inp.end());
			InstToInstM::iterator vit = sigMap.find(sig);
			if (vit != sigMap.end())
			{
				topRet = (*vit).second;
			}
			else
			{
				stringstream cName;
				int sz = sig->get_size();
				cName << sig->get_sort().sort2str() << "_" << sz << "'d*_" << ConstInst::hm_ConstInst.size();
				Inst* c = ConstInst::create(cName.str(), sz, sig, pIdx, sig->get_sort());
				sigMap[sig] = c;
				topRet = c;
			}
		}
	}
//	cout << *top << " -> " << *topRet << endl;
	return topRet;
}

Inst* Reach::replace_from_map(Inst *top, InstToInstM& subMap)
{
//  cout << "top: " << *top << endl;

  Inst* topRet = top;

  bool replaced = false;
  InstToInstM::iterator mit = subMap.find(top);
  if (mit != subMap.end()) {
    replaced = true;
    topRet = (*mit).second;
    cout << *top << " -> " << *topRet << endl;
  }

  if (!replaced) {
    const InstL* ch = top->get_children();
    if (ch)
    {
      InstL new_ch;
      bool need_new = false;

      for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it)
      {
        Inst* newCh = replace_from_map((*it), subMap);
        if (newCh != (*it))
          need_new = true;
        new_ch.push_back(newCh);
      }
      if (need_new)
        topRet = top->apply_children(new_ch);
    }
  }
//  cout << *top << " -> " << *topRet << endl;
  return topRet;
}

Inst* Reach::substitute_from_map(Inst *top, const InstToInstM* pre, const InstToInstM* next) {
	if (top->get_visit2())
	{
		return top->acex_coi;
	}
	top->set_visit2();

//  cout << "top: " << *top << endl;

  Inst* topRet = top;

  if (topRet->get_type() == Wire) {
  	if (is_next_wire(topRet)) {
  		if (next) {
				InstToInstM::const_iterator mit = next->find(topRet);
				if (mit != next->end()) {
					topRet = (*mit).second;
	//  	    cout << *top << " -> " << *topRet << endl;
				}
  		}
  	}
  	else {
  		if (pre) {
				InstToInstM::const_iterator mit = pre->find(topRet);
				if (mit != pre->end()) {
					topRet = (*mit).second;
	//  	    cout << *top << " -> " << *topRet << endl;
				}
  		}
  	}
  	topRet = topRet->get_port();
  }

  {
    const InstL* ch = topRet->get_children();
    if (ch)
    {
      InstL new_ch;
      bool need_new = false;

      for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it)
      {
        Inst* newCh = substitute_from_map((*it), pre, next);
        if (newCh != (*it))
          need_new = true;
        new_ch.push_back(newCh);
      }
      if (need_new)
        topRet = topRet->apply_children(new_ch);
    }
  }
  //  cout << *top << " -> " << *topRet << endl;

  top->acex_coi = topRet;
  return topRet;
}

/// Add all wires in the back cone of top
void Reach::add_all_wires(Inst *top, InstL& wireList, bool init_visit)
{
	if (init_visit) {
		Inst::init_visit();
	}
	if (top->get_visit()) {
		return;
	}
	top->set_visit();

	WireInst* w = WireInst::as(top);
	if (w)
	{
		wireList.push_back(w);
//		cout << "Adding wire: " << *w << endl;
	}

	const InstL* ch = top->get_children();
	if (ch)
	{
		for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it)
			add_all_wires(*it, wireList, false);
	}
}

/// Add more wires in the back cone of top
void Reach::add_more_wires(Inst *top, InstL& wireList, bool init_visit)
{
	if (init_visit) {
		Inst::init_visit();
	}
	if (top->get_visit()) {
		return;
	}
	top->set_visit();

	WireInst* w = WireInst::as(top);
	if (w)
	{
		if (w->trueFcLevel == 0)
			wireList.push_back(w);
//		cout << "Adding wire: " << *w << endl;
	}

	const InstL* ch = top->get_children();
	if (ch)
	{
		for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it)
			add_all_wires(*it, wireList, false);
	}
}

void Reach::add_gate_consistency(Inst* tve, InstL& viol, bool init_visit)
{
	if (init_visit) {
		Inst::init_visit();
	}
	if (tve->get_visit()) {
		return;
	}
	tve->set_visit();

	WireInst* w = WireInst::as(tve);
	if (w)
	{
		Inst* port = w->get_port();
		assert(port);
		Inst* gateConstraint = OpInst::create(OpInst::Eq, w, port);
		viol.push_back(gateConstraint);
	}
	else
	{
		assert(0);
	}
}

bool Reach::is_gate_consistency(Inst *tve)
{
	OpInst* op = OpInst::as(tve);
	if (op && op->get_op() == OpInst::Eq)
	{
		Inst* lhs = op->get_children()->front();
		Inst* rhs = op->get_children()->back();

		if ((lhs->get_type() == Op || lhs->get_type() == Ex) && rhs->get_type() == Wire)
		{
			Inst* tmp = lhs;
			lhs = rhs;
			rhs = tmp;
		}

		WireInst* w = WireInst::as(lhs);
		if (w)
		{
			OpInst* op_rhs = OpInst::as(rhs);
			if (op_rhs)
			{
				if (op_rhs == w->get_port())
				{
//					cout << *tve << " is gc" << endl;
					return true;
				}
			}
		}
	}
	return false;
}

/// Generalize failure condition to derive lemmas
Inst* Reach::make_lemmas(InstL& failCond)
{
	Inst::inc_rkey();
	Inst::init_visit();
	for (InstL::iterator it = failCond.begin(); it != failCond.end(); it++)
	{
		Inst* tve = (*it);
		Inst* tveNeg = OpInst::create(OpInst::LogNot, tve);
		tve->set_bval(1);
		tveNeg->set_bval(0);

		OpInst* op = OpInst::as(tve);
		if (op && op->get_op() == OpInst::Eq)
		{
			Inst* lhs = op->get_children()->front();
			Inst* rhs = op->get_children()->back();
			if (lhs->get_type() == Num)
			{
				Inst* tmp = lhs;
				lhs = rhs;
				rhs = tmp;
			}
			if (rhs->get_type() == Num)
			{
				assert(lhs->get_type() != Num);
				lhs->acex_coi = rhs;
				lhs->set_visit();
			}
		}
	}
	InstL viol;

	for (auto& c: failCond)
	{
		Inst* newC = evaluate_generalize_relation(c, viol, false);
		OpInst* opNew = OpInst::as(newC);
		if (opNew)
		{
			if (opNew->get_op() == OpInst::Eq)
			{
				if (opNew->get_children()->front() == opNew->get_children()->back())
				{
					cout << "\n" << *c << " became True" << endl;
					continue;
				}
			}
		}
		else if (newC->get_type() == Num)
		{
			assert(newC == NumInst::create(1, 1, SORT()));
			cout << "\n" << *c << " became 1'd1" << endl;
			continue;
		}

		viol.push_back(newC);
		if (c == newC)
			cout << "\n" << *c << " same" << endl;
		else
			cout << "\n" << *c << " became " << *newC << endl;
	}
	Inst* newRef = OpInst::create(OpInst::LogAnd, viol);
	return newRef;
}

pair< Inst*, Inst* > Reach::reduce_ref(Inst *top)
{
//	return top;

	Inst* topNew1 = reduce_ref_wires(top);
	Inst* topNew2 = reduce_ref_gate(topNew1);

//	Inst* topNew3 = reduce_ref_eval(topNew2);
//	return make_pair(topNew2, topNew3);

	return make_pair(topNew2, topNew2);

//	collect_cubes(top, true);
//	while(1)
//	{
//		if(generalize_ref_with_wires(_collected_cubes) == false)
//		{
//			break;
//		}
//	}
//	Inst* simplifiedRef = OpInst::create(OpInst::LogAnd, _collected_cubes);
//	Inst* reducedTop = reduce_ref_gate(simplifiedRef);
//	return reducedTop;

//	Inst* reducedTop = reduce_ref_gate(top);
//	collect_cubes(reducedTop, true);
////	while(1)
////	{
////		if(generalize_ref_with_wires(_collected_cubes) == false)
////		{
////			break;
////		}
////	}
//	Inst* simplifiedRef = OpInst::create(OpInst::LogAnd, _collected_cubes);
//	return simplifiedRef;
}

/// Reduces ref by trivial equality propagation among wires
Inst* Reach::reduce_ref_wires(Inst *top)
{
	Inst* ref = top;
//	cout << "in: " << *ref << endl;
	collect_cubes(ref, true);

	InstToPairBoolM wireMap;
	InstS wireSet;
	for(InstL::iterator cit = _collected_cubes.begin(); cit != _collected_cubes.end();)
	{
		Inst* c = (*cit);

		/// Do stuff
		OpInst* op = OpInst::as(c);
		if (op && op->get_op() == OpInst::Eq)
		{
			Inst* lhs;
			Inst* rhs;
			lhs = op->get_children()->front();
			rhs = op->get_children()->back();
			if (lhs->get_type() == Wire && rhs->get_type() == Wire)
			{
				Inst* port = WireInst::as(lhs)->get_port();
				bool found = false;
				const InstL* children = port->get_children();
				assert(children);
				for (auto& ch: *(children))
				{
					if (ch == rhs)
					{
						found = true;
						break;
					}
				}
				if (found)
				{
					wireMap[lhs] = make_pair(rhs, false);
					cit = _collected_cubes.erase(cit);

	//				cout << "\t\t[" << *lhs << "] = [" << *rhs << "]" << endl;
					continue;
				}
			}
		}
		if (c->get_type() == Wire)
			wireSet.insert(c);
		else
		{
			const InstL* children = c->get_children();
			if (children)
			{
				for (auto& ch: *children)
				{
					if (ch->get_type() == Wire)
						wireSet.insert(ch);
				}
			}
		}
		cit++;
	}

	bool mod = false;
	for(auto& wire: wireSet)
	{
		Inst* lhs = wire;
		Inst* rhs = wire;

		// skip intermediate nets
		Inst* rhsNew = rhs;
		while(1)
		{
			InstToPairBoolM::iterator mit = wireMap.find(rhsNew);
			if(mit == wireMap.end()){
				break;
			}
			rhsNew = (mit->second).first;
			(mit->second).second = true;
		}
		if (rhsNew != rhs)
		{
			mod = true;
			Inst* tveNew = OpInst::create(OpInst::Eq, lhs, rhsNew);
//			cout << "\t\t(sliced): " << *tveNew << endl;
			_collected_cubes.push_back(tveNew);
			continue;
		}
	}
	if (mod)
	{
		for (auto& m: wireMap)
		{
			if (!(m.second.second))
			{
				Inst* eq = OpInst::create(OpInst::Eq, m.first, m.second.first);
				_collected_cubes.push_back(eq);
			}
		}

		Inst* new_ref = OpInst::create(OpInst::LogAnd, _collected_cubes);

//		/// Reduce internal wires by substitution
//		InstL conjunct_new;
//		Inst::init_visit2();
//		for (auto& c: _collected_cubes)
//		{
//			Inst* cNew = evaluate_slice(c, wireMap, false);
//			OpInst* op = OpInst::as(cNew);
//			if (op && op->get_op() == OpInst::Eq)
//			{
//				if (op->get_children()->front() == op->get_children()->back())
//					continue;
//			}
//			conjunct_new.push_back(cNew);
//		}
//		Inst* new_ref = OpInst::create(OpInst::LogAnd, conjunct_new);

//		cout << "out: " << *new_ref << endl;
		return new_ref;
	}
	return top;
}

Inst* Reach::reduce_ref_gate(Inst *top)
{
	Inst* ref = top;
//	cout << "in: " << *ref << endl;
	collect_cubes(ref, true);
	bool mod = false;
	for(InstL::iterator cit = _collected_cubes.begin(); cit != _collected_cubes.end();)
	{
		Inst* tve = (*cit);
		if (is_gate_consistency(tve))
		{
//			cout << "(erasing: " << *tve << ")" << endl;
			cit = _collected_cubes.erase(cit);
			mod = true;
			continue;
		}

//		if (tve == _ve_model || tve == _ve_model_next)
//		{
////			cout << "(erasing: " << *tve << ")" << endl;
//			cit = _collected_cubes.erase(cit);
//			mod = true;
//			continue;
//		}
//
//		OpInst* op = OpInst::as(tve);
//		if (op && op->get_op() == OpInst::Eq)
//		{
//			Inst* lhs = op->get_children()->front();
//			Inst* rhs = op->get_children()->back();
//			if (lhs->find_next())
//			{
//				if (lhs->get_type() == Sig && rhs->get_type() == Wire)
//				{
//					InstToInstM::iterator mit  = Inst::_m_sn.find(lhs);
//					if (mit != Inst::_m_sn.end())
//					{
//						if ((*mit).second == rhs)
//						{
////								cout << "(erasing: " << *tve << ")" << endl;
//							cit = _collected_cubes.erase(cit);
//							mod = true;
//							continue;
//						}
//					}
//				}
//			}
//		}
		cit++;
	}
	if (mod)
	{
		Inst* new_ref = OpInst::create(OpInst::LogAnd, _collected_cubes);
//		cout << "out: " << *new_ref << endl;
		return new_ref;
	}
	return top;
}

Inst* Reach::reduce_ref_eval(Inst *top)
{
	Inst::inc_reduceKey();

	Inst* ref = top;
	collect_cubes(ref, true);
	for(InstL::iterator cit = _collected_cubes.begin(); cit != _collected_cubes.end(); cit++)
	{
		Inst* tve = (*cit);

		OpInst* op = OpInst::as(tve);
		if (op)
		{
			if (op->get_op() == OpInst::Eq)
			{
				Inst* lhs = op->get_children()->front();
				Inst* rhs = op->get_children()->back();
				if (lhs->get_type() == Num)
					swap(lhs, rhs);

				if (rhs->get_type() == Num)
				{
					if (lhs->get_type() == Sig)
					{
						lhs->set_reduceEval(rhs);
					}
					lhs->set_reduceVal(NumInst::as(rhs)->get_num());
				}
			}
			else if (op->get_op() == OpInst::LogNot)
			{
				Inst* child = op->get_children()->front();
				if (child->get_type() == Sig)
				{
					child->set_reduceEval(NumInst::create(0, 1, SORT()));
				}
			}
		}
		else
		{
			if (tve->get_type() == Sig)
			{
				tve->set_reduceEval(NumInst::create(1, 1, SORT()));
			}
		}
		Inst* tveNeg = OpInst::create(OpInst::LogNot, tve);
		tve->set_reduceVal(1);
		tveNeg->set_reduceVal(0);
	}
	Inst::init_visit();
	InstL conjunct_ref;

	/// First reduce present state expressions
	for(InstL::iterator cit = _collected_cubes.begin(); cit != _collected_cubes.end();)
	{
		Inst* tve = *cit;
		if (tve->find_next())
		{
			const InstL* ch = tve->get_children();
			if (ch)
			{
				for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it)
				{
					if (!(*it)->find_next())
						reduce_relation(*it);
				}
			}
			cit++;
		}
		else
		{
			Inst* tveNew = reduce_relation(tve);
			if (!is_redundant(tveNew))
			{
				conjunct_ref.push_back(tveNew);
			}
			cit = _collected_cubes.erase(cit);
		}
	}
	/// Now reduce remaining expressions
	for(InstL::iterator cit = _collected_cubes.begin(); cit != _collected_cubes.end();)
	{
		Inst* tve = *cit;
		Inst* tveNew = reduce_relation(tve);
		if (!is_redundant(tveNew))
		{
			conjunct_ref.push_back(tveNew);
		}
		cit = _collected_cubes.erase(cit);
	}
//  assert (!conjunct_ref.empty());
  if (conjunct_ref.empty())
    conjunct_ref.push_back(NumInst::create(0, 1, SORT()));

	Inst* refNew;
	if (conjunct_ref.size() != 1)
		refNew = OpInst::create(OpInst::LogAnd, conjunct_ref);
	else
	{
		assert(conjunct_ref.size() == 1);
		refNew = conjunct_ref.front();
	}

	if (refNew != ref)
	{
//		cout << "\t(reduced ref: " << *refNew << " )" << endl;
		ref = refNew;
	}
	return ref;
}

bool Reach::reduce_ref_eval_sim(InstL& conjunct_top, InstL& conjunct_ref)
{
	Inst::inc_reduceKey();
	Inst::init_visit();

	InstToInstM eqMap;
	list< pair< Inst*, Inst* > > delayedTop;

	for(InstL::iterator cit = conjunct_top.begin(); cit != conjunct_top.end(); cit++)
	{
		Inst* tve = (*cit);

		OpInst* op = OpInst::as(tve);
		if (op)
		{
			if (op->get_op() == OpInst::Eq)
			{
				Inst* lhs = op->get_children()->front();
				Inst* rhs = op->get_children()->back();
				if (!lhs->childrenInfo[SIG])
					swap(lhs, rhs);

				if (!rhs->childrenInfo[SIG])
				{
					if (rhs->get_type() == Const)
						rhs->set_reduceEval(lhs);
					else
					{
						if (!lhs->childrenInfo[CONST])
						{
							// No symbolic constant
							OpInst* opR = OpInst::as(rhs);
							if (opR)
							{
								if (opR->get_op() == OpInst::Concat)
								{
									delayedTop.push_back(make_pair(lhs, rhs));
								}
							}
						}
						else
							eqMap[rhs] = lhs;
					}
				}
			}
			else if (op->get_op() == OpInst::LogNot)
			{
				Inst* child = op->get_children()->front();
				if (!child->childrenInfo[SIG])
				{
					if (child->get_type() == Const)
						child->set_reduceEval(NumInst::create(0, 1, SORT()));
					else
						eqMap[child] = NumInst::create(0, 1, SORT());
				}
			}
		}
		else
		{
			if (!tve->childrenInfo[SIG])
			{
				if (tve->get_type() == Const)
					tve->set_reduceEval(NumInst::create(1, 1, SORT()));
				else
					eqMap[tve] = NumInst::create(1, 1, SORT());
			}
		}
	}

	for (auto& p: delayedTop)
	{
		Inst* lhs = p.first;
		Inst* rhs = p.second;
		OpInst* opR = OpInst::as(rhs);
		assert (opR);
		assert (opR->get_op() == OpInst::Concat);

		const InstL* ch = opR->get_children();
		unsigned s_loc = 0, e_loc = 0;
		for (InstL::const_iterator cit = ch->begin(); cit != ch->end(); ++cit)
		{
			Inst* child = *cit;
			unsigned size = child->get_size();
			s_loc = e_loc;
			e_loc += size;
//										cout << "[:] is [" << (e_loc - 1) << ":" << s_loc << "] for sz: " << size << endl;

			if (child->get_reduceEval() == NULL)
			{
				Inst* lChild = ExInst::create(lhs, (e_loc - 1), s_loc);
				lChild = lChild->t_simple;
				child->set_reduceEval(lChild);
				cout << "\t\t" << *child << " -> " << *lChild << endl;
			}
		}
	}

	bool modified = false;
	/// First reduce present state expressions
	for(InstL::iterator cit = conjunct_top.begin(); cit != conjunct_top.end(); cit++)
	{
		Inst* tve = *cit;
		if (tve->find_next())
			conjunct_ref.push_back(tve);
		else
		{
			Inst* tveNew = reduce_relation_sim(tve, eqMap);
			if (!is_redundant(tveNew))
			{
				conjunct_ref.push_back(tveNew);
				if (tveNew != (*cit))
					modified = true;
			}
			else
				conjunct_ref.push_back(tve);
		}
	}
	assert (!conjunct_ref.empty());

	return modified;
}

Inst* Reach::simplify_expr(Inst *top)
{
//	cout << "top: " << *top << endl;

#ifndef INTERPRET_EX_CC
	return top;
#endif

	ExInst* ex = ExInst::as(top);
	if (ex)
	{
		return ex->t_simple;
	}
	else
	{
		OpInst* op = OpInst::as(top);
		if (op)
		{
			if (op->get_op() == OpInst::Concat)
				return op->t_simple;
		}

    const InstL* ch = top->get_children();
    if (ch)
    {
      InstL new_ch;
      bool need_new = false;

      for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it)
      {
        Inst* newCh = simplify_expr((*it));
        if (newCh != (*it))
          need_new = true;
        new_ch.push_back(newCh);
      }
      if (need_new)
      {
        Inst* newTop = top->apply_children(new_ch);
        return newTop;
      }
    }
	}
	return top;
}

Inst* Reach::simplify_expr_all(Inst *top_orig)
{
	Inst* top = top_orig;
  const InstL* ch = top->get_children();
  if (ch) {
    InstL new_ch;
    bool need_new = false;
    for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it) {
      Inst* newCh = simplify_expr_all((*it));
      if (newCh != (*it))
        need_new = true;
      new_ch.push_back(newCh);
    }
    if (need_new)
    	top = top->apply_children(new_ch);
  }

	OpInst* op = OpInst::as(top);
	if (op)
		top = top->t_simple->t_simple;

	return top;
}

Inst* Reach::replace_with_num_excc(Inst *top, map< int, map< mpz_class, Inst* > >& numMap, InstToInstM& nextMap) {
  if (top->get_visit2()) {
    return top->acex_coi;
  }
  top->set_visit2();

  Inst* topRet = top;
  const InstL* ch = topRet->get_children();
  if (ch) {
    InstL new_ch;
    bool need_new = false;
    for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it) {
      Inst* newCh = replace_with_num_excc((*it), numMap, nextMap);
      if (newCh != (*it))
        need_new = true;
      new_ch.push_back(newCh);
    }
    if (need_new)
      topRet = top->apply_children(new_ch);
    OpInst* opRet = OpInst::as(topRet);
    if (opRet) {
      if (opRet->get_op() == OpInst::Eq || opRet->get_op() == OpInst::NotEq) {
        Inst* lhs = topRet->get_children()->front();
        Inst* rhs = topRet->get_children()->back();
        if (lhs->get_type() == Num && rhs->get_type() == Num) {
          bool val = (lhs == rhs);
          if (opRet->get_op() == OpInst::NotEq)
            val = !val;
          topRet = NumInst::create(val?1:0, 1, SORT());
        }
      }
    }
  }
  else {
    if (topRet->childrenInfo[NEXT] && topRet->get_type() == Sig) {
      InstToInstM::iterator mit = nextMap.find(topRet);
      if (mit != nextMap.end())
        topRet = replace_with_num_excc((*mit).second, numMap, nextMap);
    }
  }

  if (!topRet->childrenInfo[NEXT] && topRet->childrenInfo[SIG]) {
//  if (topRet->childrenInfo[SIG]) {
    int sz = topRet->get_size();
    if (sz == 1) {
      int bval = topRet->get_bval();
      if (bval != INVALID_SVAL)
        topRet = NumInst::create(bval, 1, SORT());
    }
    else {
      mpz_class* ival = topRet->get_ival();
      if (ival != INVALID_SMPZ) {
        map< mpz_class, Inst* >::iterator mit = numMap[sz].find(*ival);
        if (mit != numMap[sz].end())
          topRet = (*mit).second;
      }
    }
  }

  top->acex_coi = topRet;
//  cout << "top2: " << *top << "\t ret2: " << *topRet << endl;
  return topRet;
}

Inst* Reach::simplify_excc(Inst *top, map< int, map< mpz_class, Inst* > >& numMap, InstToInstM& nextMap) {
  if (top->get_visit2()) {
    return top->acex_coi;
  }
  top->set_visit2();

  Inst* topRet = top->t_simple;
  const InstL* ch = topRet->get_children();
  if (ch) {
    InstL new_ch;
    bool need_new = false;
    for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it) {
      Inst* newCh = simplify_excc((*it), numMap, nextMap);
      if (newCh != (*it))
        need_new = true;
      new_ch.push_back(newCh);
    }
    if (need_new) {
//      cout << "top  : " << *top << endl;
//      cout << "newch: " << new_ch << endl;
      topRet = topRet->apply_children(new_ch)->t_simple;
    }
    OpInst* opRet = OpInst::as(topRet);
    if (opRet) {
      if (opRet->get_op() == OpInst::Eq || opRet->get_op() == OpInst::NotEq) {
        Inst* lhs = topRet->get_children()->front();
        Inst* rhs = topRet->get_children()->back();
        if (lhs->get_type() == Num && rhs->get_type() == Num) {
          bool val = (lhs == rhs);
          if (opRet->get_op() == OpInst::NotEq)
            val = !val;
          topRet = NumInst::create(val?1:0, 1, SORT());
        }
      }
    }
  }
  else {
    if (topRet->childrenInfo[NEXT] && topRet->get_type() == Sig) {
      InstToInstM::iterator mit = nextMap.find(topRet);
      if (mit != nextMap.end())
        topRet = simplify_excc((*mit).second, numMap, nextMap);
    }
  }

  if (!topRet->childrenInfo[NEXT] && topRet->childrenInfo[SIG]) {
//  if (topRet->childrenInfo[SIG]) {
    int sz = topRet->get_size();
    if (sz == 1) {
      int bval = topRet->get_bval();
      if (bval != INVALID_SVAL)
        topRet = NumInst::create(bval, 1, SORT());
    }
    else {
      mpz_class* ival = topRet->get_ival();
      if (ival != INVALID_SMPZ) {
        map< mpz_class, Inst* >::iterator mit = numMap[sz].find(*ival);
        if (mit != numMap[sz].end())
          topRet = (*mit).second;
      }
    }
  }

  top->acex_coi = topRet;
//  cout << "top: " << *top << "\t ret: " << *topRet << endl;
  return topRet;
}

/// Converts expression to it's signal equivalent
Inst* Reach::signal_expr(Inst *top)
{
//	cout << "top: " << *top << endl;

  const InstL* ch = top->get_children();
  if (ch)
  {
    InstL new_ch;
    bool need_new = false;

    for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it)
    {
      Inst* newCh = signal_expr((*it));
      if (newCh != (*it))
        need_new = true;
      new_ch.push_back(newCh);
    }
    if (need_new)
    {
      Inst* newTop = top->apply_children(new_ch);
      return newTop;
    }
  }
	return top;
}

Inst* Reach::eliminate_dont_cares(Inst *top, ABSTRACT_CUBE& abCube, int& numOptions, bool init_visit)
{
	if (init_visit) {
		Inst::init_visit2();
	}
	if (top->get_visit2()) {
		return top->acex_coi;
	}
	top->set_visit2();

//	cout << "top: " << *top << endl;

	top->acex_coi = top;

	if (top->get_type() == Sig)
	{

	}
	else if (top->get_type() == Num)
	{

	}
//	if (top->get_dcVal(Inst::get_dckey()))
	else if (top->get_dcVal(Inst::get_dckey()))
	{
//		InstToSetM::iterator mit = abCube.internalEval.find(top);
//		if (mit != abCube.internalEval.end())
//		{
//			InstS& equivSet = (*mit).second;
//			size_t sz = equivSet.size();
//			if (sz != 0)
//			{
//				Inst* replacement;
//				replacement = (*equivSet.begin());
//
//				if (sz > 1)
//				{
//					bool popOption = false;
//					if (numOptions == 1)
//						popOption = true;
//
//					numOptions *= sz;
//					/* initialize random seed: */
//					srand (time(NULL));
//
//					/* generate secret number between 1 and 10: */
//					int select = rand() % sz;
//					int count = 0;
//					cout << "\t\t(multiple choices for replacing " << *top << " with { ";
//					for (auto& e: equivSet)
//					{
//						cout << *e << ", ";
//						if (count == select)
//						{
//							replacement = e;
//						}
//						count++;
//					}
//					cout << "}" << endl;
//					if (popOption)
//						equivSet.erase(replacement);
//				}
//				else
//					replacement = (*equivSet.begin());
//
//				top->acex_coi = replacement;
//
//				cout << "\t\t(replacing " << *top << " with " << *(top->acex_coi) << ")" << endl;;
//				top->acex_coi->set_hlVal(true);
//			}
//		}
	}
	else
	{
		const InstL* ch = top->get_children();
		if (ch)
		{
			InstL new_ch;
			bool need_new = false;

			for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it)
			{
				Inst* newCh = eliminate_dont_cares((*it), abCube, numOptions);
				if (newCh != (*it))
					need_new = true;
				new_ch.push_back(newCh);
			}
			if (need_new)
			{
				Inst* newTop = top->apply_children(new_ch);
				top->acex_coi = newTop;
			}
		}
	}
	return top->acex_coi;
}

bool Reach::find_reg(Inst *top)
{
  if (top->hasReg != DEFAULT_VAL) {
    return (top->hasReg == 1) ? true : false;
  }

//	cout << "top: " << *top << endl;

  bool res = false;

	const InstL* ch = top->get_children();
	if (ch)
	{
		for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it)
		{
			Inst * tve = *it;
			res = res || find_reg(tve);
		}
	}
	else
	{
		SigInst* sig = SigInst::as(top);
		if (sig)
		{
			if (Inst::_s_reg.find(sig) != Inst::_s_reg.end())
			  res = true;
		}
	}
	top->hasReg = res ? 1 : 0;
	return res;
}

//bool Reach::find_sig(Inst *top)
//{
////	cout << "top: " << *top << endl;
//
//	OpInst* op = OpInst::as(top);
//	ExInst* ex = ExInst::as(top);
//	if (op || ex)
//	{
//		const InstL* ch = top->get_children();
//		if (ch)
//		{
//			bool res = false;
//			for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it)
//			{
//				Inst * tve = *it;
//				if (find_sig(tve))
//					return true;
//			}
//			return false;
//		}
//	}
//	else
//	{
//		SigInst* sig = SigInst::as(top);
//		if (sig)
//			return true;
//		else
//			return false;
//	}
//	return false;
//}
//
//bool Reach::find_constant(Inst *top)
//{
////	cout << "top: " << *top << endl;
//
//	OpInst* op = OpInst::as(top);
//	ExInst* ex = ExInst::as(top);
//	if (op || ex)
//	{
//		const InstL* ch = top->get_children();
//		if (ch)
//		{
//			bool res = false;
//			for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it)
//			{
//				Inst * tve = *it;
//				if (find_constant(tve))
//					return true;
//			}
//			return false;
//		}
//	}
//	else
//	{
//		ConstInst* c = ConstInst::as(top);
//		if (c)
//			return true;
//		else
//			return false;
//	}
//	return false;
//}



bool Reach::find_from_minset(Inst *top, InstS& relSig, InstS& relConst, set< string >& relUFtype)
{
  if (top->get_visit2()) {
    return top->genBval;
  }
  top->set_visit2();

//	cout << "top: " << *top << endl;

  bool res = true;

	const InstL* ch = top->get_children();
	if (ch)
	{
		OpInst* op = OpInst::as(top);
		if (op)
		{
			string ufType = op->get_euf_func_name();
			if (ufType != "0")
			{
				if (_s_uf.find(op) != _s_uf.end())
				  cout << "\t\t(found learned uf in partition)\t" << *op << endl;
				else {
				  res = false;
				  if (relUFtype.find(ufType) != relUFtype.end()) {
				//            if (_s_local_uf.find(top) != _s_local_uf.end())
					{
					  res = true;
					}
				  }
				}

//			  if (relUFtype.find(ufType) == relUFtype.end()) {
////          cout << "not present due to " << ufType << endl;
//				  res = false;
//				}
			}
		}

		if (res)
		{
      for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it)
      {
        Inst * tve = *it;
        if (!find_from_minset(tve, relSig, relConst, relUFtype))
        {
          res = false;
          break;
        }
      }
		}
	}
	else
	{
		SigInst* sig = SigInst::as(top);
		if (sig)
		{
      if (_s_signals.find(sig) == _s_signals.end()) {
        if (relSig.find(sig) == relSig.end()) {
  //        cout << "not present due to " << *sig << endl;
          res = false;
        }
      }
		}
		else
		{
			NumInst* num = NumInst::as(top);
			if (num && num->get_size() > 1)
			{
			  if (_s_constants.find(num) == _s_constants.end()) {
          if (relConst.find(num) == relConst.end()) {
  //				  cout << "not present due to " << *num << endl;
            res = false;
          }
			  }
			}
		}
	}

	top->genBval = res;
	return res;
}

bool Reach::add_constraints_using_numbers(InstL& cubes) {
  bool modified = false;
  map < pair<int, SORT>, InstToPairListM > numMap;
  map < pair<int, SORT>, InstToPairListM > allMap;
  for (auto& cube: cubes) {
    OpInst* op = OpInst::as(cube->get_port());
    if (op) {
      OpInst::OpType opt = op->get_op();
      if (opt == OpInst::Eq || opt == OpInst::NotEq) {
        bool negated = false;
        negated = (opt == OpInst::NotEq);
        Inst* lhs = op->get_children()->front();
        Inst* rhs = op->get_children()->back();

        if (lhs->get_type() == Num)
          swap(lhs, rhs);
        if (rhs->get_type() == Num) {
          InstToPairListM& numEntry = numMap[make_pair(lhs->get_size(), lhs->get_sort())];
          pair < InstL, InstL >& entry = numEntry[rhs];
          if (negated)
            entry.second.push_back(lhs);
          else
            entry.first.push_back(lhs);
        }
        else {
            if (lhs->get_type() != Sig)
              swap(lhs, rhs);
            InstToPairListM& allEntry = allMap[make_pair(lhs->get_size(), lhs->get_sort())];

            pair < InstL, InstL >& entryL = allEntry[lhs];
            if (negated)
              entryL.second.push_back(rhs);
            else
              entryL.first.push_back(rhs);

            pair < InstL, InstL >& entryR = allEntry[rhs];
            if (negated)
              entryR.second.push_back(lhs);
            else
              entryR.first.push_back(lhs);
        }
      }
    }
  }

  bool modified1 = false;
  for (auto& entries: numMap) {
    InstToPairListM& numEntry = entries.second;

    for (auto& num: numEntry) {
      InstL& eq = num.second.first;
      InstL& neq = num.second.second;

      for (InstL::iterator lit1 = eq.begin(); lit1 != eq.end(); lit1++) {
        InstL::iterator lit2 = lit1;
        lit2++;
        Inst* lhs = (*lit1);
        for (; lit2 != eq.end(); lit2++) {
          Inst* rhs = (*lit2);
          if (lhs != rhs) {
            Inst* cond = OpInst::create(OpInst::Eq, lhs, rhs);
            cubes.push_front(cond);
            AVR_LOG(15, 0, "\t\t(added cond. from num.)\t" << *cond << endl);
            modified1 = true;
          }
        }
      }

      for (InstL::iterator lit1 = eq.begin(); lit1 != eq.end(); lit1++) {
        Inst* lhs = (*lit1);
        for (InstL::iterator lit2 = neq.begin(); lit2 != neq.end(); lit2++) {
          Inst* rhs = (*lit2);
          assert (lhs != rhs);
          Inst* cond = OpInst::create(OpInst::NotEq, lhs, rhs);
          cubes.push_front(cond);
          AVR_LOG(15, 0, "\t\t(added cond. from num.)\t" << *cond << endl);
          modified1 = true;
        }
      }

      for (auto& num2: numEntry) {
        if (num != num2) {
          InstL& eq2 = num2.second.first;

          for (InstL::iterator lit1 = eq.begin(); lit1 != eq.end(); lit1++) {
            Inst* lhs = (*lit1);
            for (InstL::iterator lit2 = eq2.begin(); lit2 != eq2.end(); lit2++) {
              Inst* rhs = (*lit2);
              assert (lhs != rhs);
              Inst* cond = OpInst::create(OpInst::NotEq, lhs, rhs);
              cubes.push_front(cond);
              AVR_LOG(15, 0, "\t\t(added cond. from num.)\t" << *cond << endl);
              modified1 = true;
            }
          }
        }
      }

    }
  }

  bool modified2 = false;
#if 0
  for (auto& entries: allMap) {
    InstToPairListM& allEntry = entries.second;

    for (auto& all: allEntry) {
      InstL& eq = all.second.first;
      InstL& neq = all.second.second;

      for (InstL::iterator lit1 = eq.begin(); lit1 != eq.end(); lit1++) {
        InstL::iterator lit2 = lit1;
        lit2++;
        Inst* lhs = (*lit1);
        for (; lit2 != eq.end(); lit2++) {
          Inst* rhs = (*lit2);
          if (lhs != rhs) {
            Inst* cond = OpInst::create(OpInst::Eq, lhs, rhs);
            cubes.push_front(cond);
            AVR_LOG(15, 0, "\t\t(added cond. from terms)\t" << *cond << endl);
            modified2 = true;
          }
        }
      }

      for (InstL::iterator lit1 = eq.begin(); lit1 != eq.end(); lit1++) {
        Inst* lhs = (*lit1);
        for (InstL::iterator lit2 = neq.begin(); lit2 != neq.end(); lit2++) {
          Inst* rhs = (*lit2);
          assert (lhs != rhs);
          Inst* cond = OpInst::create(OpInst::NotEq, lhs, rhs);
          cubes.push_front(cond);
          AVR_LOG(15, 0, "\t\t(added cond. from terms)\t" << *cond << endl);
          modified2 = true;
        }
      }

    }
  }
#endif
  modified = modified1 || modified2;
//  if (modified2) {
//	  assert(0);
//  }
  return modified;
}

void Reach::uniquify_list(InstL& l) {
	InstS bucket;
	for (auto& tve: l) {
		if (bucket.find(tve) == bucket.end())
		  bucket.insert(tve);
	}
	l.clear();
	for (auto& pred: bucket)
	  l.push_back(pred);
}

void Reach::uniquify_solution(SOLUTION& s)
{
	bool modified = false;
	InstS bucketS;
	InstV bucketV;
	for (InstL::iterator pit = s.predicates.begin(); pit != s.predicates.end(); pit++)
	{
		Inst* tve = *pit;
		if (bucketS.find(tve) != bucketS.end()) {
      modified = true;
    }
		else {
		  bucketS.insert(tve);
		  bucketV.push_back(tve);
		}
	}
//	if (Config::g_random)
//		random_shuffle(bucketV.begin(), bucketV.end());

	s.predicates.clear();
	for (auto& pred: bucketV)
	  s.predicates.push_back(pred);

	for (auto& partition: s.partitions)
	{
		for (auto& cell: partition.second)
		{
		  bucketS.clear();
		  bucketV.clear();
		  for (InstL::iterator pit = cell.second.begin(); pit != cell.second.end(); pit++)
			{
				Inst* tve = *pit;
		    if (bucketS.find(tve) != bucketS.end()) {
		      modified = true;
		    }
		    else {
		      bucketS.insert(tve);
				  bucketV.push_back(tve);
		    }
			}
//			if (Config::g_random)
//				random_shuffle(bucketV.begin(), bucketV.end());

		  cell.second.clear();
		  for (auto& e: bucketV)
		    cell.second.push_back(e);
		}
	}

//	if (modified)
//	{
//		print_solution(s, "uniquified solution");
//	}
}

#ifdef	FIND_SUB_EXPRESSION
bool Reach::simplify_solution(SOLUTION& s, InstToListM& opMap)
{
	Inst::init_visit();
  Inst::init_visit2();
	WireInst::inc_slicekey();

	bool modified = false;
	for (InstL::iterator pit = s.predicates.begin(); pit != s.predicates.end();)
	{
		Inst* tve = *pit;

//		if (tve->find_next()) {
//		  cout << "s: " << *tve << endl;
//		}

		if (tve == _ve_prop_eq_0 || tve == _ve_prop_eq_1 || tve == _ve_prop_next_eq_0 || tve == _ve_prop_next_eq_1)
//    if (tve == _ve_prop_eq_0 || tve == _ve_prop_eq_1)
		{
			pit = s.predicates.erase(pit);
			continue;
		}

		evaluate_relation(2, tve);
		Inst* tveS = tve->subs_coi;

		OpInst* op = OpInst::as(tve);
		if (op && op->get_op() == OpInst::LogNot)
		{
			Inst* child = op->get_children()->front();
      tveS = OpInst::create(OpInst::LogNot, child->subs_coi);
		}

		if (tve != tveS)
//		if (tve->get_port() != tveS->get_port())
		{
			opMap[tveS].push_back(tve);
			(*pit) = tveS;
			pit++;
//			pit = s.predicates.erase(pit);
			modified = true;
		}
		else
			pit++;
	}

	for (auto& partition: s.partitions)
	{
		for (auto& cell: partition.second)
		{
			for (InstL::iterator pit = cell.second.begin(); pit != cell.second.end();)
			{
				Inst* tve = *pit;
				evaluate_term(2, tve);
				if (tve != tve->subs_coi)
//				if (tve->get_port() != tve->subs_coi->get_port())
				{
					opMap[tve->subs_coi].push_back(tve);
					(*pit) = tve->subs_coi;
					pit++;
					modified = true;
				}
				else
					pit++;
			}
		}
	}

	uniquify_solution(s);

	if (modified)
	{
//		print_solution(s, "transformed solution");
		AVR_LOG(15, 0, "\t(map) #" << opMap.size() << "\n");
//    for (auto& m: opMap)
//    {
//      AVR_LOG(15, 0, "\t\t");
//      for (auto& rhs: m.second)
//      {
//        AVR_LOG(15, 0, *rhs << ", ")
//      }
//      AVR_LOG(15, 0, " := " << *m.first << endl);
//    }
	}

	return modified;
}
#endif

bool Reach::resimplify_solution(SOLUTION& s, InstToListM& opMap)
{
	bool modified = false;

	for (InstL::iterator pit = s.predicates.begin(); pit != s.predicates.end();)
	{
		Inst* tve = *pit;

		if (OpInst::as(tve))
		{
			InstToListM::iterator mit = opMap.find(tve);
			if (mit != opMap.end())
			{
        if (mit->second.empty())
        {
          cout << *tve << " found, but empty" << endl;
        }
        assert(!mit->second.empty());

				(*pit) = mit->second.front();
				mit->second.pop_front();
				modified = true;
			}
		}
		pit++;
	}

	for (auto& partition: s.partitions)
	{
		for (auto& cell: partition.second)
		{
			for (InstL::iterator pit = cell.second.begin(); pit != cell.second.end();)
			{
				Inst* tve = *pit;
				if (OpInst::as(tve))
				{
					InstToListM::iterator mit = opMap.find(tve);
					if (mit != opMap.end()) {
            if (mit->second.empty())
            {
              cout << *tve << " found, but empty" << endl;
            }
            assert(!mit->second.empty());

            (*pit) = mit->second.front();
            mit->second.pop_front();
            modified = true;
					}
				}
				pit++;
			}
		}
	}

	return modified;
}

bool Reach::resimplify_solution(SOLUTION& s, InstToListM& opMap, InstToInstM& subMap, InstToInstM& subMapR)
{
	bool modified = false;

	for (InstL::iterator pit = s.predicates.begin(); pit != s.predicates.end();)
	{
		Inst* tve = *pit;

		if (OpInst::as(tve))
		{
			InstToListM::iterator mit = opMap.find(tve);
			if (mit != opMap.end())
			{
        if (mit->second.empty())
        {
          cout << *tve << " found, but empty" << endl;
        }
        assert(!mit->second.empty());

//        cout << "replacing " << *tve << " with " << *(mit->second.front()) << endl;

				subMap[*pit] = mit->second.front();
				subMapR[mit->second.front()] = (*pit);
				(*pit) = mit->second.front();
				mit->second.pop_front();
				modified = true;
			}
		}
		pit++;
	}

	for (auto& partition: s.partitions)
	{
		for (auto& cell: partition.second)
		{
			for (InstL::iterator pit = cell.second.begin(); pit != cell.second.end();)
			{
				Inst* tve = *pit;
				if (OpInst::as(tve))
				{
					InstToListM::iterator mit = opMap.find(tve);
					if (mit != opMap.end()) {
            if (mit->second.empty())
            {
              cout << *tve << " found, but empty" << endl;
            }
            assert(!mit->second.empty());

//            cout << "replacing " << *tve << " with " << *(mit->second.front()) << endl;

            subMap[*pit] = mit->second.front();
            subMapR[mit->second.front()] = (*pit);
            (*pit) = mit->second.front();
            mit->second.pop_front();
            modified = true;
					}
				}
				pit++;
			}
		}
	}

//  if (modified)
  {
    print_solution(s, "gen. solution");
  }
	return modified;
}

void Reach::model_project(SOLUTION& s, SOLUTION& out, string mode, bool allowInp, bool quiet)
{
  if (mode == "pre") {
    for (InstL::iterator pit = s.predicates.begin(); pit != s.predicates.end(); pit++)
    {
      Inst* tve = *pit;
      if (!tve->find_next()) {
        if (allowInp || !find_input(tve))
          out.predicates.push_back(tve);
      }
    }
    for (auto& partition: s.partitions)
    {
    	pair< int, SORT> sz = partition.first;
      for (auto& cell: partition.second)
      {
        for (InstL::iterator pit = cell.second.begin(); pit != cell.second.end(); pit++)
        {
          Inst* tve = *pit;
          if (!tve->find_next()) {
            if (allowInp || !find_input(tve))
              out.partitions[sz][cell.first].push_back(tve);
          }
        }
      }
    }
  }
  else if (mode == "next") {
    for (InstL::iterator pit = s.predicates.begin(); pit != s.predicates.end(); pit++)
    {
      Inst* tve = *pit;
      if (!find_pre(tve))
        out.predicates.push_back(tve);
    }
    for (auto& partition: s.partitions)
    {
    	pair< int, SORT> sz = partition.first;
      for (auto& cell: partition.second)
      {
        for (InstL::iterator pit = cell.second.begin(); pit != cell.second.end(); pit++)
        {
          Inst* tve = *pit;
          if (!find_pre(tve))
            out.partitions[sz][cell.first].push_back(tve);
        }
      }
    }
  }
  else {
    AVR_LOG(15, 0, "Unknown project mode: " << mode << endl);
    assert(0);
  }

	if (!quiet)
	{
		print_solution(out, mode);
	}
}

void Reach::model_abstract(SOLUTION& s, SOLUTION& pre, SOLUTION& inp, SOLUTION& next, SOLUTION& mixed, bool quiet)
{
	for (InstL::iterator pit = s.predicates.begin(); pit != s.predicates.end(); pit++)
	{
		Inst* tve = *pit;
		if (tve->find_next())
		{
			next.predicates.push_back(tve);
		}
		else if (tve->find_sig())
		{
			if (find_input(tve))
			{
				if (find_reg(tve))
				{
					mixed.predicates.push_back(tve);
				}
				else
				{
					inp.predicates.push_back(tve);
				}
			}
			else
			{
				pre.predicates.push_back(tve);
			}
		}
		else
		{
			next.predicates.push_back(tve);
			pre.predicates.push_back(tve);
			inp.predicates.push_back(tve);
			mixed.predicates.push_back(tve);
		}
	}

	for (auto& partition: s.partitions)
	{
		pair< int, SORT> sz = partition.first;
		for (auto& cell: partition.second)
		{
			for (InstL::iterator pit = cell.second.begin(); pit != cell.second.end(); pit++)
			{
				Inst* tve = *pit;
				if (tve->find_next())
				{
					next.partitions[sz][cell.first].push_back(tve);
				}
				else if (tve->find_sig())
				{
					if (find_input(tve))
					{
						if (find_reg(tve))
						{
							mixed.partitions[sz][cell.first].push_back(tve);
						}
						else
						{
							inp.partitions[sz][cell.first].push_back(tve);
						}
					}
					else
					{
						pre.partitions[sz][cell.first].push_back(tve);
					}
				}
				else
				{
					next.partitions[sz][cell.first].push_back(tve);
					pre.partitions[sz][cell.first].push_back(tve);
					inp.partitions[sz][cell.first].push_back(tve);
					mixed.partitions[sz][cell.first].push_back(tve);
				}
			}
		}
	}
	if (!quiet)
	{
		print_solution(next, "next");
		print_solution(pre, "pre");
		print_solution(inp, "inp");
		print_solution(mixed, "mixed");
	}
}

void Reach::model_abstract(SOLUTION& s, SOLUTION& pre, SOLUTION& inp, SOLUTION& next, SOLUTION& mixed, InstToInstM& subMapR, bool quiet)
{
  bool sameN = true;
  bool sameP = true;
  bool sameI = true;
  bool sameM = true;

  for (InstL::iterator pit = s.predicates.begin(); pit != s.predicates.end(); pit++)
	{
		Inst* tve = *pit;
    Inst* tveR = *pit;
//    if (OpInst::as(tve))
    {
      InstToInstM::iterator mit = subMapR.find(tve);
      if (mit != subMapR.end())
        tveR = (*mit).second;
    }

		if (tveR->find_next())
		{
			next.predicates.push_back(tve);
			if (tve != tveR)
			  sameN = false;
		}
		else if (tveR->find_sig())
		{
			if (find_input(tveR))
			{
				if (find_reg(tveR))
				{
					mixed.predicates.push_back(tve);
		      if (tve != tveR)
		        sameM = false;
				}
				else
				{
					inp.predicates.push_back(tve);
		      if (tve != tveR)
		        sameI = false;
				}
			}
			else
			{
				pre.predicates.push_back(tve);
	      if (tve != tveR)
	        sameP = false;
			}
		}
		else
		{
	    if (tve->find_next())
	      next.predicates.push_back(tve);
	    else if (tve->find_sig()) {
        pre.predicates.push_back(tve);
        inp.predicates.push_back(tve);
      }
	    else {
        next.predicates.push_back(tve);
        pre.predicates.push_back(tve);
        inp.predicates.push_back(tve);
        mixed.predicates.push_back(tve);
	    }
      if (tve != tveR) {
        sameN = false;
        sameP = false;
        sameI = false;
        sameM = false;
      }
		}
	}

	for (auto& partition: s.partitions)
	{
		pair< int, SORT> sz = partition.first;
		for (auto& cell: partition.second)
		{
			for (InstL::iterator pit = cell.second.begin(); pit != cell.second.end(); pit++)
			{
				Inst* tve = *pit;
		    Inst* tveR = *pit;
//		    if (OpInst::as(tve))
		    {
		      InstToInstM::iterator mit = subMapR.find(tve);
		      if (mit != subMapR.end())
		        tveR = (*mit).second;
		    }

				if (tveR->find_next())
				{
					next.partitions[sz][cell.first].push_back(tve);
	        if (tve != tveR)
	          sameN = false;
				}
				else if (tveR->find_sig())
				{
					if (find_input(tveR))
					{
						if (find_reg(tveR))
						{
							mixed.partitions[sz][cell.first].push_back(tve);
			        if (tve != tveR)
			          sameM = false;
						}
						else
						{
							inp.partitions[sz][cell.first].push_back(tve);
			        if (tve != tveR)
			          sameI = false;
						}
					}
					else
					{
						pre.partitions[sz][cell.first].push_back(tve);
		        if (tve != tveR)
		          sameP = false;
					}
				}
				else
				{
				  if (tve->find_next())
				    next.partitions[sz][cell.first].push_back(tve);
				  else if (tve->find_sig()) {
				    pre.partitions[sz][cell.first].push_back(tve);
				    inp.partitions[sz][cell.first].push_back(tve);
				  }
				  else {
            next.partitions[sz][cell.first].push_back(tve);
            pre.partitions[sz][cell.first].push_back(tve);
            inp.partitions[sz][cell.first].push_back(tve);
				    mixed.partitions[sz][cell.first].push_back(tve);
				  }
		      if (tve != tveR) {
		        sameN = false;
		        sameP = false;
		        sameI = false;
		        sameM = false;
		      }
				}
			}
		}
	}
	if (!quiet)
	{
//	  if (sameN) {
//	    AVR_LOG(15, 0, "\tnext_c = next\n");
//	  }
//	  else
	    print_solution(next, "next_c");

//    if (sameP) {
//      AVR_LOG(15, 0, "\tpre_c = pre\n");
//    }
//    else
      print_solution(pre, "pre_c");

//    if (sameI) {
//      AVR_LOG(15, 0, "\tinp_c = inp\n");
//    }
//    else
      print_solution(inp, "inp_c");

//    if (sameM) {
//      AVR_LOG(15, 0, "\tmixed_c = mixed\n");
//    }
//    else
      print_solution(mixed, "mixed_c");
	}
}

#ifdef GENERALIZE_WITH_CELL
bool Reach::model_generalize(SOLUTION& s, InstS& relSig, InstS& relConst, set< string >& relUFtype)
{
  bool modified = false;
  for (InstL::iterator pit = s.predicates.begin(); pit != s.predicates.end();)
  {
    Inst* tve = *pit;

    if (!find_from_minset(tve, relSig, relConst, relUFtype))
    {
      modified = true;
      pit = s.predicates.erase(pit);
//      if (tve->find_next()) {
//        cout << "s: " << *tve << "\t->\t" << "not present" << endl;
//      }
    }
    else {
      pit++;
//      if (tve->find_next()) {
//        cout << "s: " << *tve << "\t->\t" << "present" << endl;
//      }
    }
  }

  for (map< int, map< mpz_class, InstL > >::iterator sit = s.partitions.begin(); sit != s.partitions.end();)
  {
    int sz = (*sit).first;
    for (map< mpz_class, InstL >::iterator cit = (*sit).second.begin(); cit != (*sit).second.end();)
    {
      bool include = false;
      for (InstL::iterator pit = (*cit).second.begin(); pit != (*cit).second.end();)
      {
        Inst* tve = *pit;
        if (find_from_minset(tve, relSig, relConst, relUFtype))
          include = true;
        pit++;
      }
      if (!include) {
        for (InstL::iterator pit = (*cit).second.begin(); pit != (*cit).second.end();)
        {
          Inst* tve = *pit;
          modified = true;
          pit = s.partitions[sz][(*cit).first].erase(pit);
        }
      }

      if ((*cit).second.empty())
        cit = (*sit).second.erase(cit);
      else
        cit++;
    }
    if ((*sit).second.empty())
      sit = s.partitions.erase(sit);
    else
      sit++;
  }
  if (modified) {
    print_solution(s, "gen. solution (subs.)");
  }
  return modified;
}
#else
bool Reach::model_generalize(SOLUTION& s, InstS& relSig, InstS& relConst, set< string >& relUFtype)
{
  bool modified = false;
  for (InstL::iterator pit = s.predicates.begin(); pit != s.predicates.end();)
  {
    Inst* tve = *pit;

    if (!find_from_minset(tve, relSig, relConst, relUFtype))
    {
      modified = true;
      pit = s.predicates.erase(pit);
//      if (tve->find_next()) {
//        cout << "s: " << *tve << "\t->\t" << "not present" << endl;
//      }
    }
    else {
      pit++;
//      if (tve->find_next()) {
//        cout << "s: " << *tve << "\t->\t" << "present" << endl;
//      }
    }
  }

  for (map< pair< int, SORT>, map< mpz_class, InstL > >::iterator sit = s.partitions.begin(); sit != s.partitions.end();)
  {
  	pair< int, SORT> sz = (*sit).first;
    for (map< mpz_class, InstL >::iterator cit = (*sit).second.begin(); cit != (*sit).second.end();)
    {
      for (InstL::iterator pit = (*cit).second.begin(); pit != (*cit).second.end();)
      {
        Inst* tve = *pit;
        if (!find_from_minset(tve, relSig, relConst, relUFtype))
        {
          modified = true;
          pit = s.partitions[sz][(*cit).first].erase(pit);
        }
        else
          pit++;
      }
      if ((*cit).second.empty())
        cit = (*sit).second.erase(cit);
      else
        cit++;
    }
    if ((*sit).second.empty())
      sit = s.partitions.erase(sit);
    else
      sit++;
  }
  if (modified) {
//    print_solution(s, "gen. solution (subs.)");
  }
  return modified;
}
#endif

void Reach::model_convert(SOLUTION& s, SOLUTION& out, InstToInstM& subMap, string comment, bool quiet) {
  bool modified = false;
  for (InstL::iterator pit = s.predicates.begin(); pit != s.predicates.end(); pit++)
  {
    Inst* tve = *pit;
    InstToInstM::iterator mit = subMap.find(tve);
    if (mit != subMap.end()) {
      tve = (*mit).second;
      modified = true;
    }
    out.predicates.push_back(tve);
  }

  for (auto& partition: s.partitions)
  {
  	pair< int, SORT> sz = partition.first;
    map< mpz_class, InstL>& outPartition = out.partitions[sz];
    for (auto& cell: partition.second)
    {
      InstL& outCell = outPartition[cell.first];
      for (InstL::iterator pit = cell.second.begin(); pit != cell.second.end(); pit++)
      {
        Inst* tve = *pit;
        InstToInstM::iterator mit = subMap.find(tve);
        if (mit != subMap.end()) {
          tve = (*mit).second;
          modified = true;
        }
        outCell.push_back(tve);
      }
    }
  }

  if (!quiet)
  {
    if (modified)
      print_solution(out, comment + "_c");
    else {
      AVR_LOG(15, 0, "\t(" << comment << "_c = " << comment << ")\n");
    }
  }
}


void Reach::add_from_solution(Solver*solver, SOLUTION& s, InstL& target, InstL& output, InstToInstM& subMap)
{
	InstS tSet;
	for (auto& t: target)
	{
		tSet.insert(t);
	}

	for (InstL::iterator pit = s.predicates.begin(); pit != s.predicates.end(); pit++)
	{
		Inst* tve = *pit;
		InstToInstM::iterator mit = subMap.find(tve);
		if (mit != subMap.end())
			tve = (*mit).second;
		if (tSet.find(tve) == tSet.end())
			output.push_back(tve);
	}

	for (auto& partition: s.partitions)
	{
//		int sz = partition.first;
		list < pair < Inst*, Inst* > > leaders;
		for (auto& cell: partition.second)
		{
			InstL::iterator lit = cell.second.begin();
			Inst* leader_orig = (*lit);
			InstToInstM::iterator mit = subMap.find(leader_orig);
			Inst* leader = (mit == subMap.end()) ? leader_orig : (*mit).second;
			lit++;

			if (leader->get_type() != Num)
			{
				for (; lit != cell.second.end(); lit++)
				{
					Inst* tve = *lit;
					if (tve->get_type() == Num)
					{
						leader = tve;
						break;
					}
					else if (tve->get_type() == Sig)
						leader = tve;
				}
			}
			leaders.push_back(make_pair(leader_orig, leader));

			for (InstL::iterator pit = cell.second.begin(); pit != cell.second.end(); pit++)
			{
				Inst* tve_orig = *pit;
				InstToInstM::iterator mit = subMap.find(tve_orig);
				Inst* tve = (mit == subMap.end()) ? tve_orig : (*mit).second;
				if (leader != tve)
				{
					/// Guard not needed since constants are distinct
//					if (leader->get_type() != Num || tve->get_type() != Num)
					{
						Inst* eq = OpInst::create(OpInst::Eq, tve, leader);
						if (tSet.find(eq) == tSet.end())
						{
							if (solver->get_relation(tve_orig, leader, true))
								output.push_back(eq);
						}
					}
					assert(*tve->get_ival() == *leader->get_ival());
				}
			}
		}

#ifndef GENERALIZE_WO_DISEQ
		for (list < pair < Inst*, Inst* > >::iterator cit1 = leaders.begin(); cit1 != leaders.end(); cit1++)
		{
			list < pair < Inst*, Inst* > >::iterator cit2 = cit1;
			cit2++;
			for (; cit2 != leaders.end(); cit2++)
			{
				Inst* lhs_orig = (*cit1).first;
				Inst* rhs_orig = (*cit2).first;

				Inst* lhs = (*cit1).second;
				Inst* rhs = (*cit2).second;

				if (lhs->get_type() == Num && rhs->get_type() != Num)
				{
					swap(lhs_orig, rhs_orig);
					swap(lhs, rhs);
				}

				if (lhs->get_type() != Num || rhs->get_type() != Num)
				{
					Inst* neq = OpInst::create(OpInst::NotEq, lhs, rhs);
					if (tSet.find(neq) == tSet.end())
					{
						if (solver->get_relation(lhs_orig, rhs_orig, false))
							output.push_back(neq);
					}
				}
				assert(*lhs->get_ival() != *rhs->get_ival());
			}
		}
#endif
	}
}

void Reach::add_modify_solution(Solver*solver, SOLUTION& s, InstL& target, InstL& output)
{
	bool modified = false;
	InstS tSet;
	for (auto& t: target)
	{
		tSet.insert(t);
	}

	for (InstL::iterator pit = s.predicates.begin(); pit != s.predicates.end(); pit++)
	{
		Inst* tve = *pit;
		if (tSet.find(tve) == tSet.end())
			output.push_back(tve);
	}

	for (auto& partition: s.partitions)
	{
//		int sz = partition.first;
		InstL leaders;
		for (auto& cell: partition.second)
		{
			InstL::iterator lit = cell.second.begin();
			Inst* leader = (*lit);
			lit++;

			if (leader->get_type() != Num)
			{
				for (; lit != cell.second.end(); lit++)
				{
					Inst* tve = *lit;
					if (tve->get_type() == Num)
					{
						leader = tve;
						break;
					}
					else if (tve->get_type() == Sig)
						leader = tve;
				}
			}
			leaders.push_back(leader);

			for (InstL::iterator pit = cell.second.begin(); pit != cell.second.end(); pit++)
			{
				Inst* tve = *pit;
				if (leader != tve)
				{
					if (allowed_relation(leader, tve, OpInst::Eq))
					{
						Inst* eq = OpInst::create(OpInst::Eq, tve, leader);
						if (tSet.find(eq) == tSet.end())
						{
							if (solver->get_relation(tve, leader, true))
								output.push_back(eq);
						}
						if ((leader->get_type() != Sig && leader->get_type() != Num) ||
								(tve->get_type() != Sig && tve->get_type() != Num)) {
							s.predicates.push_back(eq);
							modified = true;
						}
					}
					assert(*tve->get_ival() == *leader->get_ival());
				}
			}
		}

#ifndef GENERALIZE_WO_DISEQ
		for (InstL::iterator cit1 = leaders.begin(); cit1 != leaders.end(); cit1++)
		{
			InstL::iterator cit2 = cit1;
			cit2++;
			for (; cit2 != leaders.end(); cit2++)
			{
				Inst* lhs = *cit1;
				Inst* rhs = *cit2;

				if (lhs->get_type() == Num && rhs->get_type() != Num)
				{
					swap(lhs, rhs);
				}

				if (allowed_relation(lhs, rhs, OpInst::NotEq))
				{
					Inst* neq = OpInst::create(OpInst::NotEq, lhs, rhs);
					if (tSet.find(neq) == tSet.end())
					{
						if (solver->get_relation(lhs, rhs, false))
							output.push_back(neq);
					}
					if ((lhs->get_type() != Sig && lhs->get_type() != Num) ||
							(rhs->get_type() != Sig && rhs->get_type() != Num)) {
						s.predicates.push_back(neq);
						modified = true;
					}
				}
				assert(*lhs->get_ival() != *rhs->get_ival());
			}
		}
#endif
	}

  for (map< pair< int, SORT>, map< mpz_class, InstL > >::iterator sit = s.partitions.begin(); sit != s.partitions.end();)
  {
  	pair< int, SORT> sz = (*sit).first;
    for (map< mpz_class, InstL >::iterator cit = (*sit).second.begin(); cit != (*sit).second.end();)
    {
      for (InstL::iterator pit = (*cit).second.begin(); pit != (*cit).second.end();)
      {
        Inst* tve = *pit;
        if (tve->get_type() != Sig && tve->get_type() != Num)
        {
          modified = true;
          pit = s.partitions[sz][(*cit).first].erase(pit);
        }
        else
          pit++;
      }
      if ((*cit).second.empty())
        cit = (*sit).second.erase(cit);
      else
        cit++;
    }
    if ((*sit).second.empty())
      sit = s.partitions.erase(sit);
    else
      sit++;
  }
  if (modified) {
//    print_solution(s, "mod. solution");
  }
}

void Reach::add_from_solution(Solver*solver, SOLUTION& s, InstL& target, InstToInstM& subMap, string comment)
{
	InstL output;
	add_from_solution(solver, s, target, output, subMap);
	if (!output.empty())
	{
    if (comment != "") {
      AVR_LOG(15, 0, "\t(" << comment << ") #" << output.size() << "\n");
    }
		for (auto & p: output)
		{
      if (comment != "") {
//        AVR_LOG(15, 0, "\t\t" << *p << endl);
      }
			target.push_back(p);
		}
	}
}

void Reach::add_modify_solution(Solver*solver, SOLUTION& s, InstL& target, string comment)
{
	InstL output;
	add_modify_solution(solver, s, target, output);
  if (!output.empty())
  {
    if (comment != "") {
      AVR_LOG(15, 0, "\t(" << comment << ") #" << output.size() << "\n");
    }
    for (auto & p: output)
    {
      if (comment != "") {
//  			AVR_LOG(15, 0, "\t\t" << *p << endl);
      }
      target.push_back(p);
    }
  }
}

void Reach::add_wires_from_solution(SOLUTION& s, InstL& wires)
{
	Inst::init_visit();

	for (InstL::iterator pit = s.predicates.begin(); pit != s.predicates.end(); pit++)
	{
		add_wires(*pit, wires);
	}

	for (auto& partition: s.partitions)
	{
		for (auto& cell: partition.second)
		{
			for (InstL::iterator pit = cell.second.begin(); pit != cell.second.end(); pit++)
			{
				add_wires(*pit, wires);
			}
		}
	}
}

void Reach::add_wires_from_list(InstL& l, InstL& wires)
{
	Inst::init_visit();
	for (auto& v: l)
		add_wires(v, wires);
}

void Reach::add_wires(Inst* top, InstL& wires)
{
	if (top->get_visit()) {
		return;
	}
	top->set_visit();

//	cout << "top: " << *top << endl;

	if (top->get_type() == Wire)
	{
		WireInst* w = WireInst::as(top);
		if (w->get_sliceVal(WireInst::get_slicekey()))
		{
			wires.push_back(w);
		}
	}

	const InstL* ch = top->get_children();
	if (ch)
	{
		for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it)
			add_wires(*it, wires);
	}
}

void Reach::print_solution(SOLUTION& s, string comment, int loc, int level)
{
//	level = 0;
	bool isEmpty = true;
	ostringstream ostr;

	ostr << "\t(" << comment << ")\n";
	ostr << "\t\t    ";
	for (InstL::iterator pit = s.predicates.begin(); pit != s.predicates.end(); pit++)
	{
		ostr << *(*pit) << " ^ ";
//		ostr << *(*pit)->get_port() << " ^ ";
		if ((*pit)->find_sig())
			isEmpty = false;
	}
	if (!isEmpty)
		ostr << "\n";
	else
	{
		ostr.str("");
		ostr << "\t(" << comment << ")\n";
	}

	for (auto& partition: s.partitions)
	{
		pair< int, SORT> sz = partition.first;
	  ostringstream ostrP;
	  bool isEmptyP = true;
	  ostrP << "\t\t#" << sz.first << "_" << sz.second.sort2str() << ": { ";
		for (auto& cell: partition.second)
		{
			for (InstL::iterator pit = cell.second.begin(); pit != cell.second.end(); pit++)
			{
				ostrP << *(*pit) << ", ";
//				ostr << *(*pit)->get_port() << ", ";
				if ((*pit)->find_sig())
				  isEmptyP = false;
			}
			ostrP << "| ";
		}
		ostrP << "}\n";
		if (!isEmptyP) {
		  ostr << ostrP.str();
		  isEmpty = false;
		}
	}
	if (!isEmpty)
	{
		AVR_LOG(loc, level, ostr.str() << endl);
	}
}

void Reach::print_solution(ostream& ostr, SOLUTION& s, string comment)
{
  ostr << "\t" << comment << "\n";
  ostr << "\t\t    ";
  for (InstL::iterator pit = s.predicates.begin(); pit != s.predicates.end(); pit++)
  {
    ostr << *(*pit) << " ^ ";
//    ostr << *(*pit)->get_port() << " ^ ";
  }
  if (!s.predicates.empty())
    ostr << "\n";

  for (auto& partition: s.partitions)
  {
  	pair< int, SORT> sz = partition.first;
    ostr << "\t\t#" << sz.first << "_" << sz.second.sort2str() << ": { ";
    for (auto& cell: partition.second)
    {
      for (InstL::iterator pit = cell.second.begin(); pit != cell.second.end(); pit++)
      {
        ostr << *(*pit) << ", ";
//        ostr << *(*pit)->get_port() << ", ";
      }
      ostr << "| ";
    }
    ostr << "}\n";
  }
  ostr << "\n";
}

void Reach::merge_lists(InstL& target, InstL& side)
{
	for (auto& tve: side)
		target.push_back(tve);
}

void Reach::interpret_distinct_constant(InstL& target)
{
	InstL outList;

	// Uniquify
	InstS outSet;
	for (InstL::iterator it = target.begin(), end_it = target.end(); it != end_it; ++it)
	{
		if (outSet.find(*it) != outSet.end())
			continue;

		outList.push_back(*it);
		outSet.insert(*it);
	}

	InstS expConsts;
	for (auto& v: outList)
	{
		OpInst* op = OpInst::as(v);
		if (op && op->get_op() == OpInst::Eq)
		{
			Inst* lhs = op->get_children()->front();
			Inst* rhs = op->get_children()->back();
			if (lhs->get_type() != Num && rhs->get_type() == Num)
				expConsts.insert(lhs);
			else if (lhs->get_type() == Num && rhs->get_type() != Num)
			{
				expConsts.insert(rhs);
			}
		}
	}

	for (InstL::iterator it = outList.begin(); it != outList.end();)
	{
		OpInst* op = OpInst::as(*it);
		if (op && op->get_op() == OpInst::NotEq)
		{
			Inst* lhs = op->get_children()->front();
			Inst* rhs = op->get_children()->back();
			if (lhs->get_type() != Num && rhs->get_type() == Num)
			{
				if (expConsts.find(lhs) != expConsts.end())
				{
					it = outList.erase(it);
					continue;
				}
			}
			else if (lhs->get_type() == Num && rhs->get_type() != Num)
			{
				if (expConsts.find(rhs) != expConsts.end())
				{
					it = outList.erase(it);
					continue;
				}
			}
		}
		it++;
	}
	target.swap(outList);
}

bool Reach::find_has_limited_sigs(Inst *top, InstS& inputs)
{
	if (top->get_visit3()) {
    return top->genBval2;
  }
  top->set_visit3();

//	cout << "top: " << *top << endl;

	bool res = false;
	const InstL* ch = top->get_children();
	if (ch)
	{
		for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it)
		{
			Inst * tve = *it;
			if (find_has_limited_sigs(tve, inputs))
			{
				res = true;
				break;
			}
		}
	}
	else
	{
		SigInst* sig = SigInst::as(top);
		if (sig)
		{
			if (inputs.find(sig) != inputs.end())
				res = true;
		}
	}

	top->genBval2 = res;
	return res;
}

bool Reach::find_limited_sigs(Inst *top, InstS& inputs)
{
	if (top->get_visit2()) {
    return top->genBval;
  }
  top->set_visit2();

//	cout << "top: " << *top << endl;

	bool res = true;
	const InstL* ch = top->get_children();
	if (ch)
	{
		for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it)
		{
			Inst * tve = *it;
			if (!find_limited_sigs(tve, inputs))
			{
				res = false;
				break;
			}
		}
	}
	else
	{
		SigInst* sig = SigInst::as(top);
		if (sig)
		{
			if (inputs.find(sig) == inputs.end())
				res = false;
		}
	}

	top->genBval = res;
	return res;
}

bool Reach::find_limited_sigs(Inst *top, InstToInstM& inputs)
{
//	cout << "top: " << *top << endl;

	const InstL* ch = top->get_children();
	if (ch)
	{
		bool res = true;
		for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it)
		{
			Inst * tve = *it;
			if (!find_limited_sigs(tve, inputs))
			{
				res = false;
				break;
			}
		}
		if (res)
			return true;
		else
			return false;
	}
	else
	{
		SigInst* sig = SigInst::as(top);
		if (sig)
		{
			if (inputs.find(sig) == inputs.end())
				return false;
			else
				return true;
		}
		else
		{
			return true;
		}
	}
	assert(0);
}

bool Reach::find_limited_constants(Inst *top, InstS& constants)
{
	return true;

//	cout << "top: " << *top << endl;
	InstS constSet;
	collect_const(top, constSet, true);

	for (auto& c: constants)
	{
		constSet.erase(c);
	}
	if (constSet.empty())
		return true;
	else
		return false;
	assert(0);

  const InstL* ch = top->get_children();
  if (ch)
  {
    bool res = true;
    for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it)
    {
      Inst * tve = *it;
      if (!find_limited_constants(tve, constants))
      {
        res = false;
        break;
      }
    }
    if (res)
      return true;
    else
      return false;
  }
	else
	{
		ConstInst* c = ConstInst::as(top);
		if (c)
		{
			if (constants.find(c) == constants.end())
				return false;
			else
				return true;
		}
		else
		{
			return true;
		}
	}
	assert(0);
	return false;
}

bool Reach::find_input(Inst *top)
{
  if (top->hasInput != DEFAULT_VAL) {
    return (top->hasInput == 1) ? true : false;
  }

//	cout << "top: " << *top << endl;

  bool res = false;

  const InstL* ch = top->get_children();
  if (ch)
  {
    for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it)
    {
      Inst * tve = *it;
      if (find_input(tve)) {
        res = true;
        break;
      }
    }
  }
	else
	{
		SigInst* sig = SigInst::as(top);
		if (sig)
		{
			if (Inst::_s_inp.find(sig) != Inst::_s_inp.end()) {
			  res = true;
			}
		}
	}
  top->hasInput = res ? 1 : 0;
  return res;
}

bool Reach::is_next_wire(Inst *top)
{
	if (top->get_type() != Wire)
	{
		cout << *top << endl;
	}
	assert(top->get_type() == Wire);

	if (top->find_next())
	{
//		WireInst* w = WireInst::as(top);
//		string wName = w->get_name();
//		size_t nameLength = wName.length();
//		assert ((nameLength > NEXT_SUFFIX_LENGTH) && wName.substr((nameLength - NEXT_SUFFIX_LENGTH), NEXT_SUFFIX_LENGTH) == NEXT_SUFFIX);

//		cout << *w << "\t" << "true" << endl;
		return true;
	}
	else
	{
//		WireInst* w = WireInst::as(top);
//		string wName = w->get_name();
//		size_t nameLength = wName.length();
//		if ((nameLength > NEXT_SUFFIX_LENGTH) && wName.substr((nameLength - NEXT_SUFFIX_LENGTH), NEXT_SUFFIX_LENGTH) == NEXT_SUFFIX)
//		{
////			cout << *w << "\t" << "true" << endl;
//			return true;
//		}
//		else
		{
//			cout << *w << "\t" << "false" << endl;
			return false;
		}
	}
}

bool Reach::find_pre(Inst *top)
{
  return find_reg(top) || find_input(top);
}

/// Returns max distance of an entry added to ufDistance
/// Note- top should be an expression in only present state. No $next allowed.
int Reach::compute_comb_distances(Inst* e)
{
	int maxDistance = 0;
	deque < pair< Inst*, int > > q;
	q.push_back(make_pair(e, 0));

	Inst::init_visit();
	while (!q.empty())
	{
		Inst* top = q.front().first;
		int currDistance = q.front().second;
		q.pop_front();

		bool updateFlag = false;
		if (!(top->get_visit()))
		{
			top->fcCombDist = 0;
			updateFlag = true;
		}
		top->set_visit();

//		AVR_LOG(15, 0, "top: " << *top << " @" << currDistance << endl);

		SigInst* sig = SigInst::as(top);
		if (sig)
		{
			if (top->fcCombDist < currDistance)
				top->fcCombDist = currDistance;
//				cout << "ufD(" << *sig << ") = " << ufDistance[sig] << endl;
		}
		else
		{
			OpInst* op = OpInst::as(top);
			if (op)
			{
				string euf_func_name;
				if (op->get_type() == Op)
					euf_func_name = op->get_euf_func_name();
				else
				{
					ExInst* ex = ExInst::as(top);
					euf_func_name = ex->get_euf_func_name();
				}

				if(euf_func_name != "0")
				{
					currDistance++;
					if (maxDistance < currDistance)
						maxDistance = currDistance;
				}

				if (top->fcCombDist < currDistance)
				{
					top->fcCombDist = currDistance;
					updateFlag = true;
				}
			}
		}

		if (updateFlag)
		{
			const InstL* tch = top->get_children();
			if (tch)
			{
				for (InstL::const_iterator tit = tch->begin(); tit != tch->end(); ++tit)
				{
	//				if ((*tit)->get_visit())
	//				{
	//				}
	//				else
						q.push_back(make_pair(*tit, currDistance));
				}
			}
		}
	}
	return maxDistance;
}

/// Returns total number of UFs/Ex/Cc
/// Note- top should be an expression in only present state. No $next allowed.
/// Num - [0]
/// UF  - [1]
/// Cc  - [2]
/// Ex  - [3]
void Reach::compute_number_uf(Inst* top, vector < int >& ufInfo, bool init_visit)
{
	if (init_visit) {
		Inst::init_visit2();
		ufInfo.resize(4, 0);
	}
	if (top->get_visit2()) {
		return;
	}
	top->set_visit2();

//	cout << "top: " << *top << endl;

	const InstL* ch = top->get_children();
	if (ch)
	{
		for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it)
			compute_number_uf(*it, ufInfo);
	}

	switch(top->get_type())
	{
	case Op:
	{
		OpInst* op = OpInst::as(top);
		assert(op);
		if (op->get_op() == OpInst::Concat)
			ufInfo[2]++;
		else if (op->get_euf_type_name() != "0")
			ufInfo[1]++;
	}
	break;
	case Ex:
	{
		ufInfo[3]++;
	}
	break;
	case Num:
	{
		ufInfo[0]++;
	}
	break;
	default:
		break;
	}
}

void Reach::collect_constants(Inst *top, InstS& s, bool init_visit)
{
	if (init_visit) {
		Inst::init_visit2();
	}
	if (top->get_visit2()) {
		return;
	}
	top->set_visit2();

//	cout << "top: " << *top << endl;

	const InstL* ch = top->get_children();
	if (ch)
	{
		for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it)
		{
			Inst * tve = *it;
			collect_constants(tve, s, false);
		}
	}
	else
	{
		ConstInst* c = ConstInst::as(top);
		if (c)
		{
			s.insert(c);
		}
	}
}

///// Aman
///// Below function derived from http://stackoverflow.com/questions/5279051/how-can-i-create-cartesian-product-of-vector-of-vectors
/////
//void Reach::cart_product(
//	InstLL& rvvi, // final result
//    InstL&  rvi,   // current result
//	InstToSetM::iterator me, // current input
//	InstToSetM::iterator end) // final input
//{
//    if(me == end) {
//        // terminal condition of the recursion. We no longer have
//        // any input vectors to manipulate. Add the current result (rvi)
//        // to the total set of results (rvvvi).
//        rvvi.push_back(rvi);
//        return;
//    }
//
//    // need an easy name for my vector-of-ints
//    for(InstS::iterator it = (*me).second.begin(); it != (*me).second.end(); it++)
//    {
//        // final rvi will look like "a, b, c, ME, d, e, f"
//        // At the moment, rvi already has "a, b, c"
//        rvi.push_back((*it));  // add ME
//        InstToSetM::iterator tempIt = me;
//        tempIt++;
//        cart_product(rvvi, rvi, tempIt, end); // add "d, e, f"
//        rvi.pop_back(); // clean ME off for next round
//    }
//}

//void Reach::collect_Assignments(Inst *top, Inst* sigNext, InstToSetM m_assignments)
//{
//	cout << "top: " << *top << endl;
//
//	OpInst* op = OpInst::as(top);
//	if (op && op->get_op() == OpInst::Ternary)
//	{
//		const InstL* ch = top->get_children();
//		InstL::const_iterator it = ch->begin();
//		it++;
//		collect_Assignments((*it), sigNext, m_assignments);
//		it++;
//		collect_Assignments((*it), sigNext, m_assignments);
//	}
//	else
//	{
//		if (op)
//		{
//			InstToSetM m_assignmentsTmp;
//			const InstL* ch = top->get_children();
//			for(InstL::const_iterator it = ch->begin(); it != ch->end(); it++)
//			{
//				collect_Assignments((*it), (*it), m_assignmentsTmp);
//			}
//
//			InstLL output;
//			InstL outputTemp;
//			cart_product(output, outputTemp, m_assignmentsTmp.begin(), m_assignmentsTmp.end());
//
//			for (InstLL::iterator it = output.begin(); it != output.end(); it++)
//			{
//				cout << "-> " << (*it) << endl;
//				m_assignments[sigNext].insert(OpInst::create(op->get_op(), (*it)));
//			}
//		}
//		else
//		{
//			m_assignments[sigNext].insert(top);
//			cout << "Inserting " << *top << " in " << *sigNext << endl;
//		}
//	}
//	return;
//}

void Reach::collect_Assignments(Inst *top, Inst* sigNext, bool init_visit)
{
	if (init_visit) {
		Inst::init_visit();
	}
	if (top->get_visit()) {
		return;
	}
	top->set_visit();

//	cout << "top: " << *top << endl;

	OpInst* op = OpInst::as(top);
	if (op && op->get_op() == OpInst::Ternary)
	{
		const InstL* ch = top->get_children();
		InstL::const_iterator it = ch->begin();
		it++;
		collect_Assignments((*it), sigNext, false);
		it++;
		collect_Assignments((*it), sigNext, false);
	}
	else
	{
		_m_assignments[sigNext].push_back(top);
//		cout << "Inserting " << *top << " in " << *sigNext << endl;
	}
	return;
}

///// nextAllwed = 0 (Check for next sigs and do not add such == or != which contains next sigs)
///// else (Don't check next sigs)
//void Reach::collect_Eq(Inst *top, int nextAllowed, bool init_visit)
//{
//	if (init_visit) {
//		Inst::init_visit();
//	}
//	if (top->get_visit()) {
//		return;
//	}
//	top->set_visit();
//
////	cout << "top: " << *top << endl;
//
//	OpInst* op = OpInst::as(top);
//	if (op)
//	{
//		switch(op->get_op())
//		{
//		case OpInst::LogNot:
//		case OpInst::LogAnd:
//		case OpInst::LogOr:
//		case OpInst::Ternary:
//			{
////				if (nextAllowed == 0 && op->get_op() == OpInst::LogNot)
////				{
////					Inst* ch = op->get_children()->front();
////					assert(ch);
////					if (SigInst::as(ch))
////					{
////						if (find_next(op, true))
////							return;
////						else
////						{
////							// TODO
////						}
////					}
////				}
//
//				const InstL* ch = top->get_children();
//				for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it) {
//					Inst * tve = *it;
//					collect_Eq(tve, false);
//				}
//			}break;
//		case OpInst::Eq:
//			{
//				if (nextAllowed == 0)
//				{
//					if (find_next(op, true))
//						return;
//				}
//
//				_s_conditions.insert(op);
//				_s_conditions_next.insert(all_pre2next(op, true));
////				cout << "Inserting " << *op << endl;
//				if (nextAllowed == 0)
//				{
//					AVR_LOG(15, 0, "\t\t(adding predicate " << *op << ")" << endl);
//#ifdef ASSERT_DIFFERENT_LEMMA_CONSTANTS
//					Inst* rhs = op->get_children()->back();
//					NumInst* newNum = NumInst::as(rhs);
//					if (!newNum)
//					{
//						Inst* lhs = op->get_children()->front();
//						newNum = NumInst::as(lhs);
//						assert(newNum);
//					}
//					if (newNum->get_distinct() == false && newNum->get_size() != 1)
//					{
//						for (NumInst::NumHashM::iterator it = NumInst::hm_NumInst.begin(); it != NumInst::hm_NumInst.end(); it++)
//						{
//							if ((*it).second != newNum && (*it).second->get_size() == newNum->get_size())
//							{
//								NumInst* oldNum = NumInst::as((*it).second);
//								assert(oldNum);
//								if (oldNum->get_distinct() == true)
//									_new_refs.push_back(OpInst::create(OpInst::Eq, newNum, (*it).second));
//							}
//						}
//						newNum->set_distinct();
//					}
//#endif
//				}
//			}break;
//		case OpInst::NotEq:
//			{
//				if (nextAllowed == 0)
//				{
//					if (find_next(op, true))
//						return;
//				}
//
//				Inst* tmp = OpInst::create(OpInst::LogNot, op);
//				_s_conditions.insert(tmp);
//				_s_conditions_next.insert(all_pre2next(tmp, true));
////				cout << "Inserting " << *tmp << endl;
//				if (nextAllowed == 0)
//				{
//					AVR_LOG(15, 0, "\t\t(adding predicate " << *tmp << ")" << endl);
//#ifdef ASSERT_DIFFERENT_LEMMA_CONSTANTS
//					Inst* rhs = tmp->get_children()->back();
//					NumInst* newNum = NumInst::as(rhs);
//					if (!newNum)
//					{
//						Inst* lhs = tmp->get_children()->front();
//						newNum = NumInst::as(lhs);
//						assert(newNum);
//					}
//					if (newNum->get_distinct() == false && newNum->get_size() != 1)
//					{
//						for (NumInst::NumHashM::iterator it = NumInst::hm_NumInst.begin(); it != NumInst::hm_NumInst.end(); it++)
//						{
//							if ((*it).second != newNum && (*it).second->get_size() == newNum->get_size())
//							{
//								NumInst* oldNum = NumInst::as((*it).second);
//								assert(oldNum);
//								if (oldNum->get_distinct() == true)
//									_new_refs.push_back(OpInst::create(OpInst::Eq, newNum, (*it).second));
//							}
//						}
//						newNum->set_distinct();
//					}
//#endif
//				}
//			}break;
//		}
//	}
//	return;
//}
//
//void Reach::collect_simulation_Eq(Inst *top, InstS& eqList, bool init_visit)
//{
//	if (init_visit) {
//		Inst::init_visit();
//	}
//	if (top->get_visit()) {
//		return;
//	}
//	top->set_visit();
//
////	cout << "top: " << *top << endl;
//
//	OpInst* op = OpInst::as(top);
//	if (op)
//	{
//		switch(op->get_op())
//		{
//			case OpInst::LogNot:
//			case OpInst::LogAnd:
//			case OpInst::LogOr:
//			case OpInst::Ternary:
//			{
//				const InstL* ch = top->get_children();
//				for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it) {
//					Inst * tve = *it;
//					collect_simulation_Eq(tve, eqList, false);
//				}
//			}break;
//			case OpInst::Eq:
//			{
//				if (find_next(op, true))
//					return;
//
//				eqList.insert(op);
//			}break;
//			case OpInst::NotEq:
//			{
//				if (find_next(op, true))
//					return;
//
//				Inst* tmp = OpInst::create(OpInst::LogNot, op);
//				eqList.insert(tmp);
//			}break;
//		}
//	}
//	return;
//}

void Reach::collect_OR(Inst *top, bool init_visit) {
	if (init_visit) {
		//		Inst::init_visit();
		_collected_OR.clear();
	}
	// 	if (top->get_visit()) {
	// 		return;
	// 	}
	// 	top->set_visit();

	OpInst* op = OpInst::as(top);
	if (op && (op->get_op() == OpInst::LogOr)) {
		const InstL* ch = top->get_children();
		for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it) {
			Inst * tve = *it;
			OpInst* op2 = OpInst::as(tve);
			if (op2 && (op2->get_op() == OpInst::LogOr)) {
				collect_OR(tve);
			} else {
				{
					_collected_OR.push_back(tve);
				}
			}
		}
	} else {
		Inst * tve = top;
		{
			_collected_OR.push_back(tve);
		}
	}
	return;
}

void Reach::collect_Ternary(Inst *top, bool init_visit) {
	if (init_visit) {
		//		Inst::init_visit();
		_collected_Ternary.clear();
	}
	// 	if (top->get_visit()) {
	// 		return;
	// 	}
	// 	top->set_visit();

	OpInst* op = OpInst::as(top);
	if (op && (op->get_op() == OpInst::Ternary))
	{
		const InstL* ch = top->get_children();
		InstL::const_iterator it = ch->begin();
		Inst* tmp1;
		Inst* tmp2;
		tmp1 = (*it);
		it++;
		tmp2 = (*it);
		_collected_Ternary.push_back(make_pair(tmp1, tmp2));
		it++;
		collect_Ternary((*it));
	}
	else
	{
		/// Do nothing
	}
	return;
}

/// Aman
/// Checks SAT on conjunct_query && _negated_refs
/// Asserts SAT (UNSAT) on result when forceRes equals 1 (0) respectively
/// Default mode is abstract
/// END
int Reach::check_query (InstL& conjunct_query, string comment, int forceRes, bool abstract)
{
	AVR_LOG(13, 3, comment << endl);
	for (InstL::iterator it3 = _negated_refs.begin(); it3 != _negated_refs.end(); ++it3)
		conjunct_query.push_back(*it3);

	AVR_LOG(13, 7, "Query :" << conjunct_query << endl);
	Inst* ve_query = OpInst::create(OpInst::LogAnd, conjunct_query);

	SOLVER_AB* solver;
	bool q_result;
	if (abstract)
	{
		SOLVER_AB int_solver(_abstract_mapper, AVR_EXTRA_IDX, false, regular);
		solver = &int_solver;
		int_solver.s_assert(ve_query);
		q_result = int_solver.s_check(0);

	}
	else
	{
		SOLVER_AB int_solver(_abstract_mapper, AVR_EXTRA_IDX, false, regular);
		solver = &int_solver;
		int_solver.s_assert(ve_query);
		q_result = int_solver.s_check(0);
	}
	AVR_LOG(13, 3, "Gives " << (q_result ? "SAT" : "UNSAT") << endl);

	if (q_result && (forceRes == 0))
	{
    retrieve_cex_val(ve_query, solver, abstract, true);
//    print_abstract_min_term();

		AVR_LOG(13, 0, "Assertion UNSAT failed");
		assert(0);
	}
	else if (!q_result && (forceRes == 1))
	{
		AVR_LOG(13, 0, "Assertion SAT failed");
		assert(0);
	}

	return q_result;
}

void Reach::collect_inputs(Inst *top, InstS &s_inputs, bool init_visit) {
	if(init_visit){
		Inst::init_visit();
	}
	if(top->get_visit()){
		return;
	}
	top->set_visit();

	SigInst *sig_top = SigInst::as(top);
	if(sig_top && (Inst::_s_reg.find(top) == Inst::_s_reg.end())){
		if(!Inst::has_trelation(top)){
		//if((sig_top->get_name()).find("$next") == string::npos){
			s_inputs.insert(top);
		}
	}else{
		const InstL* ch = top->get_children();
		if (ch) {
			for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it) {
				collect_inputs(*it, s_inputs, false);
			}
		}
	}
}

void Reach::all_pre2next(InstL& viol)
{
	for (auto& v: viol)
		v = Inst::all_pre2next(v);
}

Inst *Reach::replace_inputs_with_val(Inst *e, bool init_visit) {
	Inst *res = e;
	if (init_visit) {
		Inst::init_visit2();
	}
	if (e->get_visit2()) {
		return e->acex_coi;
	}
	e->set_visit2();

	const InstL* ch = e->get_children();
	if (ch) {
		bool changed = false;
		InstL newl;
		for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it)
		{
			if ((*it)->get_type() == Num || (*it)->get_type() == Const) {
				//cout << *(*it) << endl;
				newl.push_back(*it);
				continue;
			}
			Inst *tve;
			/// Aman
			if ((*it)->get_type() == Sig)
			{
				SigInst* sig = SigInst::as(*it);
				if (Inst::_m_next_input_pre.find(sig) != Inst::_m_next_input_pre.end())
				{
					if (sig->get_size() == 1)
						tve = NumInst::create(sig->get_bval(), 1, SORT());
					else
						tve = NumInst::create(*sig->get_ival(), sig->get_size(), sig->get_sort());
					changed = true;
				}
				else
				{
					if (Inst::_s_inp.find(sig) != Inst::_s_inp.end())
					{
						if (sig->get_size() == 1)
							tve = NumInst::create(sig->get_bval(), 1, SORT());
						else
							tve = NumInst::create(*sig->get_ival(), sig->get_size(), sig->get_sort());
						changed = true;
					}
					else
					{
						tve = sig;
					}
				}
			}
			else
			{
				tve = replace_inputs_with_val(*it);
				if (tve != (*it))
					changed = true;
			}
			newl.push_back(tve);
			/// END
		}
		if (changed)
		{
			res = e->apply_children(newl);
		}
	}
	else
	{
		SigInst* sig = SigInst::as(e);
		if (sig)
		{
			if (Inst::_m_next_input_pre.find(sig) != Inst::_m_next_input_pre.end())
			{
				if (sig->get_size() == 1)
					res = NumInst::create(sig->get_bval(), 1, SORT());
				else
					res = NumInst::create(*sig->get_ival(), sig->get_size(), sig->get_sort());
			}
			else
			{
				if (Inst::_s_inp.find(sig) != Inst::_s_inp.end())
				{
					if (sig->get_size() == 1)
						res = NumInst::create(sig->get_bval(), 1, SORT());
					else
						res = NumInst::create(*sig->get_ival(), sig->get_size(), sig->get_sort());
				}
				else
				{
					res = sig;
				}
			}
		}
	}
	e->acex_coi = res;

	return res;
}

int Reach::expand_via_pme (InstL& viol)
{
	/// Random stuff
//	InstLL muses;
//	InstL dummy;
//	InstL viol_copy = viol;
//	int res = _pme_solver->get_muses(20, dummy, viol_copy, muses);
//	int count = 0;
//	REACH_COUT_A("Printing Muses" << endl);
//	for (InstLL::iterator it = muses.begin(); it != muses.end(); it++)
//	{
//		REACH_COUT_A("[" << count++ << "] " << *it << endl);
//	}
//	return 0;
	/// END

#ifdef AVR_PME_SOLVER_ENABLE
//if(_pme_fail_cnt < 3)
{
	InstL conjunct_m0;
	int res = _pme_solver->get_mus(20, viol, conjunct_m0);

	if(res == 3)
	{
		AVR_LOG(1, 0, "%%	5 _pme_solver->get_mus() TIMEOUT" << endl);
		#ifdef AVR_PME_SOLVER_ENABLE
		InstL conjunct_me;
		conjunct_me.push_back(_ve_model);
		conjunct_me.push_back(_ve_prop_eq_1);
		conjunct_me.push_back(_ve_model_nsf);
		conjunct_me.push_back(_ve_model_next);
		conjunct_me.push_back(_ve_prop_next_eq_1);
		for (InstL::iterator it3 = _negated_refs.begin(); it3 != _negated_refs.end(); ++it3)
			conjunct_me.push_back(*it3);
		Inst *ve_me = OpInst::create(OpInst::LogAnd, conjunct_me);
		AVR_LOG(1, 5, "P && T && P+:" << *ve_me);
		if (_pme_solver){
			delete _pme_solver;
			_pme_solver = NULL;
		}
		_pme_solver = new z3_API(&_abstract_mapper, AVR_PME_SOLVER_BA_IDX);
		_pme_solver->s_assert(ve_me);

		REACH_COUT_A("Trying expanding : " << viol << endl);
		res = _pme_solver->get_mus(0, viol, conjunct_m0);
		#endif
	}

	// #ifdef AVR_REMOVE_INPUT_FROM_CUBE	// we should not do this
					// input information is critical for our current DP refinement routine
					// In the DP ref routine, we only checks to see if there exists a concrete state
					// in the abstract cube, and if the input restrictions are valid in a concrete level
					// Therefore, if we remove the input information, we cannot check the second one.
	// 			InstL temp_viol;
	// 			for (InstL::iterator cc_it = conjunct_m0.begin(); cc_it != conjunct_m0.end(); ++cc_it) {
	// 				Inst *tve = *cc_it;
	// 				if((check_term_type(tve) & 2) == 0){
	// 					temp_viol.push_front(tve);
	// 				}else{	// if there exists inputs in this term-level literal
	// 					#ifdef _DEBUG_MODE_
	// 					//if((tve->get_type() == Op) && ((OpInst::as(tve))->get_op() == OpInst::Eq)){
	// 					if(1){
	// 						cout << "contains inputs: ";
	// 						node_count(tve, true);
	// 						if(_node_cnt > 10){
	// 							new_print(cout, tve, true);
	// 						}else{
	// 							cout << *tve << endl;
	// 						}
	// 					}
	// 					#endif
	// 				}
	// 			}
	// 			conjunct_m0 = temp_viol;
	// #endif
	struct rusage usage;
	struct timeval start_time, end_time;
	long long time_diff;
	TIME_E(start_time, end_time, _pme_time);
	AVR_LOG(1, 1, "$$ pme_solver->get_mus: " << res << ", " << viol.size() << " => " << conjunct_m0.size() << endl);
	AVR_LOG(1, 1, "prop me, res: " << (res ? "SUCC" : "FAIL") << ", idx: " << _frame_idx << ", runtime: " << double(time_diff)/1000000 << endl);

	if (res == 1)
	{
		_pme_succ_cnt++;
		_pme_literals_before += viol.size();
		_pme_literals_after += conjunct_m0.size();
		AVR_LOG(1, 4, "_viol after get_mus:" << _viol);
		viol = conjunct_m0;
	}
	else
	{
		_pme_fail_cnt++;
#ifdef AVR_PPC_SOLVER_ENABLE
		TIME_S(start_time);
		res = _ppc_solver->get_partial_cex(refined_viol, conjunct_m0);
		TIME_E(start_time, end_time, _pme_time);
		AVR_LOG(1, 1, "$$ ppc_solver->get_partial_cex: " << res << ", " << refined_viol.size() << " => " << conjunct_m0.size() << endl);
		AVR_LOG(1, 2, "prop pc, res: " << (res ? "SUCC" : "FAIL") << ", idx: " << _frame_idx << ", runtime: " << double(time_diff)/1000000 << endl);
		if (res == 1) {
			_viol = conjunct_m0;
			AVR_LOG(1, 4, "_viol after get_mus:" << _viol);
		}
#endif
	}
	return res;
}
#endif

	return 3;
}

void Reach::collect_all_abstract_min_terms(Solver* solver, map< int, MIN_TERMS_ABSTRACT_DETAILED >& allMinTerms, Inst* full_formula, bool concreteOnly)
{
  int res = solver->s_check(concreteOnly ? BV_QUERY_TIMEOUT : AB_QUERY_TIMEOUT, true);
  if (res == AVR_QSAT)
  {
    _min_term.clear();
    retrieve_cex_val(full_formula, solver, !concreteOnly, true, false);

    MIN_TERMS_ABSTRACT_DETAILED pre;
    model_project(_min_term.s, pre.s, "pre", false, true);
    uniquify_solution(pre.s);
    InstL minTermConditions;
    add_modify_solution(solver, pre.s, minTermConditions, "");

    pre.id = allMinTerms.size();

    Inst* newCube = OpInst::create(OpInst::LogAnd, minTermConditions);
    pre.allConditions = newCube;
    pre.trueId = newCube->get_id();

    if (concreteOnly)
      pre.feasible = "c";
    else {
      SOLVER_BV int_solver(_concrete_mapper, AVR_EXTRA_IDX, false, regular);
      int_solver.assert_all_wire_constraints();
      int_solver.s_assert(newCube);
      int feasible = int_solver.s_check(BV_QUERY_TIMEOUT, false);
      if (feasible == AVR_QSAT)
        pre.feasible = "c";
      else if (feasible == AVR_QUSAT)
        pre.feasible = "a";
      else
        pre.feasible = "?";
    }

    allMinTerms[pre.id] = pre;
    solver->s_assert(OpInst::create(OpInst::LogNot, newCube));
    collect_all_abstract_min_terms(solver, allMinTerms, full_formula, concreteOnly);
  }
}

char Reach::check_abstract_transition(InstL& conjunctTmp, bool concreteOnly)
{
	conjunctTmp.push_back(_ve_model_nsf);
	if (!concreteOnly) {
    for (InstL::iterator it = _negated_refs.begin(); it != _negated_refs.end(); it++)
    {
      conjunctTmp.push_back((*it));
    }
	}
	Inst* cube = OpInst::create(OpInst::LogAnd, conjunctTmp);

	if (concreteOnly) {
    SOLVER_BV int_solver(_concrete_mapper, AVR_EXTRA_IDX, false, regular);
    int_solver.assert_all_wire_constraints();
    int_solver.s_assert(cube);
    int res_c = int_solver.s_check(BV_QUERY_TIMEOUT, false);
    if (res_c == AVR_QSAT)
      return 'c';
    else if (res_c == AVR_QUSAT)
      return '-';
    else
      return '?';
	}
	else {
    SOLVER_AB solver(_abstract_mapper, AVR_EXTRA_IDX, false, regular);
    solver.s_assert(cube);
    int res = solver.s_check(AB_QUERY_TIMEOUT, false);
    if (res == AVR_QSAT)
    {
      SOLVER_BV int_solver(_concrete_mapper, AVR_EXTRA_IDX, false, regular);
      int_solver.assert_all_wire_constraints();
      int_solver.s_assert(cube);
      int res_c = int_solver.s_check(BV_QUERY_TIMEOUT, false);
      if (res_c == AVR_QSAT)
        return 'c';
      else if (res_c == AVR_QUSAT)
        return 'a';
      else
        return '?';
    }
    else if (res == AVR_QUSAT)
      return '-';
    else
      return '?';
	}
}

Inst* Reach::try_intermediate_form(Inst* e)
{
	return e;
	OpInst* op = OpInst::as(e);
	if (op)
	{
		Inst* w = op->get_wire();
		if (w)
		{
//			cout << "(" << *e << " is " << *w << ")" << endl;
			return w;
		}

		Inst* n_e = OpInst::create(OpInst::LogNot, e);
		OpInst* n_op = OpInst::as(n_e);
		if (n_op)
		{
			Inst* n_w = n_op->get_wire();
			if (n_w)
			{
				Inst* tmp = OpInst::create(OpInst::LogNot, n_w);
//				cout << "(" << *e << " is " << *tmp << ")" << endl;
				return tmp;
			}
		}
	}
	return e;
}

int Reach::find_value (Inst* rel, Inst* lhs, Inst* rhs)
{
	assert(rel->get_size() == 1);

	OpInst* op = OpInst::as(rel);
	if (op && op->get_euf_func_name() == "0")
	{
		if (op->get_op() == OpInst::LogNot)
		{
			lhs = op->get_children()->front();
			rhs = NumInst::create(1, 1, SORT());
			return 0;
		}
		else if (op->get_op() == OpInst::NotEq)
		{
			lhs = op->get_children()->front();
			rhs = op->get_children()->back();

			if (lhs->get_type() == Num)
			{
				Inst* tmp = lhs;
				lhs = rhs;
				rhs = tmp;
			}

			if (rhs->get_type() == Num)
				return 0;
			else
				return -1;
		}
		else if (op->get_op() == OpInst::Eq)
		{
			lhs = op->get_children()->front();
			rhs = op->get_children()->back();

			if (lhs->get_type() == Num)
			{
				Inst* tmp = lhs;
				lhs = rhs;
				rhs = tmp;
			}

			if (rhs->get_type() == Num)
				return 0;
			else
				return -1;
		}
		else
		{
			assert(0);
		}
	}
	else
	{
		lhs = rel;
		rhs = NumInst::create(1, 1, SORT());
		return 1;
	}
}

bool Reach::is_redundant (Inst* rel)
{
	if (rel)
	{
		assert(rel->get_size() == 1);

		OpInst* op = OpInst::as(rel);
		if (op && op->get_euf_func_name() == "0")
		{
			Inst* lhs = op->get_children()->front();
			Inst* rhs = op->get_children()->back();

			if (op->get_op() == OpInst::NotEq)
			{
				if (lhs == rhs)
					return true;

#ifdef ASSERT_DISTINCT_NUMBERS
				if (lhs->get_type() == Num && rhs->get_type() == Num)
					return true;
#endif
			}
			else if (op->get_op() == OpInst::Eq)
			{
				if (lhs == rhs)
					return true;
			}
			else
			{
//				assert(op->get_op() == OpInst::LogNot);
			}
		}
		else
		{
			if (rel->get_type() == Num)
			{
				NumInst* num = NumInst::as(rel);
				assert(num->get_num() == 0 || num->get_num() == 1);
				return true;
			}
		}
	}
	return false;
}

void Reach::add_fapps_constraints(InstL& viol, InstL& inputConstraints, InstType type)
{
	bool print = true;

	if (type == Op || type == Sig)
		print = true;

	InstS newConstraints;
	InstS sigConstSet;
	map<string, InstL> funcApps;
	Inst::init_visit();
	for (auto& c: inputConstraints)
	{
		get_func_applications(funcApps, c);
	}

	for (auto& func: funcApps)
	{
//		if (print)
//		{
//			AVR_LOG(15, 0, "\t\t[f] " << func.first << endl);
//			for (auto& f: func.second)
//				AVR_LOG(15, 0, "\t\t\t" << *f << endl);
//		}

		int numArgs = func.second.front()->get_children()->size();
		vector < map< mpz_class, InstS > > compareList;
		compareList.resize(numArgs);
		for (auto& app: func.second)
		{
			int argNum = 0;
			for (auto& arg: *(app->get_children()))
			{
				if (arg->get_type() == type || arg->get_type() == Num || arg->get_type() == Sig)
				{
					if (arg->get_size() == 1)
					{
//						if (arg->get_bval())
//							compareList[argNum][Inst::_mpz_one].insert(arg);
//						else
//							compareList[argNum][Inst::_mpz_zero].insert(arg);
					}
					else
						compareList[argNum][*arg->get_ival()].insert(arg);
				}
				argNum++;
			}
		}
		for (auto& map: compareList)
		{
			InstL repList;
			for (auto& args: map)
			{
				if (args.second.size() == 1)
					repList.push_back(*(args.second.begin()));
				else
				{
					InstS::iterator sit = args.second.begin();
					Inst* leader = (*sit);
					sit++;
					Inst* constant = NULL;
					if (leader->get_type() == Num)
					{
						constant = leader;
						newConstraints.insert(OpInst::create(OpInst::Eq, (*sit), leader));
						leader = (*sit);
						sit++;
					}
					for (; sit != args.second.end(); sit++)
					{
						if ((*sit)->get_type() == Num)
							constant = (*sit);
						newConstraints.insert(OpInst::create(OpInst::Eq, leader, (*sit)));
					}
					if (constant)
					{
						for (auto& s: args.second)
							if (s != constant)
								sigConstSet.insert(s);
					}
					repList.push_back(leader);
				}
			}
			for (InstL::iterator it = repList.begin(); it != repList.end(); it++)
			{
				bool isConst = false;
				bool isNum = false;
				if ((*it)->get_type() == Num)
				{
					isNum = true;
				}
				else
				{
					assert((*it)->get_type() == type || (*it)->get_type() == Sig);
					if (sigConstSet.find(*it) != sigConstSet.end())
					{
						isConst = true;
					}
				}

				InstL::iterator it2 = it;
				it2++;

				for (; it2 != repList.end(); it2++)
				{
					bool isConst2 = false;
					bool isNum2 = false;
					if ((*it2)->get_type() == Num)
					{
						isNum2 = true;
					}
					else
					{
						assert((*it2)->get_type() == type || (*it2)->get_type() == Sig);
						if (sigConstSet.find(*it2) != sigConstSet.end())
						{
							isConst2 = true;
						}
					}

					if (isNum && isNum2)
							continue;
					else if (isConst && isNum2)
						continue;
					else if (isConst2 && isNum)
						continue;

					Inst* newC;
					if (isNum2)
						newC = OpInst::create(OpInst::NotEq, *it, *it2);
					else
						newC = OpInst::create(OpInst::NotEq, *it2, *it);

					newC = try_intermediate_form(newC);
					newConstraints.insert(newC);
				}
			}
		}
	}
	for (auto& c: newConstraints)
	{
		viol.push_back(c);
		if (print)
			AVR_LOG(15, 0, "\t\t[p]: " << *c << endl);
	}
}

void Reach::project_abstract_uf(int pmode, InstL& viol, map< string, map< mpz_class, InstL > >& relevantUFs)
{
	bool print = false;
	if (pmode == 1)
		print = true;

	for (auto& uf: relevantUFs)
	{
		map< mpz_class, InstL >& mapUF = uf.second;

		for (map< mpz_class, InstL >::iterator mit = mapUF.begin(); mit != mapUF.end(); mit++)
		{
			InstL& eqUF = (*mit).second;

			InstL::iterator lit = eqUF.begin();
			Inst* rep = *lit;
			lit++;

			InstS addedEq;
			for (; lit != eqUF.end(); lit++)
			{
				if ((*lit) != rep)
				{
					Inst* eq = OpInst::create(OpInst::Eq, rep, (*lit));
					if (addedEq.find(eq) == addedEq.end())
					{
						AVR_LOG(15, 0, "\t\t\t(adding uf =: " << *eq << ")\n");
						viol.push_back(eq);
						addedEq.insert(eq);
					}
				}
			}

			map< mpz_class, InstL >::iterator mit2 = mit;
			mit2++;
			for (; mit2 != mapUF.end(); mit2++)
			{
				Inst* neq = OpInst::create(OpInst::NotEq, rep, (*mit2).second.front());
				AVR_LOG(15, 0, "\t\t\t(adding uf !=: " << *neq << ")\n");
				viol.push_back(neq);
			}
		}
	}
}


void Reach::add_predicate_constraints(Solver* solver, InstL& predConstraints, InstS& wireSet)
{
	for (InstS::iterator it = _s_conditions_pre.begin(); it != _s_conditions_pre.end(); it++)
	{
		Inst* tve = (*it);
		int tveVal = get_bval(solver, tve);
//		cout << "(pred) tveVal: " << *tve << " -> " << tveVal << endl;
		OpInst* op = OpInst::as(tve);
		if (op)
		{
			if (op->get_op() == OpInst::Eq)
			{
				Inst* lhs = op->get_children()->front();
				Inst* rhs = op->get_children()->back();

//					retrieve_cex_val(lhs, solver, true, false);
//					retrieve_cex_val(rhs, solver, true, false);
				int val = INVALID_SVAL;
				if (lhs->get_size() == 1)
				{
					int lhsVal = get_bval(solver, lhs);
					int rhsVal = get_bval(solver, rhs);
					if ((lhsVal != INVALID_SVAL) && (rhsVal != INVALID_SVAL))
					{
						val = (lhsVal == rhsVal);
//							cout << "lhs: " << *lhs << endl;
//							cout << "rhs: " << *rhs << endl;
//							cout << "Adjusting value: " << lhsVal << " =/ " << rhsVal << endl;
					}
				}
				else
				{
					mpz_class* lhsVal = get_ival(solver, lhs);
					mpz_class* rhsVal = get_ival(solver, rhs);
					if ((lhsVal != INVALID_SMPZ) && (rhsVal != INVALID_SMPZ))
					{
						val = (*lhsVal == *rhsVal);
//							cout << "lhs: " << *lhs << endl;
//							cout << "rhs: " << *rhs << endl;
//							cout << "Adjusting value: " << lhsVal << " =/ " << rhsVal << endl;
					}
				}
				if (tveVal != INVALID_SVAL) {
					if (tveVal != val) {
						if (lhs->get_size() == 1) {
								cout << "lhs: " << *lhs << "\t" << lhs->get_bval() << endl;
								cout << "rhs: " << *rhs << "\t" << rhs->get_bval() << endl;
						}
						else {
							cout << "lhs: " << *lhs << "\t" << *lhs->get_ival() << endl;
							cout << "rhs: " << *rhs << "\t" << *rhs->get_ival() << endl;
						}
						Inst* tmp = OpInst::create(OpInst::Eq, lhs, rhs);
						Inst* tmpNeg = OpInst::create(OpInst::NotEq, lhs, rhs);
						cout << "tmp:    " << *tmp << "\t" << tmp->get_bval() << endl;
						cout << "tmpNeg: " << *tmpNeg << "\t" << tmpNeg->get_bval() << endl;
						cout << "tve:    " << *tve << "\t" << tve->get_bval() << endl;

						cout << "tmp:    " << *tmp << "\t" << get_bval(solver, tmp) << endl;
						cout << "tmpNeg: " << *tmpNeg << "\t" << get_bval(solver, tmpNeg) << endl;
						cout << "tve:    " << *tve << "\t" << get_bval(solver, tve) << endl;
						assert(0);
					}
				}
				tve->set_bval(val);
				tveVal = val;
			}
			else if ((op->get_op() == OpInst::NotEq) || (op->get_op() == OpInst::LogNot))
				assert(0);
			else
			{
//					retrieve_cex_val(tve, solver, true, false);
			}
		}

		if (tveVal == 1)
		{
			predConstraints.push_back(tve);
#ifndef SUBSTITUTE
			collect_wire(tve, wireSet, true);
#endif
//			cout << "Adding to viol: " << *tve << endl;
		}
		else if (tveVal == 0)
		{
			tve = OpInst::create(OpInst::LogNot, tve);
			tve->set_bval(1);

			predConstraints.push_back(tve);
#ifndef SUBSTITUTE
			collect_wire(tve, wireSet, true);
#endif
//			cout << "Adding to viol: " << *tve << endl;
		}
		else
		{
			assert(tveVal == INVALID_SVAL);
//			cout << *tve << endl;
//			assert(0);

			continue;
//				cout << *(*it) << endl;
//				cout << (*it)->cex_val << "  " << (*it)->cex_mpz << endl;
//				cout << *((*it)->get_children()->front()) << "  " << (*it)->get_children()->front()->cex_mpz << endl;
//				cout << *((*it)->get_children()->back()) << "  " << (*it)->get_children()->back()->cex_mpz << endl;
//				assert(0);
		}

#ifdef DO_CORRECTNESS_CHECKS
		tveVal = tve->get_bval();
		OpInst* op = OpInst::as(tve);
		if (op)
		{
			bool errorFlag = false;
			if ((op->get_op() == OpInst::Eq) || (op->get_op() == OpInst::NotEq))
			{
				Inst* lhs = op->get_children()->front();
				Inst* rhs = op->get_children()->back();

				bool eq;
				if (lhs->get_size() == 1)
				{
					int lhsVal = lhs->get_bval();
					int rhsVal = rhs->get_bval();
					if (lhsVal == INVALID_SVAL || rhsVal == INVALID_SVAL)
						continue;
					eq = (lhsVal == rhsVal);
				}
				else
				{
					mpz_class lhsVal = lhs->get_ival();
					mpz_class rhsVal = rhs->get_ival();
					if (lhsVal == INVALID_SVAL || rhsVal == INVALID_SVAL)
						continue;
					eq = (lhsVal == rhsVal);
				}

				if (op->get_op() == OpInst::Eq)
				{
					if (tveVal != eq)
						errorFlag = true;
				}
				else
				{
					if (tveVal == eq)
						errorFlag = true;
				}

				if (errorFlag)
				{
					cout << "Error in handling learnt predicate: " << *tve << endl;
					cout << *tve << "  " << tveVal << endl;
					if (lhs->get_size() == 1)
					{
						cout << *lhs << "  " << lhs->get_bval() << endl;
						cout << *rhs << "  " << rhs->get_bval() << endl;
					}
					else
					{
						cout << *lhs << "  " << lhs->get_ival() << endl;
						cout << *rhs << "  " << rhs->get_ival() << endl;
						cout << "rkey: " << Inst::get_rkey() << " (solver: " << Inst::get_bIdx() << ")" << endl;
//						yices_print_model(stdout, solver->m_model);
					}
					assert(0);
				}
			}
		}
#endif
	}
}

void Reach::print_backward_coi_matrix()
{
	InstL sv;
	for (auto& m: Inst::_s_reg)
		sv.push_back(m);
	InstL inp;
	for (auto& m: Inst::_s_inp)
		inp.push_back(m);

	sv.sort(CompareBySz);
	inp.sort(CompareBySz);

	int sz = Inst::_m_backward_coi.size();
	assert(sv.size() == sz);

	string fname = _config->get_working_dir() + "/data/parse.results";
	ofstream outFile;
	outFile.open(fname.c_str(), ios_base::app);

	AVR_FILE("\n");
	AVR_FILE("-----------------\n");
	AVR_FILE("Dependency Matrix\n");
	AVR_FILE("-----------------\n");
//	AVR_LOG(15, 0, "\n---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------\n");
	AVR_FILE("  \tComb. Depth");
//	AVR_LOG(15, 0, "  \tComb. Depth\t|");
	for (auto& pre: sv)
	{
		AVR_FILE("\t" << *pre);
//		AVR_LOG(15, 0, "\t" << *pre);
	}
	AVR_FILE("\t|");
//	AVR_LOG(15, 0, "\t|");
	for (auto& in: inp)
	{
		AVR_FILE("\t" << *in);
//		AVR_LOG(15, 0, "\t" << *in);
	}
	AVR_FILE("\t\n");
//	AVR_LOG(15, 0, "\t|\n");

	AVR_FILE("  \t           ");
//	AVR_LOG(15, 0, "  \t           \t|");
	for (auto& pre: sv)
	{
		AVR_FILE("\t(" << pre->get_size() << "-bit)");
//		AVR_LOG(15, 0, "\t(" << pre->get_size() << "-bit)");
	}
	AVR_FILE("\t|");
//	AVR_LOG(15, 0, "\t|");
	for (auto& in: inp)
	{
		AVR_FILE("\t(" << in->get_size() << "-bit)");
//		AVR_LOG(15, 0, "\t(" << in->get_size() << "-bit)");
	}
	AVR_FILE("\t\n\n");
//	AVR_LOG(15, 0, "\t|");
//	AVR_LOG(15, 0, "\n---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------\n");

	for (auto& pre: sv)
	{
		Inst* lhs = Inst::_m_pre_to_next[pre];

		InstS& depSet = Inst::_m_backward_coi[lhs];
		// TODO: trel: resolve
		Inst* rhsT = Inst::_m_sn[lhs].first;
		int maxDistance = compute_comb_distances(rhsT);

		AVR_FILE(maxDistance << "\t(" << lhs->get_size() << "-bit) " << *lhs);
//		AVR_LOG(15, 0, maxDistance << "\t(" << lhs->get_size() << "-bit) " << *lhs << "\t|");
		for (auto& pre: sv)
		{
			if (depSet.find(pre) != depSet.end())
			{
				AVR_FILE("\t" << pre->fcCombDist);
//				AVR_LOG(15, 0, "\t" << pre->fcCombDist);
			}
			else
			{
				AVR_FILE("\t-");
//				AVR_LOG(15, 0, "\t-");
			}
		}
		AVR_FILE("\t|");
//		AVR_LOG(15, 0, "\t|");
		for (auto& in: inp)
		{
			if (depSet.find(in) != depSet.end())
			{
				AVR_FILE("\t" << in->fcCombDist);
//				AVR_LOG(15, 0, "\t" << in->fcCombDist);
			}
			else
			{
				AVR_FILE("\t-");
//				AVR_LOG(15, 0, "\t-");
			}
		}
		AVR_FILE("\t\n");
//		AVR_LOG(15, 0, "\t|\n");
	}
	{
		Inst* lhs = _ve_model->get_children()->front();
		Inst* rhsT = _ve_model->get_children()->back();
		if (lhs != _ve_prop_eq_1)
		{
			Inst* tmp;
			tmp = lhs;
			lhs = rhsT;
			rhsT = tmp;
			if (lhs != _ve_prop_eq_1)
			{
				cout << "LHS: " << *lhs << endl;
				cout << "RHS: " << *rhsT << endl;
				cout << "prop: " << *_ve_prop_eq_1 << endl;
				assert(lhs == _ve_prop_eq_1);
			}
		}

		InstS depSet;
		collect_sig(rhsT, depSet, true);

		int maxDistance = compute_comb_distances(rhsT);

		AVR_FILE(maxDistance << "\t(" << lhs->get_size() << "-bit) " << *lhs);
//		AVR_LOG(15, 0, maxDistance << "\t(" << lhs->get_size() << "-bit) " << *lhs << "\t|");
		for (auto& pre: sv)
		{
			if (depSet.find(pre) != depSet.end())
			{
				AVR_FILE("\t" << pre->fcCombDist);
//				AVR_LOG(15, 0, "\t" << pre->fcCombDist);
			}
			else
			{
				AVR_FILE("\t-");
//				AVR_LOG(15, 0, "\t-");
			}
		}
		AVR_FILE("\t|");
//		AVR_LOG(15, 0, "\t|");
		for (auto& in: inp)
		{
			if (depSet.find(in) != depSet.end())
			{
				AVR_FILE("\t" << in->fcCombDist);
//				AVR_LOG(15, 0, "\t" << in->fcCombDist);
			}
			else
			{
				AVR_FILE("\t-");
//				AVR_LOG(15, 0, "\t-");
			}
		}
		AVR_FILE("\t\n");
//		AVR_LOG(15, 0, "\t|\n");
	}
	AVR_FILE("-----------------\n");
//	AVR_LOG(15, 0, "---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------" << endl);

	outFile.close();
}

void Reach::print_backward_coi_list()
{
	InstL sv;
	for (auto& m: Inst::_s_reg)
		sv.push_back(m);

	sv.sort(CompareBySz);

	int sz = Inst::_m_backward_coi.size();
	assert(sv.size() == sz);

	string fname = _config->get_working_dir() + "/data/parse.results";
	ofstream outFile;
	outFile.open(fname.c_str(), ios_base::app);

	AVR_FILE("\n");
	AVR_FILE("-----------------\n");
	AVR_FILE("Dependency List\n");
	AVR_FILE("-----------------\n");
//	AVR_LOG(15, 0, "\n---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------\n");
	AVR_FILE("\n");
//	AVR_LOG(15, 0, "\n---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------\n");

	int depth = 0;

	InstS svDone;
	InstLL qq;
	{
		InstL q;
		Inst* lhs = _ve_model->get_children()->front();
		Inst* rhsT = _ve_model->get_children()->back();
		if (lhs != _ve_prop_eq_1)
		{
			Inst* tmp;
			tmp = lhs;
			lhs = rhsT;
			rhsT = tmp;
			if (lhs != _ve_prop_eq_1)
			{
				cout << "LHS: " << *lhs << endl;
				cout << "RHS: " << *rhsT << endl;
				cout << "prop: " << *_ve_prop_eq_1 << endl;
				assert(lhs == _ve_prop_eq_1);
			}
		}

		InstS depSet;
		collect_sig(rhsT, depSet, true);

		int depCount = 0;
		for (InstS::iterator sit = depSet.begin(); sit != depSet.end(); sit++)
			if (Inst::_s_reg.find(*sit) != Inst::_s_reg.end())
				depCount++;

		vector < int > ufInfo;
		compute_number_uf(rhsT, ufInfo, true);

		AVR_FILE("Depth: " << depth << endl);
		AVR_FILE("\t(" << lhs->get_size() << "-bit) #" << depCount
				<< "\tn" << ufInfo[0]
				<< "\tu" << ufInfo[1]
				<< "\tc" << ufInfo[2]
				<< "\te" << ufInfo[3]
				<< "\t" << *lhs << "\t<= ");
		for (auto& pre: depSet)
		{
			if (Inst::_s_reg.find(pre) != Inst::_s_reg.end())
			{
				if (svDone.find(pre) == svDone.end())
				{
//					svDone.insert(pre);
					q.push_back(pre);
					AVR_FILE(*pre << ", ");
				}
//				AVR_FILE(*pre << ", ");
	//			AVR_FILE(*pre << " (" << pre->fcCombDist << "), ");
			}
		}
		AVR_FILE(endl);
		if (!q.empty())
		{
			for (auto& pre: q)
				svDone.insert(pre);

			q.sort(CompareBySz);
			qq.push_back(q);
		}
	}
	AVR_FILE(endl);

	while (!qq.empty())
	{
//		InstL newCones;

		InstL& qT = qq.front();

		InstL q;
		depth++;
		AVR_FILE("Depth: " << depth << endl);
		while (!qT.empty())
		{
			Inst* s = qT.front();
			qT.pop_front();

			Inst* lhs = Inst::_m_pre_to_next[s];

			auto mit = Inst::_m_numRegs.find(lhs);
			if (mit == Inst::_m_numRegs.end())
			{
				Inst::_m_numRegs[lhs] = 0;
				mit = Inst::_m_numRegs.find(lhs);
			}

			InstS& depSet = Inst::_m_backward_coi[lhs];
			// TODO: trel: resolve
			Inst* rhsT = Inst::_m_sn[lhs].first;

			int depCount = 0;
			for (InstS::iterator sit = depSet.begin(); sit != depSet.end(); sit++)
				if (Inst::_s_reg.find(*sit) != Inst::_s_reg.end())
					depCount++;

			vector < int > ufInfo;
			compute_number_uf(rhsT, ufInfo, true);

			AVR_FILE("\t(" << lhs->get_size() << "-bit) #" << depCount
					<< "\tn" << ufInfo[0]
					<< "\tu" << ufInfo[1]
					<< "\tc" << ufInfo[2]
					<< "\te" << ufInfo[3]
					<< "\t" << *lhs << "\t<= ");
			for (auto& pre: depSet)
			{
				if (Inst::_s_reg.find(pre) != Inst::_s_reg.end())
				{
					if (svDone.find(pre) == svDone.end())
					{
//						svDone.insert(pre);
						q.push_back(pre);
						AVR_FILE(*pre << ", ");

						(*mit).second++;
					}
//					AVR_FILE(*pre << ", ");
	//				AVR_FILE(*pre << " (" << pre->fcCombDist << "), ");
				}
			}
			AVR_FILE(endl);
		}
		AVR_FILE(endl);

		qq.pop_front();
		if (!q.empty())
		{
			for (InstL::iterator qit = q.begin(); qit != q.end();)
			{
				if (svDone.find(*qit) == svDone.end())
				{
					svDone.insert(*qit);
					qit++;
				}
				else
					qit = q.erase(qit);
			}

			q.sort(CompareBySz);
			qq.push_back(q);
		}
	}
	AVR_FILE("-----------------\n");

	_resFile << "seq-dep-depth:\t" << depth << endl;

	outFile.close();
}

void Reach::print_all_abstract_min_term(InstL conjunct_top, Solver* solverIn)
{
#ifdef PERFORMANCE
	return;
#endif

	struct rusage usage;
	struct timeval start_time, end_time;
	long long time_diff;

	TIME_S(start_time);

	int count = 0;
	y2_API* ysolver = static_cast< y2_API* >(solverIn);
	ysolver->enable_model();
	assert(ysolver);
	Solver* solver = ysolver->copy_solver();
	int resQ = solver->s_check(AB_QUERY_TIMEOUT, true);
	assert(resQ == AVR_QSAT);

	bool forceExit = false;
	bool res = true;
	do
	{
		Inst* ve_top;
		if (!conjunct_top.empty())
			ve_top = OpInst::create(OpInst::LogAnd, conjunct_top);
		else
			ve_top = NumInst::create(1, 1, SORT());
		retrieve_cex_val(ve_top, solver, true, true);
		print_solution(_min_term.s, "solution #" + to_string(count));
		res = solver->s_another_solution();
		count++;
		if (count >= 1000)
		{
			forceExit = true;
			break;
		}
	} while (res);

	TIME_E(start_time, end_time, _tb_val_time);

	if (forceExit)
	{
		AVR_LOG(15, 0, "\t(# solutions) " << count << "+" << endl);
	}
	else if (count > 1)
	{
		AVR_LOG(15, 0, "\t(# solutions) " << count << endl);
	}
}

void Reach::print_concrete_min_term(string comment) {
#ifdef AVOID_LARGE_PRINTING
  return;
#endif

	AVR_LOG(4, 0, "Concrete Min Term : " << comment << endl);

	AVR_LOG(4, 0, "Assignments :" << endl);
	for (InstToMpzM::iterator it = _min_term_c.begin(); it != _min_term_c.end(); it++)
	{
		Inst* e = (*it).first;
		if (SigInst::as(e))
			AVR_LOG(4, 0, "--> " << *((*it).first) << " = " << (*it).second << endl);
	}
}

void Reach::collect_func_stat(Inst* top, int& numConst, int& numCF, int& numUF, int& numMux, int& numCc, int& numEx, map< string, int >& ufType, map< string, int >& ccType, map< string, int >& exType, InstS& constants, InstS& regs, InstS& inps, bool init_visit)
{
	if (init_visit) {
		Inst::init_visit();
	}
	if (top->get_visit()) {
		return;
	}
	top->set_visit();

	ExInst* ex = ExInst::as(top);
	if (ex)
	{
		numEx++;
		string eufName = ex->get_euf_func_name();
		map< string, int >::iterator mit = exType.find(eufName);
		if (mit != exType.end())
			(*mit).second++;
		else
			exType[eufName] = 1;
	}
	else
	{
		OpInst* op = OpInst::as(top);
		if (op)
		{
			string eufName = op->get_euf_func_name();
			if (op->get_op() == OpInst::Concat)
			{
				numCc++;
				map< string, int >::iterator mit = ccType.find(eufName);
				if (mit != ccType.end())
					(*mit).second++;
				else
					ccType[eufName] = 1;
			}
			else if (eufName != "0")
			{
				numUF++;
				map< string, int >::iterator mit = ufType.find(eufName);
				if (mit != ufType.end())
					(*mit).second++;
				else
					ufType[eufName] = 1;
			}
			else
			{
				if (op->get_op() == OpInst::Ternary)
					numMux++;
				numCF++;
			}
		}
		else if (top->get_type() == Num)
		{
			constants.insert(top);
			numConst++;
		}
		else if (top->get_type() == Sig)
		{
		  if (Inst::has_trelation(top))
		    regs.insert(top);
		  else if (Inst::_s_reg.find(top) != Inst::_s_reg.end())
        regs.insert(top);
		  else
        inps.insert(top);
		}
	}

	const InstL* tch = top->get_children();
	if (tch) {
		for (InstL::const_iterator tit = tch->begin(); tit != tch->end(); ++tit) {
			collect_func_stat(*tit, numConst, numCF, numUF, numMux, numCc, numEx, ufType, ccType, exType, constants, regs, inps);
		}
	}
}

void Reach::check_correct_lemmas() {
	if (Config::g_bmc_en)
		return;

	struct rusage usage;
	struct timeval start_time, end_time;
	long long time_diff;
	TIME_S(start_time);

	InstL conjunct_reach;
	bool res;
	Solver* int_solver;

	/// Checking lemmas
	{
		WireInst::inc_connect_key();

		conjunct_reach.clear();
//		conjunct_reach.push_back(_ve_prop_eq_1);
		conjunct_reach.push_back(_ve_model);
		conjunct_reach.push_back(_ve_model_next);
		conjunct_reach.push_back(_ve_assume);
		for (auto& v: _assume_T)
			conjunct_reach.push_back(v.first);

//	  InstL wireList;
//    add_all_wires(_ve_model, wireList, true);
//		add_all_wires(_ve_model_next, wireList, true);
//    for (auto& w: wireList)
//    {
//      WireInst* w_lhs = WireInst::as(w);
//      assert(w_lhs);
//      w_lhs->set_connect();
//    }

		for (auto& neg_ref: _negated_refs)
		{
			if (neg_ref == _ve_assume)
				continue;
			if (_all_assumptions.find(neg_ref) != _all_assumptions.end())
				continue;
			if (_assume_T.find(neg_ref) != _assume_T.end())
				continue;

			InstL conjunct_check = conjunct_reach;
			Inst* ref = OpInst::create(OpInst::LogNot, neg_ref);

			conjunct_check.push_back(ref);

//			InstL refWireList;
//			add_all_wires(ref, refWireList, true);
//	    for (auto& w: refWireList)
//	    {
//	      WireInst* w_lhs = WireInst::as(w);
//	      assert(w_lhs);
//	      w_lhs->set_connect();
//	    }

			AVR_LOG(8, 2, "checking lemma #" << neg_ref->get_id() << endl);

			int_solver = new SOLVER_BV(_concrete_mapper, AVR_EXTRA_IDX, false, regular);
			int_solver->assert_all_wire_constraints();

			AVR_LOG(8, 5, "Checking Q:" << conjunct_check);
			Inst* ve_check = OpInst::create(OpInst::LogAnd, conjunct_check);
			res = int_solver->check_sat(ve_check, 0, false);

			if(res == false)
			{
			}
			else
			{
				AVR_LOG(8, 0, "There is a wrong refinement lemma!!!" << endl);
				cout << "Ref: (id: " << neg_ref->get_id() << ") " << *neg_ref << endl;
				cout << "Check Q: " << conjunct_check << endl;

//				res = int_solver->check_sat(ve_check, 0, true);
//				static_cast<SOLVER_BV*>(int_solver)->s_print_model();
				assert(0);
			}
			delete static_cast<SOLVER_BV*>(int_solver);
		}
		AVR_LOG(8, 0, "refinement-lemmas-check successful!" << endl);
	}
	/// END

  TIME_E(start_time, end_time, _cc_time);
}

void Reach::check_correct_invariant(InstL& invariant, bool concrete) {
//  return;
	struct rusage usage;
	struct timeval start_time, end_time;
	long long time_diff;
	TIME_S(start_time);

	InstL conjunct_reach;
	Solver* int_solver;

	/// (assumptions &) Inv & T & !Inv+ [UNSAT is correct]
#ifdef INDUCT_INV_PRINT_ONLY
	if (concrete)
		int_solver = new z3_API(_concrete_mapper, AVR_EXTRA_IDX, false, regular);
	else
		int_solver = new z3_API(_abstract_mapper, AVR_EXTRA_IDX, false, regular);
#else
	if (concrete)
		int_solver = new SOLVER_BV(_concrete_mapper, AVR_EXTRA_IDX, false, regular);
	else
		int_solver = new SOLVER_AB(_abstract_mapper, AVR_EXTRA_IDX, false, regular);
#endif

	int_solver->assert_all_wire_constraints();
	if (_ve_assume != NumInst::create(1, 1, SORT()))
		conjunct_reach.push_back(_ve_assume);
	for (auto v: invariant)
		conjunct_reach.push_back(v);
	conjunct_reach.push_back(_ve_model);
	conjunct_reach.push_back(_ve_model_nsf);
	conjunct_reach.push_back(_ve_model_next);
	if (!concrete) {
		for (InstL::iterator it3 = _negated_refs.begin(); it3 != _negated_refs.end(); ++it3)
			conjunct_reach.push_back(*it3);
	}
	Inst* inv = OpInst::create(OpInst::LogAnd, invariant);
	Inst* invNext = Inst::all_pre2next(inv);
	Inst* dest = OpInst::create(OpInst::LogNot, invNext);
	conjunct_reach.push_back(dest);

	AVR_LOG(8, 6, "Checking Q:" << conjunct_reach);
	int_solver->s_assert(conjunct_reach);
#ifdef INDUCT_INV_PRINT_ONLY
	int_solver->print_query(0, NO_ERROR, "induct");
	cout << "\t(" << (concrete?"concrete":"abstract") << " induction-check query printed)" << endl;
#else
	int res = int_solver->s_check(0, false);
	if(res == AVR_QUSAT)
	{
		AVR_LOG(8, 0, (concrete?"concrete":"abstract") << " induction-check successful!" << endl);
	}
	else if (res == AVR_QSAT)
	{
		AVR_LOG(8, 0, (concrete?"concrete":"abstract") << " induction-check failed." << endl);
//		cout << "Query: " << conjunct_reach << endl;
		assert(0);
	}
	else
	{
		AVR_LOG(8, 0, (concrete?"concrete":"abstract") << " induction-check timed out)" << endl);
	}
#endif

#ifdef INDUCT_INV_PRINT_ONLY
	delete static_cast<z3_API*>(int_solver);
#else
	if (concrete)
		delete static_cast<SOLVER_BV*>(int_solver);
	else
		delete static_cast<SOLVER_AB*>(int_solver);
#endif

	/// END

  TIME_E(start_time, end_time, _cc_inv_time);
}

void Reach::minimize_inductive_invariant(InstL& invariant, bool concrete, bool fastmode) {
	struct rusage usage;
	struct timeval start_time, end_time;
	long long time_diff;
	TIME_S(start_time);

	if (invariant.size() == 1)
		return;

	InstL conjunct_reach;
	int res = AVR_QTO;
	Solver* int_solver;

	/// (assumptions &) Inv & T & !Inv+ [UNSAT is correct]
	long timeout_value = 0;
	if (concrete) {
		int_solver = new SOLVER_BV(_concrete_mapper, AVR_EXTRA_IDX, false, (fastmode) ? mus_core : regular);
		timeout_value = BV_QUERY_TIMEOUT;
	}
	else {
		int_solver = new SOLVER_AB(_abstract_mapper, AVR_EXTRA_IDX, false, (fastmode) ? mus_core : regular);
		timeout_value = AB_QUERY_TIMEOUT;
	}

//	if (!fastmode)
	int_solver->disable_fallback();

	int_solver->assert_all_wire_constraints();
	if (_ve_assume != NumInst::create(1, 1, SORT()))
		conjunct_reach.push_back(_ve_assume);

	conjunct_reach.push_back(_ve_model);
	conjunct_reach.push_back(_ve_model_nsf);
	conjunct_reach.push_back(_ve_model_next);
	if (!concrete) {
		for (InstL::iterator it3 = _negated_refs.begin(); it3 != _negated_refs.end(); ++it3)
			conjunct_reach.push_back(*it3);
	}

//	conjunct_reach.push_back(_ve_prop_next_eq_0);

	AVR_LOG(8, 6, "Checking Q:" << conjunct_reach);
	int_solver->s_assert(conjunct_reach);

	res = int_solver->s_check(0, false);
	if(res == AVR_QUSAT)
	{
		AVR_LOG(8, 0, (concrete?"concrete":"abstract") << " induction-minimization trivially successful!" << endl);
		invariant.clear();
		invariant.push_back(_ve_prop_eq_1);
	}
	else if (res == AVR_QSAT)
	{
		InstL newInv;
		AVR_LOG(8, 0, "running " << (concrete?"concrete":"abstract") << " induction-minimization ("
														 << (fastmode?"fast":"slow") << " mode)" << endl);

		if (fastmode) {
			int_solver->enable_induct_pn();
			int status = int_solver->get_unsat_core(timeout_value, invariant, newInv, num_scalls_sat_correctness, num_scalls_unsat_correctness);
			if (status == AVR_QSAT)
			{
				AVR_LOG(8, 0, (concrete?"concrete":"abstract") << " induction-minimization (fast) failed." << endl);
				assert(0);
			}
			else if (status == AVR_QUSAT)
			{
				AVR_LOG(8, 0, (concrete?"concrete":"abstract") << " induction-minimization (fast) successful (" << invariant.size() << " -> " << newInv.size() << ")" << endl);
				invariant.swap(newInv);
			}
			else
			{
				AVR_LOG(8, 0, "\t(" << (concrete?"concrete":"abstract") << " induction-minimization (fast) timed out)" << endl);
			}
		}
		else {
			int inp_sz = invariant.size();
			newInv.push_back(_ve_prop_eq_1);
			while (!invariant.empty()) {
				Inst* curr = invariant.front();
				invariant.pop_front();
				if (curr == _ve_prop_eq_1)
					continue;

				InstL conjunct_tmp = newInv;
				for (auto& v: invariant)
					conjunct_tmp.push_back(v);
				Inst* tve;
				if (conjunct_tmp.size() == 1)
					tve = conjunct_tmp.front();
				else {
					assert(conjunct_tmp.size() > 1);
					tve = OpInst::create(OpInst::LogAnd, conjunct_tmp);
				}
				tve = OpInst::create(OpInst::LogNot, tve);
				tve = Inst::all_pre2next(tve);
				conjunct_tmp.push_back(tve);
				int_solver->s_assert_retractable(conjunct_tmp);
				int status = int_solver->s_check_assume(timeout_value, false);
				if (status == AVR_QSAT)
				{
					newInv.push_back(curr);
					AVR_LOG(8, 3, "\t(" << (concrete?"concrete":"abstract") << " required: " << *curr << ")" << endl);
				}
				else if (status == AVR_QUSAT)
				{
					AVR_LOG(8, 3, "\t(" << (concrete?"concrete":"abstract") << " not required: " << *curr << ")" << endl);
				}
				else
				{
					newInv.push_back(curr);
					AVR_LOG(8, 0, "\t(" << (concrete?"concrete":"abstract") << " induction-minimization (slow) timed out)" << endl);
				}

				int_solver->s_retract_assertions();

				if ((invariant.size() % 10) == 0) {
					AVR_LOG(8, 0, "\t\t" << invariant.size() << " out of " << inp_sz << " checks remaining" << endl);
				}
			}
			AVR_LOG(8, 0, (concrete?"concrete":"abstract") << " induction-minimization (slow) successful (" << inp_sz << " -> " << newInv.size() << ")" << endl);
			invariant.swap(newInv);
		}
		AVR_LOG(8, 3, "\t(" << (concrete?"concrete":"abstract") << " invariant: " << invariant << ")" << endl);
	}
	else
	{
		AVR_LOG(8, 0, "\t(" << (concrete?"concrete":"abstract") << " induction-minimization timed out)" << endl);
	}

	if (concrete)
		delete static_cast<SOLVER_BV*>(int_solver);
	else {
		delete static_cast<SOLVER_AB*>(int_solver);
	}

	/// END

  TIME_E(start_time, end_time, _cc_inv_time);
}

#if 1
void Reach::check_correctness()
{
	if (Config::g_bmc_en)
		return;

	struct rusage usage;
	struct timeval start_time, end_time;
	long long time_diff;
	TIME_S(start_time);

	int frameIdx = 0;
	for (auto& c: _cubes) {
		AVR_LOG(15, 0, "F[" << frameIdx << "]\tc#" << c.size() << endl);
		frameIdx++;
	}
	AVR_LOG(15, 0, endl);

//#ifndef BMC
//	int converged_frame = 1;
//	for (; converged_frame <= (int)_cubes.size(); converged_frame++) {
//		if (_cubes[converged_frame].empty()) {
//			break;
//		}
//	}
//#else
//	int converged_frame = _cubes.size() - 1;
	int converged_frame = _frame_idx;
	for (; converged_frame >= 0; converged_frame--) {
		if (_cubes[converged_frame].empty()) {
			break;
		}
	}
//#endif

//	cout << _negated_cubes[converged_frame].size() << endl;

//#ifdef RESET_FRAMES_AFTER_FP
//	reset_solv();
//#endif

	_converged_frame = converged_frame;
	_resFile << "frame-conv:\t" << _converged_frame << endl;

	InstL conjunct_fConv;
	negated_cubes(converged_frame, conjunct_fConv);

	InstL conjunct_reach;
	Inst *ve_reach;
	bool res;
	Solver* int_solver;

	AVR_LOG(15, 0, endl);

	/// Checking F[converged] & P [SAT is correct]
	int_solver = new SOLVER_AB(_abstract_mapper, AVR_EXTRA_IDX, false, regular);
	int_solver->assert_all_wire_constraints();
	conjunct_reach.clear();
	conjunct_reach = conjunct_fConv;
	conjunct_reach.push_back(_ve_model);
	conjunct_reach.push_back(_ve_prop_eq_1);
	AVR_LOG(8, 6, "Checking Q:" << conjunct_reach);
	ve_reach = OpInst::create(OpInst::LogAnd, conjunct_reach);
	res = int_solver->check_sat(ve_reach, 0, false);

	if(res == false)
	{
		AVR_LOG(8, 0, "There is a wrong (UNSAT) reachability lemma!!!" << endl);

		SOLVER_MUS tmpSolver(_abstract_mapper, AVR_EXTRA_IDX, true, regular);
		tmpSolver.disable_fallback();
		tmpSolver.assert_all_wire_constraints();
		InstLL muses;
		tmpSolver.get_muses_2(0, conjunct_reach, muses, num_scalls_sat_correctness, num_scalls_unsat_correctness, &tmpSolver);
		cout << "mus: " << muses.front() << endl;
		assert(0);
	}
	else
	{
		AVR_LOG(8, 0, "reachability-lemmas-check successful!" << endl);
	}
	delete static_cast<SOLVER_AB*>(int_solver);
	/// END

	/// Checking Refinements [SAT is correct]
	if(_numRefinements > 0)
	{
		int_solver = new SOLVER_AB(_abstract_mapper, AVR_EXTRA_IDX, false, regular);
		int_solver->assert_all_wire_constraints();
		conjunct_reach.clear();
		for (InstL::iterator it3 = _negated_refs.begin(); it3 != _negated_refs.end(); ++it3)
			conjunct_reach.push_back(*it3);

		ve_reach = OpInst::create(OpInst::LogAnd, conjunct_reach);
		AVR_LOG(8, 6, "Checking Q:" << conjunct_reach);
		bool res = int_solver->check_sat(ve_reach, 0, false);

		if(res == false)
		{
			AVR_LOG(8, 0, "There is a wrong (UNSAT) datapath lemma!!!" << endl);
			AVR_LOG(8, 0, "Possible errors include: incorrect assumptions" << endl);
			int_solver->print_query(0, ERROR, "error");
			assert(0);
		}
		else
		{
			AVR_LOG(8, 0, "DP-lemmas-check successful!" << endl);
		}
		delete static_cast<SOLVER_AB*>(int_solver);
	}
	/// END

  /// (I & Refinements -> F[converged])
  int_solver = new SOLVER_AB(_abstract_mapper, AVR_EXTRA_IDX, false, regular);
  int_solver->assert_all_wire_constraints();
  conjunct_reach.clear();
	negated_cubes(0, conjunct_reach);
  for (InstL::iterator it3 = _negated_refs.begin(); it3 != _negated_refs.end(); ++it3)
    conjunct_reach.push_back(*it3);
  conjunct_reach.push_back(_ve_model);

  if (!conjunct_fConv.empty())
  {
  	Inst* fConv = OpInst::create(OpInst::LogAnd, conjunct_fConv);
    conjunct_reach.push_back(OpInst::create(OpInst::LogNot, fConv));
  }
  else {
    conjunct_reach.push_back(_ve_prop_eq_0);
  }

  ve_reach = OpInst::create(OpInst::LogAnd, conjunct_reach);
  AVR_LOG(8, 6, "Checking Q:" << conjunct_reach);
  res = int_solver->check_sat(ve_reach, 0, false);

  if(res == false)
  {
    AVR_LOG(8, 0, "initial-state-check successful!" << endl);
  }
  else
  {
    cout << "initial-state-check FAIL!" << endl;
    cout << "Frame converged: " << converged_frame << endl;
//    cout << "Query: " << conjunct_reach << endl;
    assert(0);
  }
  delete static_cast<SOLVER_AB*>(int_solver);
  /// END

	/// F[converged] & P & T & !P+ & Refinements [UNSAT is correct]
	int_solver = new SOLVER_AB(_abstract_mapper, AVR_EXTRA_IDX, false, regular);
	int_solver->assert_all_wire_constraints();
	conjunct_reach.clear();
	conjunct_reach = conjunct_fConv;
	conjunct_reach.push_back(_ve_model);
	conjunct_reach.push_back(_ve_prop_eq_1);
	conjunct_reach.push_back(_ve_model_nsf);
	conjunct_reach.push_back(_ve_model_next);
	conjunct_reach.push_back(_ve_prop_next_eq_0);
	for (InstL::iterator it3 = _negated_refs.begin(); it3 != _negated_refs.end(); ++it3)
		conjunct_reach.push_back(*it3);

	ve_reach = OpInst::create(OpInst::LogAnd, conjunct_reach);
	AVR_LOG(8, 6, "Checking Q:" << conjunct_reach);
	res = int_solver->check_sat(ve_reach, 0, false);

	if(res == false)
	{
		AVR_LOG(8, 0, "property-check successful!" << endl);

//		{
//			delete static_cast<SOLVER_AB*>(int_solver);
//			int_solver = new SOLVER_BV(_abstract_mapper, AVR_EXTRA_IDX, true, regular);
//			int_solver->assert_all_wire_constraints();
//
//			int_solver->s_assert(_ve_model);
//			res = int_solver->s_check(0, false);
//			cout << "P is: " << res << endl;
//
//			int_solver->s_assert(_ve_prop_eq_1);
//			res = int_solver->s_check(0, false);
//			cout << "P is: " << res << endl;
//
//			int_solver->s_assert(_ve_model_nsf);
//			res = int_solver->s_check(0, false);
//			cout << "P & T is: " << res << endl;
//
//			int_solver->s_assert(_ve_model_next);
//			res = int_solver->s_check(0, false);
//			cout << "P & T & !P+ is: " << res << endl;
//
//			int_solver->s_assert(_ve_prop_next_eq_0);
//			res = int_solver->s_check(0, false);
//			cout << "P & T & !P+ is: " << res << endl;
//
//			int_solver->s_assert(_negated_refs);
////			int_solver->s_assert(conjunct_fConv);
//			res = int_solver->s_check(0, false);
//			cout << "P & T & !P+ & Refs is: " << res << endl;
//
//			InstLL muses;
//			res = int_solver->get_muses_2(0, conjunct_fConv, muses, num_scalls_sat_correctness, num_scalls_unsat_correctness, int_solver);
////			res = int_solver->get_muses_2(0, _negated_refs, muses, num_scalls_sat_correctness, num_scalls_unsat_correctness, int_solver);
//			cout << "P & T & !P+ & Refs & Fconv is: " << res << endl;
//
//			if (!muses.empty())
//				cout << "Mus: " << muses.front() << endl;
//
//			assert(0);
//		}
	}
	else
	{
		cout << "property-check FAIL!" << endl;
		cout << "Frame converged: " << converged_frame << endl;
//		cout << "Query: " << conjunct_reach << endl;
		assert(0);
	}
	delete static_cast<SOLVER_AB*>(int_solver);
	/// END

	InstLL allInvariants;
	InstLL allImplications;
	InstLL allWeakInvariants;
	bool invariantHasP = false;

	if (Config::g_correctness_check > 1) {
		/// Checking F[converged] & T & !P+ & Refinements to find weakly inductive invariants
		/// Weak invariants are inductive w.r.t P (i.e. WInv & T & !P+ is UNSAT)
		int_solver = new SOLVER_AB(_abstract_mapper, AVR_EXTRA_IDX, false, regular);
		int_solver->assert_all_wire_constraints();
		int_solver->disable_fallback();
		conjunct_reach.clear();
		conjunct_reach.push_back(_ve_model);
		conjunct_reach.push_back(_ve_model_nsf);
		conjunct_reach.push_back(_ve_model_next);
		conjunct_reach.push_back(_ve_prop_next_eq_0);
		for (InstL::iterator it3 = _negated_refs.begin(); it3 != _negated_refs.end(); ++it3)
			conjunct_reach.push_back(*it3);

		AVR_LOG(8, 6, "Checking Q:" << conjunct_reach);
		ve_reach = OpInst::create(OpInst::LogAnd, conjunct_reach);
		int_solver->s_assert(ve_reach);
		res = (int_solver->s_check(0, false) == AVR_QSAT) ? true : false;

		if (!res)
		{
			/// T & !P+ & Refinements is UNSAT
			InstL conjunct_invariant;
			conjunct_invariant.push_back(_ve_prop_eq_1);
			allWeakInvariants.push_back(conjunct_invariant);
			invariantHasP = true;
			AVR_LOG(8, 0, "T & !P+ & Refinements is UNSAT!" << endl);
		}
		else
		{
	//    AVR_LOG(8, 0, "F[conv].size = " << _negated_cubes[converged_frame].size() << endl);

			int result = AVR_QSAT;
			if (!conjunct_fConv.empty())
			{
				int_solver->s_assert_retractable(conjunct_fConv);
				result = int_solver->s_check_assume(0, false);
			}
			res = (result == AVR_QSAT) ? true : false;
	//    AVR_LOG(8, 0, "F[conv] !P & Refinements is " << (res?"SAT":"UNSAT") << ", " << result << endl);

			if(!res)
			{
				assert (!conjunct_fConv.empty());
				Solver* mus_solver = new SOLVER_MUS(_abstract_mapper, AVR_EXTRA_IDX, true, regular);
				mus_solver->disable_fallback();
				mus_solver->assert_all_wire_constraints();
				int tmpRes = mus_solver->get_muses(0, conjunct_reach, conjunct_fConv, allImplications, num_scalls_sat_correctness, num_scalls_unsat_correctness, mus_solver);
				delete static_cast<SOLVER_MUS*>(mus_solver);

	//			cout << _negated_cubes[converged_frame].size() << endl;
	//			cout << tmpRes << endl;
				assert(tmpRes == 1);
				assert(!allImplications.empty());

				/// Finding all implications that are weakly inductive as well
				for (InstLL::iterator iit = allImplications.begin(); iit != allImplications.end();)
				{
					InstL conjunct_invariant = *iit;
					Inst* invariant = OpInst::create(OpInst::LogAnd, conjunct_invariant);

					/// Checking Invariant & T & !P+ & Refinements [UNSAT is correct]
					SOLVER_AB* tmp_solver = new SOLVER_AB(_abstract_mapper, AVR_EXTRA_IDX, false, regular);
					tmp_solver->assert_all_wire_constraints();
					conjunct_reach.clear();
					conjunct_reach.push_back(invariant);
	//        conjunct_reach.push_back(_ve_model_nsf);
					conjunct_reach.push_back(_ve_model_next);
					conjunct_reach.push_back(_ve_prop_eq_0);
					for (InstL::iterator it3 = _negated_refs.begin(); it3 != _negated_refs.end(); ++it3)
						conjunct_reach.push_back(*it3);

					ve_reach = OpInst::create(OpInst::LogAnd, conjunct_reach);
					AVR_LOG(8, 6, "Checking Q:" << conjunct_reach);
					res = tmp_solver->check_sat(ve_reach, 0, false);

					if(res == false)
					{
						allWeakInvariants.push_back(conjunct_invariant);
	//						iit = allImplications.erase(iit);
						iit++;
					}
					else
					{
						iit++;
					}
					delete static_cast<SOLVER_AB*>(tmp_solver);
					/// END
				}
				if (allWeakInvariants.empty())
				{
					InstL conjunct_invariant;
					conjunct_invariant = conjunct_fConv;
					allWeakInvariants.push_back(conjunct_invariant);
				}
			}
			if (allWeakInvariants.empty())
			{
				assert(allImplications.empty());
				InstL conjunct_invariant;
				conjunct_invariant = conjunct_fConv;
				conjunct_invariant.push_back(_ve_prop_eq_1);
				allWeakInvariants.push_back(conjunct_invariant);
				invariantHasP = true;

				if (false && !conjunct_fConv.empty())
				{
					/// Expand F[converged] using F[converged] & T & !P+ & Refinements [UNSAT is correct]
					Solver* mus_solver = new SOLVER_MUS(_abstract_mapper, AVR_EXTRA_IDX, false, regular);
					mus_solver->assert_all_wire_constraints();
					conjunct_reach.clear();
					conjunct_reach.push_back(_ve_model);
					conjunct_reach.push_back(_ve_prop_eq_1);
					conjunct_reach.push_back(_ve_model_nsf);
					conjunct_reach.push_back(_ve_model_next);
					conjunct_reach.push_back(_ve_prop_next_eq_0);
					for (InstL::iterator it3 = _negated_refs.begin(); it3 != _negated_refs.end(); ++it3)
						conjunct_reach.push_back(*it3);

					ve_reach = OpInst::create(OpInst::LogAnd, conjunct_reach);
					mus_solver->s_assert(ve_reach);

					InstL mus;
					int numSat = 0;
					int numUnsat = 0;
					mus_solver->s_assert(conjunct_reach);
					InstL dummy;
					mus_solver->find_unsat_core(0, dummy, conjunct_fConv, mus, numSat, numUnsat);
					assert(!mus.empty());

					InstLL muses;
					mus_solver->minimize_core(0, mus, muses, numSat, numUnsat);
					mus = muses.front();
					assert(!mus.empty());

					mus.push_back(_ve_prop_eq_1);
					invariantHasP = true;

					AVR_LOG(8, 0, "\t(expanded inductive invariant: " << conjunct_fConv.size() << " -> " << mus.size() << ")" << endl);
					allWeakInvariants.push_front(mus);

					delete static_cast<SOLVER_MUS*>(mus_solver);
				}
			}
		}
		assert(!allWeakInvariants.empty());
		delete static_cast<SOLVER_AB*>(int_solver);

		/// END

		/// Checking inductivity of weak invariants
		for (InstLL::iterator iit = allWeakInvariants.begin(); iit != allWeakInvariants.end(); iit++)
		{
			InstL& conjunct_invariant = *iit;
			Inst* invariant = OpInst::create(OpInst::LogAnd, conjunct_invariant);

			/// Checking Weak_Invariant & T & !P+ [UNSAT is correct]
			int_solver = new SOLVER_AB(_abstract_mapper, AVR_EXTRA_IDX, false, regular);
			int_solver->assert_all_wire_constraints();
			conjunct_reach.clear();
			conjunct_reach.push_back(invariant);
			if (invariantHasP)
			{
				conjunct_reach.push_back(_ve_model);
			}
			conjunct_reach.push_back(_ve_model_nsf);
			conjunct_reach.push_back(_ve_model_next);
			conjunct_reach.push_back(_ve_prop_next_eq_0);
			for (InstL::iterator it3 = _negated_refs.begin(); it3 != _negated_refs.end(); ++it3)
				conjunct_reach.push_back(*it3);

			ve_reach = OpInst::create(OpInst::LogAnd, conjunct_reach);
			AVR_LOG(8, 6, "Checking Q:" << conjunct_reach);
			res = int_solver->check_sat(ve_reach, 0, false);

			if(res == false)
			{
				AVR_LOG(8, 0, "invariant-check successful!" << endl);
			}
			else
			{
				cout << "invariant-check FAIL!" << endl;
				cout << "Query: " << conjunct_reach << endl;
				cout << "Invariant: " << conjunct_invariant << endl;
				cout << invariantHasP << endl;
				assert(res == 0);
			}
			delete static_cast<SOLVER_AB*>(int_solver);
		}
		/// END

		/// Separating invariants (w.r.t P, i.e. Inv & T & !Inv+ is UNSAT) from weak invariants
		for (InstLL::iterator iit = allWeakInvariants.begin(); iit != allWeakInvariants.end();)
		{
			InstL& conjunct_invariant = *iit;
			Inst* invariant = OpInst::create(OpInst::LogAnd, conjunct_invariant);

			/// Checking if Inv & T & !Inv+ is UNSAT
			int_solver = new SOLVER_AB(_abstract_mapper, AVR_EXTRA_IDX, false, regular);
			int_solver->assert_all_wire_constraints();
			conjunct_reach.clear();
			conjunct_reach.push_back(invariant);
			if (invariantHasP)
				conjunct_reach.push_back(_ve_model);
			conjunct_reach.push_back(_ve_model_nsf);
			if (invariantHasP)
				conjunct_reach.push_back(_ve_model_next);
			Inst* cube_dest = OpInst::create(OpInst::LogNot, Inst::all_pre2next(invariant));
			conjunct_reach.push_back(cube_dest);
			for (InstL::iterator it3 = _negated_refs.begin(); it3 != _negated_refs.end(); ++it3)
				conjunct_reach.push_back(*it3);

			ve_reach = OpInst::create(OpInst::LogAnd, conjunct_reach);
			AVR_LOG(8, 6, "Checking Q:" << conjunct_reach);
			res = int_solver->check_sat(ve_reach, 0, false);

			if(res == false)
			{
				allInvariants.push_back(conjunct_invariant);
				iit = allWeakInvariants.erase(iit);
			}
			else
			{
				AVR_LOG(8, 6, "invariant not inductive" << endl);

	//		  AVR_LOG(8, 7, "invariant: " << conjunct_invariant << endl);
	//		  retrieve_cex_val(conjunct_reach, int_solver, true, true);
	//		  collect_values(conjunct_reach, int_solver, true, true);
	//		  print_abstract_min_term();


				iit++;
			}
			delete static_cast<SOLVER_AB*>(int_solver);
			/// END
		}
		AVR_LOG(8, 0, "invariant-extraction successful!" << endl);
	}

	InstL invariant;
	if (!allInvariants.empty())
	  invariant = allInvariants.front();
	else {
//	  AVR_LOG(8, 0, "\t(warning: unable to extract inductive invariant)" << endl);
	  invariant = conjunct_fConv;
	  invariant.push_back(_ve_prop_eq_1);
	  allInvariants.push_back(invariant);
	}

	/// Expanding inductive invariants
	if (false) {
		for (InstLL::iterator iit = allInvariants.begin(); iit != allInvariants.end(); iit++)
		{
			InstL& conjunct_invariant = *iit;
			InstL conjunct_invariant2 = conjunct_invariant;
			InstL required;
			required.push_back(_ve_prop_eq_1);
			while (!conjunct_invariant2.empty()) {
				Inst* curr = conjunct_invariant2.front();
				conjunct_invariant2.pop_front();
				InstL conjunct_inv = required;
				for (auto& v: conjunct_invariant2)
					conjunct_inv.push_back(v);

				Inst* invariant = OpInst::create(OpInst::LogAnd, conjunct_inv);

				/// Checking Inv & T & Ref & !Inv+ [UNSAT is correct]
				int_solver = new SOLVER_AB(_abstract_mapper, AVR_EXTRA_IDX, false, regular);
				int_solver->assert_all_wire_constraints();
				conjunct_reach.clear();
				conjunct_reach.push_back(invariant);
				conjunct_reach.push_back(_ve_model);
				conjunct_reach.push_back(_ve_model_nsf);
				conjunct_reach.push_back(_ve_model_next);
				Inst* cube_dest = OpInst::create(OpInst::LogNot, Inst::all_pre2next(invariant));
				conjunct_reach.push_back(cube_dest);
				for (InstL::iterator it3 = _negated_refs.begin(); it3 != _negated_refs.end(); ++it3)
					conjunct_reach.push_back(*it3);

				ve_reach = OpInst::create(OpInst::LogAnd, conjunct_reach);
				AVR_LOG(8, 6, "Checking Q:" << conjunct_reach);
				res = int_solver->check_sat(ve_reach, 0, false);

				if(res == false)
				{
					AVR_LOG(8, 0, "inductive-invariant expansion successful!" << endl);
				}
				else
				{
					required.push_back(curr);
				}
				delete static_cast<SOLVER_AB*>(int_solver);
			}
			conjunct_invariant = required;
		}
	}
	/// END

	if (Config::g_correctness_check > 0) {
		/// Checking inductivity of strong invariants
		for (InstLL::iterator iit = allInvariants.begin(); iit != allInvariants.end(); iit++)
		{
			InstL& conjunct_invariant = *iit;
			Inst* invariant = OpInst::create(OpInst::LogAnd, conjunct_invariant);

			/// Checking Inv & T & Ref & !Inv+ [UNSAT is correct]
			int_solver = new SOLVER_AB(_abstract_mapper, AVR_EXTRA_IDX, false, regular);
			int_solver->assert_all_wire_constraints();
			conjunct_reach.clear();
			conjunct_reach.push_back(invariant);
			conjunct_reach.push_back(_ve_model);
			conjunct_reach.push_back(_ve_model_nsf);
			conjunct_reach.push_back(_ve_model_next);
			Inst* cube_dest = OpInst::create(OpInst::LogNot, Inst::all_pre2next(invariant));
			conjunct_reach.push_back(cube_dest);
			for (InstL::iterator it3 = _negated_refs.begin(); it3 != _negated_refs.end(); ++it3)
				conjunct_reach.push_back(*it3);

			ve_reach = OpInst::create(OpInst::LogAnd, conjunct_reach);
			AVR_LOG(8, 6, "Checking Q:" << conjunct_reach);
			res = int_solver->check_sat(ve_reach, 0, false);

			if(res == false)
			{
				AVR_LOG(8, 0, "inductive-invariant-check successful!" << endl);
			}
			else
			{
				cout << "inductive-invariant-check FAIL!" << endl;
				cout << "Query: " << conjunct_reach << endl;
				cout << "Invariant: " << conjunct_invariant << endl;
				cout << invariantHasP << endl;
				assert(res == 0);
			}
			delete static_cast<SOLVER_AB*>(int_solver);
		}
	}
	/// END


  InstLL reducedRefinements;
	if (!_negated_refs.empty()) {
// #define FIND_REFS
#ifndef FIND_REFS
		if (Config::g_correctness_check > 2)
#else
		if (true)
#endif
		{
			/// Reducing Refinements using Inv & T & !Inv+ & (assuming Refinements) [UNSAT is correct]
			int_solver = new SOLVER_MUS(_abstract_mapper, AVR_EXTRA_IDX, true, regular);
			int_solver->assert_all_wire_constraints();
			conjunct_reach.clear();
			conjunct_reach = invariant;
			conjunct_reach.push_back(_ve_model);
			conjunct_reach.push_back(_ve_model_nsf);
			conjunct_reach.push_back(_ve_model_next);

			Inst* inv = OpInst::create(OpInst::LogAnd, invariant);
			Inst* invNext = Inst::all_pre2next(inv);
			conjunct_reach.push_back(OpInst::create(OpInst::LogNot, invNext));
	//    conjunct_reach.push_back(_ve_prop_next_eq_0);

			AVR_LOG(8, 6, "Checking Q:" << conjunct_reach);
			int_solver->s_assert_retractable(conjunct_reach);
			int res = int_solver->s_check_assume(0, false);
			int_solver->s_retract_assertions();

			if (res == AVR_QSAT) {
				int_solver->s_assert(conjunct_reach);
				AVR_LOG(8, 6, "Assuming:" << _negated_refs);
				InstL core;
#ifndef FIND_REFS
				int tmpRes = int_solver->get_unsat_core(0, _negated_refs, core, num_scalls_sat_correctness, num_scalls_unsat_correctness);
#else
				_collected_cubes.clear();
				for (auto& v: _negated_refs)
					collect_cubes(v, false);
				int tmpRes = int_solver->get_unsat_core(0, _collected_cubes, core, num_scalls_sat_correctness, num_scalls_unsat_correctness);
#endif
				reducedRefinements.push_back(core);
				assert(tmpRes == AVR_QUSAT);
				assert(!reducedRefinements.empty());
			}
			delete static_cast<SOLVER_MUS*>(int_solver);
			AVR_LOG(8, 0, "axioms-extraction successful!" << endl);
		}
		else {
			reducedRefinements.push_back(_negated_refs);
		}
	}
  /// END

  bool print_wit = Config::g_print_witness;
	ofstream out;
	ofstream out_smt2;
  if (print_wit) {
		string fname = _config->get_working_dir() + "/inv.txt";
		out.open(fname.c_str());

#ifdef PRINT_INV_SMT2
		string fname_smt2 = _config->get_working_dir() + "/inv.smt2";
		out_smt2.open(fname_smt2.c_str());
#endif

		InstL propList;
		OpInst* op = OpInst::as(_ve_model);
		if (op && op->get_op() == OpInst::Eq) {
			Inst* rhs = op->get_children()->back();
			collect_all_cubes(rhs, true);
			propList.swap(_collected_cubes);
		}
		else
			propList.push_back(_ve_model);

		out << "Property (P): ";
		print_sorted_list(out, propList, true);

		out << "\nInductive Invariants (i.e. (Inv -> P) and (Inv ^ T ^ !Inv+) is UNSAT): #" << allInvariants.size() << endl;
  }
	int count = 0;
	int minSzInv = -1;
	int maxWordSz = -1;
	for (InstLL::iterator iit = allInvariants.begin(); iit != allInvariants.end(); iit++)
	{
		count++;
		int wordSz = print_sorted_list(out, *iit, true);
		maxWordSz = max(maxWordSz, wordSz);
		if ((minSzInv == -1) || (minSzInv > (*iit).size()))
			minSzInv = (*iit).size();

		if (print_wit) {
			out << "\t[" << count << "]: ";
#ifdef PRINT_INV_SMT2
			if (count == 1) {
				out_smt2 << "; inductive invariant\n";
				m5_API print_solver(_concrete_mapper, AVR_BV_IDX, false, prt);
				out_smt2 << "(define-fun .induct_inv () Bool (! \n";
				print_solver.print_expression((*iit), out_smt2);
				out_smt2 << " :invar-property 1))\n";

				InstL conjunct_tmp;
				for (auto& v: (*iit))
					conjunct_tmp.push_back(Inst::all_pre2next(v));
				out_smt2 << "\n; inductive invariant next\n";
				out_smt2 << "(define-fun .induct_inv_next () Bool \n";
				print_solver.print_expression(conjunct_tmp, out_smt2);
				out_smt2 << ")\n";

				{
					const char *text_query =
						"\n"
						"(echo \"asserting design: transition relation and global constraints\")\n"
					  "(assert .trans)\n"
					  "\n"
					  "(push 1)\n"
						"(echo \"checking (initial -> proof)\")\n"
						"(assert (and .init (not .induct_inv)))\n"
						"(check-sat)\n"
						"(pop 1)\n"
						"\n"
						"(push 1)\n"
						"(echo \"checking (proof -> property)\")\n"
						"(assert (and .induct_inv (not property)))\n"
						"(check-sat)\n"
						"(pop 1)\n"
						"\n"
						"(push 1)\n"
						"(echo \"checking (proof is inductive)\")\n"
						"(assert (and .induct_inv (not .induct_inv_next)))\n"
						"(check-sat)\n"
						"(pop 1)\n"
					  "\n";
					out_smt2 << text_query << endl;
				}
			}
#endif
		}
	}
	_resFile << "inv-max-word-sz:\t" << maxWordSz << endl;

	if (print_wit) {
		if (!allWeakInvariants.empty())
		{
			out << "\nInvariants (i.e. Inv -> P) and (Inv ^ T ^ !P+) is UNSAT): #" << allWeakInvariants.size() << endl;
			count = 0;
			for (InstLL::iterator iit = allWeakInvariants.begin(); iit != allWeakInvariants.end(); iit++)
			{
				count++;
				out << "\t[" << count << "]: ";
				print_sorted_list(out, *iit, true);
	//			if ((minSzInv == -1) || (minSzInv > (*iit).size()))
	//				minSzInv = (*iit).size();
			}
		}

		if (!allImplications.empty())
		{
			out << "\nImplications (i.e. (Inv -> P)): #" << allImplications.size() << endl;
			count = 0;
			for (InstLL::iterator iit = allImplications.begin(); iit != allImplications.end(); iit++)
			{
				count++;
				out << "\t[" << count << "]: ";
				print_sorted_list(out, *iit, true);
			}
		}

		if (_ve_assume != NumInst::create(1, 1, SORT())) {
			collect_cubes(_ve_assume, true);
			out << "\nAssumptions:" << endl;
			assert (!_collected_cubes.empty());
			{
				out << "\t[" << 1 << "]: ";
				print_sorted_list(out, _collected_cubes, true);
			}
		}

		out << "\nAxioms (refinements): #" << reducedRefinements.size() << endl;
		if (!reducedRefinements.empty())
		{
			count = 0;
			for (InstLL::iterator iit = reducedRefinements.begin(); iit != reducedRefinements.end(); iit++)
			{
				count++;
				out << "\t[" << count << "]: ";
				print_sorted_list(out, *iit, true);

	//      int count2 = 0;
	//      for (auto& v: *iit) {
	//      	if (v->get_type() == Wire)
	//      		draw_graph(0, v, WireInst::as(v)->get_name(), 0);
	//      	else
	//      		draw_graph(0, v, "assume$" + to_string(count2), 0);
	//      	count2++;
	//      }
			}
		}
		out << "\n(max frame explored)    F[" << _frame_idx << "]" << endl;
		out << "(frame converged)       F[" << converged_frame << "]" << endl;
  }

	_numStrongInvariant = allInvariants.size();
	_numWeakInvariant = allWeakInvariants.size();
	_numImplications = allImplications.size();
	_szInvariant = minSzInv;

  Inst* inv = OpInst::create(OpInst::LogAnd, invariant);

//  print_states_transitions("fsm_cc_final.txt", inv, true, true);
//  print_states_transitions("fsm_ab_final.txt", inv);

  int invsz_orig = invariant.size();
  int invsz_new = invariant.size();
//  if (!Config::g_ab_interpret && Config::g_minimize_inv_effort >= MININV_AB_FAST && invsz_new > 1)
//  {
//		minimize_inductive_invariant(invariant, false, true);
//		if (invsz_new != invariant.size()) {
//			check_correct_invariant(invariant, false);
//			if (print_wit)
//				out << "(minimizing invariant (using ab fast): " << invsz_new << " -> " << invariant.size() << ")" << endl;
//			invsz_new = invariant.size();
//		}
//  }
  if (!Config::g_ab_interpret && Config::g_minimize_inv_effort >= MININV_AB_SLOW && invsz_new > 1)
  {
		minimize_inductive_invariant(invariant, false, false);
		if (invsz_new != invariant.size()) {
			check_correct_invariant(invariant, false);
			if (print_wit)
				out << "(minimizing invariant (using ab slow): " << invsz_new << " -> " << invariant.size() << ")" << endl;
			invsz_new = invariant.size();
		}
  }
//  if (Config::g_minimize_inv_effort >= MININV_BV_FAST && invsz_new > 1)
//  {
//		minimize_inductive_invariant(invariant, true, true);
//		if (invsz_new != invariant.size()) {
//			check_correct_invariant(invariant, true);
//			if (print_wit)
//				out << "(minimizing invariant (using bv fast): " << invsz_new << " -> " << invariant.size() << ")" << endl;
//			invsz_new = invariant.size();
//		}
//  }
  if (Config::g_minimize_inv_effort >= MININV_BV_SLOW && invsz_new > 1)
  {
		minimize_inductive_invariant(invariant, true, false);
		if (invsz_new != invariant.size()) {
			check_correct_invariant(invariant, true);
			if (print_wit)
				out << "(minimizing invariant (using bv slow): " << invsz_new << " -> " << invariant.size() << ")" << endl;
			invsz_new = invariant.size();
		}
  }

	if (invsz_new != invsz_orig) {
		if (invsz_new < minSzInv)
			minSzInv = invsz_new;

		if (print_wit) {
			out << "\nMinimized Inductive Invariant (i.e. (Inv ^ T ^ !Inv+) is UNSAT):" << endl;
			print_sorted_list(out, invariant);
#ifdef PRINT_INV_SMT2
			out_smt2 << "\n; minimized inductive invariant\n";
			{
				m5_API print_solver(_concrete_mapper, AVR_BV_IDX, false, prt);
				print_solver.print_expression(invariant, out_smt2);
			}
#endif
		}
//		assert(invsz_new < invsz_orig);
	}
	if (print_wit) {
		out.close();
#ifdef PRINT_INV_SMT2
		out_smt2.close();
#endif
	}
	_szInvariant = minSzInv;

  TIME_E(start_time, end_time, _cc_time);
}
#else
void Reach::check_correctness() {
	struct rusage usage;
	struct timeval start_time, end_time;
	long long time_diff;
	TIME_S(start_time);
	int converged_frame = 1;
	for (; converged_frame <= (int)_cubes.size(); converged_frame++) {
		if (_cubes[converged_frame].empty()) {
			break;
		}
	}
	AVR_LOG(8, 0, "frame_converged: " << converged_frame << endl);
	InstL conjunct_reach;
	conjunct_reach = _negated_cubes[converged_frame];
	conjunct_reach.push_back(_ve_model);
	Inst *cube_invariant = OpInst::create(OpInst::LogAnd, conjunct_reach);

	conjunct_reach.clear();
	conjunct_reach.push_back(cube_invariant);
	conjunct_reach.push_back(_ve_model_nsf);
	Inst *cube_invariant_next = all_pre2next(cube_invariant, true);
	conjunct_reach.push_back(OpInst::create(OpInst::LogNot, cube_invariant_next));
	for (InstL::iterator it3 = _negated_refs.begin(); it3 != _negated_refs.end(); ++it3)
		conjunct_reach.push_back(*it3);
	conjunct_reach.push_back(_ve_prop_eq_1);
	conjunct_reach.push_back(_ve_prop_next_eq_1);


	Inst* ve_reach = OpInst::create(OpInst::LogAnd, conjunct_reach);
	z3_API int_solver(&_abstract_mapper, 1);
	//cout << "conjunct_reach: " << conjunct_reach << endl;
	bool res = int_solver.check_sat(ve_reach);

	if(res == false){
		AVR_LOG(8, 0, "invariant-check successful!" << endl);
	}else{
		AVR_LOG(8, 0, "invariant-check FAIL!" << endl);
	}

	TIME_E(start_time, end_time, _cc_time);
	//dump_entire_cex(ve_reach, &int_solver, true, true);
	assert(res == 0);
}
#endif

void Reach::print_frames(string comment) {
#ifdef AVOID_LARGE_PRINTING
	for (int i = 1; i < _cubes.size(); i++) {
		if ((i <= _frame_idx) && (_cubes[i].size() < 3)) {
			AVR_LOG(15, 0, "\t(F" << i << " about to converge: #" << _cubes[i].size() << ")\n");
			for (auto& cube: _cubes[i]) {
				AVR_LOG(15, 0, "\t\t" << *cube.cube << endl);
			}
		}
	}
	return;
#endif

	AVR_LOG(13, 0, "(frame restrictions: " << comment << ")\n");
  AVR_LOG(13, 0, "\t(cubes:" << ((_cubes.size() == 0) ? " Empty":"") << ")\n");
  for (int i = 0; i < _cubes.size(); i++) {
    AVR_LOG(13, 0, "\n[" << i << "]" << endl);
    for (auto& cube: _cubes[i]) {
      AVR_LOG(13, 0, "\t" << *cube.cube << endl);
    }
  }
}

void Reach::print_config() {
  _resFile << "timeout:\t" << _global_timeout << endl;
  _resFile << "memout:\t" << _global_memory_limit << endl;

  _resFile << "bmc-enabled:\t" << Config::g_bmc_en << endl;
  _resFile << "bmc-kind-enabled:\t" << Config::g_kind_en << endl;
  _resFile << "bmc-max-bound:\t" << Config::g_bmc_max_bound << endl;

  AVR_LOG(15, 0, endl);
  AVR_LOG(15, 0, "Config:" << endl);

  _resFile << "random:\t" << (Config::g_random?"true":"false") << endl;

#ifdef RANDOM_SHUFFLE_CORE
  _resFile << "random-core:\ttrue" << endl;
#else
  _resFile << "random-core:\tfalse" << endl;
#endif

#ifdef PERFORMANCE
  _resFile << "performance:\ttrue" << endl;
#else
  _resFile << "performance:\tfalse" << endl;
#endif

  _resFile << "ufbv-width-limit:\t" << Config::g_ab_interpret_limit << endl;
  cout << "\t(concrete bit-width limit: " << Config::g_ab_interpret_limit << ")" << endl;

  _resFile << "fineness:\t" << Config::g_fineness << endl;
  cout << "\t(fineness: " << Config::g_fineness << ")" << endl;

#ifdef INTERPRET_EX_CC
  _resFile << "interpret-ex-cc:\tpartial" << endl;
  cout << "\t(interpret-ex-cc-level: ";
  #ifdef EX_CC_LEVEL2
    cout << 2;
  #else
    #ifdef EX_CC_LEVEL1
      cout << 1;
    #else
      cout << 0;
    #endif
  #endif
  cout << ")"  << endl;
#else
  #ifdef TEST_ABSTRACT_BV
    _resFile << "interpret-ex-cc:\tfull" << endl;
  #else
    _resFile << "interpret-ex-cc:\tnone" << endl;
  #endif
#endif

  _resFile << "forward-check:\t" << Config::g_forward_check << endl;
  cout << "\t(forward-check:\t" << Config::g_forward_check << ")" << endl;

#ifdef SUBSTITUTION
  _resFile << "subs:\ttrue" << endl;
  cout << "\t(substitution)" << endl;
  #ifdef SEQUENTIAL_SUBSTITUTION
    cout << "\t\t(projection substitution)" << endl;
  #endif
  #ifdef SEQUENTIAL_SUBSTITUTION
    cout << "\t\t(sequential substitution, level: ";
    #ifdef SEQUENTIAL_SUBSTITUTION_LEVEL1
      cout << 1;
    #else
      cout << "?";
    #endif
    cout << ")"  << endl;
  #endif
#else
  _resFile << "subs:\tfalse" << endl;
#endif

#ifdef ASSERT_DISTINCT_NUMBERS
  _resFile << "distinct-const:\ttrue" << endl;
#else
  _resFile << "distinct-const:\tfalse" << endl;
#endif

#ifdef SIMULATION_CHECK_SELF_LOOPS
  _resFile << "sim-sloop:\ttrue" << endl;
#else
  _resFile << "sim-sloop:\tfalse" << endl;
#endif

#ifdef LIMIT_SIMULATION_ITERATIONS
  _resFile << "sloop-limit:\t" << INIT_SELF_LOOP_ALLOWANCE << endl;
#else
  _resFile << "sloop-limit:\t0" << endl;
#endif

#ifdef STRUCTURAL_PROJECTION
  #ifdef FULL_PROJECTION
    _resFile << "projection:\tstruct+full" << endl;
  #else
    _resFile << "projection:\tstruct" << endl;
  #endif
#else
  _resFile << "projection:\tfull" << endl;
#endif

#ifdef STRUCTURAL_PROJECTION
  _resFile << "sa:\ttrue" << endl;

  #ifdef SA_COMMON_NODES
    _resFile << "sa-common-node:\ttrue" << endl;
  #else
    _resFile << "sa-common-node:\tfalse" << endl;
  #endif

  #ifdef SA_COMMON_FAPPS
    _resFile << "sa-common-fapp:\ttrue" << endl;
  #else
    _resFile << "sa-common-fapp:\tfalse" << endl;
  #endif

  #ifdef SA_WAPPS
    _resFile << "sa-wapp:\ttrue" << endl;
  #else
    _resFile << "sa-wapp:\tfalse" << endl;
  #endif

#else
  _resFile << "sa:\tfalse" << endl;
  _resFile << "sa-common-node:\tna" << endl;
  _resFile << "sa-common-fapp:\tna" << endl;
  _resFile << "sa-wapp:\tna" << endl;
  cout << "\t(full projection)" << endl;
#endif

#ifdef SINGLE_TIER
  _resFile << "prioritization:\tsingle" << endl;
  cout << "\t(prioritization:\tsingle)" << endl;
#endif
#ifdef DOUBLE_TIER
  _resFile << "prioritization:\tdouble" << endl;
  cout << "\t(prioritization:\tdouble)" << endl;
#endif
#ifdef MULTI_TIER
  _resFile << "prioritization:\tmulti" << endl;
  cout << "\t(prioritization:\tmulti)" << endl;
#endif

#ifdef FULL_PROJECTION
  cout << "\t(full projection)" << endl;
#endif

#ifdef FP_EXPAND_FRAME
    cout << "\t(forward-propagation-expand-frame)" << endl;
#endif

#ifdef REACH_ADD_PATH_CONSTRAINTS
  cout << "\t(abstraction-allow-wlp)" << endl;
#endif

#ifdef LIMIT_WLP_USING_FCLEVEL
  cout << "\t(abstraction-limit-wlp-using-function-composition)" << endl;
#endif

#ifdef LIMIT_WLP_NO_EXTRA_FC
  cout << "\t(abstraction-limit-wlp-using-no-extra-function-composition)" << endl;
#endif

#ifdef AB_COURSE_AUTO
  cout << "\t(abstraction-course-automatic)" << endl;
#endif

#ifdef AB_COURSE_AS_AVR1
  cout << "\t(abstraction-course-expand-cube-as-avr1)" << endl;
#endif

#ifdef AB_COURSE_REFINE_USING_LEMMAS
  cout << "\t(abstraction-course-refine-using-lemmas)" << endl;
#endif

#ifdef ACEXT_WLP_CHECK_COURSE
  cout << "\t(ab-course-acext-wlp-check)" << endl;
#endif

#ifdef ACEXT_WLP_COURSE_REFINE_USING_LEMMAS
  cout << "\t(ab-course-acext-wlp-check-refine-using-lemmas)" << endl;
#endif

#ifdef ACEXT_WLP_CHECK
  cout << "\t(acext-wlp-check)" << endl;
#endif

#ifdef ACEXT_WLP_REFINE_USING_LEMMAS
  cout << "\t(acext-wlp-check-refine-using-lemmas)" << endl;
#endif
}

bool Reach::sort_present(SORT sort, SortType target) {
  list<SORT> q;
  q.push_back(sort);
  while (!q.empty()) {
  	SORT s = q.front();
  	if (s.type == target)
  		return true;
  	q.pop_front();
  	for (auto& v: s.args)
  		q.push_back(v);
  }
  return false;
}

void Reach::reduce_system() {
	bool complexT = collect_system_orig();
	complexT = true;
	_resFile << "complex-T:\t" << (complexT ? "true" : "false") << endl;

	bool closeAssume = true;

	int numSig[3] = { 0 };
	int numReg[3] = { 0 };
	int numAsm[3] = { 0 };

	{
		InstS sigSet;
		collect_sig(_ve_model, sigSet, true);
		collect_sig(_ve_model_nsf, sigSet);
		collect_sig(_ve_init, sigSet);
		collect_sig(_ve_assume, sigSet);

		numSig[0] = sigSet.size();
		numReg[0] = Inst::_s_reg.size();
		numAsm[0] = _assumptions.size();

		_resFile << "#orig-sigs:\t" << numSig[0] << endl;
		_resFile << "#orig-regs:\t" << numReg[0] << endl;
		_resFile << "#orig-assumes:\t" << numAsm[0] << endl;
	}

	InstS relevantSigs;
	InstS relevantRegs;
	InstS relevantAssume;

	if (!complexT) {

		set< string > simpleClocks;
		simpleClocks.insert(":global_clock");
		simpleClocks.insert("__system_clk_");

		InstL queue;
		queue.push_back(_ve_model);

		InstToSetM depSigsMap;

		while(!queue.empty()) {
			Inst* currE = queue.front();
			queue.pop_front();

			if (depSigsMap.find(currE) == depSigsMap.end()) {
				collect_sig(currE, depSigsMap[currE], true);
			}
			InstS& depSet = depSigsMap[currE];

			InstL newSigs;
			for (auto& s: depSet) {
				Inst* pre = s;
				if (relevantSigs.find(pre) == relevantSigs.end()) {
					Inst* next;
					if (pre->find_next()) {
						next = Inst::all_next2pre(pre);
						Inst* tmp = pre;
						pre = next;
						next = tmp;
					}
					else
						next = Inst::all_pre2next(pre);

					assert(pre);
					assert(next);

					newSigs.push_back(pre);
					newSigs.push_back(next);

					relevantSigs.insert(pre);
					relevantSigs.insert(next);

//					cout << "(relevantSig) " << *pre << endl;

					if (Inst::_s_reg.find(pre) != Inst::_s_reg.end()) {
						relevantRegs.insert(pre);
					}
				}
			}

			while (!newSigs.empty()) {
				Inst* currS = newSigs.front();
				newSigs.pop_front();

				if (currS->find_next()) {
					InstToPairBoolM::iterator mit = Inst::_m_sn.find(currS);
					if (mit != Inst::_m_sn.end())
						queue.push_back((*mit).second.first);
					else {
						InstToSetM::iterator mit2 = Inst::_m_inp_next.find(currS);
						if (mit2 != Inst::_m_inp_next.end()) {
							for (auto& v: (*mit2).second)
								queue.push_back(v);
						}
					}
				}
	//			else {
	//				for (auto& a: _conjunct_init) {
	//					if (relevantInit.find(a) == relevantInit.end())
	//					{
	//						if (depSigsMap.find(a) == depSigsMap.end()) {
	//							collect_sig(a, depSigsMap[a], true);
	//						}
	//						InstS& depSet = depSigsMap[a];
	//						if (depSet.find(currS) != depSet.end()) {
	//							queue.push_back(a);
	//							relevantInit.insert(a);
	//						}
	//					}
	//				}
	//			}

				if (closeAssume) {
					Inst* tve = currS;
					if (tve->find_next())
						tve = Inst::all_next2pre(tve);
					assert(tve->get_type() == Sig);
					if (!simpleClocks.count(SigInst::as(tve)->get_name())) {
						for (auto& a: _assumptions) {
							if (relevantAssume.find(a) == relevantAssume.end())
							{
								if (depSigsMap.find(a) == depSigsMap.end()) {
									collect_sig(a, depSigsMap[a], true);
								}
								InstS& depSet = depSigsMap[a];
								if (depSet.find(currS) != depSet.end()) {
									queue.push_back(a);
									relevantAssume.insert(a);
//									cout << "\t(relevantAssume) " << *currS << "\t" << *a << endl;
								}
							}
						}
					}
				}
			}
		}


		cout << "#total regs: " << Inst::_s_reg.size() << endl;

		cout << "#relevant regs: " << relevantRegs.size() << endl;
	//	cout << relevantRegs << endl;

		cout << "#relevant signals: " << relevantSigs.size() << endl;
	//	cout << relevantSigs << endl;

		cout << "#total assume: " << _assumptions.size() << endl;

		cout << "#relevant assume: " << relevantAssume.size() << endl;
	//		cout << relevantAssume << endl;

		{
			numSig[1] = relevantSigs.size();
			numReg[1] = relevantRegs.size();
			numAsm[1] = relevantAssume.size();

			_resFile << "#relevant-sigs:\t" << numSig[1] << endl;
			_resFile << "#relevant-regs:\t" << numReg[1] << endl;
			_resFile << "#relevant-assumes:\t" << numAsm[1] << endl;
		}

		{
			Inst::init_visit2();
			Inst::init_visit3();

			InstL newI;
			for (InstL::iterator it = _conjunct_init.begin(); it != _conjunct_init.end(); ++it) {
				if (find_has_limited_sigs(*it, relevantSigs)) {
					newI.push_back(*it);
				}
	//			else {
	//				if (find_has_limited_sigs(*it, relevantSigs)) {
	//					cout << "Error: found an exclusion containing relevant signal" << endl;
	//					cout << "I: " << *(*it) << endl;
	//					InstS depSigs;
	//					collect_sig(*it, depSigs, true);
	//					cout << "depSigs: " << depSigs << endl;
	//					cout << "#relevant signals: " << relevantSigs.size() << endl;
	//					cout << relevantSigs << endl;
	//					assert(0);
	//				}
	//			}
			}
			if (newI.empty())
				_ve_init = NumInst::create(1, 1, SORT());
			else
				_ve_init = OpInst::create(OpInst::LogAnd, newI);
			cout << "#final I: " << newI.size() << endl;

			InstL newT;
			for (InstL::iterator it = _conjunct_nsf.begin(); it != _conjunct_nsf.end(); ++it) {
				if (find_limited_sigs(*it, relevantSigs)) {
					newT.push_back(*it);
				}
	//			else {
	//				if (find_has_limited_sigs(*it, relevantSigs)) {
	//					cout << "Error: found an exclusion containing relevant signal" << endl;
	//					cout << "T: " << *(*it) << endl;
	//					InstS depSigs;
	//					collect_sig(*it, depSigs, true);
	//					cout << "depSigs: " << depSigs << endl;
	//					cout << "#relevant signals: " << relevantSigs.size() << endl;
	//					cout << relevantSigs << endl;
	//					assert(0);
	//				}
	//			}
			}
			if (newT.empty())
				_ve_model_nsf = NumInst::create(1, 1, SORT());
			else
				_ve_model_nsf = OpInst::create(OpInst::LogAnd, newT);
			cout << "#final T: " << newT.size() << endl;

			InstL newA;
			collect_cubes(_ve_assume, true);
			for (auto& a: _collected_cubes) {
				if (closeAssume) {
					if (find_limited_sigs(a, relevantSigs)) {
						newA.push_back(a);
					}
					else {
						if (find_has_limited_sigs(a, relevantSigs)) {
							cout << "Error: found an exclusion containing relevant signal" << endl;
							cout << "A: " << *a << endl;
							InstS depSigs;
							collect_sig(a, depSigs, true);
							cout << "depSigs: " << depSigs << endl;
							cout << "#relevant signals: " << relevantSigs.size() << endl;
							cout << relevantSigs << endl;
							assert(0);
						}
					}
				}
				else {
					if (find_has_limited_sigs(a, relevantSigs)) {
						newA.push_back(a);
					}
				}
			}
			if (newA.empty())
				_ve_assume = NumInst::create(1, 1, SORT());
			else
				_ve_assume = OpInst::create(OpInst::LogAnd, newA);
			cout << "#final A: " << newA.size() << endl;
		}
	}

  _conjunct_init.clear();
  _conjunct_nsf.clear();
  Inst::_m_sn.clear();
  Inst::_s_reg.clear();
  Inst::_m_next_to_pre.clear();
  Inst::_m_pre_to_next.clear();
  _assumptions.clear();
  Inst::_m_inp.clear();
  Inst::_m_inp_next.clear();

  collect_system();

	{
		InstS sigSet;
		collect_sig(_ve_model, sigSet, true);
		collect_sig(_ve_model_nsf, sigSet);
		collect_sig(_ve_init, sigSet);
		collect_sig(_ve_assume, sigSet);

		numSig[2] = sigSet.size();
		numReg[2] = Inst::_s_reg.size();
		numAsm[2] = _assumptions.size();

		_resFile << "#final-sigs:\t" << numSig[2] << endl;
		_resFile << "#final-regs:\t" << numReg[2] << endl;
		_resFile << "#final-assumes:\t" << numAsm[2] << endl;
	}

}

bool Reach::collect_system_orig() {
  vector<CLAUSE> tmpL;
	_cubes.push_back(tmpL);

	bool complexT = false;

  set_property();

	collect_nsfs(_ve_init, _conjunct_init, true);

  collect_nsfs(_ve_model_nsf, _conjunct_nsf, true);
  Inst::init_visit();
  for (InstL::iterator it = _conjunct_nsf.begin(); it != _conjunct_nsf.end(); ++it) {
    Inst *tve = *it;
    if (tve == NumInst::create(1, 1, SORT()))
    	continue;

    Inst *lhs;
    Inst *rhs;
    if(tve->get_children()){
      InstL::const_iterator it2 = tve->get_children()->begin();
      lhs = *it2++;
      if((tve->get_type() == Op) && (OpInst::as(tve)->get_op() == OpInst::LogNot)){
        rhs = NumInst::create(0, 1, SORT());
      }else{
        rhs = *it2;
      }
    }else{
      lhs = tve;
      rhs = NumInst::create(1, 1, SORT());
    }

    SigInst* sig = SigInst::as(lhs);
    if(!sig)  cout << *lhs << endl;
    assert(sig);
    if(!lhs->find_next())  cout << *lhs << " equals " << *rhs << endl;
    assert(lhs->find_next());

    string str_lhs = sig->get_name();
    Inst::_m_sn[lhs] = make_pair(rhs, !rhs->find_next());
    if (rhs->find_next())
    	complexT = true;

    string str_lhs_wo_next = str_lhs.substr(0, str_lhs.find_last_of('$'));

    /// Aman
    Inst* sigTmp = SigInst::create(str_lhs_wo_next, sig->get_size(), sig->get_sort());
    SigInst::as(sigTmp)->set_idx();

    Inst::_s_reg.insert(sigTmp);

    Inst::_m_next_to_pre[lhs] = sigTmp;
    Inst::_m_pre_to_next[sigTmp] = lhs;
  }

  if (_ve_assume != NumInst::create(1, 1, SORT())) {
  	collect_cubes(_ve_assume, true);
  	for (auto& v: _collected_cubes) {
  		_assumptions.insert(v->get_port());
  	}
  }

  for (auto& tve: _assumptions) {
  	if (!tve->find_next()) {
			Inst* v = tve->get_port();
			OpInst* op = OpInst::as(v);
			if (op && op->get_op() == OpInst::Eq) {
				Inst* lhs = op->get_children()->front();
				Inst* rhs = op->get_children()->back();
				if (lhs->get_type() != Sig)
					swap(lhs, rhs);
				if (lhs->get_type() == Sig) {
					if (Inst::_s_reg.find(lhs) == Inst::_s_reg.end()) {
//						assert(Inst::_s_inp.find(lhs) != Inst::_s_inp.end());
						Inst* lhsNext = Inst::all_pre2next(lhs);
						Inst* rhsNext = Inst::all_pre2next(rhs);

						Inst::_m_inp[lhs].insert(OpInst::create(OpInst::Eq, lhs, rhs));
						Inst::_m_inp_next[lhsNext].insert(OpInst::create(OpInst::Eq, lhsNext, rhsNext));
					}
				}
			}
  	}
  }

  return complexT;
}


void Reach::preprocess_system() {
//  if (_ve_assume != NumInst::create(1, 1, SORT())) {
//  	InstS initSet;
//  	collect_cubes(_ve_init, true);
//  	for (auto& v: _collected_cubes)
//  		initSet.insert(v);
//
//  	collect_cubes(_ve_assume, true);
//  	bool modified = false;
//  	for (auto& v: _collected_cubes) {
//  		v = v->get_port();
//  		Inst* vNeg = OpInst::create(OpInst::LogNot, v);
//  		if (initSet.find(vNeg) != initSet.end()) {
//  			modified = true;
//  			initSet.erase(vNeg);
//  			AVR_LOG(15, 0, "\t(warning: conflict in init and assumptions)\n");
//  			AVR_LOG(15, 0, "\t\tinit:\t" << *vNeg << endl);
//  			AVR_LOG(15, 0, "\t\tassume:\t" << *v << endl);
//  		}
//  	}
//  	if (modified) {
//  		InstL conjunct_init;
//  		for (auto& v: initSet)
//  			conjunct_init.push_back(v);
//  		if (!conjunct_init.empty())
//  			_ve_init = OpInst::create(OpInst::LogAnd, conjunct_init);
//  		else
//  			_ve_init = NumInst::create(1, 1, SORT());
//  	}
//  }
}
void Reach::collect_system() {
	preprocess_system();
  collect_nsfs(_ve_init, _conjunct_init, true);
  _neg_init.clear();
  for (InstL::iterator it = _conjunct_init.begin(); it != _conjunct_init.end(); ++it) {
    Inst *t_ve = *it;
    _neg_init.insert(OpInst::create(OpInst::LogNot, t_ve));

    OpInst* t_op = OpInst::as(t_ve);
    if (t_op && t_op->get_op() == OpInst::Eq) { // r = 5'd0
      const InstL* ch = t_op->get_children();
      InstL::const_iterator cit = ch->begin(), cit2 = ch->begin();
      cit2++;
      Inst * ve_lhs = *cit;
      Inst * ve_rhs = *cit2;

      _m_reg_init[ve_lhs] = ve_rhs;

//    	_s_constants.insert(num);

      if (ve_lhs->get_type() == Sig && !ve_rhs->childrenInfo[SIG])
      	_init_values[ve_lhs] = ve_rhs;

	if (ve_lhs->get_size() != 1) {
		add_local_eq(ve_lhs, ve_rhs);
	}

#ifdef LEARN_INIT_PREDICATE
      _init_preds.push_back(t_ve);
#endif
    }else{
      if (t_op && t_op->get_op() == OpInst::LogNot){  // !q
        Inst * ve_lhs = t_op->get_children()->front();
        if (ve_lhs->get_type() == Sig)
        	_init_values[ve_lhs] = NumInst::create(0, 1, SORT());

#ifdef LEARN_INIT_PREDICATE
        _init_preds.push_back(ve_lhs);
#endif
      }else{  // q
        if (t_ve->get_type() == Sig)
        	_init_values[t_ve] = NumInst::create(1, 1, SORT());

#ifdef LEARN_INIT_PREDICATE
        _init_preds.push_back(t_ve);
#endif
      }
      _l_negated_ff_inits.push_back(OpInst::create(OpInst::LogNot, t_ve));
      _s_negated_ff_inits.insert(OpInst::create(OpInst::LogNot, t_ve));
    }
  }

  _ve_initNeg = OpInst::create(OpInst::LogNot, _ve_init);

  collect_nsfs(_ve_model_nsf, _conjunct_nsf, true);
  /// Below line not needed I guess
  _ve_model_nsf = OpInst::create(OpInst::LogAnd, _conjunct_nsf);

  int num_bits = 0;
  int num_regs = 0;
  int num_total_bits = 0;
  map<int, int> reg_stats;
  Inst::init_visit();
  for (InstL::iterator it = _conjunct_nsf.begin(); it != _conjunct_nsf.end(); ++it) {
    Inst *tve = *it;
    if (tve == NumInst::create(1, 1, SORT()))
    	continue;

    Inst *lhs;
    Inst *rhs;
    if(tve->get_children()){
      InstL::const_iterator it2 = tve->get_children()->begin();
      lhs = *it2++;
      if((tve->get_type() == Op) && (OpInst::as(tve)->get_op() == OpInst::LogNot)){
        rhs = NumInst::create(0, 1, SORT());
      }else{
        rhs = *it2;
      }
    }else{
      lhs = tve;
      rhs = NumInst::create(1, 1, SORT());
    }

    if(reg_stats.find(lhs->get_size()) == reg_stats.end()){
      reg_stats[lhs->get_size()] = 1;
    }else{
      reg_stats[lhs->get_size()]++;
    }
    if(lhs->get_size() == 1){
      num_bits++;
      num_total_bits++;
    }else{
      num_regs++;
      num_total_bits += lhs->get_size();
    }

    SigInst* sig = SigInst::as(lhs);
    if(!sig)  cout << *lhs << endl;
    assert(sig);
    if(!lhs->find_next())  cout << *lhs << " equals " << *rhs << endl;
    assert(lhs->find_next());

    string str_lhs = sig->get_name();
		// TODO: trel: resolve
    Inst::_m_sn[lhs] = make_pair(rhs, !rhs->find_next());

    Inst::en_array |= sort_present(lhs->get_sort(), arraytype);
    Inst::en_integer |= sort_present(lhs->get_sort(), inttype);

    string str_lhs_wo_next = str_lhs.substr(0, str_lhs.find_last_of('$'));

    /// Aman
    Inst* sigTmp = SigInst::create(str_lhs_wo_next, sig->get_size(), sig->get_sort());
    SigInst::as(sigTmp)->set_idx();

    Inst::_s_reg.insert(sigTmp);

    Inst::_m_state_to_ptr[str_lhs_wo_next] = sigTmp;

    Inst::_m_next_to_pre[lhs] = sigTmp;
    Inst::_m_pre_to_next[sigTmp] = lhs;

    if (_max_funcLevel < rhs->trueFcLevel)
      _max_funcLevel = rhs->trueFcLevel;
    /// END
  }
  for (auto& m: Inst::_m_sn)
  {
    SigInst::as(m.first)->set_idx();
  }
  for (InstToPairBoolM::iterator it = Inst::_m_sn.begin(); it != Inst::_m_sn.end(); it++)
  {
		// TODO: trel: resolve
    Inst* tve = (*it).second.first;
    collect_Assignments(tve, (*it).first, true);
    AVR_LOG(0, 5, *((*it).first) << " : " << _m_assignments[(*it).first] << endl);

    Inst* lhs = (*it).first;

    InstS nextSigs;
    Inst::collect_next_reg(lhs, nextSigs, true);
    nextSigs.insert(lhs);

    InstS sig_set;
		Inst::init_visit2();
    for (auto& v: nextSigs) {
    	Inst* rel = Inst::fetch_trelation(v);
      collect_sig(rel, sig_set, false);
    }
    InstS sig_coi;
    for (auto& v: sig_set) {
    	if (!v->find_next())
    		sig_coi.insert(v);
    }
    Inst::_m_backward_coi[lhs] = sig_coi;
  }

  InstL assumptions;
  if (_ve_assume != NumInst::create(1, 1, SORT())) {
  	collect_cubes(_ve_assume, true);
  	for (auto& v: _collected_cubes) {
  		_assumptions.insert(v->get_port());
  		assumptions.push_back(v);
      numAssume++;
  	}
  	InstS assumeSig;
  	collect_sig(_ve_assume, assumeSig, true);
  	numAssumeSig = assumeSig.size();
  	for (auto& s: assumeSig) {
  		if (find_reg(s))
  			numAssumeReg++;
  	}
  }

#ifdef LEARN_INIT_PREDICATE
  Inst::init_visit2();
  for (InstL::iterator it = _init_preds.begin(); it != _init_preds.end(); it++) {
  	(*it) = add_missing_wires(*it);
  	Inst* v = (*it);
  	numAssumeInit++;
#ifdef LEARN_INIT_PREDICATE_ADD_PRED
  	_s_conditions_pre.insert(v);
#endif
#ifdef LEARN_INIT_PREDICATE_PROCESS_PRED
  	process_predicate_info(v);
#endif
  	Inst* tve = add_missing_wires(OpInst::create(OpInst::LogOr, OpInst::create(OpInst::LogNot, v), v));
  	assumptions.push_back(tve);
  }
#endif

  if (!assumptions.empty()) {
  	InstL next_assumptions;
  	for (auto& v: assumptions) {
//  		_negated_refs.push_back(v);
			if (!v->find_next()) {
				Inst* vNext = Inst::all_pre2next(v);
//				_negated_refs.push_back(vNext);
	  		next_assumptions.push_back(vNext);
			}
  	}
  	assumptions.insert(assumptions.end(), next_assumptions.begin(), next_assumptions.end());
  	_ve_assume = OpInst::create(OpInst::LogAnd, assumptions);

		if (Config::g_lazy_assume >= LAZY_ASSUME_L2) {
			for (auto& v: assumptions) {
					_all_assumptions.insert(make_pair(v, false));
			}
		}
		else {
			numAssumeLemmas++;
			_negated_refs.push_back(_ve_assume);
			_all_assumptions.insert(make_pair(_ve_assume, true));
		}

//		_negated_refs.push_back(_ve_assume);
//  	cout << "(assuming) " << *_ve_assume << endl;

  	{
			add_all_wires(_ve_assume, _assume_wires, true);
			Inst::collect_next_reg(_ve_assume, _assume_regNext, true);
			InstL assumeT;
			for (auto& sigNext : _assume_regNext) {
				Inst* coneT = Inst::fetch_trelation(sigNext);
				assumeT.push_back(coneT);
			}
			if (!assumeT.empty()) {
				Inst* tveAssume = OpInst::create(OpInst::LogAnd, assumeT);
				add_all_wires(tveAssume, _assume_Twires, true);
	  		if (Config::g_lazy_assume >= LAZY_ASSUME_L1) {
					for (auto& v: assumeT) {
							_assume_T.insert(make_pair(v, false));
					}
	  		}
				else {
					numAssumeLemmas++;
					_negated_refs.push_back(tveAssume);
					_assume_T.insert(make_pair(tveAssume, true));
				}
			}
  	}
  }

  _ve_model_next = Inst::all_pre2next(_ve_model);
  {
		InstS relevantNext;
		Inst::collect_next_reg(_ve_model_next, relevantNext, true);
		InstL conjunct_badT;
		for (auto& sigNext: relevantNext) {
			Inst* coneT = Inst::fetch_trelation(sigNext);
			conjunct_badT.push_back(coneT);
		}
		if (!conjunct_badT.empty())
			_ve_model_nextT = OpInst::create(OpInst::LogAnd, conjunct_badT);
		else
			_ve_model_nextT = NumInst::create(1, 1, SORT());
  }

  set_init_dontcare();

//  for (int i = 1; i <= 4; i++) {
////  for (int i = 1; i <= INTERPRET_UF_NUM_LIMIT; i++) {
//    for (int j = 0; j < pow(2, i); j++) {
////    	cout << "creating " << i << "'d" << j << endl;
//    	NumInst::create(j, i);
//    }
//  }

  AVR_LOG(0, 6, "State variables:" << endl);
  for (InstS::iterator it = Inst::_s_reg.begin(); it != Inst::_s_reg.end(); it++)
  {
    AVR_LOG(0, 6, *(*it) << endl);
  }

  AVR_LOG(15, 0, endl);
  AVR_LOG(15, 0, "#STAT# num_bits= " << num_bits << " num_regs= " << num_regs << " num_total_bits= " << num_total_bits << endl);
  for(map<int, int>::iterator mit = reg_stats.begin(); mit != reg_stats.end(); ++mit){
    AVR_LOG(15, 0, mit->first << "  " << mit->second << endl);
  }
}

void Reach::collect_cones() {
  AVR_LOG(0, 6, "Backward COIs" << endl);
  for (InstToSetM::iterator mit = Inst::_m_backward_coi.begin(); mit != Inst::_m_backward_coi.end(); mit++)
  {
    Inst* lhs = (*mit).first;
    AVR_LOG(0, 6, "[" << *lhs << "]: " << (*mit).second << endl);
    for (InstS::iterator sit = (*mit).second.begin(); sit != (*mit).second.end(); sit++)
    {
      Inst::_m_forward_coi[*sit].insert(lhs);
    }
  }
  AVR_LOG(0, 6, "Forward COIs" << endl);
  for (InstToSetM::iterator mit = Inst::_m_forward_coi.begin(); mit != Inst::_m_forward_coi.end(); mit++)
  {
    Inst* lhs = (*mit).first;
    AVR_LOG(0, 6, "[" << *lhs << "]: " << (*mit).second << endl);
  }
}

void Reach::collect_inputs() {
	for (InstToSetM::iterator mit = Inst::_m_forward_coi.begin(); mit != Inst::_m_forward_coi.end(); mit++)
  {
    Inst* lhs = (*mit).first;
    if (Inst::_s_reg.find(lhs) == Inst::_s_reg.end())
    {
    	assert(!lhs->find_next());
      Inst::_s_inp.insert(lhs);
      SigInst* sig = SigInst::as(lhs);
      assert(sig);
      sig->set_idx();

      string sigName = sig->get_name();
      string sigName_w_next = sigName + "$next";
      Inst* sigTmp = SigInst::create(sigName_w_next, sig->get_size(), sig->get_sort());
      Inst::_m_next_input_pre[sigTmp] = lhs;
      Inst::_m_pre_input_next[lhs] = sigTmp;
    }
  }

  InstS inputsIn_I_P_A;
  collect_sig(_ve_model, inputsIn_I_P_A, true);
  collect_sig(_ve_init, inputsIn_I_P_A);
  collect_sig(_ve_assume, inputsIn_I_P_A);
  for (auto& lhs: inputsIn_I_P_A)
  {
    if (Inst::_s_reg.find(lhs) == Inst::_s_reg.end())
    {
    	if (!lhs->find_next()) {
				Inst::_s_inp.insert(lhs);
				SigInst* sig = SigInst::as(lhs);
				assert(sig);
				sig->set_idx();

				string sigName = sig->get_name();
				string sigName_w_next = sigName + "$next";
				Inst* sigTmp = SigInst::create(sigName_w_next, sig->get_size(), sig->get_sort());
				Inst::_m_next_input_pre[sigTmp] = lhs;
				Inst::_m_pre_input_next[lhs] = sigTmp;
    	}
    }
  }

  AVR_LOG(0, 6, "Inputs: " << Inst::_s_inp << endl);

  for (auto& tve: _assumptions) {
  	if (!tve->find_next()) {
			Inst* v = tve->get_port();
			OpInst* op = OpInst::as(v);
			if (op && op->get_op() == OpInst::Eq) {
				Inst* lhs = op->get_children()->front();
				Inst* rhs = op->get_children()->back();
				if (lhs->get_type() != Sig)
					swap(lhs, rhs);
				if (lhs->get_type() == Sig) {
					if (Inst::_s_reg.find(lhs) == Inst::_s_reg.end()) {
						assert(Inst::_s_inp.find(lhs) != Inst::_s_inp.end());
						Inst* lhsNext = Inst::all_pre2next(lhs);
						Inst* rhsNext = Inst::all_pre2next(rhs);

						Inst::_m_inp[lhs].insert(OpInst::create(OpInst::Eq, lhs, rhs));
						Inst::_m_inp_next[lhsNext].insert(OpInst::create(OpInst::Eq, lhsNext, rhsNext));
					}
				}
			}
  	}
  }
}

void Reach::set_init_dontcare() {
  for (InstS::iterator it = Inst::_s_reg.begin(); it != Inst::_s_reg.end(); it++) {
    SigInst* sig = SigInst::as(*it);
    assert (sig);
    if (_init_values.find(sig) == _init_values.end())
    {
      stringstream cName;
      int sz = sig->get_size();
      cName << sig->get_sort().sort2str() << "_" << sz << "'d*_" << sig->get_name();
      Inst* c = ConstInst::create(cName.str(), sz, sig, -1, sig->get_sort());
      _init_dont_care[sig] = c;
      AVR_LOG(15, 3, "Initial don't care:\t" << *sig << " = " << *c << endl);
    }
  }
}

void Reach::print_config2() {
  AVR_LOG(15, 0, endl);
  AVR_LOG(15, 0, "\t(maximum function composition in T: " << _max_funcLevel << ")" << endl);

#ifdef ABSTRACTION_COURSE
  Inst::_allowed_abLevel = (_max_funcLevel);
  cout << "\t(abstraction-course-automatic-function-composition-limit: " << Inst::_allowed_abLevel << ")" << endl;
#endif

#ifdef LIMIT_WLP_USING_FCLEVEL
//  _allowed_funcLevel = (_max_funcLevel < 5) ? 8 : (2*_max_funcLevel);
  _allowed_funcLevel = (_max_funcLevel);
//  _allowed_funcLevel = _max_funcLevel;
  cout << "\t(abstraction-limit-wlp-using-function-composition-upto: " << _allowed_funcLevel << ")" << endl;
//  AVR_LOG(15, 0, "Allowed function composition level: " << _allowed_funcLevel << " (maximum in T: " << _max_funcLevel << ")" << endl);
#endif

  _resFile << "#uf-initial:\t" << OpInst::_numUF << endl;
  _resFile << "#extract-initial:\t" << OpInst::_numEx << endl;
  _resFile << "#concat-initial:\t" << OpInst::_numConcat << endl;

}

void Reach::print_system_stats() {
  Inst *anded_models = OpInst::create(OpInst::LogAnd, _ve_model, _ve_model_nsf);
#ifdef DETAILED_STAT_DUMP
  node_count(anded_models, true);
  AVR_LOG(15, 0, endl);
  AVR_LOG(15, 0, "System" << endl);
//  cout << *anded_models << endl;
  AVR_LOG(15, 0, "  int : " << _int_node_cnt << endl);
  AVR_LOG(15, 0, "  bool : " << _bool_node_cnt << endl);
  AVR_LOG(15, 0, "  sum : " << _node_cnt << endl);
  AVR_LOG(15, 0, "  bool_op : " << _bool_op_cnt << endl);
  AVR_LOG(15, 0, "  int_op : " << _int_op_cnt << endl);

// op_stats with the index of operator string
  for(map<string, int>::iterator mit = _op_stats.begin(); mit != _op_stats.end(); ++mit){
    AVR_LOG(15, 0, "    " << mit->first << "  " << mit->second << endl);
  }
  AVR_LOG(15, 0, endl);

  node_count(_ve_model, true);
  AVR_LOG(15, 0, endl);
  AVR_LOG(15, 0, "Property" << endl);
//  cout << *anded_models << endl;
  AVR_LOG(15, 0, "  int : " << _int_node_cnt << endl);
  AVR_LOG(15, 0, "  bool : " << _bool_node_cnt << endl);
  AVR_LOG(15, 0, "  sum : " << _node_cnt << endl);
  AVR_LOG(15, 0, "  bool_op : " << _bool_op_cnt << endl);
  AVR_LOG(15, 0, "  int_op : " << _int_op_cnt << endl);

// op_stats with the index of operator string
  for(map<string, int>::iterator mit = _op_stats.begin(); mit != _op_stats.end(); ++mit){
    AVR_LOG(15, 0, "    " << mit->first << "  " << mit->second << endl);
  }
  AVR_LOG(15, 0, endl);
#endif

  count_all_simple(_ve_model, 0, true, true);
  count_all_simple(anded_models, 0, false, true);

  int pcount = 0;
  int pmax = 0;
  for (auto& i: num_excc_prop) {
    pcount += i.second;
    pmax = max(pmax, i.first);
  }
  int acount = 0;
  int amax = 0;
  for (auto& i: num_excc_all) {
    acount += i.second;
    amax = max(amax, i.first);
  }

  AVR_LOG(15, 0, "Partial interpretation info:" << "\n");
  AVR_LOG(15, 0, "  depth: " << amax << "\n");
  AVR_LOG(15, 0, "  count: " << acount << "\n");
  AVR_LOG(15, 0, "  count (d=0): " << num_excc_all[0] << "\n");
  AVR_LOG(15, 0, "\n");
  AVR_LOG(15, 0, "  depth (prop): " << pmax << "\n");
  AVR_LOG(15, 0, "  count (prop): " << pcount << "\n");
  AVR_LOG(15, 0, "  count (d=0) (prop): " << num_excc_prop[0] << "\n");

  _resFile << "excc-max-dep:\t" << amax << endl;
  _resFile << "excc-count-d0:\t" << num_excc_all[0] << endl;
  _resFile << "excc-count:\t" << acount << endl;
  _resFile << "excc-max-dep-prop:\t" << pmax << endl;
  _resFile << "excc-count-d0-prop:\t" << num_excc_prop[0] << endl;
  _resFile << "excc-count-prop:\t" << pcount << endl;

  _resFile << "max-comb-dep:\t" << anded_models->fcLevel << endl;
  _resFile << "max-comb-uf-dep:\t" << anded_models->trueFcLevel << endl;
  _resFile << "prop-comb-dep:\t" << _ve_model->fcLevel << endl;
  _resFile << "prop-comb-uf-dep:\t" << _ve_model->trueFcLevel << endl;

#ifdef CHECK_EXCC
  AVR_LOG(15, 0, "\nChecking all Ex/Cc simplifications" << "\n");
  check_all_excc(_ve_model, true);
  check_all_excc(anded_models, false);
  AVR_LOG(15, 0, "\tsuccess" << endl);
#endif
}

void Reach::collect_struct_info() {
#ifdef STRUCTURAL_PROJECTION
  /// Already has T
  sa.start(_ve_init, _ve_model, _assumptions, "Performing Strutural Analysis for I ^ P ^ T");
   sa.add_preds(_s_conditions_pre);

  _resFile << "sa-sz-num:\t" << STRUCTURE_ANALYSIS::sz_num_compare << endl;
  _resFile << "sa-sz-wir:\t" << STRUCTURE_ANALYSIS::sz_wire_compare << endl;
  _resFile << "sa-sz-sig:\t" << STRUCTURE_ANALYSIS::sz_sig_compare << endl;
  _resFile << "sa-sz-sig-com-nodes:\t" << STRUCTURE_ANALYSIS::sz_sig_compare_common_nodes << endl;
  _resFile << "sa-sz-sig-com-fapps:\t" << STRUCTURE_ANALYSIS::sz_sig_compare_common_fapp << endl;

  _resFile << "sa-#fapps:\t" << STRUCTURE_ANALYSIS::num_fapp << endl;
  _resFile << "sa-#wapps:\t" << STRUCTURE_ANALYSIS::num_wapp << endl;
  _resFile << "sa-#com-nodes:\t" << STRUCTURE_ANALYSIS::num_common_node << endl;
  _resFile << "sa-#com-fapps:\t" << STRUCTURE_ANALYSIS::num_common_fapp << endl;
#else
  _resFile << "sa-sz-num:\t0" << endl;
  _resFile << "sa-sz-wir:\t0" << endl;
  _resFile << "sa-sz-sig:\t0" << endl;
  _resFile << "sa-sz-sig-com-nodes:\t0" << endl;
  _resFile << "sa-sz-sig-com-fapps:\t0" << endl;

  _resFile << "sa-#fapps:\t0" << endl;
  _resFile << "sa-#wapps:\t0" << endl;
  _resFile << "sa-#com-nodes:\t0" << endl;
  _resFile << "sa-#com-fapps:\t0" << endl;
#endif
}

void Reach::set_property() {
  Inst *ve_sig_prop = SigInst::create(_config->get_arg(PROP_SIG_ARG), 1, SORT());

  Inst *ve_num_1 = NumInst::create(1, 1, SORT());// NumInst::create(value, bit-width of the number)
  Inst *ve_num_0 = NumInst::create(0, 1, SORT());// NumInst::create(value, bit-width of the number)
  _ve_prop_eq_1 = OpInst::create(OpInst::Eq, ve_sig_prop, ve_num_1);
  _ve_prop_eq_0 = OpInst::create(OpInst::Eq, ve_sig_prop, ve_num_0);
  AVR_LOG(0, 5, "_ve_prop_eq_1:" << *_ve_prop_eq_1 << endl);
  AVR_LOG(0, 5, "_ve_prop_eq_0:" << *_ve_prop_eq_0 << endl);

  _ve_prop_next_eq_1 = Inst::all_pre2next(_ve_prop_eq_1);
  _ve_prop_next_eq_0 = Inst::all_pre2next(_ve_prop_eq_0);
}

void Reach::draw_system() {
#ifndef PERFORMANCE_NODRAW
	if (Config::g_print_dot[DRAW_SYSTEM] == '0')
		return;
  draw_graph(0, _ve_model, _config->get_arg(PROP_SIG_ARG), 0, 0);
//	Inst* ve_model_simple = simplify_expr_all(_ve_model);
//  draw_graph(0, ve_model_simple, _config->get_arg(PROP_SIG_ARG) + "_simp", 0, 0);

	if (Config::g_print_dot[DRAW_A] != '0') {
		int count = 0;
		for (auto& v: _assumptions) {
			if (v->get_type() == Wire)
				draw_graph(0, v, WireInst::as(v)->get_name(), 0);
			else
				draw_graph(0, v, "assume$" + to_string(count), 0);
			count++;
		}
	}

	if (Config::g_print_dot[DRAW_T] != '0') {
		draw_graph(0, _ve_model_nsf, "T", 0, 0);
		for (auto& m: Inst::_m_sn)
		{
			Inst* lhs = m.first;
			Inst* pre = Inst::_m_next_to_pre[lhs];
			assert(pre);
			SigInst* sig = SigInst::as(pre);
			assert(sig);
			string n = sig->get_name();
			if (n[0] == '\\')
				n.erase(0, 1);
			draw_graph(0, Inst::fetch_trelation(lhs), n, 0, 0);
		}
	}

	if (Config::g_print_dot[DRAW_EXCC] != '0') {
		int count = 0;
		draw_all_simple(_ve_model, count, "p", true);
		draw_all_simple(_ve_model_nsf, count, "t");
	}
#endif
}

void Reach::draw_simple(Inst* e, string comment) {
  {
    ostringstream ostr;
    ostr << "excc/" << comment << "_o" << e->get_id();
    draw_graph(1, e, ostr.str(), 0, false);
  }
  {
    OpInst* op = OpInst::as(e);
    assert(op);
    ostringstream ostr;
    ostr << "excc/" << comment << "_s" << e->get_id() << "_" << op->t_simple->get_id();
    draw_graph(1, op->t_simple, ostr.str(), 0, false);
  }
}

void Reach::draw_all_simple(Inst *top, int& count, string comment, bool init_visit)
{
#ifndef PERFORMANCE_NODRAW
  if (init_visit) {
    Inst::init_visit2();
  }
  if (top->get_visit2()) {
    return;
  }
  top->set_visit2();

  if (count > 100)
    return;

  ExInst* ex = ExInst::as(top);
  if (ex)
  {
    if (ex != ex->t_simple) {
      count++;
      draw_simple(ex, to_string(count) + "_" + comment);
      draw_all_simple(ex->t_simple, count, comment + "n");
    }
  }
  else
  {
    OpInst* op = OpInst::as(top);
    if (op)
    {
    	if (Config::g_print_dot[DRAW_EXCC_UF] != '0' || op->get_op() == OpInst::Concat) {
        if (op != op->t_simple) {
          count++;
          draw_simple(op, to_string(count) + "_" + comment);
          draw_all_simple(op->t_simple, count, comment + "n");
        }
      }
    }

    const InstL* ch = top->get_children();
    if (ch)
    {
      InstL new_ch;
      for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it) {
        draw_all_simple((*it), count, comment);
      }
    }
  }
#endif
}

void Reach::check_excc(Inst* lhs, Inst* rhs) {
  SOLVER_BV cc_solver(_concrete_mapper, AVR_EXTRA_IDX, false, regular);
  cc_solver.assert_all_wire_constraints();

//  cout << "\tChecking:" << endl;
//  cout << "\t\tLHS: #" << lhs->get_id() << "\t" << *lhs << endl;
//  cout << "\t\tRHS: #" << rhs->get_id() << "\t" << *rhs << endl;
//  draw_excc(lhs, "lhs_#" + to_string(lhs->get_id()));
//  draw_excc(rhs, "rhs_#" + to_string(rhs->get_id()));

  Inst* tve = OpInst::create(OpInst::NotEq, lhs, rhs);
  cc_solver.s_assert(tve);
  int res = cc_solver.s_check(0, false);
  // res should be false

  if (res == AVR_QSAT) {
    cout << "\t(error: ex/cc simplification invalid)" << endl;
    cout << "\t\tLHS: #" << lhs->get_id() << "\t" << *lhs << endl;
    cout << "\t\tRHS: #" << rhs->get_id() << "\t" << *rhs << endl;
    draw_simple(lhs, "error_lhs_#" + to_string(lhs->get_id()));
    draw_simple(rhs, "error_rhs_#" + to_string(rhs->get_id()));
    assert(0);
  }
  else if (res == AVR_QUSAT) {
    // successful
  }
  else {
    // Timeout/error
    cout << "\t(timeout/error: res = )" << res << endl;
  }
}

void Reach::check_all_excc(Inst *top, bool init_visit) {
  if (init_visit) {
    Inst::init_visit2();
  }
  if (top->get_visit2()) {
    return;
  }
  top->set_visit2();

  ExInst* ex = ExInst::as(top);
  if (ex)
  {
    if (ex != ex->t_simple) {
      check_excc(ex, ex->t_simple);
      check_all_excc(ex->t_simple, false);
    }
  }
  else
  {
    OpInst* op = OpInst::as(top);
    if (op)
    {
      if (op->get_op() == OpInst::Concat) {
        if (op != op->t_simple) {
          check_excc(op, op->t_simple);
          check_all_excc(op->t_simple, false);
        }
      }
    }

    const InstL* ch = top->get_children();
    if (ch)
    {
      InstL new_ch;
      for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it) {
        check_all_excc((*it), false);
      }
    }
  }
}

void Reach::count_all_simple(Inst *top, int depth, bool isProp, bool init_visit)
{
  if (init_visit) {
    Inst::init_visit2();
  }
  if (top->get_visit2()) {
    return;
  }
  top->set_visit2();

  ExInst* ex = ExInst::as(top);
  if (ex)
  {
    if (ex != ex->t_simple) {
      if (isProp) {
        map<int, int>::iterator mit = num_excc_prop.find(depth);
        if (mit != num_excc_prop.end())
          (*mit).second++;
        else
          num_excc_prop[depth] = 1;
      }
      else {
        map<int, int>::iterator mit = num_excc_all.find(depth);
        if (mit != num_excc_all.end())
          (*mit).second++;
        else
          num_excc_all[depth] = 1;
      }
      count_all_simple(ex->t_simple, depth + 1, isProp, false);
    }
  }
  else
  {
    OpInst* op = OpInst::as(top);
    if (op)
    {
#ifdef INTERPRET_UF_OP
    	if (true) {
#else
    	if (op->get_op() == OpInst::Concat) {
#endif
        if (op != op->t_simple) {
          if (isProp) {
            map<int, int>::iterator mit = num_excc_prop.find(depth);
            if (mit != num_excc_prop.end())
              (*mit).second++;
            else
              num_excc_prop[depth] = 1;
          }
          else {
            map<int, int>::iterator mit = num_excc_all.find(depth);
            if (mit != num_excc_all.end())
              (*mit).second++;
            else
              num_excc_all[depth] = 1;
          }
          count_all_simple(op->t_simple, depth + 1, isProp, false);
        }
      }
    }

    const InstL* ch = top->get_children();
    if (ch)
    {
      InstL new_ch;
      for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it) {
        count_all_simple((*it), depth, isProp, false);
      }
    }
  }
}

void Reach::print_frame_states_transitions(bool concreteS, bool concreteT) {
  InstL src;
  for (int i = 0; i <= _frame_idx; i++) {
    InstL srcC;
    negated_cubes(i, srcC);
    if (!srcC.empty()) {
      string filename = "fsm_F" + to_string(i) + "_to_!F" + to_string(i) + ".txt";
      Inst* src;
      Inst* dest;
      src = OpInst::create(OpInst::LogAnd, srcC);
      dest = OpInst::create(OpInst::LogNot, src);
      print_states_transitions(filename, src, dest, concreteS, concreteT);

      if (i == _frame_idx) {
        filename = "fsm_F" + to_string(i) + "_to_!P" + ".txt";
        print_states_transitions(filename, srcC, _ve_prop_eq_0, concreteS, concreteT);
      }
    }

    AVR_LOG(15, 0, "\tF[" << i << "] (cubes):\n");
    for (auto& v: _cubes[i]) {
      AVR_LOG(15, 0, "\t\t" << *v.cube << "\n");
    }
    AVR_LOG(15, 0, endl);
  }
}


void Reach::print_states_transitions(string filename, Inst* invariant, bool concreteS, bool concreteT) {
  Inst* src;
  Inst* dest;
  if (invariant == NULL) {
    src = _ve_prop_eq_1;
    dest = _ve_prop_eq_0;
  }
  else {
    src = invariant;
    dest = OpInst::create(OpInst::LogNot, invariant);
  }
  print_states_transitions(filename, src, dest, concreteS, concreteT);
}

void Reach::print_states_transitions(string filename, InstL& srcC, InstL& destC, bool concreteS, bool concreteT) {
  Inst* dest;
  if (destC.empty())
    dest = NumInst::create(1, 1, SORT());
  else
    dest = OpInst::create(OpInst::LogAnd, destC);
  print_states_transitions(filename, srcC, dest, concreteS, concreteT);
}

void Reach::print_states_transitions(string filename, InstL& srcC, Inst* dest, bool concreteS, bool concreteT) {
  Inst* src;
  if (srcC.empty())
    src = NumInst::create(1, 1, SORT());
  else
    src = OpInst::create(OpInst::LogAnd, srcC);
  print_states_transitions(filename, src, dest, concreteS, concreteT);
}

void Reach::print_states_transitions(string filename, Inst* src, Inst* dest, bool concreteS, bool concreteT) {
#ifdef PRINT_ALL_ABSTRACT_CUBES
  return;

//  if (!concreteS)
//    return;

  string fname_reach = _config->get_working_dir() + "/" + filename;
  ofstream out;
  out.open(fname_reach.c_str());

  collect_cubes(src, true);
  out << "S: " << _collected_cubes << "\n" << endl;
  collect_cubes(dest, true);
  out << "D: " << _collected_cubes << "\n" << endl;

  InstL conjunct_P;
  InstL conjunct_notP;

  conjunct_P.push_back(_ve_prop_eq_1);

  conjunct_P.push_back(src);
  conjunct_notP.push_back(dest);

  conjunct_P.push_back(_ve_model);
  conjunct_notP.push_back(_ve_model);

  conjunct_P.push_back(_ve_model_nsf);
  conjunct_notP.push_back(_ve_model_nsf);

//  if (!concreteS)
  {
    for (InstL::iterator it = _negated_refs.begin(); it != _negated_refs.end(); it++)
    {
      conjunct_P.push_back((*it));
      conjunct_notP.push_back((*it));
    }
  }

  Inst* formula_P = OpInst::create(OpInst::LogAnd, conjunct_P);
  Inst* formula_notP = OpInst::create(OpInst::LogAnd, conjunct_notP);

  map < int, MIN_TERMS_ABSTRACT_DETAILED > allMinTerms_P;
  map < int, MIN_TERMS_ABSTRACT_DETAILED > allMinTerms_notP;

  if (concreteS) {
    SOLVER_BV int_solver_P(_concrete_mapper, AVR_EXTRA_IDX, false, mdl);
    int_solver_P.assert_all_wire_constraints();
    int_solver_P.s_assert(formula_P);
    collect_all_abstract_min_terms(&int_solver_P, allMinTerms_P, formula_P, true);

    SOLVER_BV int_solver_notP(_concrete_mapper, AVR_EXTRA_IDX, false, mdl);
    int_solver_notP.assert_all_wire_constraints();
    int_solver_notP.s_assert(formula_notP);
    collect_all_abstract_min_terms(&int_solver_notP, allMinTerms_notP, formula_notP, true);
  }
  else {
    SOLVER_AB int_solver_P(_abstract_mapper, AVR_EXTRA_IDX, false, mdl);
    int_solver_P.s_assert(formula_P);
    collect_all_abstract_min_terms(&int_solver_P, allMinTerms_P, formula_P);

    SOLVER_AB int_solver_notP(_abstract_mapper, AVR_EXTRA_IDX, false, mdl);
    int_solver_notP.s_assert(formula_notP);
    collect_all_abstract_min_terms(&int_solver_notP, allMinTerms_notP, formula_notP);
  }

  out << "-------------" << endl;
  out << " States in S " << endl;
  out << "-------------" << endl;
  out << endl;
  int numP = 0;
  for (int i = 0; i < allMinTerms_P.size(); i++)
  {
    string name = "#" + to_string(allMinTerms_P[i].trueId) + " S_" + to_string(i) + " (" + allMinTerms_P[i].feasible + ")";
    print_solution(out, allMinTerms_P[i].s, name);
    if (allMinTerms_P[i].feasible == "c")
      numP++;
  }
  out << endl;

  out << "--------------" << endl;
  out << " States in D " << endl;
  out << "--------------" << endl;
  out << endl;
  int numNotP = 0;
  for (int i = 0; i < allMinTerms_notP.size(); i++)
  {
    string name = "#" + to_string(allMinTerms_notP[i].trueId) + " D_" + to_string(i) + " (" + allMinTerms_notP[i].feasible + ")";
    print_solution(out, allMinTerms_notP[i].s, name);
    if (allMinTerms_notP[i].feasible == "c")
      numNotP++;
  }
  out << endl;
  out.flush();

  vector < vector < char > > edgeRelation_P_to_notP;
  for (int i = 0; i < allMinTerms_P.size(); i++)
  {
    vector < char > row;
    for (int j = 0; j < allMinTerms_notP.size(); j++)
    {
      row.push_back('-');
    }
    edgeRelation_P_to_notP.push_back(row);
  }

  for (map < int, MIN_TERMS_ABSTRACT_DETAILED >::iterator sit = allMinTerms_P.begin(); sit != allMinTerms_P.end(); sit++)
  {
    int i = (*sit).first;
    MIN_TERMS_ABSTRACT_DETAILED& src = (*sit).second;

    for (map < int, MIN_TERMS_ABSTRACT_DETAILED >::iterator dit = allMinTerms_notP.begin(); dit != allMinTerms_notP.end(); dit++)
    {
      InstL conjunctTmp;
      conjunctTmp.push_back(src.allConditions);

      int j = (*dit).first;
      MIN_TERMS_ABSTRACT_DETAILED& dest = (*dit).second;
      conjunctTmp.push_back(Inst::all_pre2next(dest.allConditions));
      edgeRelation_P_to_notP[i][j] = check_abstract_transition(conjunctTmp, concreteT);
    }
  }

  vector < vector < char > > edgeRelation_P_to_P;
  for (int i = 0; i < allMinTerms_P.size(); i++)
  {
    vector < char > row;
    for (int j = 0; j < allMinTerms_P.size(); j++)
    {
      row.push_back('-');
    }
    edgeRelation_P_to_P.push_back(row);
  }

  for (map < int, MIN_TERMS_ABSTRACT_DETAILED >::iterator sit = allMinTerms_P.begin(); sit != allMinTerms_P.end(); sit++)
  {
    int i = (*sit).first;
    MIN_TERMS_ABSTRACT_DETAILED& src = (*sit).second;

    for (map < int, MIN_TERMS_ABSTRACT_DETAILED >::iterator dit = allMinTerms_P.begin(); dit != allMinTerms_P.end(); dit++)
    {
      InstL conjunctTmp;
      conjunctTmp.push_back(src.allConditions);

      int j = (*dit).first;
      MIN_TERMS_ABSTRACT_DETAILED& dest = (*dit).second;
      conjunctTmp.push_back(Inst::all_pre2next(dest.allConditions));
      edgeRelation_P_to_P[i][j] = check_abstract_transition(conjunctTmp, concreteT);
    }
  }

  out << "-----------------------" << endl;
  out << "Edge relation (S --> D)" << endl;
  out << "-----------------------" << endl;
  out << endl;
  out << "____________________________________________________________________________________________________________________________________________________" << endl;
  out << setw(11) << " " ;
  for (int j = 0; j < allMinTerms_notP.size(); j++)
  {
    out << " D_" << left << setw(3) << j << "  ";
  }
  out << endl;
  out << "____________________________________________________________________________________________________________________________________________________" << endl;

  int numT_nP_a = 0;
  int numT_nP_c = 0;
  for (int i = 0; i < allMinTerms_P.size(); i++)
  {
    int numT = 0;

    out << " S_" << left << setw(3) << i << setw(5) << "| ";
    for (int j = 0; j < allMinTerms_notP.size(); j++)
    {
      if (edgeRelation_P_to_notP[i][j] == 'a') {
        numT_nP_a++;
        numT++;
      }
      else if (edgeRelation_P_to_notP[i][j] == 'c') {
        numT_nP_c++;
        numT++;
      }
      out << setw(4) << edgeRelation_P_to_notP[i][j] << setw(4) << " ";
    }
#ifdef ASSERT_ALL_SRC_TO_DEST
    if (!concreteS && !concreteT && numT == 0) {
      AVR_LOG(15, 0, "\t(warning: found a state #" << allMinTerms_P[i].trueId << " not going to dest.)" << endl);
    }
#endif
    out << "\t|\t#" << numT << endl;
  }
  out << "____________________________________________________________________________________________________________________________________________________" << endl;
  out << endl;

  out << "-----------------------" << endl;
  out << "Edge relation (S --> S)" << endl;
  out << "-----------------------" << endl;
  out << endl;
  out << "____________________________________________________________________________________________________________________________________________________" << endl;
  out << setw(11) << " " ;
  for (int j = 0; j < allMinTerms_P.size(); j++)
  {
    out << " S_" << left << setw(3) << j << "  ";
  }
  out << endl;
  out << "____________________________________________________________________________________________________________________________________________________" << endl;

  int numT_P_a = 0;
  int numT_P_c = 0;
  for (int i = 0; i < allMinTerms_P.size(); i++)
  {
    out << " S_" << left << setw(3) << i << setw(5) << "| ";
    for (int j = 0; j < allMinTerms_P.size(); j++)
    {
      if (edgeRelation_P_to_P[i][j] == 'a')
        numT_P_a++;
      else if (edgeRelation_P_to_P[i][j] == 'c')
        numT_P_c++;
      out << setw(4) << edgeRelation_P_to_P[i][j] << setw(4) << " ";
    }
    out << endl;
  }
  out << "____________________________________________________________________________________________________________________________________________________" << endl;
  out << endl;

  out << "Total states      = " << (allMinTerms_P.size() + allMinTerms_notP.size()) << " (" << (numP + numNotP) << " feasible)" << endl;
  out << "Total states in S = " << allMinTerms_P.size() << " (" << numP << " feasible)" << endl;
  out << "Total states in D = " << allMinTerms_notP.size() << " (" << numNotP << " feasible)" << endl;
  out << endl;
  out << "Total transitions          = " << (numT_P_a + numT_P_c + numT_nP_a + numT_nP_c) << " (" << (numT_P_c + numT_nP_c) << " feasible)" << endl;
  out << "Total transitions S --> S  = " << (numT_P_a + numT_P_c) << " (" << numT_P_c << " feasible)" << endl;
  out << "Total transitions S --> D  = " << (numT_nP_a + numT_nP_c) << " (" << numT_nP_c << " feasible)" << endl;

  out.close();
#endif
}

void Reach::print_frame_summary(int k) {
  assert(k == _frame_idx);

  struct rusage usage;
  struct timeval end_time;
  long long time_diff;

  ostringstream str;
  str << "   " << _numRefinements << "\t: " << k << "\t: 0";
  int sum_cubes = 0;
  for (int i = 1; i <= k; i++) {
    sum_cubes += (_cubes[i]).size();
    str << " " << (_cubes[i]).size();
  }
  str << " s: " << sum_cubes;
//  str << " sz: " << _cubes.size();
//  str << " top: " << _frame_idx;
  AVR_LOG(8, 1, str.str() << endl);

  ostringstream str2;
  str2 << "L  " << k << " : 0";
  int sum_literals = 0;
  for (int i = 1; i <= k; i++) {
    int literals = 0;
    for(auto& cube: _cubes[i]){
    	literals += cube.literals.size();
    }
    sum_literals += literals;
    str2 << " " << literals;
  }
  getrusage(RUSAGE_SELF, &usage);
  timeradd(&usage.ru_utime, &usage.ru_stime, &end_time);
  time_diff = Timevaldiff(&_start_time, &end_time);
  double elapsed_time = ((double)time_diff / 1000000);

  unsigned memory_usage = usage.ru_maxrss/1024; // accurate memory usage in Mbytes
  str2 << " s: " << sum_literals << ", mem: " << memory_usage << ", time: " << elapsed_time << endl;
  //cout << "memUsed(): " << memUsed() << endl;
  AVR_LOG(8, 0, str2.str());
#ifdef PRINT_FRAME_SUMMARY
  string summary = "";

  summary += "   " + to_string(_numRefinements) + "\t: " + to_string(k) + "\t:";
  string fsummary = "";
  for (int i = k; i >= 0; i--) {
  	if (i == 0)
  		fsummary = " 0" + fsummary;
  	else
  		fsummary = " " + to_string((_cubes[i]).size()) + fsummary;
  	if (fsummary.length() > 30) {
  		fsummary = " ..." + fsummary;
  		break;
  	}
  }
  summary += fsummary + " s: " + to_string(sum_cubes);

  cerr << "\r" << summary << "    " << ((int) elapsed_time) << "s                  ";
#endif
}

int Reach::print_sorted_list(ofstream& out, InstL& l, bool print_msz) {
  Inst::print_cc();

  set< string > lines;
  int mmsz = 1;
  for (auto& i: l) {
    stringstream tmp;
    mmsz = (i->maxSize > mmsz) ? i->maxSize : mmsz;
//    if (print_msz)
//    	tmp << "[" << i->maxSize << "]\t";
    bool done = false;
#ifdef I4
    if (i->get_type() == Op) {
			OpInst* opi = OpInst::as(i);
			if (opi->get_op() == OpInst::LogNot) {
				Inst* ineg = opi->get_children()->front();
				if (ineg->get_type() == Op) {
					OpInst* opineg = OpInst::as(ineg);
					if (opineg->get_op() == OpInst::LogAnd) {
						set< pair<string, bool> > words;
						for (auto& ch: *opineg->get_children()) {
							Inst* child = ch;
							bool negated = false;
							if (OpInst::as(ch) && OpInst::as(ch)->get_op() == OpInst::LogNot) {
								child = ch->get_children()->front();
								negated = true;
							}
							stringstream tmp2;
							tmp2 << *child;
							words.insert(make_pair(tmp2.str(), negated));
						}
						tmp << "!(";
						int count = 0;
						for (auto& j: words) {
							count++;
							if (j.second)
								tmp << "!(";
							tmp << j.first;
							if (j.second)
								tmp << ")";
							if (count != words.size())
								tmp << " & ";
						}
						tmp << ")";
						done = true;
					}
				}
			}
    }
#endif
    if (!done)
    	tmp << *i;
    lines.insert(tmp.str());
  }

  int sz = lines.size();
  out << "(sz: " << sz << ")" << endl;
  for (auto& j: lines) {
    sz--;
    if (sz != 0)
      out << "\t\t" << j << "\t&&" << endl;
    else
      out << "\t\t" << j << endl;
  }

  Inst::print_ab();
  return mmsz;
}

}
