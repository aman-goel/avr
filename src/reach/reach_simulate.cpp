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
#ifdef SIMULATION_CHECK_SELF_LOOPS
	int Reach::sim_self_loop_allowance = INIT_SELF_LOOP_ALLOWANCE;
#endif

Inst* Reach::add_missing_wires(Inst* top) {
//  cout << "top: " << *top << " type: " << top->get_type() << endl;

  if (top->get_visit2()){
//    cout << "already visited" << endl;
    return top->nsub_coi;
  }
  top->set_visit2();

//  cout << "top: " << *top << endl;

  Inst* topRet = top;

  const InstL* ch = topRet->get_children();
  if (ch) {
    InstL new_ch;
    bool need_new = false;
    for (InstL::const_iterator cit = ch->begin(); cit != ch->end(); cit++) {
      Inst* tve = (*cit);
      Inst* newTve = add_missing_wires(tve);
      if (newTve != tve)
        need_new = true;
      new_ch.push_back(newTve);
    }
    if (need_new)
      topRet = topRet->apply_children(new_ch);
  }

  OpInst* op = OpInst::as(topRet);
  if (op) {
    Inst* w = op->get_wire();
    if (!w) {
      switch(op->get_op()) {
      case OpInst::Eq:
      case OpInst::NotEq:
      case OpInst::LogNot:
        break;
      default: {
        string name = AVR_WIRE_NAME_PREFIX + to_string(++Inst::avr_wid);
        w = WireInst::create(name, topRet->get_size(), topRet);
        AVR_LOG(15, 0, "\t\t\t(creating wire " << *w << " for port " << *topRet << ")" << endl);
        topRet = w;
      }
      }
    }
    else
        topRet = w;
  }
  if (!topRet) {
    cout << "error in " << *top << endl;
  }
  assert(topRet);
//  cout << *top << "\t->\t" << *topRet << endl;

  top->nsub_coi = topRet;
  return topRet;
}


/// Aman
Inst* Reach::apply_simulation_constants (Inst *e, InstToSetM& m_constMap, bool init_visit)
{
	if (init_visit) {
		Inst::init_visit();
	}
	if (e->get_visit()) {
		return e->acex_coi;
	}
	e->set_visit();

	bool print = false;

	e->acex_coi = e;
	if (print)
		cout << "e: " << *e << endl;

	const InstL* ch = e->get_children();
	if (ch)
	{
		bool apply_new_ch = false;
		InstL newl;

		for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it)
		{
			Inst *tve = apply_simulation_constants(*it, m_constMap);
			newl.push_back(tve);
			if (tve != *it)
			{
				apply_new_ch = true;
			}
		}

		if (apply_new_ch)
		{
			Inst *res = e->apply_children(newl);
			OpInst* opR = OpInst::as(res);
			if (opR) {
				Inst* w = opR->get_wire();
				if (w) {
					switch(opR->get_op()) {
					case OpInst::Eq:
					case OpInst::NotEq:
					case OpInst::LogNot:
						break;
					default: {
						res = w;
					}
					}
				}
			}

			if (res->childrenInfo[CONST])
			{
//				OpInst* op = OpInst::as(res);
//				if (op && op->get_op() == OpInst::Concat)
//				{
//					const InstL* ch = op->get_children();
//					assert(ch);
//					InstL newCh;
//					bool modified = false;
//					for (InstL::const_iterator cit = ch->begin(); cit != ch->end(); cit++)
//					{
//						newCh.push_back(*cit);
//						if (!modified)
//						{
//							Inst* subChild = OpInst::create(OpInst::Concat, newCh);
//							Inst* newChild = apply_simulation_constants(subChild, m_constMap);
//							if (newChild != subChild)
//							{
//								modified = true;
//								newCh.clear();
//								newCh.push_back(newChild);
//							}
//						}
//					}
//					if (modified)
//					{
//						res = OpInst::create(OpInst::Concat, newCh);
//
//						if (res->childrenInfo[CONST])
//						{
//							InstToSetM::iterator mit = m_constMap.find(res);
//							if (mit != m_constMap.end())
//							{
//								for (InstS::iterator sit = (*mit).second.begin(); sit != (*mit).second.end(); sit++)
//								{
//									if ((*sit) != e)
//									{
//										e->acex_coi = (*sit);
//										if (print)
//											cout << "returning: " << *(*sit) << " instead of " << *e << endl;
//										assert(0);
//										return (*sit);
//									}
//								}
//							}
//						}
//
//			//			if (m_constMap.find(e) != m_constMap.end())
//			//			{
//			//				m_constMap[res] = m_constMap[e];
//			//			}
//
//						e->acex_coi = res;
//						if (print)
//							cout << "returning: " << *res << " instead of " << *e << endl;
//						cout << "returning: " << *res << " instead of " << *e << endl;
//						assert(0);
//						return res;
//					}
//				}


				InstToSetM::iterator mit = m_constMap.find(e);
				if (mit != m_constMap.end())
				{
					for (InstS::iterator sit = (*mit).second.begin(); sit != (*mit).second.end(); sit++)
					{
						if ((*sit) != e)
						{
							e->acex_coi = (*sit);
//							OpInst* opE = OpInst::as(e->acex_coi);
//							if (opE && opE->get_wire())
//								e->acex_coi = opE->get_wire();

							if (print)
								cout << "returning: " << *(e->acex_coi) << " instead of " << *e << endl;
							return e->acex_coi;
						}
					}
				}
			}

//			if (m_constMap.find(e) != m_constMap.end())
//			{
//				m_constMap[res] = m_constMap[e];
//			}

			e->acex_coi = res;
//			OpInst* opE = OpInst::as(e->acex_coi);
//			if (opE && opE->get_wire())
//				e->acex_coi = opE->get_wire();

			if (print)
				cout << "returning: " << *(e->acex_coi) << " instead of " << *e << endl;
			return e->acex_coi;
		}
	}

	InstToSetM::iterator mit = m_constMap.find(e);
	if (mit != m_constMap.end())
	{
		for (InstS::iterator sit = (*mit).second.begin(); sit != (*mit).second.end(); sit++)
		{
			if ((*sit) != e)
			{
				e->acex_coi = (*sit);
//				OpInst* opE = OpInst::as(e->acex_coi);
//				if (opE && opE->get_wire())
//					e->acex_coi = opE->get_wire();

				if (print)
					cout << "returning: " << *(e->acex_coi) << " instead of " << *e << endl;
				return e->acex_coi;
			}
		}
	}

//	if (e->childrenInfo[CONST])
//	{
//		Inst* num;
//
//		if (e->get_size() == 1)
//			num = NumInst::create(e->get_bval(), 1);
//		else
//			num = NumInst::create(e->get_ival(), e->get_size());
//
//		cout << "returning: " << *num << " instead of " << *e << endl;
////		assert(0);
//		return num;
//	}
	if (print)
		cout << "returning: same for " << *e << endl;
	return e;
}

Inst* Reach::apply_simulation_constants2 (Inst *e, InstToSetM& m_constMap, bool init_visit)
{
	if (init_visit) {
		Inst::init_visit2();
	}
	if (e->get_visit2()) {
		return e->nsub_coi;
	}
	e->set_visit2();

	bool print = false;

	e->nsub_coi = e;
	if (print)
		cout << "e: " << *e << endl;

	const InstL* ch = e->get_children();
	if (ch)
	{
		bool apply_new_ch = false;
		InstL newl;

		for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it)
		{
			Inst *tve = apply_simulation_constants2(*it, m_constMap);
			newl.push_back(tve);
			if (tve != *it)
			{
				apply_new_ch = true;
			}
		}

		if (apply_new_ch)
		{
			Inst *res = e->apply_children(newl);
			OpInst* opR = OpInst::as(res);
			if (opR) {
				Inst* w = opR->get_wire();
				if (w) {
					switch(opR->get_op()) {
					case OpInst::Eq:
					case OpInst::NotEq:
					case OpInst::LogNot:
						break;
					default: {
						res = w;
					}
					}
				}
			}

			if (res->childrenInfo[CONST])
			{
				InstToSetM::iterator mit = m_constMap.find(res);
				if (mit != m_constMap.end())
				{
					for (InstS::iterator sit = (*mit).second.begin(); sit != (*mit).second.end(); sit++)
					{
						if ((*sit) != e)
						{
							e->nsub_coi = (*sit);
//							OpInst* opE = OpInst::as(e->nsub_coi);
//							if (opE && opE->get_wire())
//								e->nsub_coi = opE->get_wire();

							if (print)
								cout << "returning: " << *(e->nsub_coi) << " instead of " << *e << endl;
							return e->nsub_coi;
						}
					}
				}
			}

//			if (m_constMap.find(e) != m_constMap.end())
//			{
//				m_constMap[res] = m_constMap[e];
//			}

			e->nsub_coi = res;
//			OpInst* opE = OpInst::as(e->nsub_coi);
//			if (opE && opE->get_wire())
//				e->nsub_coi = opE->get_wire();

			if (print)
				cout << "returning: " << *(e->nsub_coi) << " instead of " << *e << endl;
			return e->nsub_coi;
		}
	}

	InstToSetM::iterator mit = m_constMap.find(e->nsub_coi);
	if (mit != m_constMap.end())
	{
		for (InstS::iterator sit = (*mit).second.begin(); sit != (*mit).second.end(); sit++)
		{
			if ((*sit) != e)
			{
				e->nsub_coi = (*sit);
//				OpInst* opE = OpInst::as(e->nsub_coi);
//				if (opE && opE->get_wire())
//					e->nsub_coi = opE->get_wire();

				if (print)
					cout << "returning: " << *(e->nsub_coi) << " instead of " << *e << endl;
				return e->nsub_coi;
			}
		}
	}

//	if (e->childrenInfo[CONST])
//	{
//		Inst* num;
//
//		if (e->get_size() == 1)
//			num = NumInst::create(e->get_bval(), 1);
//		else
//			num = NumInst::create(e->get_ival(), e->get_size());
//
//		cout << "returning: " << *num << " instead of " << *e << endl;
////		assert(0);
//		return num;
//	}
	if (print)
		cout << "returning: same for " << *e << endl;
	return e;
}
/// END

void Reach::map_bit_select_const(Inst* lhs, Inst* rhs, InstToSetM& m_constMap, InstToInstM& m_constBitMap) {
	ExInst* exR = ExInst::as(rhs);
	if (exR && exR->get_exp()->get_type() == Const) {
		int hi = exR->get_hi();
		int lo = exR->get_lo();
		Inst* exp = exR->get_exp();

		InstL args;
		InstToInstM::iterator mit2 = m_constBitMap.find(exp);
		if (mit2 != m_constBitMap.end()) {
			Inst* op_tve = (*mit2).second;
			assert(op_tve->get_type() == Op);
			assert(OpInst::as(op_tve)->get_op() == OpInst::Concat);

			const InstL* ch = op_tve->get_children();
			assert (ch);
			unsigned s_loc = 0, e_loc = 0;
			bool replaceFlag = false;
			for (InstL::const_iterator cit = ch->begin(); cit != ch->end(); ++cit)
			{
				Inst *tve = *cit;
				unsigned size = tve->get_size();
				s_loc = e_loc;
				e_loc += size;

				if (!tve->childrenInfo[CONST]) {
					args.push_back(tve);
					continue;
				}

				if (s_loc == lo)
				{
					replaceFlag = true;
					args.push_back(lhs);
					unsigned remSz = e_loc - (hi + 1);
					if (remSz > 0)
						args.push_back(ExInst::create(exp, e_loc - 1, hi + 1));
				}
				else if (!replaceFlag && (e_loc > hi))
				{
					replaceFlag = true;
					unsigned remSz = lo - s_loc;
					if (remSz > 0)
						args.push_back(ExInst::create(exp, lo - 1, s_loc));
					args.push_back(lhs);
					remSz = e_loc - (hi + 1);
					if (remSz > 0)
						args.push_back(ExInst::create(exp, e_loc - 1, hi + 1));
				}
				else
					args.push_back(tve);
			}
			if (!replaceFlag)
			{
				cout << "trying adding " << *exp << " in " << *rhs << " = " << *lhs << endl;
				cout << "args: " << args << endl;
			}
			assert(replaceFlag);
		}
		else {
			if (lo != 0)
				args.push_back(ExInst::create(exp, lo - 1, 0));
			args.push_back(lhs);
			if (hi != (exp->get_size() - 1))
				args.push_back(ExInst::create(exp, exp->get_size() - 1, hi + 1));
		}

		Inst* l = OpInst::create(OpInst::Concat, args);
		assert(l->get_size() == exp->get_size());

		m_constBitMap[exp] = l;
		if (!l->childrenInfo[CONST]) {
			AVR_LOG(14, 4, "Adding " << *exp << " -> " << *l << endl);
			m_constMap[exp].insert(l);
		}
	}
}

/// Aman
// true if c_ref has been changed
bool Reach::generalize_simulation_predicates(InstL& c_ref, InstToSetM& m_constMap, bool& learn)
{
	AVR_LOG(14, 8, "> generalize_predicates, before:" << c_ref << endl);

	InstToInstM m_constBitMap;

	InstL tc_ref = c_ref;
	for(InstL::iterator it = tc_ref.begin(); it != tc_ref.end(); it++)
	{
		Inst *tve = *it;
		Inst* lhs;
		Inst* rhs;
		if ((tve->get_type() == Op) && ((OpInst::as(tve))->get_op() == OpInst::Eq))
		{
			const InstL* ch = tve->get_children();
			InstL::const_iterator ch_it = ch->begin();
			lhs = *(ch_it++);
			rhs = *ch_it;

			if(lhs->childrenInfo[CONST])
			{
				Inst* tmp = lhs;
				lhs = rhs;
				rhs = tmp;
			}
			if (lhs->childrenInfo[CONST])
			{
				Inst* lhs_new = lhs;
				Inst* rhs_new = rhs;

				InstToSetM::iterator mit = m_constMap.find(rhs);
				if (mit != m_constMap.end())
				{
					// Do nothing
				}
				else
				{
					InstToSetM::iterator mit2 = m_constMap.find(lhs_new);
					while (mit2 != m_constMap.end()) {
						if (lhs_new == *((*mit2).second.begin()))
							break;
						lhs_new = *((*mit2).second.begin());
						mit2 = m_constMap.find(lhs_new);
					}

					if (lhs_new != rhs) {
						InstS tmp;
						tmp.insert(lhs_new);
						m_constMap[rhs] = tmp;
					}
				}

				mit = m_constMap.find(lhs);
				if (mit != m_constMap.end())
				{
					// Do nothing
				}
				else
				{
					InstToSetM::iterator mit2 = m_constMap.find(rhs_new);
					while (mit2 != m_constMap.end()) {
						rhs_new = *((*mit2).second.begin());
						if (rhs_new == *((*mit2).second.begin()))
							break;
						mit2 = m_constMap.find(rhs_new);
					}

					if (rhs_new != lhs) {
						InstS tmp;
						tmp.insert(rhs_new);
						m_constMap[lhs] = tmp;
					}
				}
			}

			assert(rhs->childrenInfo[CONST]);
			if (lhs != rhs) {
				InstToSetM::iterator mit = m_constMap.find(rhs);
				if (mit != m_constMap.end())
				{
					if (!lhs->childrenInfo[CONST])
					{
						InstS& tmpSet = (*mit).second;
						for (InstS::iterator sit = tmpSet.begin(); sit != tmpSet.end();)
						{
							if ((*sit)->childrenInfo[CONST])
							{
								sit = tmpSet.erase(sit);
							}
							else
								sit++;
						}
					}
					(*mit).second.insert(lhs);
				}
				else
				{
					InstS tmp;
					tmp.insert(lhs);
					m_constMap[rhs] = tmp;
				}
			}
		}
		else
		{
			if ((tve->get_type() == Op) && ((OpInst::as(tve))->get_op() == OpInst::LogNot))
			{
				lhs = NumInst::create(0, 1, SORT());
				rhs = tve->get_children()->front();
				assert(rhs->childrenInfo[CONST]);

				InstToSetM::iterator mit = m_constMap.find(rhs);
				if (mit != m_constMap.end())
				{
					Inst* val = *((*mit).second.begin());
					if (val != lhs) {
//					if (!lhs->childrenInfo[CONST])
						{
							InstS& tmpSet = (*mit).second;
							for (InstS::iterator sit = tmpSet.begin(); sit != tmpSet.end();)
							{
								if ((*sit)->childrenInfo[CONST])
								{
									sit = tmpSet.erase(sit);
								}
								else
									sit++;
							}
						}
						(*mit).second.insert(lhs);
					}
//					assert(val == lhs);
				}
				else
				{
					InstS tmp;
					tmp.insert(lhs);
					m_constMap[lhs] = tmp;
				}
			}
			else
			{
				lhs = NumInst::create(1, 1, SORT());
				rhs = tve;
				assert(rhs->childrenInfo[CONST]);

				InstToSetM::iterator mit = m_constMap.find(rhs);
				if (mit != m_constMap.end())
				{
					Inst* val = *((*mit).second.begin());
          if (val != lhs) {
						{
							InstS& tmpSet = (*mit).second;
							for (InstS::iterator sit = tmpSet.begin(); sit != tmpSet.end();)
							{
								if ((*sit)->childrenInfo[CONST])
								{
									sit = tmpSet.erase(sit);
								}
								else
									sit++;
							}
						}
						(*mit).second.insert(lhs);
          }
//					assert(val == lhs);
				}
				else
				{
					InstS tmp;
					tmp.insert(lhs);
					m_constMap[rhs] = tmp;
				}
			}
		}
//		map_bit_select_const(lhs, rhs, m_constMap, m_constBitMap);
	}
	if(m_constMap.empty())
	{
		return false;
	}

  for (auto& m: m_constMap)
  {
    InstS& rhsS = m.second;
    InstL insertSet;
    InstL eraseSet;
    for (auto& rhs: rhsS) {
      if (rhs->get_type() == Const) {
        InstToSetM::iterator mit = m_constMap.find(rhs);
        if (mit != m_constMap.end()) {
          InstS& rhsN = (*mit).second;
          for (auto& r: rhsN) {
          	insertSet.push_back(r);
          }
          eraseSet.push_back(rhs);
        }
      }
    }
    for (auto& v: insertSet)
    	rhsS.insert(v);
    for (auto& v: eraseSet)
    	rhsS.erase(v);
  }


	AVR_LOG(14, 6, "Printing m_constMap" << endl);
	for (InstToSetM::iterator it = m_constMap.begin(); it != m_constMap.end(); it++) {
	  AVR_LOG(14, 6, "[" << *(*it).first << "] = " << (*it).second << endl);
	}

	bool res = true;
	c_ref.clear();

	for (InstToSetM::iterator it = m_constMap.begin(); it != m_constMap.end(); it++)
	{
		if ((*it).second.size() > 2)
		{
			for (InstS::iterator sit = (*it).second.begin(); sit != (*it).second.end();)
			{
				Inst* first = (*sit);
				sit++;
				for (InstS::iterator sit2 = sit; sit2 != (*it).second.end(); sit2++)
				{
					Inst* second = (*sit2);
					c_ref.push_back(OpInst::create(OpInst::Eq, first, second));
				}
			}
		}
	}

	Inst* numTrue = NumInst::create(1,1, SORT());

	InstL remainingExp;
	Inst::init_visit();
	Inst::init_visit2();
	for(InstL::iterator it = tc_ref.begin(); it != tc_ref.end(); it++)
	{
		Inst *tve = apply_simulation_constants(*it, m_constMap);
		Inst *tve2 = apply_simulation_constants2(*it, m_constMap);
		AVR_LOG(14, 4, "\t\t\t" << *(*it) << " -> " << *tve << " i.e. " << *tve2 << endl);

//		if (tve == numTrue)
//			continue;

		if (tve == *it)
			tve = tve2;
		OpInst* op = OpInst::as(tve);
		if (op && op->get_op() == OpInst::Eq)
		{
			Inst* lhs = tve->get_children()->front();
			Inst* rhs = tve->get_children()->back();
			if (lhs == rhs)
				tve = tve2;
		}

		if (tve != *it)
		{
			OpInst* op = OpInst::as(tve);
			if (op && op->get_op() == OpInst::Eq)
			{
				Inst* lhs = tve->get_children()->front();
				Inst* rhs = tve->get_children()->back();
				if (lhs != rhs)
				{
					if (tve->childrenInfo[CONST])
					{
						res = false;
						remainingExp.push_back(tve);
					}
					else
						c_ref.push_back(tve);
				}

//				else
				{
					if (!(ConstInst::as((*it)->get_children()->front()) || ConstInst::as((*it)->get_children()->back())))
					{
////						res = false;
////						remainingExp.push_back((*it));
//						cout << "\tWarning: skipping condition " << *(*it) << endl;
//						if ((*it)->ve_sim_orig)
//							cout << "i.e. " << *((*it)->ve_sim_orig) << endl;
//
//						Inst::num_warnings++;
//						learn = false;
////						assert(0);

					  Inst::num_warnings++;

//            AVR_LOG(15, 0, "\t\t(trying instantiating symbolic expression)\t" << *(*it) << endl);
//						Inst* newTve = replace_constant_with_value(*it);
//            AVR_LOG(15, 0, "\t\t(instantiated symbolic expression)\t" << *(*it) << " := " << *newTve << endl);
//						assert(!newTve->childrenInfo[CONST]);
//            c_ref.push_back(newTve);
            c_ref.push_back(*it);
					}
					else
            c_ref.push_back(*it);
				}
			}
			else
			{
				if (tve->childrenInfo[CONST])
				{
					res = false;
					remainingExp.push_back(tve);
				}
				else {
					if (tve == numTrue)
						c_ref.push_back(*it);
					else
						c_ref.push_back(tve);
				}
			}
		}
		else
			c_ref.push_back(tve);
	}

//	cout << "Post Printing m_constMap" << endl;
//	for (InstToSetM::iterator it = m_constMap.begin(); it != m_constMap.end(); it++)
//	{
//		cout << "[" << *(*it).first << "] = " << (*it).second << endl;
//	}

	if (!res)
	{
		for (auto& v: remainingExp)
			c_ref.push_back(v);

//		InstToSetM m_constMapTmp;
//		if (remainingExp.size() < tc_ref.size())
//			generalize_simulation_predicates(remainingExp, m_constMapTmp, learn);
//		for(InstL::iterator it = remainingExp.begin(); it != remainingExp.end(); it++)
//		{
//		  Inst* tve = *it;
//		  if (tve->childrenInfo[CONST])
//      {
//        Inst* newTve = replace_constant_with_value(tve);
//        cout << "\t\t(instantiating symbolic value)\t" << *tve << " := " << *newTve << endl;
//        assert(!newTve->childrenInfo[CONST]);
//        c_ref.push_back(newTve);
//      }
//		}
	}
	AVR_LOG(14, 8, "generalize_predicates, after:" << c_ref << endl);
	return res;
}
/// END

/// Aman
void Reach::fetch_failure_condition(Inst* next, InstL exit, bool resExitAb, InstL conjunct_T, InstLL& failConditions)
{
	InstLL muses;

#ifdef SUBSTITUTE
	collect_cubes(next, true);
	for (InstL::iterator nit = _collected_cubes.begin(); nit != _collected_cubes.end(); nit++)
	{
		SigInst* sig = SigInst::as(*nit);
		if (sig)
		{
			assert(sig->get_size() == 1);
		}
		else
		{
			OpInst* op = OpInst::as(*nit);
			assert(op);

			if (op->get_op() == OpInst::LogNot)
				sig = SigInst::as((*nit)->get_children()->front());
			else
			{
				assert(op->get_op() == OpInst::Eq);
				sig = SigInst::as((*nit)->get_children()->front());
				assert(sig);

//				if (!sig)
//				{
//					sig = SigInst::as((*nit)->get_children()->back());
//				}
//				else if (Inst::_m_sn.find(sig) == Inst::_m_sn.end())
//				{
//					sig = SigInst::as((*nit)->get_children()->back());
//				}
			}
		}

		assert(sig);
		InstToInstM::iterator mit = Inst::_m_sn.find(sig);
		if (mit != Inst::_m_sn.end())
		{
			Inst* tmp = OpInst::create(OpInst::Eq, (*mit).first, (*mit).second);
			conjunct_T.push_back(tmp);
			cout << "Replacing " << (*(*nit)) << endl;
			cout << "with " << *conjunct_T.back() << endl;
		}
		else
			assert(0);
	}
#else
	collect_cubes(next, true);
	for (InstL::iterator nit = _collected_cubes.begin(); nit != _collected_cubes.end(); nit++)
	{
		Inst* tve = (*nit);

		OpInst* op = OpInst::as(tve);
		if (op && op->get_op() == OpInst::Eq) {
			Inst* lhs = tve->get_children()->front();
			SigInst* sigNext = SigInst::as(lhs);
			if (sigNext && sigNext->find_next()) {
				if (Inst::has_trelation(sigNext)) {
					Inst* rel = Inst::fetch_trelation(sigNext);
					if (tve == rel) {
						conjunct_T.push_back(tve);
						continue;
					}
				}
			}
		}
//		cout << "adding to exit: " << *tve << endl;
//		assert(0);
		exit.push_back(tve);
	}
#endif

//	cout << "Fail: " << exit << endl;
//	cout << "T(mus): " << conjunct_T << endl;

#ifdef Z3_INTERPOLATION
	{
		z3_API* itp_solver = dynamic_cast<z3_API*> (new_conc_solver(true, AVR_BV_IDX));
		InstL interpolant;
		itp_solver->get_interpolant(BV_QUERY_TIMEOUT, exit, conjunct_T, interpolant, num_scalls_sat_mus_sim, num_scalls_unsat_mus_sim);
	}
#endif

	Solver* mus_solver;
	int resMus = false;
	if (!resExitAb)
	{
		SOLVER_MUS int_solver2(_abstract_mapper, AVR_EXTRA_IDX, true, regular);
		mus_solver = &int_solver2;

		Inst* ve_T = OpInst::create(OpInst::LogAnd, conjunct_T);
		mus_solver->s_assert(ve_T);
		mus_solver->s_assert_retractable(exit);
		int res = mus_solver->s_check_assume(AB_QUERY_TIMEOUT, false);

		if (res == AVR_QSAT)
		{
			assert(0);

			retrieve_cex_val(ve_T, mus_solver, true, true);
			for(auto& v: exit)
				retrieve_cex_val(v, mus_solver, true, false);

			InstL viol;
			InstL conjunct_nextEval;
			InstToInstM nextMap;
			InstL conjunct_tmp;

			InstS relevantNext;
			Inst::collect_next_reg(ve_T, relevantNext, true);
			InstL conjunct_next;
			for (auto& s: relevantNext)
			{
				conjunct_next.push_back(Inst::fetch_trelation(s));
			}
			collect_cubes(next, true);
			for (auto& c: _collected_cubes)
				conjunct_next.push_back(c);

			Inst* nextT = OpInst::create(OpInst::LogAnd, conjunct_next);
			nextT->set_bval(1);
			InstS relevantSigs;
			InstS relevantConst;
			set < string > relevantUFtype;
			/// Aman TODO: Remove unnecessary collection of relevantSigs here
			ABSTRACT_REACH_VIOL tmpViol;
			EVAL tb(tmpViol, nextMap, relevantSigs, relevantSigs, relevantSigs, relevantSigs, relevantConst, relevantUFtype, mus_solver);

			Inst::init_visit();
			evaluate_abstract_relation(2, nextT, tb);
			viol.swap(tmpViol.mainConstraints);
			conjunct_nextEval.swap(tmpViol.nextStateConstraints);

			cout << "Viol: " << viol << endl;
			cout << "NextEval: " << endl;
			for (auto& m: nextMap)
				cout << *(m.first) << " == " << *(m.second) << endl;

			mus_solver->s_retract_assertions();
			InstL conjunct_mus;
			conjunct_mus = exit;
			for (auto& c: _collected_cubes)
				conjunct_mus.push_back(c);

			Solver* core_solver = mus_solver;
#ifdef USE_Z3_CORE
			z3_API solverCore(_abstract_mapper, AVR_EXTRA_IDX, true, regular);
			core_solver = &solverCore;
			core_solver->s_assert(ve_T);
#endif

			resMus = mus_solver->get_muses_2(AB_QUERY_TIMEOUT, conjunct_mus, muses, num_scalls_sat_mus_sim, num_scalls_unsat_mus_sim, core_solver);
			assert(resMus);
			int count = 0;
			for (InstLL::iterator it_muses2 = muses.begin(); it_muses2 != muses.end(); ++it_muses2)
			{
				cout << "[" << ++count << "]: " << (*it_muses2) << endl;
			}
			assert(0);
		}
		else
		{
			assert(res == 0);
			mus_solver->s_retract_assertions();

			Solver* core_solver = mus_solver;
#ifdef USE_Z3_CORE
			z3_API solverCore(_abstract_mapper, AVR_EXTRA_IDX, true, regular);
			core_solver = &solverCore;
			core_solver->s_assert(ve_T);
#endif

			resMus = mus_solver->get_muses_2(AB_QUERY_TIMEOUT, exit, muses, num_scalls_sat_mus_sim, num_scalls_unsat_mus_sim, core_solver);
			/// resMus can become false in rare case because of simplification
			if (resMus)
			{
				for (InstLL::iterator it_muses2 = muses.begin(); it_muses2 != muses.end(); ++it_muses2)
				{
		//			Inst* failC = OpInst::create(OpInst::LogAnd, (*it_muses2));
		////			cout << "Mus: " << *it_muses2 << endl;
		//
		//			InstS relevantStates;
		//			collect_next_reg(failC, relevantStates, true);
		//			for (InstS::iterator sit = relevantStates.begin(); sit != relevantStates.end(); sit++)
		//			{
		//				Inst* sigNext = (*sit);
		//				InstToInstM::iterator ait = m_sig_next.find(sigNext);
		//				if (ait != m_sig_next.end())
		//					(*it_muses2).push_back((*ait).second);
		//				else
		//					assert(sigNext == _ve_prop_next_eq_1);
		//			}

					InstS relevantNext;
					Inst::init_visit();
					for (auto& m: (*it_muses2))
					{
						Inst::collect_next_reg(m, relevantNext, false);
					}
					for (auto& sig: relevantNext)
					{
						(*it_muses2).push_back(Inst::fetch_trelation(sig));
					}
					failConditions.push_back(*it_muses2);
				}
			}
			else
				assert(0);
		}
	}
	if (!resMus)
	{
		mus_solver = dynamic_cast<SOLVER_BV*> (new_conc_solver(true, AVR_BV_IDX));
//		mus_solver->assert_all_wire_constraints();
		mus_solver->s_assert(conjunct_T);
		Solver* core_solver = mus_solver;

//    BR_QUERY q;
//    q.dest.insert(exit.begin(), exit.end());
//    q.frameIdx = -1;
//    generalize_unsat_query(q, muses, core_solver, mus_solver);

#ifdef USE_Z3_CORE_BV
    z3_API solverCore(_concrete_mapper, AVR_BV_IDX, true, conc);
    core_solver = &solverCore;
    core_solver->s_assert(conjunct_T);
#endif

		int resMusBv = mus_solver->get_muses_2(BV_QUERY_TIMEOUT, exit, muses, num_scalls_sat_mus_sim, num_scalls_unsat_mus_sim, core_solver);
		cout << "resMusBv: " << resMusBv << endl;
		if (resMusBv == 0) {
			cout << "resExitAb: " << resExitAb << endl;
			for (auto& mus: muses) {
			  cout << "MUS b4: " << mus << endl;
			}
			muses.clear();

			SOLVER_BV* tmpSolver = dynamic_cast<SOLVER_BV*> (new_conc_solver(true, AVR_BV_IDX));
			tmpSolver->s_assert(conjunct_T);
			int res = tmpSolver->get_muses_2(BV_QUERY_TIMEOUT, exit, muses, num_scalls_sat_mus_sim, num_scalls_unsat_mus_sim, tmpSolver);
			cout << "res: " << res << endl;
			for (auto& mus: muses) {
			  cout << "MUS: " << mus << endl;
			}
			cout << "Exit: " << exit << endl;
			cout << "T: " << conjunct_T << endl;
			assert(0);
		}


		for (InstLL::iterator it_muses2 = muses.begin(); it_muses2 != muses.end(); ++it_muses2)
		{
//			Inst* failC = OpInst::create(OpInst::LogAnd, (*it_muses2));
////			cout << "Mus: " << *it_muses2 << endl;
//
//			InstS relevantStates;
//			collect_next_reg(failC, relevantStates, true);
//
//			for (InstS::iterator sit = relevantStates.begin(); sit != relevantStates.end(); sit++)
//			{
//				Inst* sigNext = (*sit);
//				InstToInstM::iterator ait = m_sig_next.find(sigNext);
//				if (ait != m_sig_next.end())
//					(*it_muses2).push_back((*ait).second);
//				else
//				{
////										cout << "relevantStates: " << relevantStates << endl;
//					assert(sigNext == _ve_prop_next_eq_1);
//				}
//			}

			InstS relevantNext;
			Inst::init_visit();
			for (auto& m: (*it_muses2))
			{
				Inst::collect_next_reg(m, relevantNext, false);
			}
			for (auto& sig: relevantNext)
			{
				(*it_muses2).push_back(Inst::fetch_trelation(sig));
			}
			failConditions.push_back(*it_muses2);
		}
	}

#ifdef M5_INTERPOLATION
	if (Config::g_interpolation >= INTERPOLATION_END)
	{
		InstL new_preds;
		{
			InstL exit2;
			InstL conjunct_T2 = conjunct_T;
			for (auto& v: exit) {
				if (v->find_next())
					conjunct_T2.push_back(v);
				else
					exit2.push_back(v);
			}
			m5_API itp_solver(_concrete_mapper, AVR_BV_IDX, false, regular);
			itp_solver.get_interpolant(BV_QUERY_TIMEOUT, exit2, conjunct_T2, new_preds, num_scalls_sat_mus_sim, num_scalls_unsat_mus_sim);
		}
//		{
//			m5_API itp_solver(_concrete_mapper, AVR_BV_IDX, false, regular);
//			itp_solver.get_interpolant(BV_QUERY_TIMEOUT, exit, conjunct_T, new_preds, num_scalls_sat_mus_sim, num_scalls_unsat_mus_sim);
//			//		itp_solver.get_interpolant(BV_QUERY_TIMEOUT, failConditions.front(), conjunct_T, new_preds, num_scalls_sat_mus_sim, num_scalls_unsat_mus_sim);
//		}
		for (auto& v: new_preds) {
//			cout << "adding to fail conds: " << *v << endl;
			Inst* tve = v;
			if (tve->find_next() && !find_pre(tve))
				tve = Inst::all_next2pre(tve);
			failConditions.front().push_back(tve);
		}
	}
#endif
}

//struct inpInfo
//{
//	Inst* inp;
//	mpz_class val;
//	int idx;
//};
//typedef map<Inst*, inpInfo, compare> InstToInpinfoM;

bool Reach::simulation_check(deque< ABSTRACT_CUBE >& rcext, ABSTRACT_CUBE& _badCube)
{
//	cout << "(concrete simulation broken, exiting..)" << endl;
//	assert(0);

//	constMap.clear();
	/// TODO: remove return
//	return 1;
	/// Aman TODO: Figure out need to do simulation check without asserting input conditions when looping
	/// Aman TODO: Figure out avoiding asserting complete transition relation by using _next_state
	/// Aman TODO: Figure out how to derive DPR refinements to eliminate reoccurence of infeasible ACEXT
	/// Aman TODO: Remove relevantStates etc. if not needed
	/// Aman TODO: Search for better ways of asserting transition relation (if needed) and extracting MUS

	struct rusage usage;
	struct timeval start_time, end_time;
	long long time_diff;
	TIME_S(start_time);

	num_sim_iterations++;
	AVR_LOG(15, 0, "\n\t[Simulation check]: " << endl);
	AVR_LOG(14, 1, "=========== Simulation Begins ===============" << endl);
	AVR_LOG(4, 4, "Simulation for ACEXT:" << endl);

	_cext_idx.clear();
	int numIter = 0;

#ifdef SIMULATION_CHECK_SELF_LOOPS
//	Reach::sim_self_loop_allowance += 20;
	AVR_LOG(14, 1, "(self loop allowance: " << Reach::sim_self_loop_allowance << ")" << endl);
	bool repetitionInLearning = false;
	#ifdef LIMIT_SIMULATION_ITERATIONS
		int maxIter = rcext.size() + Reach::sim_self_loop_allowance;
	#endif
#endif

#ifdef SIM_SIMPLIFY_EX_CC
		Inst::wn_simplify_extract = true;
		Inst::wn_simplify_concat = true;
#endif

//	for(deque< ABSTRACT_CUBE >::iterator it = rcext.begin(); it != rcext.end(); it++)
//	{
//		AVR_LOG(4, 4, "F[" << (*it).frame << "] - " << *((*it).cube) << " Next: " << *((*it).next) << endl);
//	}
//	AVR_LOG(4, 4, endl);

	int unsatIdx = rcext.size() - 1;

	SIMULATION_POSITION curr;
	SIMULATION_POSITION& sCurr = curr;

	sCurr.sIdx = unsatIdx;
	sCurr.src = -1;
	sCurr.dest = ((unsatIdx - 1) >= 0 ? (unsatIdx - 1) : -1);

	InstLL failConditions;
	list< SIMULATION_POSITION > retractPoints;
	InstL learnedLemmas;
	int lemmaCount = 0;

	AVR_LOG(14, 4, "(asserting I in the beginning)" << endl);
	assert(sCurr.sIdx == unsatIdx);
	/// Find starting conditions

	/// Setting sCurr.val map equal to initial dont care map,
	/// and adding map conditions to sCurr.conditions
	sCurr.val = _init_dont_care;
	for (InstToInstM::iterator mit = sCurr.val.begin(); mit != sCurr.val.end(); mit++)
	{
		sCurr.sigs.insert((*mit).first);
	}

	/// Adding initial conditions to sCurr.val map and sCurr.conditions
	if (!_conjunct_init.empty())
		collect_sig(_ve_init, sCurr.sigs, true);
	for (InstL::iterator fit = _conjunct_init.begin(); fit != _conjunct_init.end(); fit++)
	{
		Inst* tve = (*fit);
		assert(tve);

		bool done = false;
		OpInst* op = OpInst::as(tve);
		if (op)
		{
			if (op->get_op() == OpInst::Eq)
			{
				Inst* lhs = op->get_children()->front();
				Inst* rhs = op->get_children()->back();
				assert(lhs && rhs);

				SigInst* sig = SigInst::as(lhs);
				if (sig && !rhs->childrenInfo[SIG]) {
					if (Inst::_s_reg.find(sig) != Inst::_s_reg.end()) {
						NumInst* num = NumInst::as(rhs);
						if (num) {
							sCurr.val[sig] = num;
							sCurr.s[sig] = num->get_mpz();
						}
						else {
							sCurr.val[sig] = rhs;
		//					sCurr.s[sig] = num->get_mpz();
						}
						done = true;
					}
				}
			}
			else if (op->get_op() == OpInst::LogNot)
			{
				Inst* tveTmp = op->get_children()->front();
				assert(tveTmp);
				SigInst* sig = SigInst::as(tveTmp);
				if (sig) {
					if (Inst::_s_reg.find(sig) != Inst::_s_reg.end()) {
						NumInst* num = NumInst::as(NumInst::create(0, 1, SORT()));
						sCurr.val[sig] = num;
						sCurr.s[sig] = num->get_mpz();
						done = true;
					}
				}
			}
		}
		else
		{
			SigInst* sig = SigInst::as(tve);
			if (sig) {
				if (Inst::_s_reg.find(sig) != Inst::_s_reg.end()) {
					Inst* num = NumInst::create(1, 1, SORT());
					sCurr.val[sig] = num;
					sCurr.s[sig] = NumInst::as(num)->get_mpz();
					done = true;
				}
			}
		}

		if (!done) {
			sCurr.postConditions.push_back(tve);

		}
	}

	while(1)
	{
		numIter++;
		Inst* cube = rcext[sCurr.sIdx].cube;
//		int frame = rcext[sCurr.sIdx].frame;
		Inst* next = rcext[sCurr.sIdx].next;
		InstL relevantWires = *(rcext[sCurr.sIdx].relevantWires);

		for (auto& w: *(rcext[sCurr.sIdx].relevantWiresNext))
			relevantWires.push_back(w);

		Inst::init_visit();
		for (auto& v: sCurr.postConditions) {
			add_all_wires(v, relevantWires, false);
		}

		AVR_LOG(14, 5, "Cube: " << *cube << endl);
		AVR_LOG(14, 5, "next: " << *next << endl);

		InstL conjunct_q;
		InstL conjunct_T, conjunct_Tr_w_ref;

		/// cubeConstConditions include cube constraints not involving any state register
		InstL cubeConstConditions;

		/// Adding entries in sCurr.pConditions and sCurr.val from cube
		InstL cubeConditions;
		collect_cubes(cube, true);
		for (auto& v: sCurr.postConditions)
			_collected_cubes.push_back(v);
		for (InstL::iterator cit = _collected_cubes.begin(); cit != _collected_cubes.end(); cit++)
		{
			Inst* tve = (*cit);
			assert(tve);

//			cout << *tve << " -> ";
			if (!find_reg(tve))
			{
				cubeConstConditions.push_back(tve);
//				cout << "cubeConst" << endl;
			}
			else
			{
				OpInst* op = OpInst::as(tve);
				if (op)
				{
					if (op->get_op() == OpInst::Eq)
					{
						Inst* lhs = op->get_children()->front();
						Inst* rhs = op->get_children()->back();
						assert(lhs && rhs);

						if (NumInst::as(lhs) && SigInst::as(rhs))
						{
							Inst* tmp = lhs;
							lhs = rhs;
							rhs = tmp;
						}

						if (SigInst::as(lhs) && NumInst::as(rhs))
						{
							if (Inst::_s_reg.find(lhs) != Inst::_s_reg.end())
							{
								InstToInstM::iterator vit = sCurr.val.find(lhs);
								if (vit != sCurr.val.end())
								{
									if ((*vit).second != rhs)
										sCurr.cConditions.insert(OpInst::create(OpInst::Eq, (*vit).second, rhs));
								}
								sCurr.val[lhs] = rhs;
								sCurr.s[lhs] = NumInst::as(rhs)->get_mpz();
								sCurr.sigs.insert(lhs);
//								cout << "sCurr.val" << endl;
							}
							else
							{
								cubeConditions.push_back(tve);
//								cout << "cubeCond" << endl;
							}
						}
						else
						{
							cubeConditions.push_back(tve);
//							cout << "cubeCond" << endl;
						}
					}
					else
					{
						if (op->get_op() == OpInst::LogNot)
						{
							Inst* tveTmp = op->get_children()->front();
							assert(tveTmp);
							SigInst* sig = SigInst::as(tveTmp);
							if (sig && Inst::_s_reg.find(sig) != Inst::_s_reg.end())
							{
								Inst* rhs = NumInst::create(0, 1, SORT());
								InstToInstM::iterator vit = sCurr.val.find(sig);
								if (vit != sCurr.val.end())
								{
									sCurr.cConditions.insert(OpInst::create(OpInst::Eq, (*vit).second, rhs));
								}
								sCurr.val[sig] = rhs;
								sCurr.s[sig] = NumInst::as(rhs)->get_mpz();
								sCurr.sigs.insert(tveTmp);
//								sCurr.pConditions.push_back(tve);
//								cout << "sCurr.val" << endl;
							}
							else
							{
								cubeConditions.push_back(tve);
//								cout << "cubeCond" << endl;
							}
						}
						else
						{
							cubeConditions.push_back(tve);
//							cout << "cubeCond" << endl;
						}
					}
				}
				else
				{
					SigInst* sig = SigInst::as(tve);
					if (sig && Inst::_s_reg.find(sig) != Inst::_s_reg.end())
					{
						Inst* rhs = NumInst::create(1, 1, SORT());
						InstToInstM::iterator vit = sCurr.val.find(sig);
						if (vit != sCurr.val.end())
						{
							sCurr.cConditions.insert(OpInst::create(OpInst::Eq, (*vit).second, rhs));
						}
						sCurr.val[sig] = rhs;
						sCurr.s[sig] = NumInst::as(rhs)->get_mpz();
						sCurr.sigs.insert(tve);
//						sCurr.pConditions.push_back(tve);
//						cout << "sCurr.val" << endl;
					}
					else
					{
						cubeConditions.push_back(tve);
//						cout << "cubeCond" << endl;
					}
				}
			}
		}

		AVR_LOG(14, 5, "cubeConditions: " << cubeConditions << endl);
		AVR_LOG(14, 5, "cubeConstConditions: " << cubeConstConditions << endl);
		AVR_LOG(14, 5, "cConditions: " << sCurr.cConditions << endl);

		/// Collecting all sigs (i.e registers and inputs) in sCurr.pConditions
		if (!cubeConditions.empty())
			collect_sig(OpInst::create(OpInst::LogAnd, cubeConditions), sCurr.sigs, true);
		if (!cubeConstConditions.empty())
			collect_sig(OpInst::create(OpInst::LogAnd, cubeConstConditions), sCurr.sigs, true);

		AVR_LOG(14, 6, "Relevant Signals: " << sCurr.sigs << endl);

		for (auto& v: Inst::_s_reg)
			sCurr.sigs.insert(v);

		/// Collecting all next state registers affected by sCurr.sigs
		InstS cubeCOI;
		for (InstS::iterator sit = sCurr.sigs.begin(); sit != sCurr.sigs.end(); sit++)
		{
			InstToSetM::iterator fcoi = Inst::_m_forward_coi.find(*sit);
			if (fcoi != Inst::_m_forward_coi.end())
			{
				for (InstS::iterator sit2 = (*fcoi).second.begin(); sit2 != (*fcoi).second.end(); sit2++)
				{
					cubeCOI.insert(*sit2);
				}
			}

			if (sCurr.val.find(*sit) == sCurr.val.end())
			{
        AVR_LOG(14, 8, *(*sit) << " not found in .val" << "\t");
				if (Inst::_s_reg.find(*sit) != Inst::_s_reg.end())
				{
          AVR_LOG(14, 8, "but is reg" << "\t");
					Inst* lhs = (*sit);
					assert(SigInst::as(lhs));
					ostringstream cName;
					int sz = lhs->get_size();
					cName << lhs->get_sort().sort2str() << "_" << sz << "'d*_" << ConstInst::hm_ConstInst.size();
					Inst* c = ConstInst::create(cName.str(), sz, lhs, -1, lhs->get_sort());
					sCurr.val[lhs] = c;
					if (sCurr.s.find(lhs) == sCurr.s.end())
					{
						AVR_LOG(14, 1, "Warning: Unable to find value corresponding to " << *lhs << endl);
						Inst::num_warnings++;
//								assert(0);
					}
					AVR_LOG(14, 5, "Adding COI_b " << *lhs << " == " << *c << endl);
				}
			}
		}
		AVR_LOG(14, 6, "Cube COI_f: " << cubeCOI << endl);

		for (auto& v: Inst::_m_sn)
			cubeCOI.insert(v.first);

		/// Adding cube to conjunct_q
//		conjunct_q.push_back(cube);
		for (InstL::iterator lit = cubeConditions.begin(); lit != cubeConditions.end(); lit++)
		{
			conjunct_q.push_back(*lit);
		}
		for (InstL::iterator lit = cubeConstConditions.begin(); lit != cubeConstConditions.end(); lit++)
		{
			conjunct_q.push_back(*lit);
		}

		/// Finding all next state registers in next,
		/// and adding corresponding assignment conditions to conjunct_q and conjunct_T
		collect_cubes(next, true);
//		InstS nextRegs;
		for (InstL::iterator cit = _collected_cubes.begin(); cit != _collected_cubes.end(); cit++)
		{
//			conjunct_q.push_back(*cit);
			conjunct_T.push_back(*cit);
//			Inst::collect_next_reg(*cit, nextRegs, true);
		}

//		InstS allSigs;
//		collect_sig(next, nextRegs, true);
//		for (auto& v: allSigs) {
//			if (v->find_next() && Inst::_m_sn.find(v) != Inst::_m_sn.end())
//				nextRegs.insert(v);
//		}
//		AVR_LOG(14, 6, "Next regs: " << nextRegs << endl);


		/// Finding all next state registers not in next, but is in COI
		/// and adding corresponding transition relation to conjunct_q and conjunct_T
		for (InstS::iterator sit = cubeCOI.begin(); sit != cubeCOI.end(); sit++)
		{
			Inst* eq = Inst::fetch_trelation(*sit);
//			if (nextRegs.find(*sit) == nextRegs.end())
//			if (find(_collected_cubes.begin(), _collected_cubes.end(), eq) == _collected_cubes.end())
			{
//				conjunct_q.push_back(eq);
				conjunct_T.push_back(eq);
				conjunct_Tr_w_ref.push_back(eq);
				add_all_wires(eq, relevantWires, true);

				/// Aman TODO - Check for necessity of below code
				/// and make appropriate changes (in simeval and sim check) if not needed
				InstToSetM::iterator bcoi = Inst::_m_backward_coi.find(*sit);
				assert(bcoi != Inst::_m_backward_coi.end());
        AVR_LOG(14, 8, "COI_b of " << *(*sit) << endl);
				for (InstS::iterator sit2 = (*bcoi).second.begin(); sit2 != (*bcoi).second.end(); sit2++)
				{
	        AVR_LOG(14, 8, "\t" << *(*sit2) << "\t");
					if (sCurr.val.find(*sit2) == sCurr.val.end())
					{
	          AVR_LOG(14, 8, "not found in .val" << "\t");
						if (Inst::_s_reg.find(*sit2) != Inst::_s_reg.end())
						{
	            AVR_LOG(14, 8, "but is reg" << "\t");
							Inst* lhs = (*sit2);
							assert(SigInst::as(lhs));
							ostringstream cName;
							int sz = lhs->get_size();
							cName << sz << "'d*_" << ConstInst::hm_ConstInst.size();
							Inst* c = ConstInst::create(cName.str(), sz, lhs, -1, lhs->get_sort());
							sCurr.val[lhs] = c;
							if (sCurr.s.find(lhs) == sCurr.s.end())
							{
								AVR_LOG(14, 1, "Warning: Unable to find value corresponding to " << *lhs << endl);
								Inst::num_warnings++;
//								assert(0);
							}
							AVR_LOG(14, 5, "Adding COI_b " << *lhs << " == " << *c << endl);
						}
						else
						{
              AVR_LOG(14, 8, "not a reg" << "\t");
						}
					}
					else
					{
            AVR_LOG(14, 8, "found in .val" << "\t");
            AVR_LOG(14, 8, *sCurr.val[*sit2] << "\t");
					}
          AVR_LOG(14, 8, endl);
				}
			}
		}
		/// Q: next & T(remaining coi)
		AVR_LOG(14, 7, "T: " << conjunct_T << endl);

//		if (conjunct_T.size() == 1)
//			_simeval_depth = 1;
//		else
//			_simeval_depth = 0;

		Inst* ve_T = OpInst::create(OpInst::LogAnd, conjunct_T);

		for (InstS::iterator sit = sCurr.cConditions.begin(); sit != sCurr.cConditions.end(); sit++)
		{
			conjunct_q.push_back(*sit);
		}

		Inst::init_visit();

		for (auto& v: _all_assumptions) {
			conjunct_q.push_back(v.first);
//			add_all_wires(v.first, relevantWires);
		}
		relevantWires.insert(relevantWires.end(), _assume_wires.begin(), _assume_wires.end());
		for (auto& v: _assume_T) {
			conjunct_q.push_back(v.first);
//			add_all_wires(v.first, relevantWires);
		}
		relevantWires.insert(relevantWires.end(), _assume_Twires.begin(), _assume_Twires.end());

		/// Adding refinements to conjunct_q
		for (InstL::iterator it3 = _negated_refs.begin(); it3 != _negated_refs.end(); ++it3)
		{
//			conjunct_q.push_back(*it3);
			conjunct_Tr_w_ref.push_back(*it3);
			add_all_wires(*it3, relevantWires);
		}
		for (InstL::iterator it3 = learnedLemmas.begin(); it3 != learnedLemmas.end(); ++it3)
		{
//			conjunct_q.push_back(*it3);
			conjunct_Tr_w_ref.push_back(*it3);
		}

		/// Q: cube & next & T(remaining coi)
		AVR_LOG(14, 7, "Q: " << conjunct_q << endl);

		/// Finding cubeNext based on destination
		Inst* cubeNext;
		if (sCurr.dest == -1)
		{
			assert(sCurr.sIdx == 0);
//			InstL conjunct_prop;
//			conjunct_prop.push_back(_ve_model_next);
//			conjunct_prop.push_back(_ve_prop_next_eq_0);
//			cubeNext = OpInst::create(OpInst::LogAnd, conjunct_prop);
			cubeNext = _badCube.cube;
		}
		else
		{
			cubeNext = Inst::all_pre2next(rcext[sCurr.dest].cube);
		}
		AVR_LOG(14, 6, "Cube$next: " << *cubeNext << endl);

		/// conjunct_next: cube & next & T(remaining coi) & cubeNext+
		InstL conjunct_next = conjunct_q;

		collect_cubes(cubeNext, true);
		for (InstL::iterator cit = _collected_cubes.begin(); cit != _collected_cubes.end(); cit++)
		{
			conjunct_next.push_back(*cit);
		}

#ifdef SIMULATION_CHECK_SELF_LOOPS
		bool selfCheck = true;
		/// conjunct_self: cube & next & T(remaining coi) & cubeSelf+
		InstL conjunct_self = conjunct_q;
		Inst* cubeSelf = all_pre2next(cube, true);
		conjunct_self.push_back(cubeSelf);
		AVR_LOG(14, 7, "Cube$self: " << *cubeSelf << endl);

//		for (InstL::iterator wit = relevantWires.begin(); wit != relevantWires.end();)
//		{
//			Inst* tve = (*wit);
//			if (is_next_wire(tve))
//			{
//				wit = relevantWires.erase(wit);
//			}
//			wit++;
//		}
//		Inst::init_visit2();
//		for (auto& w: *(rcext[sCurr.sIdx].relevantWires))
//		{
//			relevantWires.push_back(all_pre2next(w));
//		}

#ifndef LIMIT_SIMULATION_ITERATIONS
		if (cubeSelf == cubeNext)
		{
#else
		if (cubeSelf == cubeNext || numIter > maxIter || frame == 0)
		{
			if (numIter > maxIter)
			{
				AVR_LOG(14, 1, "(maximum self looping limit reached)" << endl);
			}
#endif
			selfCheck = false;
		}
#endif

		InstL conjunct_fail = conjunct_next;
		conjunct_next.push_back(next);
#ifdef SIMULATION_CHECK_SELF_LOOPS
		conjunct_self.push_back(next);
#endif
		for(InstL::iterator cit = conjunct_Tr_w_ref.begin(); cit != conjunct_Tr_w_ref.end(); cit++)
		{
			conjunct_next.push_back(*cit);
#ifdef SIMULATION_CHECK_SELF_LOOPS
			conjunct_self.push_back(*cit);
#endif
		}

		bool res = false;
		while (1)
		{
			AVR_LOG(15, 0, "\t" << numIter << ": A[" << sCurr.sIdx << "]" << endl);
			_cext_idx.push_back(sCurr.sIdx);


#ifdef SIMULATION_CHECK_SELF_LOOPS
			InstL conjunct_loop = conjunct_self;
#endif
			InstL conjunct_exit = conjunct_next;

			AVR_LOG(15, 2, "\tstate:" << endl);

			for (InstToInstM::iterator mit = sCurr.val.begin(); mit != sCurr.val.end(); mit++)
			{
				assert((*mit).first->get_type() == Sig);

				Inst* tmp = OpInst::create(OpInst::Eq, (*mit).first, (*mit).second);
#ifdef SIMULATION_CHECK_SELF_LOOPS
				conjunct_loop.push_back(tmp);
#endif
				conjunct_exit.push_back(tmp);
				conjunct_fail.push_back(tmp);
				AVR_LOG(15, 2, "\t\t" << *(*mit).first << " = " << *(*mit).second << endl);
			}
			AVR_LOG(15, 2, endl);

//			for (InstL::iterator cit = sCurr.pConditions.begin(); cit != sCurr.pConditions.end(); cit++)
//			{
//#ifdef SIMULATION_CHECK_SELF_LOOPS
//				conjunct_loop.push_back(*cit);
//#endif
//				conjunct_exit.push_back(*cit);
//				AVR_LOG(14, 4, "\t" << *(*cit) << endl);
//			}

#ifdef SIMULATION_CHECK_SELF_LOOPS
			bool loopStuck = true;
			bool resLoop = false;
			SIMULATION_POSITION loopNext;

			if (selfCheck == false)
			{
				loopStuck = false;
				resLoop = false;
			}
			else
			{
				AVR_LOG(14, 8, "CubeLoop Q: " << conjunct_loop << endl);
				Inst* ve_loop = OpInst::create(OpInst::LogAnd, conjunct_loop);

				bool resLoopAb = false;

				z3_API* loop_solver = new z3_API(&_abstract_mapper, AVR_EXTRA_IDX, false, false);
				resLoopAb = loop_solver->check_sat(ve_loop);

				if (resLoopAb)
				{
#ifndef SUBSTITUTE
					WireInst::inc_connect_key();

					for (auto& w: relevantWires)
					{
						WireInst* w_lhs = WireInst::as(w);
						assert(w_lhs);
						w_lhs->set_connect();
//						cout << "relevant: " << *w_lhs << endl;
					}
#endif
					delete loop_solver;
					loop_solver = dynamic_cast<z3_API*> (new_conc_solver(false, 1));
					resLoop = loop_solver->check_sat(ve_loop);
				}
				else
				{
					resLoop = false;
					delete loop_solver;
				}

				AVR_LOG(14, 2, "[" << sCurr.sIdx << "] Cube to CubeSelf+ is " << (resLoop?"SAT":"UNSAT") << endl);

				if (resLoop)
				{
					/// Collect values of state variables (location variables not included)
					retrieve_cex_val(ve_loop, loop_solver, false, true);
					print_concrete_min_term("To CubeSelf+");

					/// Aman TODO: Modify retrieve_cex_val to directly give values of concerned state variables

					loopNext.sIdx = sCurr.sIdx;
					loopNext.src  = sCurr.sIdx;
					loopNext.dest = sCurr.dest;

					ve_T->set_bval(1);

					evaluate_simulation_relation(1, ve_T, sCurr, loopNext, loopStuck, true);

					for (InstL::iterator cit = cubeConditions.begin(); cit != cubeConditions.end(); cit++)
					{
						evaluate_simulation_relation(2, (*cit), sCurr, loopNext, loopStuck, true);
					}

	//				cout << "CubeConds: " << cubeConstConditions.size() << endl;
	//				cout << "exit.cC: " << exitNext.cConditions.size() << endl;
	//				cout << "curr.cC: " << sCurr.cConditions.size() << endl;

					for (InstL::iterator cit = cubeConstConditions.begin(); cit != cubeConstConditions.end(); cit++)
					{
						if (find_limited_sigs(*cit, loopNext.inp2Const))
						{
							Inst* newCondition = replace_with_constant(*cit, loopNext.inp2Const);
							loopNext.cConditions.insert(newCondition);
						}
					}

					for (InstS::iterator cit = loopNext.cConditions.begin(); cit != loopNext.cConditions.end();)
					{
						if (!find_limited_constants(*cit, loopNext.consts))
						{
							loopNext.cConditions.erase(cit);
						}
						cit++;
					}
					for (InstS::iterator cit = sCurr.cConditions.begin(); cit != sCurr.cConditions.end(); cit++)
					{
						if (find_limited_constants(*cit, loopNext.consts))
						{
							loopNext.cConditions.insert(*cit);
						}
					}

					AVR_LOG(14, 4, "\tReg$next: " << endl);
					for (InstToInstM::iterator mit = loopNext.val.begin(); mit != loopNext.val.end(); mit++)
					{
						AVR_LOG(14, 4, "\t\t" << *((*mit).first) << " = " << *((*mit).second) << endl);
					}
	//				AVR_LOG(14, 5, "\tpCond$next: " << exitNext.pConditions << endl);
	//				AVR_LOG(14, 5, "\tcCond$next: " << exitNext.cConditions << endl);

					AVR_LOG(14, 6, "\tConstants relevant: " << endl);
					for (InstS::iterator sit = loopNext.consts.begin(); sit != loopNext.consts.end(); sit++)
					{
						if ((*sit)->get_size() == 1)
						{
							AVR_LOG(14, 6, "\t\t" << *(*sit) << " ( " << (*sit)->get_bval() << " )" << endl);
						}
						else
						{
							AVR_LOG(14, 6, "\t\t" << *(*sit) << " ( " << (*sit)->get_ival().get_str(2) << " )" << endl);
						}
					}
					AVR_LOG(14, 6, endl);

					AVR_LOG(14, 4, "\tInputs transformed: " << endl);
					for (InstToInstM::iterator mit = loopNext.inp2Const.begin(); mit != loopNext.inp2Const.end(); mit++)
					{
						if ((*mit).second->get_size() == 1)
						{
							AVR_LOG(14, 4, "\t\t" << *((*mit).first) << " -> " << *((*mit).second) << " ( " << (*mit).second->get_bval() << " )" << endl);
						}
						else
						{
							AVR_LOG(14, 4, "\t\t" << *((*mit).first) << " -> " << *((*mit).second) << " ( " << (*mit).second->get_ival().get_str(2) << " )" << endl);
						}
					}
					AVR_LOG(14, 4, endl);
				}
				AVR_LOG(14, 4, endl);
			}
#endif

			AVR_LOG(14, 8, "CubeNext Q: " << conjunct_exit << endl);
			Inst* ve_exit = OpInst::create(OpInst::LogAnd, conjunct_exit);

			bool resExitAb = true;
			bool resExit = false;
			Solver* exit_solver;

//			Solver* exit_solver = new SOLVER_AB(_abstract_mapper, AVR_EXTRA_IDX, false, regular);
//			resExitAb = exit_solver->check_sat(ve_exit, AB_QUERY_TIMEOUT, false);

//			if (resExitAb)
			{
#ifndef SUBSTITUTE
				WireInst::inc_connect_key();
				for (auto& w: relevantWires)
				{
					WireInst* w_lhs = WireInst::as(w);
					assert(w_lhs);
					w_lhs->set_connect();
//					cout << "relevant: " << *w_lhs << endl;
				}
#endif
//				delete static_cast<SOLVER_AB*>(exit_solver);
				exit_solver = (new_conc_solver(false, AVR_BV_IDX, mdl));
//				exit_solver->assert_all_wire_constraints();
				resExit = exit_solver->check_sat(ve_exit, BV_QUERY_TIMEOUT, true);
			}
//			else
//			{
////				AVR_LOG(15, 0, "CubeNext Q: " << conjunct_exit << endl);
//				resExit = false;
//				delete static_cast<SOLVER_AB*>(exit_solver);
//			}

			if (!resExit)
			{
				AVR_LOG(15, 0, "[" << sCurr.sIdx << "] Cube to CubeNext+ is " << (resExit?"SAT":"UNSAT") << endl);
			}

			SIMULATION_POSITION exitNext;
			if (resExit)
			{
				/// Collect values of state variables (location variables not included)
				retrieve_cex_val(ve_exit, exit_solver, false, true);
				print_concrete_min_term("To CubeNext+");

				/// Aman TODO: Modify retrieve_cex_val to directly give values of concerned state variables

				exitNext.sIdx = sCurr.dest;
				exitNext.src  = sCurr.sIdx;
				exitNext.dest = (sCurr.dest - 1);

				ve_T->set_bval(1);
				_ve_assume->set_bval(1);
//				cubeNext->set_bval(1);

				bool dummyStuck = false;
//				Inst::wn_simplify_extract_adv = true;
//				Inst::wn_simplify_extract = true;

//			  Inst::init_visit();
//				COI_generalize_sim(ve_T, sCurr, exitNext);
				evaluate_simulation_relation(1, ve_T, sCurr, exitNext, dummyStuck, true);

				evaluate_simulation_relation(1, _ve_assume, sCurr, exitNext, dummyStuck, false);
//				evaluate_simulation_relation(1, cubeNext, sCurr, exitNext, dummyStuck, false);


				for (InstL::iterator cit = cubeConditions.begin(); cit != cubeConditions.end(); cit++)
				{
//	        Inst::init_visit();
//	        COI_generalize_sim((*cit), sCurr, exitNext);
					evaluate_simulation_relation(2, (*cit), sCurr, exitNext, dummyStuck, true);
				}

//				cout << "CubeConds: " << cubeConstConditions.size() << endl;
//				cout << "exit.cC: " << exitNext.cConditions.size() << endl;
//				cout << "curr.cC: " << sCurr.cConditions.size() << endl;

				for (InstL::iterator cit = cubeConstConditions.begin(); cit != cubeConstConditions.end(); cit++)
				{
					if (find_limited_sigs(*cit, exitNext.inp2Const))
					{
						Inst* newCondition = replace_with_constant(*cit, exitNext.inp2Const, sCurr.sIdx);
						exitNext.cConditions.insert(newCondition);
						collect_constants(newCondition, exitNext.consts, true);
					}
				}

				for (InstS::iterator cit = exitNext.cConditions.begin(); cit != exitNext.cConditions.end();)
				{
					if (!find_limited_constants(*cit, exitNext.consts))
					{
						cit = exitNext.cConditions.erase(cit);
					}
					else
					  cit++;
				}
				for (InstS::iterator cit = sCurr.cConditions.begin(); cit != sCurr.cConditions.end(); cit++)
				{
					if (find_limited_constants(*cit, exitNext.consts))
					{
						exitNext.cConditions.insert(*cit);
					}
				}

//				for (InstToInstM::iterator mit = exitNext.inp2Const.begin(); mit != exitNext.inp2Const.end(); mit++)
//				{
//					Inst* inp = (*mit).first;
//					Inst* lhs = (*mit).second;
//					inpInfo tmp;
//					tmp.idx = sCurr.sIdx;
//					tmp.inp = inp;
//					tmp.val = lhs->cex_mpz;
//					constMap[lhs] = tmp;
//				}
//
//				for (InstS::iterator sit = exitNext.consts.begin(); sit != exitNext.consts.end(); sit++)
//				{
//					constMap[*sit].val = (*sit)->cex_mpz;
//				}

//				Inst::wn_simplify_extract_adv = false;
//				Inst::wn_simplify_extract = false;

//				AVR_LOG(14, 5, "\tpCond$next: " << exitNext.pConditions << endl);
//				AVR_LOG(14, 5, "\tcCond$next: " << exitNext.cConditions << endl);

				if (!exitNext.consts.empty())
				{
					AVR_LOG(15, 2, "\t\tsymbolic constants: " << endl);
					for (InstS::iterator sit = exitNext.consts.begin(); sit != exitNext.consts.end(); sit++)
					{
						if ((*sit)->get_size() == 1)
						{
							AVR_LOG(15, 2, "\t\t\t" << *(*sit) << " ( " << "1'd" << (*sit)->get_bval() << " )" << endl);
						}
						else
						{
							AVR_LOG(15, 2, "\t\t\t" << *(*sit) << " ( " << (*sit)->get_size() << "'d" << (*sit)->get_ival()->get_str(10) << " )" << endl);
						}
					}
					AVR_LOG(15, 2, endl);
				}

				if (!exitNext.inp2Const.empty())
				{
					AVR_LOG(15, 2, "\t\tInputs transformed: " << endl);
					for (InstToInstM::iterator mit = exitNext.inp2Const.begin(); mit != exitNext.inp2Const.end(); mit++)
					{
						if ((*mit).second->get_sort_type() != arraytype) {
							Inst* num;
							if ((*mit).second->get_size() == 1)
								num = NumInst::create((*mit).second->get_bval(), 1, SORT());
							else
								num = NumInst::create(*(*mit).second->get_ival(), (*mit).second->get_size(), (*mit).second->get_sort());
							AVR_LOG(15, 2, "\t\t\t" << *((*mit).first) << " -> " << *((*mit).second) << " ( " << *num << " ) @" << ConstInst::as((*mit).second)->get_parent_index() << endl);
						}
						else {
							AVR_LOG(15, 2, "\t\t\t" << *((*mit).first) << " -> " << *((*mit).second) << " ( " << (*mit).second->get_ival()->get_str(2) << " ) @" << ConstInst::as((*mit).second)->get_parent_index() << endl);
						}
					}
				AVR_LOG(15, 2, endl);
				}

				AVR_LOG(15, 2, "\tnext: " << endl);
				for (InstToInstM::iterator mit = exitNext.val.begin(); mit != exitNext.val.end(); mit++)
				{
					AVR_LOG(15, 2, "\t\t" << *((*mit).first) << " = " << *((*mit).second) << endl);
				}

				if (!exitNext.cConditions.empty())
				{
					AVR_LOG(15, 6, "\t\tConst conditions: " << endl);
					for (auto& v: exitNext.cConditions)
					{
						AVR_LOG(15, 6, "\t\t\t" << *v << endl);
					}
					AVR_LOG(15, 6, endl);
				}

				if (!exitNext.postConditions.empty())
				{
					AVR_LOG(15, 6, "\t\tPost conditions: " << endl);
					for (auto& v: exitNext.postConditions)
					{
						AVR_LOG(15, 6, "\t\t\t" << *v << endl);
					}
					AVR_LOG(15, 6, endl);
				}
			}
			AVR_LOG(15, 0, endl);

#ifdef SIMULATION_CHECK_SELF_LOOPS
			if (resLoop && loopStuck)
				AVR_LOG(15, 0, "\n\t\tFound infinite loop at A[" << sCurr.sIdx << "]" << endl);

			if (resLoop)
			{
				if (resExit)
				{
					/// Aman - TODO: Choose "better" one, and better ordering of retractPoints
					if (loopStuck)
					{
						AVR_LOG(14, 2, "Choosing CubeNext+ over CubeSelf+" << endl);
						sCurr = exitNext;
//						selfLoopCount = -1;
						res = true;
						break;
					}
					else
					{
						AVR_LOG(14, 2, "Choosing CubeNext+ over CubeSelf+" << endl);
						sCurr = exitNext;
						retractPoints.push_front(loopNext);
//						selfLoopCount = -1;
						res = true;
						break;
					}
				}
				else
				{
					if (loopStuck)
					{
						res = false;
						if (retractPoints.empty())
							fetch_failure_condition(next, conjunct_fail, resExitAb, conjunct_Tr_w_ref, failConditions);
						break;
					}
					else
					{
#ifdef LEARN_EVERYTHING_FROM_SELF_LOOPS
						InstLL failC;
						fetch_failure_condition(next, conjunct_fail, resExitAb, conjunct_Tr_w_ref, failC);
						AVR_LOG(15, 1, "\t\t(learning the following)" << endl);

						bool exitFlag = true;
						for (InstLL::iterator fit = failC.begin(); fit != failC.end(); fit++)
						{
							InstL newLemmas;
							bool resC = convert_to_lemmas(*fit, newLemmas, sCurr);
							exitFlag = exitFlag && (!resC);

							for (InstL::iterator lit = newLemmas.begin(); lit != newLemmas.end(); lit++)
							{
								Inst* ref = OpInst::create(OpInst::LogNot, *lit);
//								conjunct_self.push_back(ref);
								learnedLemmas.push_back(ref);
								lemmaCount++;
								AVR_LOG(15, 1, "    \t\t[" << lemmaCount << "] " << *ref << endl);
							}
						}
						if (exitFlag)
						{
							repetitionInLearning = true;
							res = false;
							break;
						}
						else
#endif
						{
							sCurr = loopNext;
							res = true;
							break;
						}
					}
				}
			}
			else
			{
#endif
				if (resExit)
				{
					sCurr = exitNext;
					res = true;
					break;
				}
				else
				{
					res = false;
					if (retractPoints.empty())
//						fetch_failure_condition(next, conjunct_exit, resExitAb, conjunct_Tr_w_ref, failConditions);
						fetch_failure_condition(next, conjunct_fail, resExitAb, conjunct_Tr_w_ref, failConditions);
					break;
				}
#ifdef SIMULATION_CHECK_SELF_LOOPS
			}
#endif
		}

		if(res)
		{
			if (sCurr.sIdx == -1)
			{
				AVR_LOG(15, 0, "\t\tACEXT is feasible" << endl);
				_feas_sat_res = true;
				break;
			}
		}
		else
		{
#ifdef SIMULATION_CHECK_SELF_LOOPS
			if (retractPoints.empty() || repetitionInLearning)
#else
			if (retractPoints.empty())
#endif
			{
				AVR_LOG(15, 0, "\t\tACEXT is infeasible" << endl);
				if (sCurr.dest != -1)
				{
					AVR_LOG(15, 0, "\t\t\t(unsat: A[" << sCurr.sIdx << "] to A[" << sCurr.dest << "] )" << endl);
				}
				else
				{
					AVR_LOG(15, 0, "\t\t\t(unsat: A[" << sCurr.sIdx << "] to A[End]" << endl);
				}

				_feas_sat_res = false;
				break;
			}
			else
			{
				sCurr = retractPoints.front();
				retractPoints.pop_front();
			}
		}
	}

	if (_feas_sat_res == true)
	{
		_new_refs.clear();
		AVR_LOG(14, 1, "=========== Simulation Ends ===============" << endl);
//		simulation_check_old(rcext);
//		assert(0);

#ifdef SIM_SIMPLIFY_EX_CC
		Inst::wn_simplify_extract = false;
		Inst::wn_simplify_concat = false;
#endif
		TIME_E(start_time, end_time, _sim_time);
		return true;
	}
	else
	{
		/// Aman - TODO Learn more lemmas to eliminate this ACEXT to occur again
//		InstL conjunct_tmp;
//		Inst* tve_assign;
//		if (sCurr.sIdx != -1)
//		{
//			conjunct_tmp.push_back(rcext[conflict.src].cube);
//			failCondition.push_back(all_pre2next(rcext[conflict.dest].cube, true));
//
//			tve_assign = OpInst::create(OpInst::LogAnd, conflict.assignments);
//			Inst* tve_next = all_pre2next(tve_assign, true);
//			failCondition.push_back(OpInst::create(OpInst::LogNot, tve_next));
//			AVR_LOG(14, 4, "Adding lemma to ensure following never happens: " << failCondition << endl);
//			_new_refs.push_back(OpInst::create(OpInst::LogAnd, failCondition));
//		}
//		else
//		{
//			failCondition = _negated_cubes[0];
//			failCondition.push_back(rcext[conflict.dest].cube);
//
//			tve_assign = OpInst::create(OpInst::LogAnd, conflict.assignments);
//			failCondition.push_back(OpInst::create(OpInst::LogNot, tve_assign));
//			AVR_LOG(14, 4, "Adding lemma to ensure following never happens: " << failCondition << endl);
//			_new_refs.push_back(OpInst::create(OpInst::LogAnd, failCondition));
//		}

//		Negating failed destination and asserting in reachability frame
//		if (sCurr.dest == -1)
//		{
//			/// TODO
//			assert(0);
//		}
//		else
//		{
//			Inst* fCube = rcext[sCurr.dest].cube;
//			int fFrame = rcext[sCurr.dest].frame;
//			_cubes[fFrame].push_back(fCube);
//			Inst* fCubeNeg = OpInst::create(OpInst::LogNot, fCube);
//			cout << "Asserting " << *fCubeNeg << " in F[" << fFrame << "]" << endl;
//
//			for (int i = 0; i <= fFrame; i++)
//			{
//				if (i != 0)
//					_negated_cubes[i].push_back(fCubeNeg);
//
//				if (_reach_solvers[i])
//				{
//					_reach_solvers[i]->s_assert(fCubeNeg);
//				}
//				if(i >= _frame_idx)
//				{
//					if (_cti_solver)
//					{
//						_cti_solver->s_assert(fCubeNeg);
//					}
//				}
//			}
//		}

		if (!failConditions.empty())
		{
			AVR_LOG(15, 1, "\t\t(learning the following)" << endl);
			for (InstLL::iterator cit = failConditions.begin(); cit != failConditions.end(); cit++)
			{
				InstL newLemmas;
				convert_to_lemmas(*cit, newLemmas, sCurr, rcext);
				for (InstL::iterator lit = newLemmas.begin(); lit != newLemmas.end(); lit++)
				{
					Inst* ref = OpInst::create(OpInst::LogNot, *lit);
					lemmaCount++;
					AVR_LOG(15, 1, "    \t\t[" << lemmaCount << "] " << *ref << endl);
				}
				break;
			}
			_refine_exit_frame = rcext[sCurr.sIdx].frame;
		}

		AVR_LOG(14, 1, "=========== Simulation Ends ===============" << endl);
#ifdef SIM_SIMPLIFY_EX_CC
		Inst::wn_simplify_extract = false;
		Inst::wn_simplify_concat = false;
#endif
		TIME_E(start_time, end_time, _sim_time);
		return false;
	}
}

bool Reach::process_predicate_info(Inst* top) {
  bool status = false;
  const InstL* ch = top->get_children();
  if (ch)
  {
    for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it)
      status |= process_predicate_info(*it);

    OpInst* op = OpInst::as(top);
    if (op)
    {
      string ufType = op->get_euf_func_name();
      if (ufType != "0")
      {
        if (_s_uf_types.find(ufType) == _s_uf_types.end()) {
          AVR_LOG(15, 0, "\t\t\t\t\t\t(learning uf type   " << ufType << " )" << endl);
        	_s_uf_types.insert(ufType);
        }

        if (_s_uf.find(op) == _s_uf.end()) {
          AVR_LOG(15, 0, "\t\t\t\t\t\t(learning uf        " << *op << " )" << endl);
          _s_uf.insert(op);
          status = true;
        }
      }
    }
  }
  else
  {
    NumInst* num = NumInst::as(top);
    if (num)
    {
      if (_s_constants.find(num) == _s_constants.end()) {
        AVR_LOG(15, 0, "\t\t\t\t\t\t(learning constant  " << *num << " )" << endl);
        _s_constants.insert(num);
        status = true;
      }
    }
    else
    {
      SigInst* sig = SigInst::as(top);
      if (sig)
      {
        if (_s_signals.find(sig) == _s_signals.end()) {
          AVR_LOG(15, 0, "\t\t\t\t\t\t(learning signal    " << *sig << " )" << endl);
          _s_signals.insert(sig);
          status = true;
        }
      }
    }
  }
  return status;
}

Inst* Reach::sanitize_predicate(Inst* tve) {
	tve = tve->get_port();
	OpInst* op = OpInst::as(tve);
  if (op)
  {
    OpInst::OpType opType = op->get_op();
    if (opType == OpInst::LogNot || opType == OpInst::NotEq) {
      tve = OpInst::create(OpInst::LogNot, tve);
    }
  }

  op = OpInst::as(tve->get_port());
  if (op) {
    OpInst::OpType opType = op->get_op();
    if (opType == OpInst::LogNot || opType == OpInst::NotEq) {
      tve = OpInst::create(OpInst::LogNot, tve);
    }
  }

  return tve;
}

bool Reach::add_predicate(Inst* pred_orig, InstL& newRef, InstS& cubeSet, InstS& predSetN, InstL& predList, InstToSetM& constMap, InstToInstM& valMap) {
  int error = 0;
  bool instantiate = false;

  Inst* tve = pred_orig;

  Inst* newTve = tve;
  if (tve->childrenInfo[CONST]) {
    AVR_LOG(15, 0, "\t\t\t(trying instantiating symbolic expression)\t" << *tve << endl);
    newTve = replace_constant_with_value(tve);
    AVR_LOG(15, 0, "\t\t\t(symbolic expression instance)" << endl);
    AVR_LOG(15, 0, "\t\t\t\t" << *tve << " := " << *newTve << endl);
    instantiate = true;
  }

  if (newTve->get_type() == Num) {
		assert(NumInst::as(newTve)->get_num() == 1);
    error = 1;
    return true;
  }
  if (newTve->childrenInfo[CONST])
    error = 2;

  if (error != 0) {
    cout << "Error (" << error << ") illegal predicate: " << *newTve << endl;
    cout << "Original predicate: " << *pred_orig << endl;
    cout << "predicateSetN: " << predSetN << endl;
    cout << "predicateList: " << predList << endl;
    cout << "Printing m_constMap" << endl;
    for (InstToSetM::iterator it = constMap.begin(); it != constMap.end(); it++)
    {
      cout << "[" << *(*it).first << "] = " << (*it).second << endl;
    }
    assert(0);
  }

  bool status = true;

  Inst* pred = add_missing_wires(newTve);
  Inst* pred_ref = pred;

  if (_s_conditions_pre.find(sanitize_predicate(pred)) != _s_conditions_pre.end())
  {
    AVR_LOG(15, 1, "\t\t\t(repeated predicate)" << endl);
    if (find(newRef.begin(), newRef.end(), pred_ref) == newRef.end())
      newRef.push_front(pred_ref);
  }
  else {
//    if (!find_input(pred_ref) && cubeSet.find(pred_ref) != cubeSet.end()) {
    if (cubeSet.find(pred_ref) != cubeSet.end()) {
      AVR_LOG(15, 0, "\t\t\t(skipping predicate (present)  " << *pred << " )" << endl);
      newRef.push_front(pred_ref);
    }
    else if (!is_redundant(pred) && !is_redundant(OpInst::create(OpInst::LogNot, pred))){
      newRef.push_front(pred_ref);
      Inst* newPred = sanitize_predicate(pred);
			AVR_LOG(15, 0, "\t\t\t(adding predicate (absent)   " << *newPred << " )" << endl);
      _s_conditions_pre.insert(newPred);
			newRef.push_front(OpInst::create(OpInst::LogOr, newPred, OpInst::create(OpInst::LogNot, newPred)));

      Inst* pred_new = pred;
      bool added = false;
      if (tve->childrenInfo[CONST]) {
        AVR_LOG(15, 0, "\t\t\t(finding parent expressions)\t" << *tve << endl);

        list< pair< Inst*, pair< int, Inst* > > > l;
        while(1) {
        	int idx = -1;
        	Inst* newPred = replace_constant_with_all_parent(tve, idx, l, valMap, true);
        	if (idx == -1)
        		break;
        	else if (newPred->childrenInfo[CONST])
        		continue;
        	else {
            AVR_LOG(15, 0, "\t\t\t\t(parent expression) @" << idx << endl);
            AVR_LOG(15, 0, "\t\t\t\t\t" << *tve << " := " << *newPred << endl);
        		if (newPred->childrenInfo[CONST]) {
        			cout << "(error: new predicate has symbolic constant for " << *newPred << ")" << endl;
        		}
        		assert(!newPred->childrenInfo[CONST]);
        		if (!is_redundant(newPred)) {
        			newPred = add_missing_wires(newPred);
        			newPred = sanitize_predicate(newPred);
        			if (_s_conditions_pre.find(newPred) == _s_conditions_pre.end()) {
								AVR_LOG(15, 0, "\t\t\t\t(adding predicate (from parent)   " << *newPred << " )" << endl);
								_s_conditions_pre.insert(newPred);
								newRef.push_front(OpInst::create(OpInst::LogOr, newPred, OpInst::create(OpInst::LogNot, newPred)));
        			}
        		}
            added |= process_predicate_info(newPred);
        	}
        }
        for (auto& v: l)
        	v.first->add_parent(v.second.second, v.second.first);

        pred_new = replace_constant_with_parent(tve, valMap, true);
        AVR_LOG(15, 0, "\t\t\t\t(parent expression: main)" << endl);
        AVR_LOG(15, 0, "\t\t\t\t\t" << *tve << " := " << *pred_new << endl);
    		if (!is_redundant(pred_new)) {
					Inst* pred_ref_new = pred_new;
					newRef.push_front(pred_ref_new);
					pred_new = sanitize_predicate(pred_new);
    			if (_s_conditions_pre.find(pred_new) == _s_conditions_pre.end()) {
						AVR_LOG(15, 0, "\t\t\t\t(adding predicate (from parent main)   " << *pred_new << " )" << endl);
						_s_conditions_pre.insert(pred_new);
						newRef.push_front(OpInst::create(OpInst::LogOr, pred_new, OpInst::create(OpInst::LogNot, pred_new)));
    			}
    		}
      }
      else if (tve->childrenInfo[NUM]) {
        AVR_LOG(15, 0, "\t\t\t(finding parent expressions)\t" << *tve << endl);

      	Inst* newPred = replace_constant_with_parent(tve, valMap, true);
        AVR_LOG(15, 0, "\t\t\t\t(parent expression)" << endl);
        AVR_LOG(15, 0, "\t\t\t\t\t" << *tve << " := " << *newPred << endl);
    		if (newPred != tve && !is_redundant(newPred)) {
    			newPred = add_missing_wires(newPred);
    			Inst* pred_ref_new = newPred;
					newRef.push_front(pred_ref_new);
    			newPred = sanitize_predicate(newPred);
    			if (_s_conditions_pre.find(newPred) == _s_conditions_pre.end()) {
						AVR_LOG(15, 0, "\t\t\t\t(adding predicate (from parent)   " << *newPred << " )" << endl);
						_s_conditions_pre.insert(newPred);
						newRef.push_front(OpInst::create(OpInst::LogOr, newPred, OpInst::create(OpInst::LogNot, newPred)));
    			}
    		}
        added |= process_predicate_info(newPred);
      }

      bool added2 = process_predicate_info(pred_new);
//      if (!added) {
//        AVR_LOG(15, 0, "\t(error: unable to find new UFs)" << endl);
//      }
//      assert(added);

      status = !(added || added2);
      status = false;
#ifdef SIMULATION_CHECK_LIMIT_INSTANTIATION
      status = instantiate ? !added : false;
#endif
    }
  }
  return status;
}

/// Returns true if new predicate(s) learnt,
/// Returns false if a predicate already learnt is learnt again
bool Reach::convert_to_lemmas(InstL& failureCondition, InstL& newLemmas, SIMULATION_POSITION& sCurr, deque< ABSTRACT_CUBE >& rcext)
{
	assert(failureCondition.size() != 0);

	AVR_LOG(14, 1, "Adding lemma to ensure following never happens: " << failureCondition << endl);

	InstS failConds;
	InstL failureConditionNew;
	_collected_cubes.clear();

	for (auto& v: failureCondition) {
		if (failConds.find(v) == failConds.end()) {
			failConds.insert(v);
			failureConditionNew.push_back(v);
			if (v != v->t_simple) {
				collect_cubes(v->t_simple, false);
			}
		}
	}
	for (auto& v: _collected_cubes) {
		if (failConds.find(v) == failConds.end()) {
			failConds.insert(v);
			failureConditionNew.push_back(v);
		}
	}
	failureCondition.swap(failureConditionNew);

	AVR_LOG(14, 1, "Processing failure condition: " << failureCondition << endl);

//	InstL subFailureCondition;
//	bool mod = reduce_ref_eval_sim(failureCondition, subFailureCondition);
//	if (mod)
//	{
//		AVR_LOG(14, 1, "\tReduced lemma: " << subFailureCondition << endl);
//		failureCondition.swap(subFailureCondition);
////		assert(0);
//	}

//	bool learnLemmas = !mod;
	bool learnLemmas = true;
	InstL conjunct_ref = failureCondition;
	Inst* ve_ref = OpInst::create(OpInst::LogAnd, conjunct_ref);


//			while(1)
//			{
//				if(generalize_ref(conjunct_ref) == false)
//				{
//					ve_ref = OpInst::create(OpInst::LogAnd, conjunct_ref);
//					break;
//				}
//			}

	InstS predicateSetC, predicateSetN, predicateSetNext;
	InstL newRef;
	InstL predicateList, cNext;

//	while(generalize_ref(failureCondition));

	for (InstL::iterator cit = failureCondition.begin(); cit != failureCondition.end(); cit++)
	{
		if (!(*cit)->find_next())
		{
			if ((*cit)->childrenInfo[CONST])
			{
				Inst* cOrig = (*cit);
				Inst* c = cOrig;
//				c = simplify_expr(cOrig);
//				if (cOrig != c)
//				{
//					cout << "\t(simplified: " << *cOrig << " -> " << *c << ")" << endl;
//				}

				if (c->childrenInfo[CONST])
				{
					predicateSetC.insert(c);
					predicateList.push_back(c);
				}
				else
				{
					if (!((*cit) == _ve_model || (*cit) == _ve_prop_eq_1))
						predicateSetN.insert(c);
					else
						newRef.push_back(c);
				}
			}
			else
			{
				if (!((*cit) == _ve_model || (*cit) == _ve_prop_eq_1))
					predicateSetN.insert((*cit));
				else
					newRef.push_back((*cit));
			}
		}
		else
		{
#ifdef LEARN_ALL_PREDICATES
			if (!((*cit) == _ve_model_next || (*cit) == _ve_prop_next_eq_0))
				cNext.push_back(*cit);
#endif
			newRef.push_back((*cit));
		}
	}

#ifdef LEARN_ALL_PREDICATES
	if (!cNext.empty())
	{
		for (InstL::iterator pit = cNext.begin(); pit != cNext.end(); pit++)
		{
			if (!find_pre((*pit)))
			{
				predicateSetNext.insert(all_next2pre(*pit, true));
			}
		}
//		generalize_ref(cNext);
//		for (InstL::iterator pit = cNext.begin(); pit != cNext.end(); pit++)
//		{
//			if (!find_pre((*pit), true))
//			{
//				predicateSetNext.insert(all_next2pre(*pit, true));
//			}
//			else if (!find_next((*pit), true))
//			{
//				predicateSetNext.insert(*pit);
//			}
//		}
	}
#endif

	AVR_LOG(14, 5, "\t\t(predicateSetN)" << endl);
	for (InstS::iterator sit = predicateSetN.begin(); sit != predicateSetN.end(); sit++)
	{
		AVR_LOG(15, 1, "\t\t\t(original predicate " << *(*sit) << " )" << endl);
	}

	AVR_LOG(14, 5, "\t\t(predicateSetC)" << endl);
	for (InstS::iterator sit = predicateSetC.begin(); sit != predicateSetC.end(); sit++)
	{
		AVR_LOG(15, 1, "\t\t\t(original predicate " << *(*sit) << " )" << endl);
	}

#ifdef LEARN_ALL_PREDICATES
	AVR_LOG(14, 5, "\t\t(predicateSetNext)" << endl);
	for (InstS::iterator sit = predicateSetNext.begin(); sit != predicateSetNext.end(); sit++)
	{
		AVR_LOG(15, 1, "\t\t\t(original predicate " << *(*sit) << " )" << endl);
	}
#endif

	AVR_LOG(14, 5, "\t\t(predicateList)" << endl);
	for (InstL::iterator lit = predicateList.begin(); lit != predicateList.end(); lit++)
	{
		AVR_LOG(14, 5, "\t\t\t(predicate " << *(*lit) << " )" << endl);
	}

//	AVR_LOG(14, 5, "\t\t(cNext)" << endl);
//	for (InstL::iterator lit = cNext.begin(); lit != cNext.end(); lit++)
//	{
//		AVR_LOG(14, 5, "\t\t\t(predicate " << *(*lit) << " )" << endl);
//	}

	AVR_LOG(14, 5, "\t\t(newRefs)" << endl);
	for (InstL::iterator lit = newRef.begin(); lit != newRef.end(); lit++)
	{
		AVR_LOG(14, 5, "\t\t\t(predicate " << *(*lit) << " )" << endl);
	}

	InstToSetM m_constMap;
	InstToInstM m_valMap;
	for (InstToInstM::iterator mit = sCurr.val.begin(); mit != sCurr.val.end(); mit++)
	{
		assert(SigInst::as((*mit).first));
		if (ConstInst::as((*mit).second))
		{
			InstS tmp;
			tmp.insert((*mit).first);
			m_constMap[(*mit).second] = tmp;
		}
		else if (NumInst::as((*mit).second))
		{
			m_valMap[(*mit).second] = (*mit).first;
		}
	}
	if (!predicateList.empty())
	{
//		for (InstToInstM::iterator mit = sCurr.inp2Const.begin(); mit != sCurr.inp2Const.end(); mit++)
//		{
//			assert(SigInst::as((*mit).first));
//			assert(ConstInst::as((*mit).second));
//			InstS tmp;
//			tmp.insert((*mit).first);
//			m_constMap[(*mit).second] = tmp;
//		}
		for (InstS::iterator sit = sCurr.cConditions.begin(); sit != sCurr.cConditions.end(); sit++)
		{
			Inst* tve = *sit;
			OpInst* op = OpInst::as(tve);
			bool negated = false;
			if (op && op->get_op() == OpInst::LogNot)
			{
				tve = op->get_children()->front();
				negated = true;
			}

			ConstInst* cSig = ConstInst::as(tve);
			if (cSig)
			{
				assert(tve->get_size() == 1);
				Inst* lhs = negated ? NumInst::create(0, 1, SORT()) : NumInst::create(1, 1, SORT());
				InstToSetM::iterator mit = m_constMap.find(cSig);
				if (mit != m_constMap.end())
				{
					(*mit).second.insert(lhs);
				}
				else
				{
					InstS tmp;
					tmp.insert(lhs);
					m_constMap[tve] = tmp;
				}
			}
			else
			{
				OpInst* op = OpInst::as(tve);
				if (op)
				{
					if (((op->get_op() == OpInst::Eq) && !negated) ||
						((op->get_op() == OpInst::NotEq) && negated))
					{
						const InstL* ch = tve->get_children();
						InstL::const_iterator ch_it = ch->begin();
						Inst* lhs = *(ch_it++);
						Inst* rhs = *ch_it;

						if(lhs->childrenInfo[CONST])
						{
							Inst* tmp = lhs;
							lhs = rhs;
							rhs = tmp;
						}
						if (lhs->childrenInfo[CONST])
							continue;

						if (rhs->childrenInfo[CONST])
						{
							InstToSetM::iterator mit = m_constMap.find(rhs);
							if (mit != m_constMap.end())
							{
								(*mit).second.insert(lhs);
							}
							else
							{
								InstS tmp;
								tmp.insert(lhs);
								m_constMap[rhs] = tmp;
							}
						}
					}
				}
			}
		}

		bool learn = true;
		generalize_simulation_predicates(predicateList, m_constMap, learn);
//		if (!learn || predicateList.empty())
//		if (predicateList.empty())
//			learnLemmas = false;

//		for (InstL::iterator pit = predicateList.begin(); pit != predicateList.end(); pit++)
//		{
//			Inst* tve = (*pit);
//
//			if (tve->childrenInfo[CONST])
//			{
//        AVR_LOG(15, 0, "\t\t(trying instantiating symbolic expression)\t" << *tve << endl);
//        Inst* newTve = replace_constant_with_value(tve);
//        AVR_LOG(15, 0, "\t\t(instantiated symbolic expression)\t" << *tve << " := " << *newTve << endl);
//        assert(!newTve->childrenInfo[CONST]);
//        (*pit) = newTve;
//			}
//		}
	}

	bool exitFlag = true;

	InstS cubeSet;

	Inst* cubeSrc = rcext[sCurr.sIdx].cube;
	collect_cubes(cubeSrc, true);
	for (auto& c: _collected_cubes)
		cubeSet.insert(c);

  Inst::init_visit2();
	for (InstS::iterator sit = predicateSetN.begin(); sit != predicateSetN.end(); sit++)
	{
    exitFlag &= add_predicate(*sit, newRef, cubeSet, predicateSetN, predicateList, m_constMap, m_valMap);
	}

	for (InstL::iterator pit = predicateList.begin(); pit != predicateList.end(); pit++)
	{
    exitFlag &= add_predicate(*pit, newRef, cubeSet, predicateSetN, predicateList, m_constMap, m_valMap);
	}

#ifdef LEARN_ALL_PREDICATES
	for (InstS::iterator sit = predicateSetNext.begin(); sit != predicateSetNext.end(); sit++)
	{
		Inst* tve_orig = (*sit);
		Inst* tve = tve_orig;
		OpInst* op = OpInst::as(tve_orig);
		if (op)
		{
			OpInst::OpType opType = op->get_op();
			if (opType == OpInst::LogNot)
				tve = tve_orig->get_children()->front();
				else if (opType == OpInst::NotEq)
				{
					tve = OpInst::create(OpInst::LogNot, tve_orig);
				}
		}

		if (_s_conditions_pre.find(tve) != _s_conditions_pre.end())
		{
			AVR_LOG(15, 1, "\t\t\t(repeated predicate)" << endl);
		}
		else
		{
      add_predicate(tve);
			exitFlag = false;
		}
	}
#endif

	if (exitFlag)
	{
    AVR_LOG(15, 0, "\t\t\t(unable to find new UFs)" << endl);
		AVR_LOG(15, 1, "\t\t\t(not learning due to all repeated predicates)" << endl);
//		cout << "Preds: " <<_s_conditions_pre << endl;

		if (Config::g_ab_granularity < AB_GRANULARITY_MAX) {
//	if (false && Config::g_allow_inputs < MAX_AB_FINENESS) {
//			Config::g_ab_granularity++;
			Config::g_ab_granularity = AB_GRANULARITY_INPUT;
			AVR_LOG(15, 0, "(no new predicate learnt, incrementing abstraction granularity to level " << Config::g_ab_granularity << ")" << endl);
//		assert(0);
		}
		else if (Config::g_fineness < FINENESS_MAX) {
			Config::g_fineness++;
			AVR_LOG(15, 0, "(no new predicate learnt, incrementing abstraction fineness to level " << Config::g_fineness << ")" << endl);
//		assert(0);
		}
		else if (learnLemmas) {
			AVR_LOG(15, 0, "\t\t(warning: instantiated predicates learnt only)" << endl);
//			assert(0);
		}
		else {
			AVR_LOG(15, 0, "(error: no new lemma predicate learnt)" << endl);
			assert(0);
		}

//		return false;
//		assert(0);
	}

	if (!learnLemmas)
	{
		AVR_LOG(15, 1, "\t\t\t(learning only predicates)" << endl);
		assert(!exitFlag);
//		assert(0);
		return false;
	}

	ve_ref = OpInst::create(OpInst::LogAnd, newRef);

	if (ve_ref->childrenInfo[CONST])
	{
		cout << "Found constant in the following lemma condition: " << newRef << endl;
		while(1)
		{
			if(generalize_ref(conjunct_ref) == false)
			{
				break;
			}
		}
		Inst* simplifiedRef = OpInst::create(OpInst::LogNot, OpInst::create(OpInst::LogAnd, conjunct_ref));
		AVR_LOG(15, 1, "\n\t\t\t(simplified: " << *simplifiedRef << " )" << endl);
		assert(0);
	}

//	while(1)
//	{
//		if(generalize_ref(newRef) == false)
//		{
//			break;
//		}
//	}
//	Inst* simplifiedRef = OpInst::create(OpInst::LogNot, OpInst::create(OpInst::LogAnd, newRef));
//	AVR_LOG(15, 1, "\n\t\t\t(simplified: " << *simplifiedRef << " )" << endl);

	_new_refs.push_back(ve_ref);
	newLemmas.push_back(ve_ref);

#ifdef AVR_ADD_NEXT_REF
//	if (!ve_ref->find_next())
//	{
//		Inst* nextRef = Inst::all_pre2next(ve_ref);
//		_new_refs.push_back(nextRef);
//		newLemmas.push_back(nextRef);
//	}
	/// Below ref can be wrong in rare case (when I violates this ref).
//	else if (!find_pre(ve_ref, true))
//	{
//		Inst* preRef = all_next2pre(ve_ref, true);
//		_new_refs.push_back(preRef);
//		newLemmas.push_back(preRef);
//	}
#endif
	return true;
}


//bool Reach::simulation_check_old(deque< ABSTRACT_CUBE >& rcext)
//{
//	/// TODO: remove return
////	return 1;
//	/// Aman TODO: Figure out need to do simulation check without asserting input conditions when looping
//	/// Aman TODO: Figure out avoiding asserting complete transition relation by using _next_state
//	/// Aman TODO: Figure out how to derive DPR refinements to eliminate reoccurence of infeasible ACEXT
//	/// Aman TODO: Remove relevantStates etc. if not needed
//	/// Aman TODO: Search for better ways of asserting transition relation (if needed) and extracting MUS
//
//
//	AVR_LOG(15, 0, "\n\t[Simulation check]: ");
//	AVR_LOG(14, 1, "=========== Simulation Begins ===============" << endl);
//	AVR_LOG(4, 4, "Simulation for ACEXT:" << endl);
//
//	for(deque< ABSTRACT_CUBE >::iterator it = rcext.begin(); it != rcext.end(); it++)
//	{
//		AVR_LOG(4, 4, "F[" << (*it).frame << "] - " << *((*it).cube) << " Next: " << *((*it).next) << endl);
////		InstL conjunct_tmp;
////		collect_cubes((*it).cube, true);
////		for (InstL::iterator vit = _collected_cubes.begin(); vit != _collected_cubes.end(); vit++)
////		{
////			if (!find_input(*vit, true))
////					conjunct_tmp.push_back(*vit);
////		}
////		assert(!conjunct_tmp.empty());
////		(*it).cube_wo_input = OpInst::create(OpInst::LogAnd, conjunct_tmp);
//	}
//	AVR_LOG(4, 4, endl);
//
//	int unsatIdx = rcext.size() - 1;
//
//	SIMULATION_POSITION curr;
//	SIMULATION_POSITION& sCurr = curr;
//
//	sCurr.sIdx = unsatIdx;
//	sCurr.src = -1;
//	sCurr.dest = ((unsatIdx - 1) >= 0 ? (unsatIdx - 1) : -1);
//
//	InstL failConditions;
//	list< SIMULATION_POSITION > retractPoints;
//
//	while(1)
//	{
//		Inst* cube = rcext[sCurr.sIdx].cube;
//		int frame = rcext[sCurr.sIdx].frame;
//		Inst* next = rcext[sCurr.sIdx].next;
//
//		InstL conjunct_q;
//		InstL assignments;
//
//		conjunct_q.push_back(cube);
////		conjunct_q.push_back(next);
//		conjunct_q.push_back(_ve_model_nsf);
//
////		collect_cubes(next, true);
////		for(InstL::iterator cit = _collected_cubes.begin(); cit != _collected_cubes.end(); cit++)
////		{
////			Inst* tve = (*cit);
////			OpInst* op = OpInst::as(tve);
////			if (op)
////			{
////				if (op->get_op() == OpInst::Eq)
////				{
////					Inst* lhs = op->get_children()->front();
////					Inst* rhs = op->get_children()->back();
////					assert(lhs && rhs);
////
////					if (SigInst::as(lhs) && SigInst::as(rhs))
////					{
////						if (_m_sn.find(lhs) != _m_sn.end() && _s_inp.find(rhs) != _s_inp.end())
////						{
//////							Inst* ex = ExInst::create(rhs, 127, 0);
////
////							string numC92  = "011110000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001";
////							string numC96  = "100100000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000";
////							string numC100 = "010110000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000";
////							string numC104 = "000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001";
////							string numC108 = "000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001";
////							string numC1   = "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001";
////							SigInst* inp = SigInst::as(rhs);
////							assert(inp);
////
////							string inpName = inp->get_name();
////							string numC = "";
////
////							switch(sCurr.sIdx)
////							{
////							case 6:
////								if (inpName == "i5")			/// 3d137
////								{
////									numC = "001";
////								}
////								if (inpName == "i8")			/// 135d138
////								{
////									numC = "000" + numC1;
////								}
////								if (inpName == "i10")			/// 3d136
////								{
////									numC = "000";
////								}
////								if (inpName == "i13")			///- 132d135
////								{
////									numC = "011100000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000";
////								}
////								break;
////							case 5:
////								if (inpName == "i5")			/// 3d140
////								{
////									numC = "001";
////								}
////								if (inpName == "i8")			/// 135d141
////								{
////									numC = "000" + numC1;
////								}
////								if (inpName == "i10")			/// 3d142
////								{
////									numC = "000";
////								}
////								if (inpName == "i11")			///- 132d139
////								{
////									numC = "000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000";
////								}
////								break;
////							case 4:
////								if (inpName == "i5")			/// 3d145
////								{
////									numC = "000";
////								}
////								if (inpName == "i8")			/// 135d146
////								{
////									numC = "000" + numC1;
////								}
////								if (inpName == "i10")			/// 3d144
////								{
////									numC = "001";
////								}
////								if (inpName == "i12")			///- 132d143
////								{
////									numC = "000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000";
////								}
////								break;
////							case 3:
////								if (inpName == "i5")			/// 3d149
////								{
////									numC = "001";
////								}
////								if (inpName == "i8")			/// 135d150
////								{
////									numC = "000" + numC1;
////								}
////								if (inpName == "i10")			/// 3d148
////								{
////									numC = "011";
////								}
////								if (inpName == "i14")			///- 132d147
////								{
////									numC = "011100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000";
////								}
////								break;
////							case 2:
////								if (inpName == "i5")			/// 3d153
////								{
////									numC = "001";
////								}
////								if (inpName == "i8")			/// 135d154
////								{
////									numC = "000" + numC1;
////								}
////								if (inpName == "i10")			/// 3d152
////								{
////									numC = "100";
////								}
////								if (inpName == "i15")			///- 132d151
////								{
////									numC = "011000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000";
////								}
////								break;
////							case 1:
////								if (inpName == "i5")			/// 3d155
////								{
////									numC = "110";
////								}
////								break;
////							case 0:
////								break;
////							}
////
////							if (numC != "")
////							{
////								Inst* num = NumInst::create(numC, rhs->get_size(), 2);
////								Inst* newC = OpInst::create(OpInst::Eq, rhs, num);
////								conjunct_q.push_back(newC);
////								cout << "\n\t -------- Adding assertion: " << *rhs << " == " << numC << " ---------- " << endl;
////							}
////						}
////					}
////				}
////			}
////		}
//
////		for (InstToInpinfoM::iterator it3 = constMap.begin(); it3 != constMap.end(); ++it3)
////		{
////			inpInfo& rhs = (*it3).second;
////
////			if (rhs.idx == sCurr.sIdx)
////			{
////				Inst* tmp = OpInst::create(OpInst::Eq, rhs.inp, NumInst::create(rhs.val, rhs.inp->get_size()));
////				conjunct_q.push_back(tmp);
////				cout << "Asserting " << *(rhs.inp) << " == " << rhs.val.get_str(2) << endl;
////			}
////		}
//
//		for (InstL::iterator it3 = _negated_refs.begin(); it3 != _negated_refs.end(); ++it3)
//			conjunct_q.push_back(*it3);
//
//		Inst* cubeNext;
//		if (sCurr.dest == -1)
//		{
//			assert(sCurr.sIdx == 0);
//
//			InstL conjunct_prop;
//			conjunct_prop.push_back(_ve_model_next);
//			conjunct_prop.push_back(_ve_prop_next_eq_0);
//			cubeNext = OpInst::create(OpInst::LogAnd, conjunct_prop);
//		}
//		else
//		{
//			cubeNext = all_pre2next(rcext[sCurr.dest].cube, true);
//		}
//
//		AVR_LOG(14, 5, "Cube: " << *cube << endl);
//
//		AVR_LOG(14, 7, "Q: " << conjunct_q << endl);
//
//		InstL conjunct_next = conjunct_q;
//		conjunct_next.push_back(cubeNext);
//
//		AVR_LOG(14, 6, "Cube$next: " << *cubeNext << endl);
//
//#ifdef SIMULATION_CHECK_SELF_LOOPS
//		InstL conjunct_self = conjunct_q;
//		Inst* cubeSelf = all_pre2next(cube, true);
//		conjunct_self.push_back(cubeSelf);
//
//		AVR_LOG(14, 6, "Cube$self: " << *cubeSelf << endl);
//
//		InstS relevantStatesSelf;
////		collect_next_sig(cubeSelf, relevantStatesSelf, true);
//		collect_next_reg(_ve_model_nsf, relevantStatesSelf, true);
//#endif
//
//		InstS relevantStatesNext;
////		collect_next_sig(cubeNext, relevantStatesNext, true);
//		collect_next_reg(_ve_model_nsf, relevantStatesNext, true);
//
//		bool res = false;
//		while (1)
//		{
////			cout << "A[" << sCurr.sIdx << "]" << endl;
//
//#ifdef SIMULATION_CHECK_SELF_LOOPS
//			InstL conjunct_loop = conjunct_self;
//#endif
//			InstL conjunct_exit = conjunct_next;
//
//			if (sCurr.src == -1)
//			{
//				AVR_LOG(14, 4, "Asserting I" << endl);
//				assert(sCurr.sIdx == unsatIdx);
//				/// Find starting conditions
//				for (InstL::iterator fit = _negated_cubes[frame].begin(); fit != _negated_cubes[frame].end(); fit++)
//				{
//#ifdef SIMULATION_CHECK_SELF_LOOPS
//					conjunct_loop.push_back(*fit);
//#endif
//					conjunct_exit.push_back(*fit);
//					cout << "\t" << *(*fit) << endl;
//				}
//			}
//			else
//			{
//				cout << "src:" << endl;
//				for(InstToMpzM::iterator vit = sCurr.s.begin(); vit != sCurr.s.end(); vit++)
//				{
//					Inst* tmp = OpInst::create(OpInst::Eq, (*vit).first, NumInst::create((*vit).second, (*vit).first->get_size()));
//#ifdef SIMULATION_CHECK_SELF_LOOPS
//					conjunct_loop.push_back(tmp);
//#endif
//					conjunct_exit.push_back(tmp);
////					assignments.push_back(tmp);
//					cout << "\t" << *tmp << endl;
//				}
//			}
//
//#ifdef SIMULATION_CHECK_SELF_LOOPS
//			AVR_LOG(14, 7, "Loop Q: " << conjunct_loop << endl);
//			Inst* ve_loop = OpInst::create(OpInst::LogAnd, conjunct_loop);
//			SolverAPI* loop_solver = dynamic_cast<SolverAPI*> (new_conc_solver(1));
//			bool resLoop = loop_solver->check_sat(ve_loop);
//			AVR_LOG(14, 4, "[" << sCurr.sIdx << "] Cube to CubeSelf+ is " << (resLoop?"SAT":"UNSAT") << endl);
//
//			SIMULATION_POSITION loopNext;
//
//			bool loopStuck = (sCurr.src == -1) ? false : true;
//			if (resLoop)
//			{
//
//				/// Collect values of state variables (location variables not included)
//				retrieve_cex_val(ve_loop, loop_solver, false, true);
//				print_concrete_min_term("To CubeSelf+");
//
//				/// Aman TODO: Modify retrieve_cex_val to directly give values of concerned state variables
////				cout << "self:" << endl;
//				for (InstS::iterator it = relevantStatesSelf.begin(); it != relevantStatesSelf.end(); it++)
//				{
//					Inst* e = (*it);
//					InstToMpzM::iterator cit = _min_term_c.find(e);
//
//					assert(cit != _min_term_c.end());
//					Inst* sig_pre = _m_next_to_pre[e];
//
//					/// Aman - sig_pre can be false due to input sigs
//					if (sig_pre)
//					{
//						loopNext.s[sig_pre] = (*cit).second;
////						cout << "(" << *sig_pre << " == " << (*cit).second << ")" << endl;
//						if (loopStuck == true)
//						{
//							InstToMpzM::iterator oldVal = sCurr.s.find(sig_pre);
//							if (oldVal != sCurr.s.end())
//							{
//								if ((*oldVal).second != (*cit).second)
//									loopStuck = false;
//							}
//						}
//					}
//				}
//				loopNext.sIdx = sCurr.sIdx;
//				loopNext.src  = sCurr.sIdx;
//				loopNext.dest = sCurr.dest;
//			}
//			else
//				loopStuck = false;
//#endif
//
//			AVR_LOG(14, 7, "CubeNext Q: " << conjunct_exit << endl);
//			Inst* ve_exit = OpInst::create(OpInst::LogAnd, conjunct_exit);
//			SolverAPI* exit_solver = dynamic_cast<SolverAPI*> (new_conc_solver(1));
//			bool resExit = exit_solver->check_sat(ve_exit);
//			AVR_LOG(14, 4, "[" << sCurr.sIdx << "] Cube to CubeNext+ is " << (resExit?"SAT":"UNSAT") << endl);
//
//			SIMULATION_POSITION exitNext;
//			if (resExit)
//			{
//				/// Collect values of state variables (location variables not included)
//				retrieve_cex_val(ve_exit, exit_solver, false, true);
//				print_concrete_min_term("To CubeNext+");
//
//				/// Aman TODO: Modify retrieve_cex_val to directly give values of concerned state variables
////				cout << "dest:" << endl;
//				for (InstS::iterator it = relevantStatesNext.begin(); it != relevantStatesNext.end(); it++)
//				{
//					Inst* e = (*it);
//					InstToMpzM::iterator cit = _min_term_c.find(e);
//
//					assert(cit != _min_term_c.end());
//					Inst* sig_pre = _m_next_to_pre[e];
//
//					/// Aman - sig_pre can be false due to input sigs
//					if (sig_pre)
//					{
//						exitNext.s[sig_pre] = (*cit).second;
////						cout << "(" << *sig_pre << " == " << (*cit).second << ")" << endl;
//					}
//				}
//				exitNext.sIdx = sCurr.dest;
//				exitNext.src  = sCurr.sIdx;
//				exitNext.dest = (sCurr.dest - 1);
//			}
//
//			AVR_LOG(14, 4, endl);
//
//#ifdef SIMULATION_CHECK_SELF_LOOPS
//			if (loopStuck)
//				AVR_LOG(15, 0, "\n\t\tFound infinite loop at A[" << sCurr.sIdx << "]" << endl);
//			if (resLoop)
//			{
//				if (resExit)
//				{
//					/// Both true, take one of them.
//					/// Aman - TODO: Choose "better" one, and better ordering of retractPoints
//
//					if (loopStuck)
//					{
//						AVR_LOG(14, 4, "Choosing CubeNext+ over CubeSelf+" << endl);
//						sCurr = exitNext;
////						retractPoints.push_front(loopNext);
//						res = true;
//						break;
//					}
//					else
//					{
//						AVR_LOG(14, 4, "Choosing CubeSelf+ over CubeNext+" << endl);
//						sCurr = loopNext;
//						retractPoints.push_front(exitNext);
//					}
//				}
//				else
//				{
//					if (loopStuck)
//					{
//						res = false;
//
//						if (retractPoints.empty())
//						{
//							InstLL muses;
//
//							collect_cubes(next, true);
//							InstL conjunct_tmp;
//							InstToInstM m_sig_next;
//							for (InstL::iterator nit = _collected_cubes.begin(); nit != _collected_cubes.end(); nit++)
//							{
//	//							cout << (*(*nit)) << endl;
//								SigInst* sig = SigInst::as(*nit);
//								if (sig)
//								{
//									assert(sig->get_size() == 1);
//									m_sig_next[sig] = (*nit);
//								}
//								else
//								{
//									OpInst* op = OpInst::as(*nit);
//									assert(op);
//									assert(op->get_op() == OpInst::Eq || op->get_op() == OpInst::LogNot);
//
//									SigInst* sigTmp = SigInst::as((*nit)->get_children()->front());
//									assert(sigTmp);
//									m_sig_next[sigTmp] = (*nit);
//								}
//							}
//
//							AVR_LOG(14, 6, "Next:" << endl);
//							for (InstToInstM::iterator mit = m_sig_next.begin(); mit != m_sig_next.end(); mit++)
//							{
//								AVR_LOG(14, 6, *((*mit).first) << " = " << *((*mit).second) << endl);
//							}
//
//							collect_cubes(ve_exit, true);
//							AVR_LOG(14, 6, "Unsat query is " << _collected_cubes << endl);
//
//							SolverAPI* mus_solver = dynamic_cast<SolverAPI*> (new_conc_solver(1));
//							int res = mus_solver->get_muses(0, _conjunct_nsf, _collected_cubes, muses);
//							for (InstLL::iterator it_muses2 = muses.begin(); it_muses2 != muses.end(); ++it_muses2)
//							{
//								Inst* failC = OpInst::create(OpInst::LogAnd, (*it_muses2));
////								cout << "MUS: " << (*it_muses2) << endl;
//								InstS relevantStates;
//								collect_next_reg(failC, relevantStates, true);
////								cout << "Relevant states:" << endl;
//								for (InstS::iterator sit = relevantStates.begin(); sit != relevantStates.end(); sit++)
//								{
//									Inst* sigNext = (*sit);
////									cout << "sigNext: " << *sigNext << endl;
//									InstToInstM::iterator ait = m_sig_next.find(sigNext);
//									if (ait != m_sig_next.end())
//										(*it_muses2).push_back((*ait).second);
//									else
//									{
////										cout << "sigNext: " << *sigNext << endl;
//										assert(sigNext == _ve_prop_next_eq_1);
//									}
//								}
//								failConditions.push_back(OpInst::create(OpInst::LogAnd, (*it_muses2)));
//							}
//						}
//						break;
//					}
//					else
//					{
//						sCurr = loopNext;
//						continue;
//					}
//				}
//			}
//			else
//			{
//#endif
//				if (resExit)
//				{
//					sCurr = exitNext;
//					res = true;
//					break;
//				}
//				else
//				{
//					res = false;
//
//					if (retractPoints.empty())
//					{
//						InstLL muses;
//
//						collect_cubes(next, true);
//						InstL conjunct_tmp;
//						InstToInstM m_sig_next;
//						for (InstL::iterator nit = _collected_cubes.begin(); nit != _collected_cubes.end(); nit++)
//						{
////							cout << (*(*nit)) << endl;
//							SigInst* sig = SigInst::as(*nit);
//							if (sig)
//							{
//								assert(sig->get_size() == 1);
//								m_sig_next[sig] = (*nit);
//							}
//							else
//							{
//								OpInst* op = OpInst::as(*nit);
//								assert(op);
//								assert(op->get_op() == OpInst::Eq || op->get_op() == OpInst::LogNot);
//
//								SigInst* sigTmp = SigInst::as((*nit)->get_children()->front());
//								assert(sigTmp);
//								m_sig_next[sigTmp] = (*nit);
//							}
//						}
//
//						collect_cubes(ve_exit, true);
////						cout << "Unsat query is " << _collected_cubes << endl;
//
//						SolverAPI* mus_solver = dynamic_cast<SolverAPI*> (new_conc_solver(1));
//						int res = mus_solver->get_muses(0, _conjunct_nsf, _collected_cubes, muses);
//						for (InstLL::iterator it_muses2 = muses.begin(); it_muses2 != muses.end(); ++it_muses2)
//						{
//							Inst* failC = OpInst::create(OpInst::LogAnd, (*it_muses2));
//
//							InstS relevantStates;
//							collect_next_reg(failC, relevantStates, true);
//							for (InstS::iterator sit = relevantStates.begin(); sit != relevantStates.end(); sit++)
//							{
//								Inst* sigNext = (*sit);
//								InstToInstM::iterator ait = m_sig_next.find(sigNext);
//								if (ait != m_sig_next.end())
//									(*it_muses2).push_back((*ait).second);
//								else
//									assert(sigNext == _ve_prop_next_eq_1);
//							}
//							failConditions.push_back(OpInst::create(OpInst::LogAnd, (*it_muses2)));
//						}
//					}
//					break;
//				}
//#ifdef SIMULATION_CHECK_SELF_LOOPS
//			}
//#endif
//		}
//
//		if(res)
//		{
//			if (sCurr.sIdx == -1)
//			{
//				AVR_LOG(15, 0, "\t\tACEXT is feasible" << endl);
//				_feas_sat_res = true;
//				break;
//			}
//		}
//		else
//		{
//			if (retractPoints.empty())
//			{
//				AVR_LOG(15, 0, "ACEXT is infeasible" << endl);
//				if (sCurr.dest != -1)
//				{
//					AVR_LOG(15, 0, "\t\t\t(unsat: A[" << sCurr.sIdx << "] to A[" << sCurr.dest << "]" << endl);
//				}
//				else
//				{
//					AVR_LOG(15, 0, "\t\t\t(unsat: A[" << sCurr.sIdx << "] to A[End]" << endl);
//				}
//
//				_feas_sat_res = false;
//				break;
//			}
//			else
//			{
//				sCurr = retractPoints.front();
//				retractPoints.pop_front();
//			}
//		}
//	}
//
//	if (_feas_sat_res == true)
//	{
//		_new_refs.clear();
//		AVR_LOG(14, 1, "=========== Simulation Ends ===============" << endl);
//		return true;
//	}
//	else
//	{
//		/// Aman - TODO Learn more lemmas to eliminate this ACEXT to occur again
////		InstL conjunct_tmp;
////		Inst* tve_assign;
////		if (sCurr.sIdx != -1)
////		{
////			conjunct_tmp.push_back(rcext[conflict.src].cube);
////			failCondition.push_back(all_pre2next(rcext[conflict.dest].cube, true));
////
////			tve_assign = OpInst::create(OpInst::LogAnd, conflict.assignments);
////			Inst* tve_next = all_pre2next(tve_assign, true);
////			failCondition.push_back(OpInst::create(OpInst::LogNot, tve_next));
////			AVR_LOG(14, 4, "Adding lemma to ensure following never happens: " << failCondition << endl);
////			_new_refs.push_back(OpInst::create(OpInst::LogAnd, failCondition));
////		}
////		else
////		{
////			failCondition = _negated_cubes[0];
////			failCondition.push_back(rcext[conflict.dest].cube);
////
////			tve_assign = OpInst::create(OpInst::LogAnd, conflict.assignments);
////			failCondition.push_back(OpInst::create(OpInst::LogNot, tve_assign));
////			AVR_LOG(14, 4, "Adding lemma to ensure following never happens: " << failCondition << endl);
////			_new_refs.push_back(OpInst::create(OpInst::LogAnd, failCondition));
////		}
//
////		Negating failed destination and asserting in reachability frame
////		if (sCurr.dest == -1)
////		{
////			/// TODO
////			assert(0);
////		}
////		else
////		{
////			Inst* fCube = rcext[sCurr.dest].cube;
////			int fFrame = rcext[sCurr.dest].frame;
////			_cubes[fFrame].push_back(fCube);
////			Inst* fCubeNeg = OpInst::create(OpInst::LogNot, fCube);
////			cout << "Asserting " << *fCubeNeg << " in F[" << fFrame << "]" << endl;
////
////			for (int i = 0; i <= fFrame; i++)
////			{
////				if (i != 0)
////					_negated_cubes[i].push_back(fCubeNeg);
////
////				if (_reach_solvers[i])
////				{
////					_reach_solvers[i]->s_assert(fCubeNeg);
////				}
////				if(i >= _frame_idx)
////				{
////					if (_cti_solver)
////					{
////						_cti_solver->s_assert(fCubeNeg);
////					}
////				}
////			}
////		}
//
//
//		for (InstL::iterator cit = failConditions.begin(); cit != failConditions.end(); cit++)
//		{
//			Inst* ve_ref = (*cit);
//
//			AVR_LOG(14, 3, "Adding lemma to ensure following never happens: " << *ve_ref << endl);
//
//			collect_Eq(ve_ref, 0, true);
//
//			_new_refs.push_back(ve_ref);
//
//			#ifdef AVR_ADD_NEXT_REF
//				if (!find_next(ve_ref, true))
//				{
//					Inst* nextRef = all_pre2next(ve_ref, true);
//					_new_refs.push_back(nextRef);
//				}
//			#endif
//		}
//		AVR_LOG(14, 1, "Note: Need to learn a refinement lemma to eliminate this ACEXT to appear again" << endl);
//		AVR_LOG(14, 1, "=========== Simulation Ends ===============" << endl);
////		assert(0);
//		return false;
//	}
//}

}
