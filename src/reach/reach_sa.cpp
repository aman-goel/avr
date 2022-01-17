/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


/*
 * reach_sa.cpp
 *
 *  Created on: Nov 15, 2017
 *      Author: rock
 */

#include "reach_sa.h"

namespace reach
{
#ifdef STRUCTURAL_PROJECTION

long long STRUCTURE_ANALYSIS::sz_sig_compare = 0;
long long STRUCTURE_ANALYSIS::sz_num_compare = 0;
long long STRUCTURE_ANALYSIS::sz_wire_compare = 0;

long long STRUCTURE_ANALYSIS::sz_sig_compare_common_nodes = 0;
long long STRUCTURE_ANALYSIS::sz_sig_compare_common_fapp = 0;

int STRUCTURE_ANALYSIS::num_fapp = 0;
int STRUCTURE_ANALYSIS::num_common_fapp = 0;
int STRUCTURE_ANALYSIS::num_common_node = 0;
int STRUCTURE_ANALYSIS::num_wapp = 0;

void STRUCTURE_ANALYSIS::init()
{
	numCompare.resize(_idxHash.size());
	sigCompare.resize(_idxHash.size());
	wCompare.resize(_wIdxHash.size());
//	cout << _idxHash.size() << endl;
//	cout << Inst::_s_reg.size() << endl;
//	cout << Inst::_s_inp.size() << endl;
//	cout << Inst::_m_sn.size() << endl;

	Inst::init_visit();
}

void STRUCTURE_ANALYSIS::start(Inst* iC, Inst* pC, InstS& aC, string message)
{
	AVR_LOG(15, 0, endl << message << endl);

	init();

	get_fapps(iC, NULL);
	get_fapps(pC, NULL);
	for (auto& v: aC)
		get_fapps(v, NULL);

	for (auto& m: Inst::_m_sn)
	{
		Inst* sig = Inst::_m_next_to_pre[m.first];
		Inst* rhs = m.second.first;
		get_fapps(rhs, sig);
	}

//	print_fapps();
	fill_compares();
//	check_further_compares();
//	print_compares(15, 0);
}

void STRUCTURE_ANALYSIS::get_fapps(Inst* top, Inst* parent, string s)
{
	if (top->get_visit())
	{
		// Structural hashing string
		if (top->saPrefix.find(s) != top->saPrefix.end())
		{
#ifdef SA_COMMON_NODES
			if (s != "" && (parent != NULL))
			{
				fAppsCommon[make_pair(top, parent->get_size())].insert(parent);
//				if (fAppsCommon[make_pair(top, parent->get_size())].size() == 2)
//					cout << "common node: " << *top << " with s: " << s << endl;
			}
#endif
			return;
		}
	}
	top->set_visit();
	string prefix = s;
	string midix = "";

//	bool print = true;

	bool isUF = false;

	switch(top->get_type())
	{
		case Sig:
		case Num:
		{
			if (s != "")
			{
				s += PREFIX + to_string(top->get_size());
				fApps[s].insert(top);
#ifdef SA_COMMON_FAPPS
				if (parent != NULL)
				{
					string sP = PREFIX + to_string(parent->get_size()) + "_" + s;
					fAppsParent[sP].insert(parent);
				}
#endif
//				if (print)
//					cout << "(add)  " << s << "   <= " << *top << endl;
			}
		}
		break;
		case Wire:
		{
#ifdef SA_WAPPS
			if (s != "")
			{
				s += PREFIX + to_string(top->get_size());
				fAppsW[s].insert(top);
//				if (print)
//					cout << "(add)  " << s << "   <= " << *top << endl;
			}
#endif
		}
		break;
		case Op:
		case Ex:
		{
			OpInst* op = OpInst::as(top);
//			if (op->get_op() != OpInst::Concat)
			{
				string euf_type_name = op->get_euf_type_name();
				if (s != "" && op->get_op() == OpInst::Ternary) {
					euf_type_name = "MUX";
				}
				if (euf_type_name != "0")
				{
					midix = euf_type_name + "(";
					isUF = true;
				}
				else
				{
					if (op->get_op() == OpInst::Eq || op->get_op() == OpInst::NotEq)
					{
//						isUF = true;
//						midix = "== (";


						Inst* lhs = top->get_children()->front();
						Inst* rhs = top->get_children()->back();
						if (lhs->get_type() == Num)
							swap(lhs, rhs);
						if (lhs->get_type() == Sig)
						{
							if (rhs->get_type() == Sig)
							{
								sigCompare[get_idx(lhs)].insert(rhs);
								sigCompare[get_idx(rhs)].insert(lhs);
//								if (print)
//									cout << "@" << get_idx(lhs) << " " << get_idx(rhs) << "\t[" << *lhs << " ?= " << *rhs << "]" << endl;
							}
							else if (rhs->get_type() == Num)
							{
								numCompare[get_idx(lhs)].insert(rhs);
//								if (print)
//									cout << "@" << get_idx(lhs) << "\t[" << *lhs << " ?= " << *rhs << "]" << endl;
							}
						}
					}
				}
			}
		}
		break;
//		case Ex:
//		{
////			ExInst* ex = ExInst::as(top);
////			string euf_type_name = ex->get_euf_type_name();
////			if (euf_type_name == "0")
////				cout << *top << endl;
////
////			assert (euf_type_name != "0");
////			midix = euf_type_name + "(";
////			isUF = true;
//		}
//		break;
		default:
			assert(0);
	}
	top->saPrefix.insert(prefix);

	const InstL* ch = top->get_children();
	if (ch)
	{
		string suffix = "";
		for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it)
		{
			if (!isUF)
			{
				if ((*it)->get_size() == 1)
				{
					get_fapps(*it, parent, midix + suffix);
					continue;
				}
			}
			get_fapps(*it, parent, prefix + midix + suffix);

			if (isUF)
				suffix += ", ";
		}
	}
}

void STRUCTURE_ANALYSIS::print_fapps()
{
	cout << "\t(sa)"  << endl;
	cout << "\t  (wfapps)"  << endl;
	for (auto& m: fAppsW)
	{
		if (m.second.size() > 1)
		{
//			cout << "\t\t" << m.first << "\t<= ";
			cout << "\t\t\t<= ";
			for (auto& tve: m.second)
				cout << *tve << ", ";
			cout << endl;
		}
	}

	cout << "\t  (fapps)"  << endl;
	for (auto& m: fApps)
	{
		if (m.second.size() > 1)
		{
//			cout << "\t\t" << m.first << "\t<= ";
			cout << "\t\t\t<= ";
			for (auto& tve: m.second)
				cout << *tve << ", ";
			cout << endl;
		}
	}

#ifdef SA_COMMON_FAPPS
	cout << "\t  (common fapps)"  << endl;
	for (auto& m: fAppsParent)
	{
		if (m.second.size() > 1)
		{
			cout << "\t\t" << m.first << "\t<= ";
			for (auto& tve: m.second)
				cout << *tve << ", ";
			cout << endl;
		}
	}
#endif

#ifdef SA_COMMON_NODES
	cout << "\t  (common nodes)"  << endl;
	for (auto& m: fAppsCommon)
	{
		if (m.second.size() > 1)
		{
			cout << "\t\t" << *(m.first.first) << "\t<= ";
			for (auto& tve: m.second)
				cout << *tve << ", ";
			cout << endl;
		}
	}
#endif
}

void STRUCTURE_ANALYSIS::fill_compares()
{
	for (auto& m: fAppsW)
	{
		InstS& compareSet = m.second;
		if (compareSet.size() > 1)
			num_wapp++;
		for (auto& lhs: compareSet)
		{
			int lhsIdx = WireInst::as(lhs)->get_idx();
			for (auto& rhs: compareSet)
			{
				if (lhs != rhs)
				{
					if (wCompare[lhsIdx].find(rhs) == wCompare[lhsIdx].end())
						sz_wire_compare++;
					wCompare[lhsIdx].insert(rhs);
				}
			}
		}
	}

	for (auto& m: fApps)
	{
		InstS& compareSet = m.second;
		if (compareSet.size() > 1)
			num_fapp++;
		for (auto& lhs: compareSet)
		{
			if (lhs->get_type() == Num)
				continue;

			int lhsIdx = SigInst::as(lhs)->get_idx();
			for (auto& rhs: compareSet)
			{
				if (lhs != rhs)
				{
					if (rhs->get_type() == Num)
					{
						if (numCompare[lhsIdx].find(rhs) == numCompare[lhsIdx].end())
							sz_num_compare++;
						numCompare[lhsIdx].insert(rhs);
					}
					else
					{
						if (sigCompare[lhsIdx].find(rhs) == sigCompare[lhsIdx].end())
							sz_sig_compare++;
						sigCompare[lhsIdx].insert(rhs);
					}
				}
			}
		}
	}

	for (auto& m: fAppsParent)
	{
		InstS& compareSet = m.second;
		if (compareSet.size() > 1)
			num_common_fapp++;
		for (auto& lhs: compareSet)
		{
			assert (lhs->get_type() == Sig);

			int lhsIdx = SigInst::as(lhs)->get_idx();
			for (auto& rhs: compareSet)
			{
				if (lhs != rhs)
				{
					assert (rhs->get_type() == Sig);
					if (sigCompare[lhsIdx].find(rhs) == sigCompare[lhsIdx].end())
					{
						sz_sig_compare_common_fapp++;
						sz_sig_compare++;
					}
					sigCompare[lhsIdx].insert(rhs);
				}
			}
		}
	}

	for (auto& m: fAppsCommon)
	{
		InstS& compareSet = m.second;
		if (compareSet.size() > 1)
			num_common_node++;
		for (auto& lhs: compareSet)
		{
			assert (lhs->get_type() == Sig);

			int lhsIdx = SigInst::as(lhs)->get_idx();
			for (auto& rhs: compareSet)
			{
				if (lhs != rhs)
				{
					assert (rhs->get_type() == Sig);
					if (sigCompare[lhsIdx].find(rhs) == sigCompare[lhsIdx].end())
					{
						sz_sig_compare_common_nodes++;
						sz_sig_compare++;
					}
					sigCompare[lhsIdx].insert(rhs);
				}
			}
		}
	}
}

void STRUCTURE_ANALYSIS::check_further_compares()
{
//	map< int, InstToListM > controlMap;
	map< int, InstS > controlMap;
	for (auto& sig1: Inst::_s_reg)
	{
		if ((sig1->get_size() > 1))
		{
			bool done = false;
			for (auto& sig2: sigCompare[SigInst::as(sig1)->get_idx()])
			{
				if (SigInst::as(sig2)->is_pre_reg())
				{
					done = true;
					break;
				}
			}
			if (!done)
			{
				controlMap[sig1->get_size()].insert(sig1);
//
//				InstS& bcCone = Inst::_m_backward_coi[Inst::_m_pre_to_next[sig]];
//				InstL bcReg;
//				for (auto& bc: bcCone)
//				{
//					if (bc->get_size() > 1 && SigInst::as(bc)->is_pre_reg())
//						bcReg.push_back(bc);
//				}
//				controlMap[sig->get_size()].insert(make_pair(sig, bcReg));
			}
		}
	}

	for (auto& m: controlMap)
	{
		for (auto sit1 = m.second.begin(); sit1 != m.second.end(); sit1++)
		{
			Inst* sig1 = (*sit1);
			auto sit2 = sit1;
			sit2++;
			for (; sit2 != m.second.end(); sit2++)
			{
				Inst* sig2 = (*sit2);
				cout << "\t(relevant: " << *sig1 << " and " << *sig2 << ")" << endl;
				sigCompare[SigInst::as(sig1)->get_idx()].insert(sig2);
				sigCompare[SigInst::as(sig2)->get_idx()].insert(sig1);
			}
		}
	}

//	for (auto& m: controlMap)
//	{
////		cout << m.first << "\t<= " << m.second << endl;
//		for (auto sit1 = m.second.begin(); sit1 != m.second.end(); sit1++)
//		{
//			Inst* sig1 = (*sit1).first;
//			InstL& bCone1 = (*sit1).second;
//
//			auto sit2 = sit1;
//			sit2++;
//			for (; sit2 != m.second.end(); sit2++)
//			{
//				Inst* sig2 = (*sit2).first;
//				InstL& bCone2 = (*sit2).second;
//
//				if (relevant(sig1, sig2))
//					continue;
//
//				bool rel = true;
//				for (auto& lhs: bCone1)
//				{
//					bool misMatch = false;
//					for (auto& rhs: bCone2)
//					{
//						if (lhs != rhs)
//						{
//							if ((lhs != sig1) && (rhs != sig2))
//							{
//								if (lhs->get_size() == rhs->get_size())
//								{
//									if (irrelevant(lhs, rhs))
//										misMatch = true;
//								}
//							}
//						}
//					}
//					if (misMatch)
//					{
//						cout << "\t(irrelevant due to no companion for " << *lhs << " in " << *sig1 << ")" << endl;
//						rel = false;
//						break;
//					}
//				}
//				if (rel)
//				{
//					cout << "\t(relevant: " << *sig1 << " and " << *sig2 << ")" << endl;
//					sigCompare[SigInst::as(sig1)->get_idx()].insert(sig2);
//					sigCompare[SigInst::as(sig2)->get_idx()].insert(sig1);
//				}
//			}
//		}
//	}
}

void STRUCTURE_ANALYSIS::print_compares(int loc, int level)
{
	AVR_LOG(loc, level, "\t(regs)"  << endl);
	for (auto& lhs: Inst::_s_reg)
	{
		int idx = get_idx(lhs);
		if (!(sigCompare[idx].empty()))
		{
			cout << "\t\t[" << *lhs << "]\t=> ";
			for (InstS::iterator sit = sigCompare[idx].begin(); sit != sigCompare[idx].end(); sit++)
				cout << *(*sit) << ", ";
			cout << endl;
		}
	}

	AVR_LOG(loc, level, "\t(inps)"  << endl);
	for (auto& lhs: Inst::_s_inp)
	{
		int idx = get_idx(lhs);
		if (!(sigCompare[idx].empty()))
		{
			cout << "\t\t[" << *lhs << "]\t=> ";
			for (InstS::iterator sit = sigCompare[idx].begin(); sit != sigCompare[idx].end(); sit++)
				cout << *(*sit) << ", ";
			cout << endl;
		}
	}

	AVR_LOG(loc, level, "\t(num)"  << endl);
	for (int i = 0; i< numCompare.size(); i++)
	{
		if (!numCompare[i].empty())
		{
			cout << "\t\t" << *(_idxHash[i]) << "\t=> ";
			for (auto& rhs: numCompare[i])
				cout << *rhs << ", ";
			cout << endl;
		}
	}

//	AVR_LOG(loc, level, "\t(wir)"  << endl);
//	for (int i = 0; i< wCompare.size(); i++)
//	{
//		if (!wCompare[i].empty())
//		{
//			cout << "\t\t" << *(_wIdxHash[i]) << "\t=> ";
//			for (auto& rhs: wCompare[i])
//				cout << *rhs << ", ";
//			cout << endl;
//		}
//	}
}

set<int> tmpS;
bool STRUCTURE_ANALYSIS::relevant(Inst* lhs_orig, Inst* rhs_orig)
{
	set<int>::iterator sit = tmpS.find(lhs_orig->get_type());
	if (sit == tmpS.end()) {
		tmpS.insert(lhs_orig->get_type());
		cout << "tmpS: " << lhs_orig->get_type() << endl;
	}
	sit = tmpS.find(rhs_orig->get_type());
	if (sit == tmpS.end()) {
		tmpS.insert(rhs_orig->get_type());
		cout << "tmpS: " << rhs_orig->get_type() << endl;
	}

//	cout << *lhs_orig << " ?= " << *rhs_orig << endl;
//	return false;

	Inst* lhs = lhs_orig;
	Inst* rhs = rhs_orig;

	OpInst* opL = OpInst::as(lhs);
	if (opL) {
		Inst* wL = opL->get_wire();
		if (wL == NULL)
			return false;
		else
			lhs = wL;
	}

	OpInst* opR = OpInst::as(rhs);
	if (opR) {
		Inst* wR = opR->get_wire();
		if (wR == NULL)
			return false;
		else
			rhs = wR;
	}

	SigInst* sig1 = SigInst::as(lhs);
	bool result;
	if (!sig1)
	{
		if (lhs->get_type() != Wire) {
			return false;
		}
		if (rhs->get_type() != Wire) {
			return false;
		}

		assert(lhs->get_type() == Wire);

		if (lhs->find_next())
		{
			lhs = Inst::_m_next_wire_pre[lhs];
			assert(rhs->find_next());
			rhs = Inst::_m_next_wire_pre[rhs];
		}
		assert (rhs->get_type() == Wire);

		WireInst* w1 = WireInst::as(lhs);
		assert(w1);

		int idx = w1->get_idx();
		if (idx >= wCompare.size())
			return false;
		result = (wCompare[w1->get_idx()].find(rhs) != wCompare[w1->get_idx()].end());
	}
	else
	{
		assert(sig1);
		if (lhs->find_next())
		{
			string str_lhs = sig1->get_name();
			string str_lhs_wo_next = str_lhs.substr(0, str_lhs.find_last_of('$'));
			lhs = SigInst::create(str_lhs_wo_next, lhs->get_size(), lhs->get_sort());
			sig1 = SigInst::as(lhs);

			if (rhs->get_type() == Sig)
			{
				string str_rhs = SigInst::as(rhs)->get_name();
				string str_rhs_wo_next = str_rhs.substr(0, str_rhs.find_last_of('$'));
				rhs = SigInst::create(str_rhs_wo_next, rhs->get_size(), rhs->get_sort());
			}
		}

		if (rhs->get_type() == Num)
		{
			result = (numCompare[sig1->get_idx()].find(rhs) != numCompare[sig1->get_idx()].end());
		}
		else if (rhs->get_type() == Sig)
		{
			result = (sigCompare[sig1->get_idx()].find(rhs) != sigCompare[sig1->get_idx()].end());
		}
	}

//	cout << "\t\t(" << *lhs_orig << " ?= " << *rhs_orig << ") is " << (result ? "relevant" : "irrelevant") << endl;
	return result;
}

void STRUCTURE_ANALYSIS::add_relevant(Inst* lhs_orig, Inst* rhs_orig)
{
	Inst* lhs = lhs_orig;
	Inst* rhs = rhs_orig;

	SigInst* sig1 = SigInst::as(lhs);
	if (!sig1)
	{
		assert(lhs->get_type() == Wire);
		if (lhs->find_next())
		{
			lhs = Inst::_m_next_wire_pre[lhs];
			assert(rhs->find_next());
			rhs = Inst::_m_next_wire_pre[rhs];
		}

		WireInst* w1 = WireInst::as(lhs);
		WireInst* w2 = WireInst::as(rhs);
		assert (w2);
		wCompare[w1->get_idx()].insert(rhs);
		wCompare[w2->get_idx()].insert(lhs);
	}
	else
	{
		assert(sig1);
		if (lhs->find_next())
		{
			string str_lhs = sig1->get_name();
			string str_lhs_wo_next = str_lhs.substr(0, str_lhs.find_last_of('$'));
			lhs = SigInst::create(str_lhs_wo_next, lhs->get_size(), lhs->get_sort());
			sig1 = SigInst::as(lhs);

			if (rhs->get_type() == Sig)
			{
				string str_rhs = SigInst::as(rhs)->get_name();
				string str_rhs_wo_next = str_rhs.substr(0, str_rhs.find_last_of('$'));
				rhs = SigInst::create(str_rhs_wo_next, rhs->get_size(), rhs->get_sort());
			}
		}

		if (rhs->get_type() == Num)
		{
			numCompare[sig1->get_idx()].insert(rhs);
		}
		else
		{
			SigInst* sig2 = SigInst::as(rhs);
			assert(sig2);
			sigCompare[sig1->get_idx()].insert(rhs);
			sigCompare[sig2->get_idx()].insert(lhs);
		}
	}

//	cout << "\t\t(adding) (" << *lhs_orig << " ?= " << *rhs_orig << ") as relevant" << endl;
}

int STRUCTURE_ANALYSIS::add_preds(InstS& conditions_pre) {
	return 0;

	int numAdded = 0;

	cout << "\t  (added preds)"  << endl;
	for (auto& m: fApps)
	{
		if (m.second.size() == 2)
		{
			InstS::const_iterator sit = m.second.begin();
			Inst* lhs = (*sit);
			sit++;
			for (; sit != m.second.end(); sit++) {
				Inst* rhs = (*sit);
				if ((lhs->get_type() == Sig) && (rhs->get_type() == Sig)) {
					if (Inst::_s_reg.count(lhs) && Inst::_s_reg.count(rhs)) {
						Inst* eq = OpInst::create(OpInst::Eq, lhs, rhs);
						if (conditions_pre.find(eq) == conditions_pre.end()) {
							conditions_pre.insert(eq);
							numAdded++;
							cout << "\t  \t" << *eq  << endl;
						}
					}
				}
			}
		}
	}
	cout << "\t   #" << numAdded  << endl;

	return numAdded;
}


#endif
}






