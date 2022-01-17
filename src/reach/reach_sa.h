/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


/*
 * reach_sa.h
 *
 *  Created on: Nov 15, 2017
 *      Author: rock
 */

#ifndef SRC_REACH_REACH_SA_H_
#define SRC_REACH_REACH_SA_H_

#include "avr_util.h"
#include "avr_word_netlist.h"

#define PREFIX "utt"

namespace reach
{
#ifdef STRUCTURAL_PROJECTION

#define SA_WAPPS
//#define SA_COMMON_NODES
//#define SA_COMMON_FAPPS

typedef map< pair< Inst*, int >, InstS, compare_pair_int> PairIntToSetM;

class STRUCTURE_ANALYSIS
{
public:
	STRUCTURE_ANALYSIS()
	{

	}

	~STRUCTURE_ANALYSIS()
	{

	}


	/// Functions
	void start(Inst* iC, Inst* pC, InstS& aC, string message = "");
	bool relevant(Inst* lhs, Inst* rhs);
	bool irrelevant(Inst* lhs, Inst* rhs)
	{
		return !(relevant(lhs, rhs));
	}
	void add_relevant(Inst* lhs, Inst* rhs);
	int add_preds(InstS& conditions_pre);

//	int num_fapps() 	   {	return fApps.size();		}
//	int num_fapps_parent() {	return fAppsParent.size();	}
//	int num_wapps() 	   {	return fAppsW.size();		}
//	int num_fapps_common() {	return fAppsCommon.size();	}

	static long long sz_sig_compare;
	static long long sz_num_compare;
	static long long sz_wire_compare;

	static long long sz_sig_compare_common_nodes;
	static long long sz_sig_compare_common_fapp;

	static int num_fapp;
	static int num_common_fapp;
	static int num_common_node;
	static int num_wapp;

private:
	void init();
	void get_fapps(Inst* top, Inst* parent, string s = "");
	void fill_compares();
	void check_further_compares();
	void print_fapps();
	void print_compares(int loc, int level);

	int get_idx(Inst* sig)
	{
		assert(sig->get_type() == Sig);
		int idx = SigInst::as(sig)->get_idx();
		if (idx == -1)
		{
			cout << "error: " << *sig << endl;
			int count = 0;
			for (auto& c: _idxHash)
				cout << count++ << "\t" << *c << endl;
		}
		assert(idx != -1);
		return idx;
	}

	/// Variables
	PairIntToSetM fAppsCommon;
	map< string, InstS > fAppsParent;
	map< string, InstS > fApps;
	vector< InstS > numCompare;
	vector< InstS > sigCompare;

	map< string, InstS > fAppsW;
	vector< InstS > wCompare;
//	vector< InstS > nwCompare;
};

#endif

}

#endif /* SRC_REACH_REACH_SA_H_ */
