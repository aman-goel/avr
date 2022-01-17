/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


/*
 * reach_bool.h
 *
 *  Created on: Jan 13, 2020
 *      Author: rock
 */

#ifndef SRC_REACH_REACH_BOOL_H_
#define SRC_REACH_REACH_BOOL_H_

#include "avr_word_netlist.h"

//class BoolNode {
//public:
//	Inst* wnode;						// corresponding word node
//	vector< int > bnode;
//
//	BoolNode(Inst* wn = NULL) {
//		wnode = wn;
//		bnode.clear();
//	}
//};
//
//class BoolNet {
//public:
//	vector< pair<Inst*, int> > var2Inst;
//
//	BoolNode& convert_w2b(Inst* node) {
//
//	}
//
//	void inline convert_ivar(Inst* node) {
//		BoolNode bn;
//		bn.wnode = node;
//		for (int i = 0; i < node->get_size(); i++)
//			bn.bnode.push_back(add_variable(node, i));
//
//		return
//		assert(i < node->get_size());
//		var2Inst.push_back(make_pair(node, i));
//	}
//
//	int add_variable(Inst* node, int i) {
//		assert(i < node->get_size());
//		var2Inst.push_back(make_pair(node, i));
//		return var2Inst.size();
//	}
//};



#endif /* SRC_REACH_REACH_BOOL_H_ */
