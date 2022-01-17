/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


/*
 * reach_cex.h
 *
 *  Created on: Sep 21, 2018
 *      Author: rock
 */

#ifndef SRC_REACH_REACH_CEX_H_
#define SRC_REACH_REACH_CEX_H_

#include "avr_util.h"
#include "avr_word_netlist.h"

namespace reach
{

class CEX_NODE {
public:
	int step;
	Inst* input;
	Inst* constant;
	bool isinput;

	CEX_NODE() {
		step = -1;
		input = NULL;
		constant = NULL;
		isinput = false;
	}
};

class CEX {
public:
	CEX() {
		backward = true;
	}

	static InstToIntM m_instId;
	void add (int st, Inst* inp, Inst* con, bool isinput);
	void reset ();
	void print (ofstream& out, int length, InstL& propList);
	void process_step (ofstream& out, InstToMpzM& m, int idx, bool isinput);
	string get_string (Inst* lhs, mpz_class& val);
	void str_extend (string& s, int sz);
	int get_id(Inst* v);
	bool is_input(Inst* v);
	int get_bad_id(InstL& propList);
	bool is_failing(Inst* p, int valrhs);
	int get_bad_id(Inst* p);

	bool backward;
	list < CEX_NODE > cex;
private:
};



}




#endif /* SRC_REACH_REACH_CEX_H_ */
