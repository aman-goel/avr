/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


/*
 * reach_bmc.h
 *
 *  Created on: Oct 10, 2019
 *      Author: rock
 */

#ifndef SRC_REACH_REACH_BMC_H_
#define SRC_REACH_REACH_BMC_H_


#include "avr_util.h"
#include "avr_word_netlist.h"

namespace reach
{

#define BMC_ABSTRACT

class BMC {
public:
	int safe_bound;
	Inst* dest;
	Solver* solv_c;

#ifdef BMC_ABSTRACT
	Solver* solv_a;
	bool use_abstract;
#endif

private:

};


}


#endif /* SRC_REACH_REACH_BMC_H_ */
