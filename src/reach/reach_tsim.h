/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


/*
 * reach_tsim.h
 *
 *  Created on: Apr 11, 2018
 *      Author: rock
 */

#ifndef SRC_REACH_REACH_TSIM_H_
#define SRC_REACH_REACH_TSIM_H_

#include "avr_util.h"
#include "avr_word_netlist.h"

namespace reach
{

class TERNARY_SIM {
public:

  TERNARY_SIM() {
    tsim_key = -1;
  }

  void ternary_sim (InstL& input, InstL& original, Inst* dest);


private:
  int tsim_key;

  void tsim_set (InstL& input);
  void tsim_inc_key ();
  int tsim_evaluate (Inst* in);

  int tsim_not( int Value );
  int tsim_and( int n, int *Value );
  int tsim_or ( int n, int *Value );
  int tsim_eq ( int n, int *Value );
  int tsim_neq( int n, int *Value );
  int tsim_ite( int n, int *Value );
};




}




#endif /* SRC_REACH_REACH_TSIM_H_ */
