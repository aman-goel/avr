/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


/*
 * reach_tsim.cpp
 *
 *  Created on: Apr 11, 2018
 *      Author: rock
 */
#include "reach_tsim.h"
#include <execinfo.h> // to dump call stacks (backtrace, backtrace_symbols)

namespace reach
{

#define AVR_ZER  0
#define AVR_ONE  1
#define AVR_UND -1

int TERNARY_SIM::tsim_not( int Value )
{
    if ( Value == AVR_ZER )
        return AVR_ONE;
    else if ( Value == AVR_ONE )
        return AVR_ZER;
    return AVR_UND;
}

int TERNARY_SIM::tsim_and( int n, int *Value )
{
  bool all_one = true;
  for (int i = 0; i < n; i++) {
    if (Value[i] == AVR_ZER)
      return AVR_ZER;
    else if (Value[i] == AVR_UND)
      all_one = false;
  }
  return (all_one ? AVR_ONE : AVR_UND);
}

int TERNARY_SIM::tsim_or( int n, int *Value )
{
  bool all_zero = true;
  for (int i = 0; i < n; i++) {
    if (Value[i] == AVR_ONE)
      return AVR_ONE;
    else if (Value[i] == AVR_UND)
      all_zero = false;
  }
  return (all_zero ? AVR_ZER : AVR_UND);
}

int TERNARY_SIM::tsim_eq( int n, int *Value )
{
  assert(n == 2);
  if ( Value[0] != AVR_UND && Value[1] != AVR_UND )
    return (Value[0] == Value[1]) ? AVR_ONE : AVR_ZER;
  return AVR_UND;
}

int TERNARY_SIM::tsim_neq( int n, int *Value )
{
  assert(n == 2);
  if ( Value[0] != AVR_UND && Value[1] != AVR_UND )
    return (Value[0] != Value[1]) ? AVR_ONE : AVR_ZER;
  return AVR_UND;
}

int TERNARY_SIM::tsim_ite( int n, int *Value )
{
  assert(n == 3);
  if ( Value[0] == AVR_ONE )
    return Value[1];
  else if ( Value[0] == AVR_ZER )
    return Value[2];
  else if ( Value[1] == Value[2] )
    return Value[1];
  return AVR_UND;
}

int TERNARY_SIM::tsim_evaluate(Inst* top) {
  int val = AVR_UND;

  if (top->get_tsim_key() == tsim_key)
    val = top->get_tsim_val(tsim_key);
  else {
    const InstL* ch = top->get_children();
    int sz = ch ? ch->size() : 0;
    int value[sz];

    if (ch) {
      int i = 0;
      for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it)
        value[i++] = tsim_evaluate(*it);
    }

    switch (top->get_type()) {
    case Sig:
      if (top->find_next()) {
        InstToPairBoolM::iterator mit = Inst::_m_sn.find(top);
        if (Inst::has_trelation(top)) {
      		// TODO: trel: resolve
          val = tsim_evaluate((*mit).second.first);
          top->set_tsim_val(val);
        }
        else {
          val = AVR_UND;
          top->set_tsim_val(val);
          AVR_LOG(18, 0, "\t" << *top << " v: " << val << endl);
        }
      }
      else
        val = top->get_tsim_val(tsim_key);
      break;
    case Num:
      switch (NumInst::as(top)->get_num()) {
      case 0:
        val = AVR_ZER;
        top->set_tsim_val(AVR_ZER);
        break;
      case 1:
        val = AVR_ONE;
        top->set_tsim_val(AVR_ONE);
        break;
      default:
        AVR_LOG(18, 0, "(error: unexpected number during evaluate for " << *top << ")\n");
        assert(0);
      }
      break;
    case Wire:
      val = value[0];
      top->set_tsim_val(val);
      break;
    case Op:
      switch(OpInst::as(top)->get_op()) {
      case OpInst::LogNot:
        val = tsim_not(value[0]);
        top->set_tsim_val(val);
        break;
      case OpInst::LogAnd:
        val = tsim_and(sz, value);
        top->set_tsim_val(val);
        break;
      case OpInst::LogOr:
        val = tsim_or(sz, value);
        top->set_tsim_val(val);
        break;
      case OpInst::Eq:
        val = tsim_eq(sz, value);
        top->set_tsim_val(val);
        break;
      case OpInst::NotEq:
        val = tsim_neq(sz, value);
        top->set_tsim_val(val);
        break;
      case OpInst::Ternary:
        val = tsim_ite(sz, value);
        top->set_tsim_val(val);
        break;
      default:
          AVR_LOG(18, 0, "(error: unexpected operation during evaluate for " << *top << ")\n");
          assert(0);
        }
      break;
    default:
        AVR_LOG(18, 0, "(error: unexpected type during evaluate for " << *top << ")\n");
        assert(0);
    }
  }
//  if (top->find_next())
//    AVR_LOG(18, 0, "\t" << *top << " v: " << val << endl);
//  AVR_LOG(18, 6, *top << " v: " << val << endl);
  return val;
}

void TERNARY_SIM::tsim_inc_key() {
  Inst::inc_tsim_key();
  tsim_key = Inst::tsim_key();
}

void TERNARY_SIM::tsim_set (InstL& input) {
  for (auto& inp: input) {
    assert(inp->get_size() == 1);
    switch (inp->get_type()) {
    case Sig:
      inp->set_tsim_val(AVR_ONE);
      break;
    case Op: {
      OpInst* op = OpInst::as(inp);
      if (op->get_op() == OpInst::LogNot) {
        Inst* ch1 = op->get_children()->front();
        if (ch1->get_type() == Sig)
          ch1->set_tsim_val(AVR_ZER);
        else {
          AVR_LOG(18, 0, "(error: expected sig type with operation ! for " << *inp << ")\n");
          assert(0);
        }
      }
      else {
        AVR_LOG(18, 0, "(error: operation not allowed for " << *inp << ")\n");
        assert(0);
      }
    }
      break;
    case Ex:
    case Num:
    case Wire:
    default:
      AVR_LOG(18, 0, "(error: type not allowed for " << *inp << ")\n");
      assert(0);
    }
  }
}

void TERNARY_SIM::ternary_sim (InstL& inputs, InstL& original, Inst* dest) {
  InstL expanded;
  int sz = original.size();

  AVR_LOG(18, 0, "dest: " << *dest << endl);
  AVR_LOG(18, 0, "original: #" << sz << " " << original << endl);
  AVR_LOG(18, 0, "inputs:   #" << inputs.size() << " " << inputs << endl);
  tsim_inc_key();
  tsim_set(inputs);
  tsim_set(original);
  int val = tsim_evaluate(dest);
  assert(val == AVR_ONE);
  while (!original.empty()) {
    Inst* curr = original.back();
    AVR_LOG(18, 2, "trying removing: " << *curr << endl);
    original.pop_back();
    tsim_inc_key();
    tsim_set(inputs);
    tsim_set(original);
    val = tsim_evaluate(dest);
    if (val == AVR_ONE) {
      AVR_LOG(18, 0, "removed: " << *curr << endl);
    }
    else if (val == AVR_UND) {
      expanded.push_front(curr);
    }
    else
      assert(val == AVR_ZER);
  }
  if (sz != expanded.size()) {
    AVR_LOG(18, 0, "expanded: #" << sz << " -> #" << expanded.size() << " " << expanded << endl);
  }
  expanded.swap(original);
}




}



