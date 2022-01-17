/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


/*
 * reach_coi.cpp
 *
 *  Created on: Jun 14, 2018
 *      Author: rock
 */

#include "reach_core.h"
#include <execinfo.h> // to dump call stacks (backtrace, backtrace_symbols)

namespace reach
{

Inst* Reach::try_wired_form(Inst* e) {
  OpInst* op = OpInst::as(e);
  if (op) {
    Inst* w = op->get_wire();
    if (w) {
//      cout << "(" << *e << " is " << *w << ")" << endl;
      return w;
    }

    Inst* n_e = OpInst::create(OpInst::LogNot, e);
    OpInst* n_op = OpInst::as(n_e);
    if (n_op) {
      Inst* n_w = n_op->get_wire();
      if (n_w) {
        Inst* tmp = OpInst::create(OpInst::LogNot, n_w);
//        cout << "(" << *e << " is " << *tmp << ")" << endl;
        return tmp;
      }
    }
  }
  return e;
}

#ifdef	FIND_SUB_EXPRESSION
void Reach::COI_generalize(Inst*e, EVAL& s)
{
  _trace_depth++;
  assert(e != 0);
  if (e->get_visit()) {
    _trace_depth--;
    return;
  }
  e->set_visit();

#ifdef DRAW_TRANSITION
  e->set_drVal(1);
#endif

  AVR_LOG(9, 1, "[COI]: (entry) " << *e << endl);

  e->acex_coi = e;
  e->subs_coi = e;
  pair< Inst*, Inst* > reduced;

  bool isPred = false;
  bool update = false;
  InstL childList;
  bool update_sub = false;
  InstL childList_sub;
  switch (e->get_type()) {
  case Sig: {
    if (e->find_next()) {
      InstToInstM::iterator mit = Inst::_m_sn.find(e);
      if (mit != Inst::_m_sn.end()) {
        s.relevantSet->insert(e);
//        COI_generalize((*mit).second, s);
      }
      else if (e != _ve_prop_next_eq_1)
        s.relevantInp->insert(e);
      isPred = (e->get_size() == 1) && (e != _ve_prop_next_eq_1);
    }
    else {
      if (Inst::_s_reg.find(e) != Inst::_s_reg.end())
        s.relevantSet->insert(e);
      else if (e != _ve_prop_eq_1)
        s.relevantInp->insert(e);
      isPred = (e->get_size() == 1) && (e != _ve_prop_eq_1);
    }
  }
  break;
  case Wire: {
    WireInst* w = WireInst::as(e);
    Inst* port = w->get_port();
    COI_generalize(port, s);
    e->subs_coi = port->subs_coi;
    if (port->acex_coi != port) {
      e->acex_coi = port->acex_coi;
//      update = true;
//      childList.push_back(port->acex_coi);
    }

    if (is_next_wire(w))
      s.bins->relevantWiresNext.push_back(w);
    else
      s.bins->relevantWires.push_back(w);
  }
  break;
  case Const: {
    assert(0);
  }
  break;
  case Num: {
    if (NumInst::as(e)->fromSystem())
      s.relevantConst->insert(e);
  }
  break;
  case Ex:
  case Op: {
    OpInst* op = OpInst::as(e);
    assert(op != 0);
    const InstL* ch = e->get_children();

    OpInst::OpType opT = op->get_op();

    if (opT == OpInst::Ternary) {
      assert(ch != 0);
      InstL::const_iterator it = ch->begin();

      Inst* if_e = *(it++);
      Inst* then_e = *(it++);
      Inst* else_e = *(it++);
      COI_generalize(if_e, s);

      int ifVal = if_e->get_bval();
      if (ifVal == 0) {
        COI_generalize(else_e, s);
        e->subs_coi = else_e->subs_coi;
        e->acex_coi = else_e->acex_coi;
      }
      else if (ifVal == 1) {
        COI_generalize(then_e, s);
        e->subs_coi = then_e->subs_coi;
        e->acex_coi = then_e->acex_coi;
      }
      else
        assert(0);

      Inst* w = op->get_wire();
      if (!w)
        cout << "\t(error: missing wire)\t" << *op << endl;
      assert(w);
      reduced.first = w;
      reduced.second = e->acex_coi;

      if (e->get_size() == 1) {
        int eVal = e->get_bval();
        assert(eVal != INVALID_SVAL);
        e->subs_coi = NumInst::create(eVal, 1);
      }
    }
    else if (opT == OpInst::LogNot) {
      assert(ch != 0);
      Inst* child = ch->front();
      COI_generalize(child, s);

      assert (e->get_size() == 1);
      int eVal = e->get_bval();
      assert(eVal != INVALID_SVAL);
      e->subs_coi = NumInst::create(eVal, 1);

//      if (child != child->acex_coi) {
//        update = true;
//        childList.push_back(child->acex_coi);
//      }
    }
    else if (opT == OpInst::LogAnd || opT == OpInst::LogOr) {
      int eVal = e->get_bval();
      assert(eVal != INVALID_SVAL);

      if (eVal == controlling(opT)) {
        for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it) {
          int itVal = (*it)->get_bval();
          if (itVal == controlling(opT)) {
            COI_generalize(*it, s);
            e->acex_coi = (*it)->acex_coi;

            Inst* w = op->get_wire();
            if (!w)
              cout << "\t(error: missing wire)\t" << *op << endl;
            assert(w);
            reduced.first = w;
            reduced.second = e->acex_coi;
            break;
          }
        }
      }
      else {
        InstS children;
        for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it) {
          COI_generalize(*it, s);
//          if ((*it) != (*it)->acex_coi)
//            update = true;
//          if (children.find((*it)->acex_coi) == children.end()) {
//            children.insert((*it)->acex_coi);
//            childList.push_back((*it)->acex_coi);
//          }
        }

      }

      assert (e->get_size() == 1);
      assert(eVal != INVALID_SVAL);
      e->subs_coi = NumInst::create(eVal, 1);
    }
    else if (opT == OpInst::Eq || opT == OpInst::NotEq) {
      Inst* lhs = ch->front();
      Inst* rhs = ch->back();

      COI_generalize(lhs, s);
      COI_generalize(rhs, s);

      update_sub = true;
      childList_sub.push_back(lhs->subs_coi);
      childList_sub.push_back(rhs->subs_coi);
      if (lhs != lhs->acex_coi || rhs != rhs->acex_coi) {
        update = true;
        childList.push_back(lhs->acex_coi);
        childList.push_back(rhs->acex_coi);
      }

      if (lhs->get_size() != 1) {
        if (lhs->get_type() != Sig && lhs->get_type() != Num)
          isPred = true;
        else if (rhs->get_type() != Sig && rhs->get_type() != Num)
          isPred = true;
      }
    }
    else {
      string ufType = op->get_euf_func_name();
      if (ufType == "0")
        cout << "\t(error: unexpected uf type)\t" << *e << endl;
      assert (ufType != "0");
      s.relevantUFtype->insert(ufType);

      for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it) {
        COI_generalize(*it, s);
        update_sub = true;
        childList_sub.push_back((*it)->subs_coi);

//        if ((*it) != (*it)->acex_coi)
//          update = true;
//        childList.push_back((*it)->acex_coi);

        isPred = (e->get_size() == 1);
      }
    }
  }
    break;
  case UF:
  case Mem:
  default:
    assert(0);
  }

  if (update_sub)
    e->subs_coi = e->apply_children(childList_sub);
  if (update)
    e->acex_coi = e->apply_children(childList);

  if (e->get_size() == 1) {
    int eVal = e->get_bval();
    assert(eVal != INVALID_SVAL);

    int eaVal = e->acex_coi->get_bval();
    int eaValSub = e->subs_coi->get_bval();
    if (eaValSub != INVALID_SVAL) {
      if (eaValSub != eVal) {
        cout << "newCh: " << childList_sub << endl;
        cout << "e      : " << *e << " (val: " << eVal << ")" << endl;
        cout << "e->subs_coi: " << *(e->subs_coi) << " (val: " << eaValSub << ")" << endl;
      }
      assert(eaValSub == eVal);
    }
    else {
      e->subs_coi->set_bval(eVal);
      eaValSub = eVal;
    }

    if (eaVal != INVALID_SVAL) {
      if (eaVal != eVal) {
        cout << "newCh: " << childList << endl;
        cout << "e      : " << *e << " (val: " << eVal << ")" << endl;
        cout << "e->acex_coi: " << *(e->acex_coi) << " (val: " << eaVal << ")" << endl;
      }
      assert(eaValSub == eVal);
    }
    else {
      e->acex_coi->set_bval(eVal);
      eaVal = eVal;
    }

    if (eaVal != eaValSub) {
      AVR_LOG(9, 0, "[COI] e: " << *e << " -> " << *(e->acex_coi) << " (i.e. " << *(e->subs_coi) << ")" << endl);
      AVR_LOG(9, 0, "[COI] e:  " << e->get_bval() << " " << eVal << endl);
      AVR_LOG(9, 0, "[COI] eA: " << e->acex_coi->get_bval() << " " << eaVal << endl);
      AVR_LOG(9, 0, "[COI] eS: " << e->subs_coi->get_bval() << " " << eaValSub << endl);
    }
  }
  else {
    mpz_class* eVal = e->get_ival();
    assert(eVal != INVALID_SMPZ);

    mpz_class* eaVal = e->acex_coi->get_ival();
    mpz_class* eaValSub = e->subs_coi->get_ival();
    if (eaValSub != INVALID_SMPZ) {
      if (*eaValSub != *eVal) {
        cout << "newCh: " << childList_sub << endl;
        cout << "e : " << *e << " (val: " << *eVal << ")" << endl;
        cout << "eS: " << *(e->subs_coi) << " (val: " << *eaValSub << ")" << endl;
      }
      assert(*eaValSub == *eVal);
    }
    else {
      e->subs_coi->set_ival(eVal);
      eaValSub = eVal;
    }

    if (eaVal != INVALID_SMPZ) {
      if (*eaVal != *eVal) {
        cout << "newCh: " << childList << endl;
        cout << "e : " << *e << " (val: " << *eVal << ")" << endl;
        cout << "eA: " << *(e->acex_coi) << " (val: " << *eaVal << ")" << endl;
      }
      assert(*eaValSub == *eVal);
    }
    else {
      e->acex_coi->set_ival(eVal);
      eaVal = eVal;
    }

    if (*eaVal != *eaValSub) {
      AVR_LOG(9, 0, "[COI] e : " << *e << " -> " << *(e->acex_coi) << " (i.e. " << *(e->subs_coi) << ")" << endl);
      AVR_LOG(9, 0, "[COI] e : " << *e->get_ival() << " " << *eVal << endl);
      AVR_LOG(9, 0, "[COI] eA: " << *e->acex_coi->get_ival() << " " << *eaVal << endl);
      AVR_LOG(9, 0, "[COI] eS: " << *e->subs_coi->get_ival() << " " << *eaValSub << endl);
    }
  }

  if (reduced.first) {
    assert(reduced.second);
  }

  if (isPred) {
    Inst* tveCc = e;
    if (tveCc->get_bval() == 0)
      tveCc = OpInst::create(OpInst::LogNot, tveCc);
    if (!is_redundant(tveCc)) {
      tveCc = try_wired_form(tveCc);
      if (tveCc->find_next())
        s.bins->nextStateConstraints.push_back(tveCc);
      else
        s.bins->concreteConstraints.push_back(tveCc);
    }

    Inst* tve = e->acex_coi;
    tve = try_wired_form(tve);
    if (tve->get_bval() == 0)
      tve = OpInst::create(OpInst::LogNot, tve);
    if (!is_redundant(tve) && !find_input(tve)) {
      if (tve->find_next()) {
//        s.bins->nextStateConstraints.push_back(tve);
      }
      else
        s.bins->mainConstraints.push_back(tve);
    }

    Inst* tveSub = e->subs_coi;
    if (tveSub->get_bval() == 0)
      tveSub = OpInst::create(OpInst::LogNot, tveSub);
    if (!is_redundant(tveSub)) {
      if (tveSub->find_next())
        s.bins->nextStateSubConstraints.push_back(tveSub);
      else
        s.bins->mainSubConstraints.push_back(tveSub);
    }
  }

  AVR_LOG(9, 1, "[COI]: (leave) e: " << *e << " -> " << *(e->acex_coi) << " (i.e. " << *(e->subs_coi) << ")" << endl);
  _trace_depth--;
}

void Reach::COI_generalize_sim(Inst*e, SIMULATION_POSITION& pre, SIMULATION_POSITION& next)
{
  _simeval_depth++;
  assert(e != 0);
  if (e->get_visit()) {
    _simeval_depth++;
    return;
  }
  e->set_visit();

//#ifdef DRAW_TRANSITION
//  e->set_drVal(1);
//#endif

  AVR_LOG(14, 6, "[COI_sim]: (entry) " << *e << endl);

  e->subs_coi = e;
  pair< Inst*, Inst* > reduced;

  bool isPred = false;
  InstL childList;
  bool update_sub = false;
  InstL childList_sub;
  switch (e->get_type()) {
  case Sig: {
    if (e->find_next()) {
      if (Inst::_m_sn.find(e) == Inst::_m_sn.end()) {
        AVR_LOG(15, 0, "\t(error: unexpected term)\t" << *e << endl);
      }
      assert(Inst::_m_sn.find(e) != Inst::_m_sn.end());
    }
    else {
      InstToInstM::iterator vit = pre.val.find(e);
      if (vit != pre.val.end()) {
        e->subs_coi = (*vit).second;
      }
      else {
        InstToInstM::iterator nit = next.inp2Const.find(e);
        if (nit != next.inp2Const.end()) {
          e->subs_coi = (*nit).second;
        }
        else if (Inst::_s_inp.find(e) != Inst::_s_inp.end()) {
          stringstream cName;
          int sz = e->get_size();
          cName << sz << "'d*_" << ConstInst::hm_ConstInst.size();
          e->subs_coi = ConstInst::create(cName.str(), sz, e, pre.sIdx);
          /// Aman TODO: Optimize here
          next.inp2Const[e] = e->subs_coi;
        }
        else {
          AVR_LOG(15, 0, "\t(error: unexpected term)\t" << *e << endl);
          assert(0);
        }
      }
    }

    isPred = (e->get_size() == 1);
  }
  break;
  case Wire: {
    WireInst* w = WireInst::as(e);
    if (w->is_connected(WireInst::get_connect_key())) {
      Inst* port = w->get_port();
      COI_generalize_sim(port, pre, next);
        e->subs_coi = port->subs_coi;
    }
  }
  break;
  case Const: {

    isPred = (e->get_size() == 1);
  }
  break;
  case Num: {
  }
  break;
  case Ex:
  case Op: {
    OpInst* op = OpInst::as(e);
    assert(op != 0);
    const InstL* ch = e->get_children();

    OpInst::OpType opT = op->get_op();

    if (opT == OpInst::Ternary) {
      assert(ch != 0);
      InstL::const_iterator it = ch->begin();

      Inst* if_e = *(it++);
      Inst* then_e = *(it++);
      Inst* else_e = *(it++);
      COI_generalize_sim(if_e, pre, next);

      int ifVal = if_e->get_bval();
      if (ifVal == 0) {
        COI_generalize_sim(else_e, pre, next);
        e->subs_coi = else_e->subs_coi;
      }
      else if (ifVal == 1) {
        COI_generalize_sim(then_e, pre, next);
        e->subs_coi = then_e->subs_coi;
      }
      else
        assert(0);
    }
    else if (opT == OpInst::LogNot) {
      assert(ch != 0);
      Inst* child = ch->front();
      COI_generalize_sim(child, pre, next);

      assert (e->get_size() == 1);
      int eVal = e->get_bval();
      assert(eVal != INVALID_SVAL);
      e->subs_coi = NumInst::create(eVal, 1);
    }
    else if (opT == OpInst::LogAnd || opT == OpInst::LogOr) {
      int eVal = e->get_bval();
      assert(eVal != INVALID_SVAL);

      if (eVal == controlling(opT)) {
        for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it) {
          int itVal = (*it)->get_bval();
          if (itVal == controlling(opT)) {
            COI_generalize_sim(*it, pre, next);
            break;
          }
        }
      }
      else {
        InstS children;
        for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it) {
          COI_generalize_sim(*it, pre, next);
        }
      }

      assert (e->get_size() == 1);
      assert(eVal != INVALID_SVAL);
      e->subs_coi = NumInst::create(eVal, 1);
    }
    else if (opT == OpInst::Eq || opT == OpInst::NotEq) {
      Inst* lhs = ch->front();
      Inst* rhs = ch->back();

      COI_generalize_sim(lhs, pre, next);
      COI_generalize_sim(rhs, pre, next);

      update_sub = true;
      childList_sub.push_back(lhs->subs_coi);
      childList_sub.push_back(rhs->subs_coi);

      isPred = (lhs->get_size() == 1);
    }
    else {
      string ufType = op->get_euf_func_name();
      if (ufType == "0")
        cout << "\t(error: unexpected uf type)\t" << *e << endl;
      assert (ufType != "0");

      for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it) {
        COI_generalize_sim(*it, pre, next);
        update_sub = true;
        childList_sub.push_back((*it)->subs_coi);

        isPred = (e->get_size() == 1);
      }
    }
  }
    break;
  case UF:
  case Mem:
  default:
    assert(0);
  }

  if (update_sub)
    e->subs_coi = e->apply_children(childList_sub);

  if (e->get_size() == 1) {
    int eVal = e->get_bval();
    assert(eVal != INVALID_SVAL);

    int eaValSub = e->subs_coi->get_bval();
    if (eaValSub != INVALID_SVAL) {
      if (eaValSub != eVal) {
        cout << "newCh: " << childList_sub << endl;
        cout << "e      : " << *e << " (val: " << eVal << ")" << endl;
        cout << "e->subs_coi: " << *(e->subs_coi) << " (val: " << eaValSub << ")" << endl;
      }
      assert(eaValSub == eVal);
    }
    else {
      e->subs_coi->set_bval(eVal);
      eaValSub = eVal;
    }
  }
  else {
    mpz_class* eVal = e->get_ival();
    assert(eVal != INVALID_SMPZ);

    mpz_class* eaValSub = e->subs_coi->get_ival();
    if (eaValSub != INVALID_SMPZ) {
      if (*eaValSub != *eVal) {
        cout << "newCh: " << childList_sub << endl;
        cout << "e : " << *e << " (val: " << *eVal << ")" << endl;
        cout << "eS: " << *(e->subs_coi) << " (val: " << *eaValSub << ")" << endl;
      }
      assert(*eaValSub == *eVal);
    }
    else {
      e->subs_coi->set_ival(eVal);
      eaValSub = eVal;
    }
  }

  //TODO
  if (isPred) {
    Inst* tve = e->subs_coi;
    if (tve->get_bval() == 0)
      tve = OpInst::create(OpInst::LogNot, tve);
    if (!is_redundant(tve)) {
      if (tve->find_next()) {
        if (find_pre(tve)) {
          AVR_LOG(15, 0, "\t(error: unexpected relation with both pre & next)\t"
              << *tve << " (derived from " << *e << ")" << endl);
          cout << "find_pre: " << find_pre(tve) << endl;
          cout << "find_reg: " << find_reg(tve) << endl;
          cout << "find_inp: " << find_input(tve) << endl;
          assert(0);
        }

        Inst* tvePre = all_next2pre(tve);
        OpInst* opPre = OpInst::as(tvePre);
        if (opPre && opPre->get_op() == OpInst::Eq)
        {
          Inst* lhs = opPre->get_children()->front();
          Inst* rhs = opPre->get_children()->back();
          if (!SigInst::as(lhs))
          {
            assert (SigInst::as(rhs));
            /// Swap lhs and rhs
            swap(lhs, rhs);
          }

          /// TODO: Below search can be pushed inside the following if-if, when next.s not needed
          InstToInstM::iterator mit = Inst::_m_pre_to_next.find(lhs);
          assert(mit != Inst::_m_pre_to_next.end());
          Inst* sig = (*mit).second;

          mpz_class* sigVal = sig->get_ival();
          next.s[lhs] = (sigVal);

          OpInst* opRhs = OpInst::as(rhs);
          if (opRhs) {
            if (!rhs->childrenInfo[CONST]) {
              rhs = NumInst::create(*sigVal, sig->get_size());
              tvePre = OpInst::create(OpInst::Eq, lhs, rhs);
              AVR_LOG(14, 6, "(actual) Inserting in c$: " << *tvePre << " [@ " << _simeval_depth << " for " << *e << " ]" << endl);
            }
          }

          next.val[lhs] = rhs;
          next.sigs.insert(lhs);
          collect_constants(rhs, next.consts, true);
          AVR_LOG(14, 6, "Inserting in v$: " << *e->subs_coi << " [@ " << _simeval_depth << " for " << *e << " ]" << endl);
        }
        else {
          Inst* lhs;
          Inst* rhs;
          SigInst* sig = SigInst::as(tvePre);
          if (sig) {
            assert(sig->get_size() == 1);
            lhs = sig;
            rhs = NumInst::create(1, 1);
          }
          else {
            OpInst* op = OpInst::as(tvePre);
            assert(op);
            assert(op->get_op() == OpInst::LogNot);
            lhs = op->get_children()->front();
            assert(SigInst::as(lhs));
            rhs = NumInst::create(0, 1);
          }
          next.val[lhs] = rhs;
          next.s[lhs] = NumInst::as(rhs)->get_mpz();
          next.sigs.insert(lhs);

          AVR_LOG(14, 6, "Inserting in v$: " << *e->subs_coi << " [@ " << _simeval_depth << " for " << *e << " ]" << endl);
        }
      }
      else {
        Inst* newCondition = NULL;
        if (!e->subs_coi->childrenInfo[SIG]) {
          newCondition = e->subs_coi;
        }
        else if (find_limited_sigs(e->subs_coi, next.inp2Const)) {
          newCondition = replace_with_constant(e->subs_coi, next.inp2Const, pre.sIdx);
        }

        if (newCondition != NULL && newCondition->childrenInfo[CONST]) {
          next.cConditions.insert(newCondition);
          AVR_LOG(14, 6, "Inserting in c$: " << *e->subs_coi << " [@ " << _simeval_depth << " for " << *e << " ]" << endl);
        }
      }
    }
  }

  AVR_LOG(14, 6, "[COI_sim]: (leave) e: " << *e << " -> " << *(e->subs_coi) << endl);
  _simeval_depth--;
}
#endif

void Reach::simplify_solution2()
{
	WireInst::inc_slicekey();
	KEY_COI_VALUE::inc_project_key();
}

bool Reach::model_generalize2(Solver* solver, InstL& conjunct_q, MIN_TERM_ABSTRACT& m, InstS& relSig, InstS& relConst, set< string >& relUFtype, int mode)
{
	struct rusage usage;
	struct timeval start_time, end_time;
	long long time_diff;

	TIME_S(start_time);
  Inst::init_visit3();
	for (auto& v: conjunct_q)
		retrieve_ab_sol(solver, v, relSig, relConst, relUFtype);
	for (auto& v: relSig)
		retrieve_ab_sol(solver, v, relSig, relConst, relUFtype);
	for (auto& v: relConst)
		retrieve_ab_sol(solver, v, relSig, relConst, relUFtype);
	TIME_E(start_time, end_time, _tb_val_time);
	if (mode == AB_REACH_TOP)
		_cti_val_time += time_diff;

	for (InstL::iterator pit = m.all_predicates.begin(); pit != m.all_predicates.end(); pit++) {
    Inst* tve = *pit;
		if (tve == _ve_prop_eq_0 || tve == _ve_prop_eq_1 || tve == _ve_prop_next_eq_0 || tve == _ve_prop_next_eq_1)
//    if (tve == _ve_prop_eq_0 || tve == _ve_prop_eq_1)
		{
			continue;
		}

  	bool set_pred = false;
//  	if (Inst::_s_inp.find(tve) != Inst::_s_inp.end()) {
//  		set_pred = true;
//  	}
//  	else if (Inst::_s_reg.find(tve) != Inst::_s_reg.end()) {
//  		set_pred = true;
//  	}

    if (set_pred || find_from_minset2(solver, tve, relSig, relConst, relUFtype)) {
    	int val = get_bval(solver, tve);
    	if (val == 1) {
    		m.s.predicates.push_back(tve);
    		if (set_pred) {
    			tve->coi.set_pred();
    			tve->coi.set_present();
    		}
    	}
    	else {
    		if (val != INVALID_SVAL) {
					assert(val == 0);
					Inst* tveNeg = OpInst::create(OpInst::LogNot, tve);
					bool res = (set_pred || find_from_minset2(solver, tveNeg, relSig, relConst, relUFtype));
					assert(res);
					m.s.predicates.push_back(tveNeg);
	    		if (set_pred) {
	    			tveNeg->coi.set_pred();
	    			tveNeg->coi.set_present();
	    		}
    		}
    	}
    }
  }

  for (map< pair< int, SORT>, InstL >::iterator sit = m.all_terms.begin(); sit != m.all_terms.end(); sit++)
  {
  	pair< int, SORT> sz = (*sit).first;
		for (InstL::iterator pit = (*sit).second.begin(); pit != (*sit).second.end(); pit++)
		{
			Inst* tve = *pit;
			if (find_from_minset2(solver, tve, relSig, relConst, relUFtype))
			{
				mpz_class* val = get_ival(solver, tve);
				if (val != INVALID_SMPZ) {
					m.s.partitions[sz][*val].push_back(tve);
				}
			}
		}
  }

	uniquify_solution(m.s);

//  if (modified)
  {
    print_solution(m.s, "gen. solution");
#ifdef INTERACTIVE_CUBE
    print_solution(cerr, s, "\ngen. solution");
#endif
  }
  return true;
}

bool Reach::find_from_minset2(Solver* solver, Inst*e, InstS& relSig, InstS& relConst, set< string >& relUFtype)
{
  assert(e != 0);
  if (e->coi.valid_project_key()) {
    return e->coi.present();
  }
  e->coi.set_project_key();
	e->coi.set_present();

  AVR_LOG(9, 1, "[COI]: (entry) " << *e << endl);

  bool noprune = false;
#ifdef GENERALIZE_OFF
  noprune = true;
#endif

  switch (e->get_type()) {
  case Sig: {
		if (noprune || relSig.find(e) != relSig.end()) {
			if (e->find_next()) {
				if (Inst::has_trelation(e)) {
					e->coi.set_next_reg();
				}
				else {
					e->coi.set_next_inp();
				}
			}
			else {
				if (Inst::_s_reg.find(e) != Inst::_s_reg.end()) {
					e->coi.set_reg();
				}
				else
					e->coi.set_inp();
			}
		}
		else {
			e->coi.set_absent();
		}
  }
  break;
  case Wire: {
    WireInst* w = WireInst::as(e);
		w->set_sliceVal();

    Inst* port = w->get_port();
    find_from_minset2(solver, port, relSig, relConst, relUFtype);
    e->coi.update(port->coi);
  }
  break;
  case Const: {
    assert(0);
  }
  break;
  case Num: {
    if (e->get_size() != 1)
    	if (noprune || relConst.find(e) != relConst.end()) {
    	}
    	else
    		e->coi.set_absent();
  }
  break;
  case Ex:
  case Op: {
    OpInst* op = OpInst::as(e);
    assert(op != 0);
    const InstL* ch = e->get_children();

    OpInst::OpType opT = op->get_op();

    if (opT == OpInst::Ternary) {
      assert(ch != 0);
      InstL::const_iterator it = ch->begin();

      Inst* if_e = *(it++);
      Inst* then_e = *(it++);
      Inst* else_e = *(it++);
      find_from_minset2(solver, if_e, relSig, relConst, relUFtype);
      e->coi.update(if_e->coi);

      int ifVal = get_bval(solver, if_e);
      if (ifVal == INVALID_SVAL) {
    		e->coi.set_absent();
      }
      else {
				if (noprune || ifVal == 0) {
					find_from_minset2(solver, else_e, relSig, relConst, relUFtype);
					e->coi.update(else_e->coi);
				}
				if (noprune || ifVal == 1) {
					find_from_minset2(solver, then_e, relSig, relConst, relUFtype);
					e->coi.update(then_e->coi);
				}
      }
    }
    else if (opT == OpInst::LogNot) {
      assert(ch != 0);
      Inst* child = ch->front();
    	find_from_minset2(solver, child, relSig, relConst, relUFtype);
      e->coi.update(child->coi);
    }
    else if (opT == OpInst::LogAnd || opT == OpInst::LogOr) {
      int eVal = get_bval(solver, e);
//  	  AVR_LOG(9, 1, "[COI]: (sval) e: " << *e << "\t" << eVal << endl);
      if (eVal == INVALID_SVAL) {
    		e->coi.set_absent();
//    	  AVR_LOG(9, 1, "[COI]: (noval) e: " << *e << "\t" << e->coi.str() << "\tv" << e->get_drVal(Inst::get_drkey()) << endl);
      }
      else {
      	bool done = false;
      	if (eVal == controlling(opT)) {
					for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it) {
						int itVal = get_bval(solver, (*it));
						if (noprune || itVal == controlling(opT)) {
							find_from_minset2(solver, *it, relSig, relConst, relUFtype);
							e->coi.update((*it)->coi);
							done = true;
							break;
						}
					}
				}

      	if (!done) {
					InstS children;
					for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it) {
						find_from_minset2(solver, *it, relSig, relConst, relUFtype);
						e->coi.update((*it)->coi);
						// TODO: choose from children
					}
				}
      }
    }
    else if (opT == OpInst::Eq || opT == OpInst::NotEq) {
      Inst* lhs = ch->front();
      Inst* rhs = ch->back();

    	find_from_minset2(solver, lhs, relSig, relConst, relUFtype);
      e->coi.update(lhs->coi);
    	find_from_minset2(solver, rhs, relSig, relConst, relUFtype);
      e->coi.update(rhs->coi);
    }
    else {
      string ufType = op->get_euf_func_name();
      if (ufType == "0")
        cout << "\t(error: unexpected uf type)\t" << *e << endl;
      assert (ufType != "0");

//      if (_s_uf.find(e) != _s_uf.end()) {
//				for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it) {
//					find_from_minset2(*it, relSig, relConst, relUFtype);
//					e->coi.update((*it)->coi);
//				}
//				e->coi.set_present();
//      }
//      else
      {
				if (noprune || relUFtype.find(ufType) != relUFtype.end()) {
					for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it) {
						find_from_minset2(solver, *it, relSig, relConst, relUFtype);
						e->coi.update((*it)->coi);
					}
				}
				else {
					e->coi.set_absent();
				}
      }
    }
  }
    break;
  case UF:
  case Mem:
  default:
    assert(0);
  }

  AVR_LOG(9, 1, "[COI]: (leave) e: " << *e << "\t" << e->coi.str() << "\tv" << e->get_drVal(Inst::get_drkey()) << endl);

  if (e->coi.valid_coi_key()) {
//  	assert(e->coi.present());
  }
  if (e->coi.pred()) {
//  	assert(e->coi.present());
  }

#ifdef GENERALIZE_OFF
  assert(e->coi.present());
#endif

  return e->coi.present();
}

void Reach::model_abstract2(SOLUTION& s, SOLUTION& pre, SOLUTION& inp, SOLUTION& next, SOLUTION& mixed, bool quiet)
{
	for (InstL::iterator pit = s.predicates.begin(); pit != s.predicates.end(); pit++)
	{
		Inst* tve = *pit;
		if (!tve->coi.present()) {
			cout << *tve << endl;
		}
		assert(tve->coi.present());

		if (tve->coi.has_next_reg())
		{
			next.predicates.push_back(tve);
			if (!tve->find_next())
				assert(0);
		}
		else if (tve->coi.has_next_inp())
		{
			next.predicates.push_back(tve);
			if (!tve->find_next())
				assert(0);
		}
		else if (tve->coi.has_inp())
		{
			if (tve->find_next())
				assert(0);

			if (tve->coi.has_reg())
			{
				mixed.predicates.push_back(tve);
			}
			else
			{
				inp.predicates.push_back(tve);
			}
//			mixed.predicates.push_back(tve);
//			pre.predicates.push_back(tve);
		}
		else if (tve->coi.has_reg())
		{
			if (tve->find_next()) {
				cout << "warning: node has pre reg and next: " << *tve << endl;
//				InstS tmpSet;
//				collect_sig(tve, tmpSet, true);
//				cout << "sigs: " << tmpSet << endl;

				next.predicates.push_back(tve);
			}
			else
				pre.predicates.push_back(tve);
		}
		else
		{
			if (tve->find_next() && find_pre(tve))
				assert(0);

			if (tve->find_next())
				next.predicates.push_back(tve);
			else {
				pre.predicates.push_back(tve);
				inp.predicates.push_back(tve);
				mixed.predicates.push_back(tve);
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
				assert(tve->coi.present());

				if (tve->coi.has_next_reg())
				{
					next.partitions[sz][cell.first].push_back(tve);
				}
				else if (tve->coi.has_next_inp())
				{
					next.partitions[sz][cell.first].push_back(tve);
				}
				else if (tve->coi.has_inp())
				{
					if (tve->coi.has_reg())
					{
						mixed.partitions[sz][cell.first].push_back(tve);
					}
					else
					{
						inp.partitions[sz][cell.first].push_back(tve);
					}
//					mixed.partitions[sz][cell.first].push_back(tve);
				}
				else if (tve->coi.has_reg())
				{
					pre.partitions[sz][cell.first].push_back(tve);
//					mixed.partitions[sz][cell.first].push_back(tve);
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

bool Reach::add_local_eq(Inst* lhs, Inst* rhs) {
	if (Config::g_fineness < FINENESS_EQLOCAL)
		return false;
	if (lhs != rhs) {
    if (lhs->find_next() && rhs->find_next())
      if (!find_pre(lhs) && !find_pre(rhs)) {
        lhs = Inst::all_next2pre(lhs);
        rhs = Inst::all_next2pre(rhs);
      }

    if (!lhs->find_next() && !rhs->find_next()) {
      if ((Config::g_fineness < FINENESS_EQSIG) ||
      		(lhs->get_type() != Sig && lhs->get_type() != Num) ||
          (rhs->get_type() != Sig && rhs->get_type() != Num)
					) {
    		if (lhs->get_type() == Num && rhs->get_type() == Num)
    			return false;
        if (!(lhs->get_id() < rhs->get_id()))
          swap(lhs, rhs);
        pair< Inst*, Inst* > eq = make_pair(lhs, rhs);
        if (_s_local_eq.find(eq) == _s_local_eq.end()) {
          _s_local_eq.insert(eq);
          pair< Inst*, Inst* > eq2 = make_pair(Inst::all_pre2next(lhs), Inst::all_pre2next(rhs));
          _s_local_eq.insert(eq2);

          AVR_LOG(15, 3, "\t(new eq. predicate)\t" << *eq.first << " ?= " << *eq.second << endl);
          num_local_eq++;
          if (lhs->get_type() == Sig || rhs->get_type() == Sig)
          	num_local_eq_sig++;
          if (lhs->get_type() == Num || rhs->get_type() == Num)
          	num_local_eq_num++;
          if ((lhs->get_type() != Sig && lhs->get_type() != Num) ||
              (rhs->get_type() != Sig && rhs->get_type() != Num))
          	num_local_eq_uf++;
//          else {
//            AVR_LOG(15, 0, "\t(new eq. predicate here)\t" << *eq.first << " ?= " << *eq.second << endl);
//          }
        }
        return true;
      }
    }
  }
  return false;
}

bool Reach::allowed_relation(Inst* lhs, Inst* rhs, OpInst::OpType opt) {
	assert(lhs->get_sort() == rhs->get_sort());

	if (lhs->get_sort_type() == bvtype && lhs->get_size() == 1)
		return false;
	if (lhs->get_type() == Num && rhs->get_type() == Num) {
		if (opt == OpInst::Eq) {
			cout << *lhs << "\t=\t" << *rhs << endl;
		}
		assert(opt != OpInst::Eq);
		return false;
	}

	if (lhs->get_sort_type() == bvtype || lhs->get_sort_type() == inttype) {
		if (Config::g_fineness >= FINENESS_EQUF)
			return true;
		else if (Config::g_fineness >= FINENESS_EXCCSIG) {
			if ((lhs->trueFcLevel == 0) &&
					(rhs->trueFcLevel == 0) &&
					(!lhs->childrenInfo[MUX]) &&
					(!rhs->childrenInfo[MUX]) &&
					(!lhs->childrenInfo[CTRL]) &&
					(!rhs->childrenInfo[CTRL])
					) {
//				if ((lhs->fcLevel != 0) || (rhs->fcLevel != 0)) {
//					cout << "allowing: " << *lhs << " ?= " << *rhs << "\n";
//				}
				return true;
			}
		}
		else if (Config::g_fineness >= FINENESS_EQSIG) {
			if (lhs->get_type() == Sig) {
				if (rhs->get_type() == Sig)
					return true;
				else if (rhs->get_type() == Num)
					return true;
			}
			else if (lhs->get_type() == Num) {
				if (rhs->get_type() == Sig)
					return true;
				else if (rhs->get_type() == Num)
					return false;
			}
		}
	}

	if (Config::g_fineness >= FINENESS_EQLOCAL) {
		pair< Inst*, Inst* > eq;
		if (!(lhs->get_id() < rhs->get_id())) {
			eq.first = rhs;
			eq.second = lhs;
		}
		else {
			eq.first = lhs;
			eq.second = rhs;
		}
		if (_s_local_eq.find(eq) != _s_local_eq.end())
			return true;
	}

//	if (sa.relevant(lhs, rhs)) {
//		AVR_LOG(15, 0, "\t\t(struct relevant) " << *lhs << " ?= " << *rhs << endl);
////		assert(0);
//		return true;
//	}

	return false;
}

void Reach::add_from_solution(Solver*solver, SOLUTION& s, InstL& target, InstL& output)
{
	InstS tSet;
	for (auto& t: target)
	{
		tSet.insert(t);
	}

	for (InstL::iterator pit = s.predicates.begin(); pit != s.predicates.end(); pit++)
	{
		Inst* tve = *pit;
		if (Config::g_fineness >= FINENESS_UP ||
				tve->coi.pred() ||
				(Config::g_fineness >= FINENESS_EQLOCAL && tve->coi.local_pred()))
		{
			if (tSet.find(tve) == tSet.end()) {
				output.push_back(tve);
				tSet.insert(tve);
			}
		}
	}

	for (auto& partition: s.partitions)
	{
//		int sz = partition.first;
#if 1
		InstL leaders;
		bool addLT = false;
#ifdef GENERALIZE_WITH_LESSTHAN
		addLT = Config::g_ab_interpret && (partition.first.second.type == inttype);
		vector < pair < mpz_class, Inst* > > leaders_val;
#endif
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
#ifdef GENERALIZE_WITH_LESSTHAN
			if (addLT)
				leaders_val.push_back(make_pair(cell.first.get_si(), leader));
#endif

			for (InstL::iterator pit = cell.second.begin(); pit != cell.second.end(); pit++)
			{
				Inst* tve = *pit;
				if (leader != tve)
				{
					if (allowed_relation(leader, tve, OpInst::Eq))
					{
						Inst* eq = OpInst::create(OpInst::Eq, tve, leader);
//						if (addLT)
//							eq = OpInst::create(OpInst::IntLeEq, tve, leader);
						if (tSet.find(eq) == tSet.end())
						{
							if (solver->get_relation(tve, leader, true)) {
								output.push_back(eq);
								tSet.insert(eq);
							}
						}
					}
					assert(*tve->get_ival() == *leader->get_ival());
				}
			}
		}

#ifndef GENERALIZE_WO_DISEQ
		if (!addLT) {
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
							if (solver->get_relation(lhs, rhs, false)) {
								output.push_back(neq);
								tSet.insert(neq);
							}
						}
					}
					assert(*lhs->get_ival() != *rhs->get_ival());
				}
			}
		}
#endif

#ifdef GENERALIZE_WITH_LESSTHAN
		if (addLT) {
			// no need for sorting since should already be in ascending order
//			std::sort(leaders_val.begin(), leaders_val.end());
			vector < pair < mpz_class, Inst* > >::iterator vit = leaders_val.begin();

#ifdef GENERALIZE_WITH_LESSTHAN_QUADRATIC
			// quadratic inequalities
			for (vector < pair < mpz_class, Inst* > >::iterator vit1 = leaders_val.begin(); vit1 != leaders_val.end(); vit1++)
			{
				pair < mpz_class, Inst* >& lhs = *vit1;
				vector < pair < mpz_class, Inst* > >::iterator vit2 = vit1;
				vit2++;
				for (; vit2 != leaders_val.end(); vit2++)
				{
					pair < mpz_class, Inst* >& rhs = *vit2;
					assert(lhs.first < rhs.first);
					if (allowed_relation(lhs.second, rhs.second, OpInst::IntLe))
					{
						Inst* lt = OpInst::create(OpInst::IntLe, lhs.second, rhs.second);
						if (tSet.find(lt) == tSet.end())
						{
							if (solver->get_relation(lhs.second, rhs.second, false)) {
								output.push_back(lt);
								tSet.insert(lt);
							}
						}
					}
				}
			}
#else
#ifdef GENERALIZE_WITH_LESSTHAN_LINEAR
			// linear inequalities
			pair< mpz_class, Inst* >& lhs = (*vit);
			vit++;
			for (; vit != leaders_val.end(); vit++)
			{
				pair< mpz_class, Inst* >& rhs = (*vit);
				assert(lhs.first < rhs.first);
				if (allowed_relation(lhs.second, rhs.second, OpInst::IntLe))
				{
					Inst* lt = OpInst::create(OpInst::IntLe, lhs.second, rhs.second);
					if (tSet.find(lt) == tSet.end())
					{
						if (solver->get_relation(lhs.second, rhs.second, false)) {
							output.push_back(lt);
							tSet.insert(lt);
						}
					}
				}
				lhs = rhs;
			}
#endif
#endif
		}
#endif

#else
		// Experimental (add all partition constraints)
    for (auto& cell1: partition.second)
    {
      for (auto& lhs: cell1.second)
      {
        for (auto& cell2: partition.second)
        {
          bool same = (cell1.first == cell2.first);
          for (auto& rhs: cell2.second)
          {
            if (lhs != rhs)
            {
//              if (lhs->get_type() == Sig || rhs->get_type() == Sig)
              if (lhs->get_type() != Num || rhs->get_type() != Num)
              {
                Inst* cond = OpInst::create(OpInst::Eq, lhs, rhs);
                if (!same)
                  cond = OpInst::create(OpInst::LogNot, cond);

                if (tSet.find(cond) == tSet.end())
                {
                  if (solver->get_relation(lhs, rhs, true))
                    output.push_back(cond);
                }
              }
              if (same)
                assert(*lhs->get_ival() == *rhs->get_ival());
              else
                assert(*lhs->get_ival() != *rhs->get_ival());
            }
          }
        }
      }
    }
#endif
	}
}

void Reach::add_from_solution(Solver*solver, SOLUTION& s, InstL& target, string comment)
{
	InstL output;
	add_from_solution(solver, s, target, output);
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
//			AVR_LOG(15, 3, "\t\t" << *p << endl);
    }
  }
}


void Reach::add_pred_from_solution(SOLUTION& s, InstL& target, string comment) {
	InstS tSet;
	for (auto& t: target)
	{
		tSet.insert(t);
	}

	InstL added;
	for (InstL::iterator pit = s.predicates.begin(); pit != s.predicates.end(); pit++)
	{
		Inst* tve = *pit;
		if (tve->coi.pred()) {
			if (tSet.find(tve) == tSet.end()) {
				target.push_back(tve);
				tSet.insert(tve);
				added.push_back(tve);
			}
		}
	}

	if (!added.empty()) {
    if (comment != "") {
      AVR_LOG(15, 0, "\t(" << comment << ") #" << added.size() << "\n");
//      for (auto & p: added)
//      {
//  			AVR_LOG(15, 0, "\t\t" << *p << endl);
//			}
    }
	}
}

void Reach::add_required_pred_from_solution(SOLUTION& s, InstL& target, int level, string comment) {
	if (Config::g_ab_granularity < level)
		return;

	InstS tSet;
	for (auto& t: target)
	{
		tSet.insert(t);
	}

	InstL added;
	for (InstL::iterator pit = s.predicates.begin(); pit != s.predicates.end(); pit++)
	{
		Inst* tve = *pit;
		if (tve->coi.pred()) {
//		if (tve->coi.pred() && tve->coi.has_reg()) {
//		if (tve->coi.req_pred() && tve->coi.pred()) {
			if (tSet.find(tve) == tSet.end()) {
				target.push_back(tve);
				tSet.insert(tve);
				added.push_back(tve);
			}
		}
	}

	if (!added.empty()) {
    if (comment != "") {
      AVR_LOG(15, 0, "\t(" << comment << ") #" << added.size() << "\n");
//      for (auto & p: added)
//      {
//  			AVR_LOG(15, 3, "\t\t" << *p << endl);
//			}
    }
	}
}

void Reach::add_pred_from_solution(SOLUTION& s, InstL& target, InstL& wires, string comment) {
	Inst::init_visit();

	InstS tSet;
	for (auto& t: target)
	{
		tSet.insert(t);
	}

	InstL added;
	for (InstL::iterator pit = s.predicates.begin(); pit != s.predicates.end(); pit++)
	{
		Inst* tve = *pit;
		if (tve->coi.pred()) {
			if (tSet.find(tve) == tSet.end()) {
				target.push_back(tve);
				tSet.insert(tve);
				added.push_back(tve);
				add_wires(tve, wires);
			}
		}
	}

	if (!added.empty()) {
    if (comment != "") {
      AVR_LOG(15, 0, "\t(" << comment << ") #" << added.size() << "\n");
//      for (auto & p: added)
//      {
//  			AVR_LOG(15, 0, "\t\t" << *p << endl);
//			}
    }
	}
}

void Reach::COI_prune_relation(Inst*e, EVAL& s, int region)
{
	_trace_depth++;

	OpInst::OpType op_type = OpInst::Unknown;

	assert(e != 0);
	if (e->get_visit())
	{
		_trace_depth--;
		return;
	}
	e->set_visit();
	assert(e->get_size() == 1);

	e->coi.set_coi_key();
#ifndef PERFORMANCE_NODRAW
	if (Config::g_print_dot[DRAW_TRANSITION] != '0')
		e->set_drVal(1);
#endif

//	// TODO temporary fix for the next state function, "reg_reset$next = 1"
//	// With wn_simplify_const_pred enabled, "reg_reset$next = 1" is simplified as "reg_reset$next"
//	// However, m_sn[reg_reset$next] still is a NumInst, 1'b1.
//	// Therefore, eval_formula(2, 1'b1) is called due to the codes below "if (_m_sn.find(e) != _m_sn.end()) {"
//	// As 1'b1 was not in T (omitted during simplification), its cex_val and cex_mpz  also have not been initialized
//	// Here, I temporarily assign the fields, but I should fix this problem properly later.
//	NumInst *num_temp = NumInst::as(e);
//	if(num_temp)
//	{
//		if(e->get_size() == 1)
//		{
//			if(num_temp->get_num() == 0)
//				e->set_bval(0);
//			else
//				e->set_bval(1);
//		}
//	}

	int eVal = get_bval(s.solver, e);

	AVR_LOG(9, 4, "[Eval]: " << *e << " (id: " << eVal << ")" << endl);

	e->acex_coi = e;
  e->nsub_coi = e;

	if (!(eVal == 1 || eVal == 0))
	{
		return;
		cout << "e->cex_mpz: " << e->get_size() << "'d";
		cout << "e->val: " << eVal << endl;
		cout << "e: " << *e << endl;
		assert(0);
	}

  bool isPred = false;
  bool addCond = false;

	bool intpd = false;
	bool call_eval_term = false;
	switch (e->get_type()) {
	case Sig:
	{
		if (e->find_next())
		{
			if (Inst::has_trelation(e))
			{
				s.relevantSetNext->insert(e);
				Inst* v = e->fetch_trelation(e);
    		if (get_bval(s.solver, v) != INVALID_SVAL)
    			COI_prune_relation(v, s, 1);
			}
      else if (e != _ve_prop_next_eq_1)
      {
        s.relevantInpNext->insert(e);
        InstToSetM::iterator mit = Inst::_m_inp_next.find(e);
        if (mit != Inst::_m_inp_next.end()) {
        	for (auto& v: (*mit).second) {
        		if (get_bval(s.solver, v) != INVALID_SVAL)
        			COI_prune_relation(v, s, 1);
        	}
        }
      }
		}
		else
		{
			if (Inst::_s_reg.find(e) != Inst::_s_reg.end())
			{
				s.relevantSet->insert(e);
			}
      else if (e != _ve_prop_eq_1)
			{
				s.relevantInp->insert(e);
//        InstToSetM::iterator mit = Inst::_m_inp.find(e);
//        if (mit != Inst::_m_inp.end()) {
//        	for (auto& v: (*mit).second) {
//    				COI_prune_relation(v, s, 1);
//        	}
//        }
			}
		}
		addCond = true;
	}break;
	case Wire:
	{
		WireInst* w = WireInst::as(e);
		Inst* port = w->get_port();
		COI_prune_relation(port, s, region);

		OpInst* op_port = OpInst::as(port);
		if (op_port)
		{
			if (is_next_wire(w))
				s.bins->relevantWiresNext.push_back(w);
			else
				s.bins->relevantWires.push_back(w);
		}
		else
			assert(0);

		if (port->nsub_coi != port)
		  e->nsub_coi = port->nsub_coi;

	}break;
	case Const:
	{
		assert(0);
	}break;
	case Num: {
		// nothing
	}break;
	case Op: {
		OpInst* op = OpInst::as(e);
		assert(op != 0);
		op_type = op->get_op();
		if (op_type == OpInst::LogAnd || op_type == OpInst::LogOr || op_type == OpInst::LogNot || op_type
				== OpInst::Ternary)
			intpd = true;
		else if (op_type == OpInst::Concat)
		{
			/// Concat size cannot be 1
			assert(0);
		}
		else
		{
			call_eval_term = true;
		}
	}
		break;
	case UF:
	case Ex: {
		call_eval_term = true;
	}break;
	case Mem:
	default:
		assert(0);
	}

	// deal with all predicates (UPs and Equality)
	if (call_eval_term)
	{

		string ufType = OpInst::as(e)->get_euf_func_name();
		if (ufType != "0")
		{
			s.relevantUFtype->insert(ufType);
		}

		InstL new_ch;
		const InstL* ch = e->get_children();
		assert(ch != 0);
		bool all_ch_size_one = true;

		InstToInstM tmpMap;
		for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it)
		{
			if ((*it)->get_size() == 1)
			{
				COI_prune_relation(*it, s, region);
			}
			else
			{
				COI_prune_term(*it, s, region);
				all_ch_size_one = false;
			}
		}

    if((op_type == OpInst::Eq) || (op_type == OpInst::NotEq)) {
      Inst* lhs = ch->front();
      Inst* rhs = ch->back();

      if (lhs != lhs->nsub_coi || rhs != rhs->nsub_coi) {
        lhs = lhs->nsub_coi;
        rhs = rhs->nsub_coi;
        e->nsub_coi = OpInst::create(op_type, lhs, rhs);

        int nVal = e->nsub_coi->get_bval();
        if (false && nVal != INVALID_SVAL)
        {
          if (nVal != eVal)
          {
            cout << "e  : " << *e << " (val: " << eVal << ")" << endl;
            cout << "nSub: " << *e->nsub_coi << " (val: " << nVal << ")" << endl;
          }
          assert(nVal == eVal);
        }
        else
        {
          e->nsub_coi->set_bval(eVal);
        }
      }

      if (lhs->get_size() != 1)
      {
        isPred = add_local_eq(lhs, rhs);
      }
    }


		if((((op_type == OpInst::Eq) || (op_type == OpInst::NotEq)) && all_ch_size_one == true))
		{
			// do nothing
		}
		else
		{
			addCond = true;
		}
	}
	else if (intpd)
	{
		assert(e->get_type() == Op);
		const InstL* ch = e->get_children();
		assert(ch != 0);

		e->acex_coi = NumInst::create(eVal, e->get_size(), e->get_sort());

		switch (op_type)
		{
		case OpInst::LogNot:
			COI_prune_relation(*(ch->begin()), s, region);
			break;
		case OpInst::LogAnd:
		case OpInst::LogOr: {
			for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it)
			{
				int itVal = get_bval(s.solver, (*it));

				if (eVal == controlling(op_type))
				{
					if (itVal == controlling(op_type))
					{
						COI_prune_relation(*it, s, region);
						e->nsub_coi = (*it)->nsub_coi;
						break;
					}
				}
				else
				{
					COI_prune_relation(*it, s, region);
				}
			}
		}break;
		case OpInst::Ternary: {
			InstL::const_iterator it = ch->begin();
			Inst* if_e = *(it++);
			Inst* then_e = *(it++);
			Inst* else_e = *(it++);
			COI_prune_relation(if_e, s, region);

			int ifVal = get_bval(s.solver, if_e);
			if (ifVal == 0) {
				COI_prune_relation(else_e, s, region);
				e->acex_coi = else_e;
				e->nsub_coi = else_e->nsub_coi;
			} else if (ifVal == 1) {
				COI_prune_relation(then_e, s, region);
				e->acex_coi = then_e;
				e->nsub_coi = then_e->nsub_coi;
			} else {
				COI_prune_relation(else_e, s, region);
				COI_prune_relation(then_e, s, region);
			}
		}break;
		default:
			assert(0);
		}
	}

	if (addCond)
	{
		Inst* eqRel = e;
		if (eqRel->get_bval() == 0)
			eqRel = OpInst::create(OpInst::LogNot, eqRel);
		if (!is_redundant(eqRel)) {
//			if (eqRel->find_next() && find_pre(eqRel))
			if (eqRel->find_next() && region == 1)
				s.bins->nextStateConstraints.push_back(eqRel);
			else {
				_min_term.all_predicates.push_back(e);
				eqRel->coi.set_pred();
			}
		}
	}

	if (isPred) {
	  Inst* eqRel = e->nsub_coi;
    if (e->nsub_coi->get_bval() == 0)
      eqRel = OpInst::create(OpInst::LogNot, eqRel);
	  if (eqRel != e && !is_redundant(eqRel)) {
//			if (eqRel->find_next() && find_pre(eqRel))
			if (eqRel->find_next() && region == 1)
				s.bins->nextStateConstraints.push_back(eqRel);
			else {
				_min_term.all_predicates.push_back(e->nsub_coi);
				eqRel->coi.set_local_pred();
			}
	  }
	}

	AVR_LOG(9, 2, "[EvalA] e: " << *e << " -> " << *(e->acex_coi) << endl);

	_trace_depth--;
}

void Reach::COI_prune_term(Inst*e, EVAL& s, int region)
{
	_trace_depth++;
	assert(e != 0);
	if (e->get_visit())
	{
		_trace_depth--;
		return;
	}
	e->set_visit();

	e->coi.set_coi_key();
#ifndef PERFORMANCE_NODRAW
	if (Config::g_print_dot[DRAW_TRANSITION] != '0')
		e->set_drVal(1);
#endif

	AVR_LOG(9, 4, "[Eval]: " << *e << endl);

	mpz_class* eVal = get_ival(s.solver, e);
	e->acex_coi = e;
  e->nsub_coi = e;

	if (eVal == INVALID_SMPZ)
	{
		return;
		cout << "e: " << *e << endl;
		cout << "e->val: " << eVal << endl;
		assert(0);
	}

	bool apply_on_children = false;

	mpz_class* eaVal = eVal;

	switch (e->get_type())
	{
	case Sig:
	{
		if (e->find_next())
		{
			if (Inst::has_trelation(e))
			{
				s.relevantSetNext->insert(e);
				Inst* v = e->fetch_trelation(e);
    		if (get_bval(s.solver, v) != INVALID_SVAL)
    			COI_prune_relation(v, s, 1);
			}
      else
      {
        s.relevantInpNext->insert(e);
        InstToSetM::iterator mit = Inst::_m_inp_next.find(e);
        if (mit != Inst::_m_inp_next.end()) {
        	for (auto& v: (*mit).second) {
        		if (get_bval(s.solver, v) != INVALID_SVAL)
        			COI_prune_relation(v, s, 1);
        	}
        }
      }
		}
		else
		{
			if (Inst::_s_reg.find(e) != Inst::_s_reg.end())
			{
				s.relevantSet->insert(e);
			}
			else
			{
				s.relevantInp->insert(e);
//        InstToSetM::iterator mit = Inst::_m_inp.find(e);
//        if (mit != Inst::_m_inp.end()) {
//        	for (auto& v: (*mit).second) {
//    				COI_prune_relation(v, s, 1);
//        	}
//        }
			}
		}

		// leave it as "itself"
	}break;
	case Wire:
	{
//		bins.relevantWires.push_back(e);
		WireInst* w = WireInst::as(e);
		Inst* port = w->get_port();
		COI_prune_term(port, s, region);

		OpInst* op_port = OpInst::as(port);
		if (op_port)
		{
			if (is_next_wire(w))
				s.bins->relevantWiresNext.push_back(w);
			else
				s.bins->relevantWires.push_back(w);
		}
		else
			assert(0);

		if (port->nsub_coi != port)
		  e->nsub_coi = port->nsub_coi;
	}break;
	case Const:
	{
		assert(0);
	}break;
	case Num:
	{
//		if (NumInst::as(e)->fromSystem())
			s.relevantConst->insert(e);
		// leave it as "itself"
	}break;
	case Op:
	{
		OpInst* op = OpInst::as(e);
		assert(op != 0);
		OpInst::OpType t = op->get_op();

		if (t == OpInst::Ternary) {
			const InstL* ch = e->get_children();
			assert(ch != 0);
			InstL::const_iterator it = ch->begin();
			Inst* if_e = *(it++);
			Inst* then_e = *(it++);
			Inst* else_e = *(it++);
			COI_prune_relation(if_e, s, region);

			int ifVal = if_e->get_bval();
			if (ifVal == 0) {
				COI_prune_term(else_e, s, region);
				e->acex_coi = else_e;
				e->nsub_coi = else_e->nsub_coi;
				eaVal = e->acex_coi->get_ival();
			} else if (ifVal == 1) {
				COI_prune_term(then_e, s, region);
				e->acex_coi = then_e;
				e->nsub_coi = then_e->nsub_coi;
				eaVal = e->acex_coi->get_ival();
			} else {
				COI_prune_term(else_e, s, region);
				COI_prune_term(then_e, s, region);
			}
		}
		else
		{
			apply_on_children = true;
		}
	}
		break;
	case UF:
	case Ex: {
		apply_on_children = true;
	}
		break;
	case Mem:
	default:
		assert(0);
	}

	if (apply_on_children) {

		string ufType = OpInst::as(e)->get_euf_func_name();
		if (ufType != "0")
		{
			s.relevantUFtype->insert(ufType);
		}

		const InstL* ch = e->get_children();
		assert(ch != 0);
		InstL new_ch;

		for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it)
		{
			if ((*it)->get_size() == 1)
			{
				COI_prune_relation(*it, s, region);
			}
			else
			{
				COI_prune_term(*it, s, region);
			}
		}
	}
	else
	{
		// leave it as ""itself"
	}

  if (false && eaVal != INVALID_SMPZ) {
		if (*eVal != *eaVal)
		{
			AVR_LOG(9, 0, "[EvalA] e: " << *e << "\t" << *e->get_ival() << " " << *eVal << endl);
			AVR_LOG(9, 0, "[EvalA] eA: " << *e->acex_coi << "\t" << *e->acex_coi->get_ival() << " " << *eaVal << endl);
		}
		assert(*eVal == *eaVal);
  }
	AVR_LOG(9, 2, "[EvalA] e: " << *e << " -> " << *(e->acex_coi) << endl);

	_trace_depth--;
}




}





