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
/// Aman
/// mode = 1, Explore complete COI
/// else, explore relevant COI
/// mode = 3, same as else case but also assert no function composition

void Reach::evaluate_abstract_relation(int mode, Inst*e, EVAL& s)
{
	_trace_depth++;

	OpInst::OpType op_type = OpInst::Unknown;

//	if (init_visit) {
//		Inst::init_visit();
//	}

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

	// TODO temporary fix for the next state function, "reg_reset$next = 1"
	// With wn_simplify_const_pred enabled, "reg_reset$next = 1" is simplified as "reg_reset$next"
	// However, m_sn[reg_reset$next] still is a NumInst, 1'b1.
	// Therefore, eval_formula(2, 1'b1) is called due to the codes below "if (_m_sn.find(e) != _m_sn.end()) {"
	// As 1'b1 was not in T (omitted during simplification), its cex_val and cex_mpz  also have not been initialized
	// Here, I temporarily assign the fields, but I should fix this problem properly later.
	NumInst *num_temp = NumInst::as(e);
	if(num_temp)
	{
		if(e->get_size() == 1)
		{
			if(num_temp->get_num() == 0)
				e->set_bval(0);
			else
				e->set_bval(1);
		}
	}

	int eVal = e->get_bval();

	if((e->get_size() == 1) && (!(eVal == 1 || eVal == 0)))
	{
		cout << "e->cex_mpz: " << e->get_size() << "'d";
		cout << "e->val: " << eVal << endl;
		cout << "e: " << *e << endl;
		assert(0);
	}

	if (!(eVal == 1 || eVal == 0))
	{
		cout << "e->cex_mpz: " << e->get_size() << "'d";
		cout << "e->val: " << eVal << endl;
		cout << "e: " << *e << endl;
		assert(0);
	}

	AVR_LOG(9, 4, "[Eval]: " << *e << " (id: " << eVal << ")" << endl);

//	Inst* e_orig = e;
//#ifdef INTERPRET_EX_CC
//	OpInst* op = OpInst::as(e);
//	if (op)
//	{
//		e = op->t_simple;
//		assert(e->get_bval() == eVal);
//	}
//#endif

	// resulting relation to add to viol
	Inst* rel = 0;

	e->acex_coi = 0;
  e->nsub_coi = e;
#ifdef	FIND_SUB_EXPRESSION
	e->subs_coi = 0;
#endif

  bool isPred = false;

	bool intpd = false;
	bool call_eval_term = false;
	switch (e->get_type()) {
	case Sig:
	{
		if (e->find_next())
		{
			if (Inst::has_trelation(e))
			{
				s.relevantSet->insert(e);
			}
      else if (e != _ve_prop_next_eq_1)
      {
        s.relevantInp->insert(e);
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
			}
		}

		rel = e;
	}break;
	case Wire:
	{
//		bins.relevantWires.push_back(e);
		WireInst* w = WireInst::as(e);
		Inst* port = w->get_port();
		evaluate_abstract_relation(mode, port, s);
		OpInst* op_port = OpInst::as(port);
		if (op_port)
		{
//			/// UP
//			if (op_port->get_euf_func_name() != "0")
			{
//				add_gate_consistency(w, bins.mainConstraints);
				if (is_next_wire(w))
					s.bins->relevantWiresNext.push_back(w);
				else
					s.bins->relevantWires.push_back(w);
			}
//				rel2 = OpInst::create(OpInst::Eq, w, op_port);
		}
		else
			assert(0);

		if (port->nsub_coi != port)
		  e->nsub_coi = port->nsub_coi;

//		rel = e;
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
#ifdef ABSTRACTION_COURSE
			if (Inst::check_if_uf_black(e) == INVALID)
				rel = e;
			else
#endif
			{
				call_eval_term = true;
//				if (mode == 3)
//				{
//					if (!(op_type == OpInst::Eq || op_type == OpInst::NotEq))
//						ufFlag = true;
//				}
			}
		}
	}
		break;
	case UF:
	case Ex: {
		call_eval_term = true;
//		if (mode == 3)
//			ufFlag = true;
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

		const InstL* ch = e->get_children();
		assert(ch != 0);
		bool all_ch_size_one = true;

		InstToInstM tmpMap;
		for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it)
		{
			if ((*it)->get_size() == 1)
			{
				evaluate_abstract_relation(mode, *it, s);
			}
			else
			{
				evaluate_abstract_term(mode, *it, s);
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
			rel = e;
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
			evaluate_abstract_relation(mode, *(ch->begin()), s);
			break;
		case OpInst::LogAnd:
		case OpInst::LogOr: {
			for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it)
			{
				if (mode == 1)
				{
					evaluate_abstract_relation(mode, *it, s);
				}
				else
				{
					int itVal = (*it)->get_bval();
					if (eVal == controlling(op_type))
					{
						if (itVal == controlling(op_type))
						{
							evaluate_abstract_relation(mode, *it, s);
							e->nsub_coi = (*it)->nsub_coi;
							break;
						}
					}
					else
					{
						evaluate_abstract_relation(mode, *it, s);
					}
				}
			}
		}break;
		case OpInst::Ternary: {
			InstL::const_iterator it = ch->begin();
			Inst* if_e = *(it++);
			Inst* then_e = *(it++);
			Inst* else_e = *(it++);
			evaluate_abstract_relation(mode, if_e, s);

			int ifVal = if_e->get_bval();
			if (mode == 1)
			{
				evaluate_abstract_relation(mode, else_e, s);
				evaluate_abstract_relation(mode, then_e, s);

				if (ifVal == 0) {
					e->acex_coi = else_e;
					e->nsub_coi = else_e->nsub_coi;
				} else if (ifVal == 1) {
					e->acex_coi = then_e;
          e->nsub_coi = then_e->nsub_coi;
				} else {
					assert(0);
				}
			}
			else
			{
				if (ifVal == 0) {
					evaluate_abstract_relation(mode, else_e, s);
					e->acex_coi = else_e;
          e->nsub_coi = else_e->nsub_coi;
				} else if (ifVal == 1) {
					evaluate_abstract_relation(mode, then_e, s);
					e->acex_coi = then_e;
          e->nsub_coi = then_e->nsub_coi;
				} else {
					assert(0);
				}
			}
		}break;
		default:
			assert(0);
		}
	}

	if (!e->acex_coi)
	{
		// We should put this code before rel is negated
		if (rel)
		{
			e->acex_coi = rel;
		}
		else
		{
			e->acex_coi = e;
		}
	}

	if (rel)
	{
		if (eVal == 0)
		{
			if (rel == NumInst::create(1, 1, SORT()))
				assert(0);

			rel = OpInst::create(OpInst::LogNot, rel);
			rel->set_bval(1);
		}
		if (rel == NumInst::create(0,1, SORT()))
		{
			cout << "Error inserting in c$: " << *rel << " [@ " << _trace_depth << " for " << *e << " ]" << endl;
			assert(0);
		}

		int rVal = rel->get_bval();
		if (rVal != 1)
		{
			cout << "e  : " << *e << " (val: " << eVal << ")" << endl;
			cout << "rel: " << *rel << " (val: " << rVal << ")" << endl;
//			cout << "e  : " << "invalid: " << Inst::check_v_important(e) << endl;
//			cout << "rel: " << "invalid: " << Inst::check_v_important(rel) << endl;
		}
		assert(rVal == 1);
	}

//	if (functionComposition)
//		rel = 0;

	if (is_redundant(rel))
		rel = 0;

#ifdef ALLOW_INPUTS_IN_PREFIX
	bool addInp = true;
#else
	bool addInp = false;
#endif
	if (rel)
	{
		_min_term.s.predicates.push_back(rel);
		rel->coi.set_pred();

		if (false)
		{
			if (rel->find_next())
			{
				s.bins->nextStateConstraints.push_back(rel);
				AVR_LOG(9, 1, "Inserting in c$: " << *rel << " [@ " << _trace_depth << " for " << *e << " ]" << endl);

	//			OpInst* op = OpInst::as(rel);
	//			if (op && (op->get_op() == OpInst::Eq))
	//			{
	//				Inst* lhs = op->get_children()->front();
	//				Inst* rhs = op->get_children()->back();
	//				assert(lhs && rhs);
	//
	//				if (!SigInst::as(lhs))
	//				{
	//					assert (SigInst::as(rhs));
	//					Inst* tmp = lhs;
	//					lhs = rhs;
	//					rhs = tmp;
	//				}
	//
	//				nextMap[lhs] = rhs;
	//
	//				if (lhs->get_size() == 1)
	//				{
	//					int lhsVal = lhs->get_bval();
	//					int rhsVal = rhs->get_bval();
	//					if (lhsVal != rhsVal)
	//					{
	//						cout << "LHS: " << *lhs << " -> " << lhsVal << endl;
	//						cout << "RHS: " << *rhs << " -> " << rhsVal << endl;
	//					}
	//					assert(lhsVal == rhsVal);
	//				}
	//				else
	//				{
	//					mpz_class lhsVal = lhs->get_ival();
	//					mpz_class rhsVal = rhs->get_ival();
	//					assert(lhsVal == rhsVal);
	//				}
	//
	//				if (lhs->get_size() != 1)
	//				{
	//					rel = try_intermediate_form(rel);
	//					bins.nextStateConstraints.push_back(rel);
	//				}
	//				else
	//				{
	//					rel = try_intermediate_form(rel);
	//					bins.nextStateConstraints.push_back(rel);
	////					AVR_LOG(9, 5, "No insert: " << " [ for " << *e << " ]_" << endl);
	//				}
	//			}
	//			else
	//			{
	//				assert(rel->get_size() == 1);
	//				rel = try_intermediate_form(rel);
	//				bins.nextStateConstraints.push_back(rel);
	//			}
			}
			else
			{
				rel = try_intermediate_form(rel);
				if (addInp || !find_input(rel))
					s.bins->mainConstraints.push_back(rel);
				AVR_LOG(9, 1, "Inserting in c: " << *rel << " [@ " << _trace_depth << " for " << *e << " ]" << endl);

				if (rel && rel == NumInst::create(0,1, SORT()))
				{
					cout << "Inserting in c: " << *rel << " [@ " << _trace_depth << "]" << endl;
					cout << "Cond: " << s.bins->mainConstraints << endl;
					cout << "Cond$: " << s.bins->nextStateConstraints << endl;
					assert(0);
				}
			}
		}
	}
	else
	{
		AVR_LOG(9, 5, "No insert: " << " [@ " << _trace_depth << " for " << *e << " ]" << endl);
	}

	if (isPred) {
	  Inst* eqRel = e->nsub_coi;
    if (eqRel->get_bval() == 0)
      eqRel = OpInst::create(OpInst::LogNot, eqRel);
	  if (eqRel != rel && !is_redundant(eqRel)) {
			_min_term.s.predicates.push_back(eqRel);
			eqRel->coi.set_local_pred();

			if (false)
			{
				if (eqRel->find_next()) {
					s.bins->nextStateConstraints.push_back(eqRel);
					AVR_LOG(9, 1, "Inserting in c$: " << *eqRel << " [@ " << _trace_depth << " for " << *e << " ]" << endl);
				}
				else {
					eqRel = try_intermediate_form(eqRel);
					if (addInp || !find_input(eqRel))
						s.bins->mainConstraints.push_back(eqRel);
					s.bins->concreteConstraints.push_back(eqRel);
					AVR_LOG(9, 1, "Inserting in c: " << *eqRel << " [@ " << _trace_depth << " for " << *e << " ]" << endl);
				}
			}
	  }
	}

	AVR_LOG(9, 2, "[EvalA] e: " << *e << " -> " << *(e->acex_coi) << endl);

//	if (e != e->acex_coi)
//		bins.internalEval[e->acex_coi].insert(e);

	_trace_depth--;
}

void Reach::evaluate_abstract_term(int mode, Inst*e, EVAL& s)
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

	mpz_class* eVal = e->get_ival();
	assert(eVal != INVALID_SMPZ);

	bool apply_on_children = false;

//	Inst* e_orig = e;
//#ifdef INTERPRET_EX_CC
//	OpInst* op = OpInst::as(e);
//	if (op)
//	{
//		e = op->t_simple;
//		assert(e->get_ival() == eVal);
//	}
//#endif

	e->acex_coi = e;
  e->nsub_coi = e;
	mpz_class* eaVal = e->acex_coi->get_ival();

	switch (e->get_type())
	{
	case Sig:
	{
		if (e->find_next())
		{
			if (Inst::has_trelation(e))
			{
				s.relevantSet->insert(e);
			}
      else
      {
        s.relevantInp->insert(e);
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
			}
		}

		// leave it as "itself"
	}break;
	case Wire:
	{
//		bins.relevantWires.push_back(e);
		WireInst* w = WireInst::as(e);
		Inst* port = w->get_port();
		evaluate_abstract_term(mode, port, s);
		OpInst* op_port = OpInst::as(port);
		if (op_port)
		{
//			if (op_port->get_euf_func_name() != "0")
			{
				if (is_next_wire(w))
					s.bins->relevantWiresNext.push_back(w);
				else
					s.bins->relevantWires.push_back(w);
//				rel2 = OpInst::create(OpInst::Eq, w, op_port);
			}
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
			evaluate_abstract_relation(mode, if_e, s);

			int ifVal = if_e->get_bval();
			if (mode == 1)
			{
				evaluate_abstract_term(mode, else_e, s);
				evaluate_abstract_term(mode, then_e, s);

				if (ifVal == 0) {
					e->acex_coi = else_e;
          e->nsub_coi = else_e->nsub_coi;
				} else if (ifVal == 1) {
					e->acex_coi = then_e;
          e->nsub_coi = then_e->nsub_coi;
				} else
					assert(0);
			}
			else
			{
				if (ifVal == 0) {
					evaluate_abstract_term(mode, else_e, s);
					e->acex_coi = else_e;
          e->nsub_coi = else_e->nsub_coi;
				} else if (ifVal == 1) {
					evaluate_abstract_term(mode, then_e, s);
					e->acex_coi = then_e;
          e->nsub_coi = then_e->nsub_coi;
				} else
					assert(0);
			}
			eaVal = e->acex_coi->get_ival();
		}
		else
		{
#ifdef ABSTRACTION_COURSE
			if (Inst::check_if_uf_black(e) == VALID)
#endif
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

		for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it)
		{
			if ((*it)->get_size() == 1)
			{
				evaluate_abstract_relation(mode, *it, s);
			}
			else
			{
				evaluate_abstract_term(mode, *it, s);
			}
		}
	}
	else
	{
		// leave it as ""itself"
	}

  assert(eaVal != INVALID_SMPZ);
//#ifndef ABSTRACTION_COURSE
//	assert(*eVal == *eaVal);
//#endif

	AVR_LOG(9, 2, "[EvalA] e: " << *e << " -> " << *(e->acex_coi) << endl);
	_trace_depth--;
}

/// Aman
/// mode = 1, Explore complete COI
/// else, explore relevant COI
/// mode = 3, same as else case but also assert no function composition
#ifdef	FIND_SUB_EXPRESSION
void Reach::evaluate_substitute_relation(int mode, Inst*e, ABSTRACT_REACH_VIOL& bins, InstToInstM& nextMap, InstS& relevantSet, bool init_visit)
{
	_trace_depth++;

	OpInst::OpType op_type = OpInst::Unknown;

	if (init_visit) {
		Inst::init_visit();
	}

	assert(e != 0);
	if (e->get_visit())
	{
		_trace_depth--;
		return;
	}
	e->set_visit();
	assert(e->get_size() == 1);

	// TODO temporary fix for the next state function, "reg_reset$next = 1"
	// With wn_simplify_const_pred enabled, "reg_reset$next = 1" is simplified as "reg_reset$next"
	// However, m_sn[reg_reset$next] still is a NumInst, 1'b1.
	// Therefore, eval_formula(2, 1'b1) is called due to the codes below "if (_m_sn.find(e) != _m_sn.end()) {"
	// As 1'b1 was not in T (omitted during simplification), its cex_val and cex_mpz  also have not been initialized
	// Here, I temporarily assign the fields, but I should fix this problem properly later.
	NumInst *num_temp = NumInst::as(e);
	if(num_temp)
	{
		if(e->get_size() == 1)
		{
			if(num_temp->get_num() == 0)
				e->set_bval(0);
			else
				e->set_bval(1);
		}
	}

	int eVal = e->get_bval();

	if((e->get_size() == 1) && (!(eVal == 1 || eVal == 0)))
	{
		cout << "e->cex_mpz: " << e->get_size() << "'d";
		cout << "e->val: " << eVal << endl;
		cout << "e: " << *e << endl;
		assert(0);
	}

	if (!(eVal == 1 || eVal == 0))
	{
		cout << "e->cex_mpz: " << e->get_size() << "'d";
		cout << "e->val: " << eVal << endl;
		cout << "e: " << *e << endl;
		assert(0);
	}

	AVR_LOG(9, 4, "[Eval]: " << *e << endl);

//	Inst* e_orig = e;
//#ifdef INTERPRET_EX_CC
//	OpInst* op = OpInst::as(e);
//	if (op)
//	{
//		e = op->t_simple;
//		assert(e->get_bval() == eVal);
//	}
//#endif

	// resulting relation to add to viol
	Inst* rel = 0;

	e->subs_coi = 0;

	bool intpd = false;
	bool call_eval_term = false;
	switch (e->get_type()) {
	case Sig:
	{
		if (e->find_next())
		{
			if (Inst::_m_sn.find(e) != Inst::_m_sn.end())
				relevantSet.insert(e);
		}
		else
		{
			if (Inst::_s_reg.find(e) != Inst::_s_reg.end())
				relevantSet.insert(e);
		}

		rel = e;
	}break;
	case Wire:
	{
		WireInst* w = WireInst::as(e);
		Inst* port = w->get_port();
		evaluate_substitute_relation(mode, port, bins, nextMap, relevantSet);
		e->subs_coi = port->subs_coi;
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
#ifdef ABSTRACTION_COURSE
			if (Inst::check_if_uf_black(e) == INVALID)
				rel = e;
			else
#endif
			{
				call_eval_term = true;
//				if (mode == 3)
//				{
//					if (!(op_type == OpInst::Eq || op_type == OpInst::NotEq))
//						ufFlag = true;
//				}
			}
		}
	}
		break;
	case UF:
	case Ex: {
		call_eval_term = true;
//		if (mode == 3)
//			ufFlag = true;
	}break;
	case Mem:
	default:
		assert(0);
	}

	// deal with all predicates (UPs and Equality)
	if (call_eval_term)
	{
		InstL new_ch;
		const InstL* ch = e->get_children();
		assert(ch != 0);
		bool need_new = false;
		bool all_ch_size_one = true;

		for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it)
		{
			if ((*it)->get_size() == 1)
			{
				evaluate_substitute_relation(mode, *it, bins, nextMap, relevantSet);
			}
			else
			{
				evaluate_substitute_term(mode, *it, bins, nextMap, relevantSet);
				all_ch_size_one = false;
			}
			new_ch.push_back((*it)->subs_coi);
			need_new = need_new || (*it != (*it)->subs_coi);
		}

		if((((op_type == OpInst::Eq) || (op_type == OpInst::NotEq)) && all_ch_size_one == true))
		{
			e->subs_coi = NumInst::create(eVal, e->get_size());
			// do nothing
		}
		else
		{
			if (need_new)
			{
				rel = e->apply_children(new_ch);

				int rVal = rel->get_bval();
				if (rVal != INVALID_SVAL)
				{
					if (rVal != eVal)
					{
						cout << "e  : " << *e << " (val: " << eVal << ")" << endl;
						cout << "rel: " << *rel << " (val: " << rVal << ")" << endl;
					}
					assert(rVal == eVal);
				}
				else
				{
					rel->set_bval(eVal);
				}
			}
			else
			{
				rel = e;
			}
		}
	}
	else if (intpd)
	{
		assert(e->get_type() == Op);
		const InstL* ch = e->get_children();
		assert(ch != 0);

		e->subs_coi = NumInst::create(eVal, e->get_size());

		switch (op_type)
		{
		case OpInst::LogNot:
			evaluate_substitute_relation(mode, *(ch->begin()), bins, nextMap, relevantSet);
			break;
		case OpInst::LogAnd:
		case OpInst::LogOr: {
			for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it)
			{
				if (mode == 1)
				{
					evaluate_substitute_relation(mode, *it, bins, nextMap, relevantSet);
				}
				else
				{
					int itVal = (*it)->get_bval();
					if (eVal == controlling(op_type))
					{
						if (itVal == controlling(op_type))
						{
							evaluate_substitute_relation(mode, *it, bins, nextMap, relevantSet);
							break;
						}
					}
					else
					{
						evaluate_substitute_relation(mode, *it, bins, nextMap, relevantSet);
					}
				}
			}
		}break;
		case OpInst::Ternary: {
			InstL::const_iterator it = ch->begin();
			Inst* if_e = *(it++);
			Inst* then_e = *(it++);
			Inst* else_e = *(it++);
			evaluate_substitute_relation(mode, if_e, bins, nextMap, relevantSet);

			int ifVal = if_e->get_bval();
			if (mode == 1)
			{
				evaluate_substitute_relation(mode, else_e, bins, nextMap, relevantSet);
				evaluate_substitute_relation(mode, then_e, bins, nextMap, relevantSet);

				if (ifVal == 0) {
					e->subs_coi = else_e->subs_coi;
				} else if (ifVal == 1) {
					e->subs_coi = then_e->subs_coi;
				} else {
					assert(0);
				}
			}
			else
			{
				if (ifVal == 0) {
					evaluate_substitute_relation(mode, else_e, bins, nextMap, relevantSet);
					e->subs_coi = else_e->subs_coi;
				} else if (ifVal == 1) {
					evaluate_substitute_relation(mode, then_e, bins, nextMap, relevantSet);
					e->subs_coi = then_e->subs_coi;
				} else {
					assert(0);
				}
			}
		}break;
		default:
			assert(0);
		}
	}

	if (!e->subs_coi)
	{
		// We should put this code before rel is negated
		if (rel)
		{
			e->subs_coi = rel;
		}
		else
		{
			e->subs_coi = e;
		}
	}

	if (rel)
	{
		if (eVal == 0)
		{
			if (rel == NumInst::create(1, 1))
				assert(0);

			rel = OpInst::create(OpInst::LogNot, rel);
			rel->set_bval(1);
		}
		if (rel == NumInst::create(0,1))
		{
			cout << "Error inserting in c$: " << *rel << " [@ " << _trace_depth << " for " << *e << " ]" << endl;
			assert(0);
		}

		int rVal = rel->get_bval();
		if (rVal != 1)
		{
			cout << "e  : " << *e << " (val: " << eVal << ")" << endl;
			cout << "rel: " << *rel << " (val: " << rVal << ")" << endl;
//			cout << "e  : " << "invalid: " << Inst::check_v_important(e) << endl;
//			cout << "rel: " << "invalid: " << Inst::check_v_important(rel) << endl;
		}
		assert(rVal == 1);
	}

//	if (functionComposition)
//		rel = 0;

	if (is_redundant(rel))
		rel = 0;

	if (rel)
	{
		if (rel->find_next())
		{
			bins.nextStateConstraints.push_back(rel);
			AVR_LOG(9, 1, "Inserting in c$: " << *rel << " [@ " << _trace_depth << " for " << *e << " ]" << endl);
		}
		else
		{
			rel = try_intermediate_form(rel);
			bins.mainConstraints.push_back(rel);
			AVR_LOG(9, 1, "Inserting in c: " << *rel << " [@ " << _trace_depth << " for " << *e << " ]" << endl);

			if (rel && rel == NumInst::create(0,1))
			{
				cout << "Inserting in c: " << *rel << " [@ " << _trace_depth << "]" << endl;
				cout << "Cond: " << bins.mainConstraints << endl;
				cout << "Cond$: " << bins.nextStateConstraints << endl;
				assert(0);
			}
		}
	}
	else
	{
		AVR_LOG(9, 5, "No insert: " << " [@ " << _trace_depth << " for " << *e << " ]" << endl);
	}

	AVR_LOG(9, 2, "[EvalA] e: " << *e << " -> " << *(e->subs_coi) << endl);

	_trace_depth--;
}

void Reach::evaluate_substitute_term(int mode, Inst*e, ABSTRACT_REACH_VIOL& bins, InstToInstM& nextMap, InstS& relevantSet)
{
	_trace_depth++;
	assert(e != 0);
	if (e->get_visit())
	{
		_trace_depth--;
		return;
	}
	e->set_visit();
	AVR_LOG(9, 4, "[Eval]: " << *e << endl);

	mpz_class* eVal = e->get_ival();
	assert(eVal != INVALID_SMPZ);

	bool apply_on_children = false;

//	Inst* e_orig = e;
//#ifdef INTERPRET_EX_CC
//	OpInst* op = OpInst::as(e);
//	if (op)
//	{
//		e = op->t_simple;
//		assert(e->get_ival() == eVal);
//	}
//#endif

	e->subs_coi = e;
	mpz_class* eaVal = e->subs_coi->get_ival();

	switch (e->get_type())
	{
	case Sig:
	{
		if (e->find_next())
		{
			if (Inst::_m_sn.find(e) != Inst::_m_sn.end())
				relevantSet.insert(e);
		}
		else
		{
			if (Inst::_s_reg.find(e) != Inst::_s_reg.end())
				relevantSet.insert(e);
		}

		// leave it as "itself"
	}break;
	case Wire:
	{
//		bins.relevantWires.push_back(e);
		WireInst* w = WireInst::as(e);
		Inst* port = w->get_port();
		evaluate_substitute_term(mode, w->get_port(), bins, nextMap, relevantSet);
		e->subs_coi = port->subs_coi;
	}break;
	case Const:
	{
		assert(0);
	}break;
	case Num:
	{
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
			evaluate_substitute_relation(mode, if_e, bins, nextMap, relevantSet);

			int ifVal = if_e->get_bval();
			if (mode == 1)
			{
				evaluate_substitute_term(mode, else_e, bins, nextMap, relevantSet);
				evaluate_substitute_term(mode, then_e, bins, nextMap, relevantSet);

				if (ifVal == 0) {
					e->subs_coi = else_e->subs_coi;
				} else if (ifVal == 1) {
					e->subs_coi = then_e->subs_coi;
				} else
					assert(0);
			}
			else
			{
				if (ifVal == 0) {
					evaluate_substitute_term(mode, else_e, bins, nextMap, relevantSet);
					e->subs_coi = else_e->subs_coi;
				} else if (ifVal == 1) {
					evaluate_substitute_term(mode, then_e, bins, nextMap, relevantSet);
					e->subs_coi = then_e->subs_coi;
				} else
					assert(0);
			}
			eaVal = e->subs_coi->get_ival();
		}
		else
		{
#ifdef ABSTRACTION_COURSE
			if (Inst::check_if_uf_black(e) == VALID)
#endif
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
		const InstL* ch = e->get_children();
		assert(ch != 0);
		InstL new_ch;
		bool need_new = false;

		for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it)
		{
			if ((*it)->get_size() == 1)
			{
				evaluate_substitute_relation(mode, *it, bins, nextMap, relevantSet);
			}
			else
			{
				evaluate_substitute_term(mode, *it, bins, nextMap, relevantSet);
			}
			new_ch.push_back((*it)->subs_coi);
			need_new = need_new || (*it != (*it)->subs_coi);
		}
		if (need_new)
		{
			e->subs_coi = e->apply_children(new_ch);

			eaVal = e->subs_coi->get_ival();
			if (eaVal != INVALID_SMPZ)
			{
				if (*eaVal != *eVal)
				{
					cout << "newCh: " << new_ch << endl;
					cout << "e      : " << *e << " (val: " << eVal << ")" << endl;
					cout << "e->subs_coi: " << *(e->subs_coi) << " (val: " << eaVal << ")" << endl;
				}
				assert(*eaVal == *eVal);
			}
			else
			{
				e->subs_coi->set_ival(eVal);
				eaVal = eVal;
			}
		}
	}
	else
	{
		// leave it as ""itself"
	}

  assert(eaVal != INVALID_SMPZ);
//#ifndef ABSTRACTION_COURSE
	assert(*eVal == *eaVal);
//#endif

	AVR_LOG(9, 2, "[EvalA] e: " << *e << " -> " << *(e->subs_coi) << endl);
	_trace_depth--;
}
#endif

/// Aman
/// mode = 1, Explore complete COI
/// else, explore relevant COI
/// mode = 3, same as else case but also assert no function composition
#ifdef	FIND_SUB_EXPRESSION
void Reach::evaluate_path_relation(int mode, Inst*e, ABSTRACT_REACH_VIOL& bins, InstToInstM& nextMap, bool init_visit)
{
	_trace_depth++;

	OpInst::OpType op_type = OpInst::Unknown;

	if (init_visit) {
		Inst::init_visit();
	}

	assert(e != 0);
	if (e->get_visit())
	{
		_trace_depth--;
		return;
	}
	e->set_visit();
	assert(e->get_size() == 1);

	// TODO temporary fix for the next state function, "reg_reset$next = 1"
	// With wn_simplify_const_pred enabled, "reg_reset$next = 1" is simplified as "reg_reset$next"
	// However, m_sn[reg_reset$next] still is a NumInst, 1'b1.
	// Therefore, eval_formula(2, 1'b1) is called due to the codes below "if (_m_sn.find(e) != _m_sn.end()) {"
	// As 1'b1 was not in T (omitted during simplification), its cex_val and cex_mpz  also have not been initialized
	// Here, I temporarily assign the fields, but I should fix this problem properly later.
	NumInst *num_temp = NumInst::as(e);
	if(num_temp)
	{
		if(e->get_size() == 1)
		{
			if(num_temp->get_num() == 0)
				e->set_bval(0);
			else
				e->set_bval(1);
		}
	}

	int eVal = e->get_bval();

	if((e->get_size() == 1) && (!(eVal == 1 || eVal == 0)))
	{
		cout << "e->cex_mpz: " << e->get_size() << "'d";
		cout << "e->val: " << eVal << endl;
		cout << "e: " << *e << endl;
		assert(0);
	}

	if (!(eVal == 1 || eVal == 0))
	{
		cout << "e->cex_mpz: " << e->get_size() << "'d";
		cout << "e->val: " << eVal << endl;
		cout << "e: " << *e << endl;
		assert(0);
	}

	AVR_LOG(9, 4, "[Eval]: " << *e << endl);

//	Inst* e_orig = e;
//#ifdef INTERPRET_EX_CC
//	OpInst* op = OpInst::as(e);
//	if (op)
//	{
//		e = op->t_simple;
//		assert(e->get_bval() == eVal);
//	}
//#endif

	// resulting relation to add to viol
	Inst* rel = 0;

	e->subs_coi = 0;

	bool intpd = false;
	bool call_eval_term = false;
	switch (e->get_type()) {
	case Sig:
	{
		if (e->find_next())
		{
			InstToInstM::iterator mit = nextMap.find(e);
			if (mit != nextMap.end())
			{
				rel = (*mit).second;

				int rVal = rel->get_bval();
				if (rVal != eVal)
				{
					cout << "rel: " << *rel << " " << rVal << endl;
					cout << "e: " << *e << " " << eVal << endl;
					assert(0);
				}
			}
			// else, it's prop$next or input
			else
			{
				rel = e;
			}
		}
		else
		{
			rel = e;
		}

	}break;
	case Wire:
	{
		WireInst* w = WireInst::as(e);
		Inst* port = w->get_port();
		evaluate_path_relation(mode, port, bins, nextMap);
		e->subs_coi = port->subs_coi;
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
#ifdef ABSTRACTION_COURSE
			if (Inst::check_if_uf_black(e) == INVALID)
				rel = e;
			else
#endif
			{
				call_eval_term = true;
//				if (mode == 3)
//				{
//					if (!(op_type == OpInst::Eq || op_type == OpInst::NotEq))
//						ufFlag = true;
//				}
			}
		}
	}
		break;
	case UF:
	case Ex: {
		call_eval_term = true;
//		if (mode == 3)
//			ufFlag = true;
	}break;
	case Mem:
	default:
		assert(0);
	}

	// deal with all predicates (UPs and Equality)
	if (call_eval_term)
	{
		InstL new_ch;
		const InstL* ch = e->get_children();
		assert(ch != 0);
		bool need_new = false;
		bool all_ch_size_one = true;

		for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it)
		{
			if ((*it)->get_size() == 1)
			{
				evaluate_path_relation(mode, *it, bins, nextMap);
			}
			else
			{
				evaluate_path_term(mode, *it, bins, nextMap);
				all_ch_size_one = false;
			}
			new_ch.push_back((*it)->subs_coi);
			need_new = need_new || (*it != (*it)->subs_coi);
		}

		if((((op_type == OpInst::Eq) || (op_type == OpInst::NotEq)) && all_ch_size_one == true))
		{
			e->subs_coi = NumInst::create(eVal, e->get_size());
			// do nothing
		}
		else
		{
			if (need_new)
			{
				rel = e->apply_children(new_ch);

				int rVal = rel->get_bval();
				if (rVal != INVALID_SVAL)
				{
					if (rVal != eVal)
					{
						cout << "e  : " << *e << " (val: " << eVal << ")" << endl;
						cout << "rel: " << *rel << " (val: " << rVal << ")" << endl;
					}
					assert(rVal == eVal);
				}
				else
				{
					rel->set_bval(eVal);
				}
			}
			else
			{
				rel = e;
			}
		}
	}
	else if (intpd)
	{
		assert(e->get_type() == Op);
		const InstL* ch = e->get_children();
		assert(ch != 0);

		e->subs_coi = NumInst::create(eVal, e->get_size());

		switch (op_type)
		{
		case OpInst::LogNot:
			evaluate_path_relation(mode, *(ch->begin()), bins, nextMap);
			break;
		case OpInst::LogAnd:
		case OpInst::LogOr: {
			for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it)
			{
				if (mode == 1)
				{
					evaluate_path_relation(mode, *it, bins, nextMap);
				}
				else
				{
					int itVal = (*it)->get_bval();
					if (eVal == controlling(op_type))
					{
						if (itVal == controlling(op_type))
						{
							evaluate_path_relation(mode, *it, bins, nextMap);
							break;
						}
					}
					else
					{
						evaluate_path_relation(mode, *it, bins, nextMap);
					}
				}
			}
		}break;
		case OpInst::Ternary: {
			InstL::const_iterator it = ch->begin();
			Inst* if_e = *(it++);
			Inst* then_e = *(it++);
			Inst* else_e = *(it++);
			evaluate_path_relation(mode, if_e, bins, nextMap);

			int ifVal = if_e->get_bval();
			if (mode == 1)
			{
				evaluate_path_relation(mode, else_e, bins, nextMap);
				evaluate_path_relation(mode, then_e, bins, nextMap);

				if (ifVal == 0) {
					e->subs_coi = else_e->subs_coi;
				} else if (ifVal == 1) {
					e->subs_coi = then_e->subs_coi;
				} else {
					assert(0);
				}
			}
			else
			{
				if (ifVal == 0) {
					evaluate_path_relation(mode, else_e, bins, nextMap);
					e->subs_coi = else_e->subs_coi;
				} else if (ifVal == 1) {
					evaluate_path_relation(mode, then_e, bins, nextMap);
					e->subs_coi = then_e->subs_coi;
				} else {
					assert(0);
				}
			}
		}break;
		default:
			assert(0);
		}
	}

	if (!e->subs_coi)
	{
		// We should put this code before rel is negated
		if (rel)
		{
			e->subs_coi = rel;
		}
		else
		{
			e->subs_coi = e;
		}
	}

	if (rel)
	{
		if (eVal == 0)
		{
			if (rel == NumInst::create(1, 1))
				assert(0);

			rel = OpInst::create(OpInst::LogNot, rel);
			rel->set_bval(1);
		}
		if (rel == NumInst::create(0,1))
		{
			cout << "Error inserting in c$: " << *rel << " [@ " << _trace_depth << " for " << *e << " ]" << endl;
			assert(0);
		}

		int rVal = rel->get_bval();
		if (rVal != 1)
		{
			cout << "e  : " << *e << " (val: " << eVal << ")" << endl;
			cout << "rel: " << *rel << " (val: " << rVal << ")" << endl;
//			cout << "e  : " << "invalid: " << Inst::check_v_important(e) << endl;
//			cout << "rel: " << "invalid: " << Inst::check_v_important(rel) << endl;
		}
		assert(rVal == 1);
	}

//	if (functionComposition)
//		rel = 0;

	if (is_redundant(rel))
		rel = 0;

	if (rel)
	{
		if (rel->find_next())
		{
			// Do nothing
		}
		else
		{
//			if ((rel->fcLevel == 0) || (rel->trueFcLevel > 0 && rel->trueFcLevel <= _max_funcLevel))
			{
				rel = try_intermediate_form(rel);
//				AVR_LOG(15, 0, "\t\t" << *rel << endl);
				bins.subsConstraints.push_back(rel);
	//			AVR_LOG(15, 0, "(path) " << *e << " -> " << *rel << ")" << endl);
				AVR_LOG(9, 1, "Inserting in c: " << *rel << " [@ " << _trace_depth << " for " << *e << " ]" << endl);

				if (rel && rel == NumInst::create(0,1))
				{
					cout << "Inserting in c: " << *rel << " [@ " << _trace_depth << "]" << endl;
					cout << "Cond: " << bins.mainConstraints << endl;
					cout << "Cond$: " << bins.nextStateConstraints << endl;
					assert(0);
				}
			}
//			else
//			{
//				AVR_LOG(9, 5, "No insert: " << " [@ " << _trace_depth << " for " << *e << " ]" << endl);
//			}
		}
	}
	else
	{
		AVR_LOG(9, 5, "No insert: " << " [@ " << _trace_depth << " for " << *e << " ]" << endl);
	}

	AVR_LOG(9, 2, "[EvalA] e: " << *e << " -> " << *(e->subs_coi) << endl);

	_trace_depth--;
}

void Reach::evaluate_path_term(int mode, Inst*e, ABSTRACT_REACH_VIOL& bins, InstToInstM& nextMap)
{
	_trace_depth++;
	assert(e != 0);
	if (e->get_visit())
	{
		_trace_depth--;
		return;
	}
	e->set_visit();
	AVR_LOG(9, 4, "[Eval]: " << *e << endl);

	mpz_class* eVal = e->get_ival();
	assert(eVal != INVALID_SMPZ);

	bool apply_on_children = false;

//	Inst* e_orig = e;
//#ifdef INTERPRET_EX_CC
//	OpInst* op = OpInst::as(e);
//	if (op)
//	{
//		e = op->t_simple;
//		assert(e->get_ival() == eVal);
//	}
//#endif

	e->subs_coi = e;
	mpz_class* eaVal = e->subs_coi->get_ival();

	switch (e->get_type())
	{
	case Sig:
	{
		if (e->find_next())
		{
			InstToInstM::iterator mit = nextMap.find(e);
			if (mit != nextMap.end())
			{
				e->subs_coi = (*mit).second;
			}
			else
			{
				e->subs_coi = e;
			}
		}
		else
		{
			e->subs_coi = e;
		}

		// leave it as "itself"
	}break;
	case Wire:
	{
//		bins.relevantWires.push_back(e);
		WireInst* w = WireInst::as(e);
		Inst* port = w->get_port();
		evaluate_path_term(mode, w->get_port(), bins, nextMap);
		e->subs_coi = port->subs_coi;
	}break;
	case Const:
	{
		assert(0);
	}break;
	case Num:
	{
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
			evaluate_path_relation(mode, if_e, bins, nextMap);

			int ifVal = if_e->get_bval();
			if (mode == 1)
			{
				evaluate_path_term(mode, else_e, bins, nextMap);
				evaluate_path_term(mode, then_e, bins, nextMap);

				if (ifVal == 0) {
					e->subs_coi = else_e->subs_coi;
				} else if (ifVal == 1) {
					e->subs_coi = then_e->subs_coi;
				} else
					assert(0);
			}
			else
			{
				if (ifVal == 0) {
					evaluate_path_term(mode, else_e, bins, nextMap);
					e->subs_coi = else_e->subs_coi;
				} else if (ifVal == 1) {
					evaluate_path_term(mode, then_e, bins, nextMap);
					e->subs_coi = then_e->subs_coi;
				} else
					assert(0);
			}
			eaVal = e->subs_coi->get_ival();
		}
		else
		{
#ifdef ABSTRACTION_COURSE
			if (Inst::check_if_uf_black(e) == VALID)
#endif
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
		const InstL* ch = e->get_children();
		assert(ch != 0);
		InstL new_ch;
		bool need_new = false;

		for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it)
		{
			if ((*it)->get_size() == 1)
			{
				evaluate_path_relation(mode, *it, bins, nextMap);
			}
			else
			{
				evaluate_path_term(mode, *it, bins, nextMap);
			}
			new_ch.push_back((*it)->subs_coi);
			need_new = need_new || (*it != (*it)->subs_coi);
		}
		if (need_new)
		{
			e->subs_coi = e->apply_children(new_ch);

			eaVal = e->subs_coi->get_ival();
			if (eaVal != INVALID_SMPZ)
			{
				if (*eaVal != *eVal)
				{
					cout << "newCh: " << new_ch << endl;
					cout << "e      : " << *e << " (val: " << eVal << ")" << endl;
					cout << "e->subs_coi: " << *(e->subs_coi) << " (val: " << eaVal << ")" << endl;
				}
				assert(*eaVal == *eVal);
			}
			else
			{
				e->subs_coi->set_ival(eVal);
				eaVal = eVal;
			}
		}
	}
	else
	{
		// leave it as ""itself"
	}

  assert(eaVal != INVALID_SMPZ);
//#ifndef ABSTRACTION_COURSE
	assert(*eVal == *eaVal);
//#endif

	AVR_LOG(9, 2, "[EvalA] e: " << *e << " -> " << *(e->subs_coi) << endl);
	_trace_depth--;
}
#endif

/// Aman
/// mode = 1, Explore complete COI
/// else, explore relevant COI
/// same as else case but assert no function composition
void Reach::evaluate_abstract_destination(int mode, Inst*e, InstL& bin_pre, InstToInstM& nextMap, bool init_visit)
{
	OpInst::OpType op_type = OpInst::Unknown;

	if (init_visit) {
		Inst::init_visit();
	}

	assert(e != 0);
	if (e->get_visit())
	{
		return;
	}
	e->set_visit();
	assert(e->get_size() == 1);

	// TODO temporary fix for the next state function, "reg_reset$next = 1"
	// With wn_simplify_const_pred enabled, "reg_reset$next = 1" is simplified as "reg_reset$next"
	// However, m_sn[reg_reset$next] still is a NumInst, 1'b1.
	// Therefore, eval_formula(2, 1'b1) is called due to the codes below "if (_m_sn.find(e) != _m_sn.end()) {"
	// As 1'b1 was not in T (omitted during simplification), its cex_val and cex_mpz  also have not been initialized
	// Here, I temporarily assign the fields, but I should fix this problem properly later.
	NumInst *num_temp = NumInst::as(e);
	if(num_temp)
	{
		if(e->get_size() == 1)
		{
			if(num_temp->get_num() == 0)
				e->set_bval(0);
			else
				e->set_bval(1);
		}
	}

	int eVal = e->get_bval();

	if((e->get_size() == 1) && (!(eVal == 1 || eVal == 0)))
	{
		cout << "e->cex_mpz: " << e->get_size() << "'d";
		cout << "e->val: " << eVal << endl;
		cout << "e: " << *e << endl;
		assert(0);
	}

	if (!(eVal == 1 || eVal == 0))
	{
		cout << "e->cex_mpz: " << e->get_size() << "'d";
		cout << "e->val: " << eVal << endl;
		cout << "e: " << *e << endl;
		assert(0);
	}

	AVR_LOG(9, 4, "[EvalD]: " << *e << endl);

	Inst* e_orig = e;
//#ifdef INTERPRET_EX_CC
//	OpInst* op = OpInst::as(e);
//	if (op)
//	{
//		e = op->t_simple;
//		assert(e->get_bval() == eVal);
//	}
//#endif

	// resulting relation to add to viol
	Inst* rel = 0;
	e->acex_coi = 0;

	bool ufFlag = false;
	bool functionComposition = false;

	bool intpd = false;
	bool call_eval_term = false;
	bool op_concat = false;
	switch (e->get_type()) {
	case Sig:
	{
		SigInst* sig = SigInst::as(e);
		assert(sig);
		if (sig->childrenInfo[NEXT])
		{
			InstToInstM::iterator mit = nextMap.find(e);
			if (mit != nextMap.end())
			{
				rel = (*mit).second;
				int rVal = rel->get_bval();
				if (rVal != eVal)
				{
					cout << "rel: " << *rel << " " << rVal << endl;
					cout << "e: " << *e << " " << eVal << endl;
					assert(0);
				}
			}
			// else, it's prop$next or input
			else
			{
				rel = e;
			}
		}
		else
		{
			rel = e;
		}
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

			op_concat = true;
			if (mode == 3)
				ufFlag = true;
		}
		else
		{
#ifdef ABSTRACTION_COURSE
			if (Inst::check_if_uf_black(e) == INVALID)
				rel = e;
			else
#endif
			{
				call_eval_term = true;
				if (!(op_type == OpInst::Eq || op_type == OpInst::NotEq))
				{
					if (mode == 3)
						ufFlag = true;
				}
			}
		}
	}
		break;
	case UF:
	case Ex: {
		{
			call_eval_term = true;
			if (mode == 3)
				ufFlag = true;
		}
	}break;
	case Mem:
	default:
		assert(0);
	}

	// deal with all predicates (UPs and Equality)
	if (call_eval_term)
	{
		InstL new_ch;
		const InstL* ch = e->get_children();
		assert(ch != 0);
		bool need_new = false;
		bool all_ch_size_one = true;

		for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it)
		{
			if ((*it)->get_size() == 1)
			{
				evaluate_abstract_destination(mode, *it, bin_pre, nextMap);
				if ((*it)->acex_coi->acex_fc)
				{
					functionComposition = true;
				}
			}
			else
			{
				all_ch_size_one = false;
				evaluate_abstract_destination_term(mode, *it, bin_pre, nextMap);
				if ((*it)->acex_coi->acex_fc)
				{
					functionComposition = true;
				}
			}

			if (*it != (*it)->acex_coi)
			{
				if (ufFlag)
				{
					if (functionComposition == false && (*it)->acex_coi->get_type() == Op)
					{
						OpInst* op = OpInst::as((*it)->acex_coi);
						assert(op);
						if (op->get_euf_func_name() != "0")
						{
							functionComposition = true;
						}
					}
					else
					{
						ExInst* ex = ExInst::as((*it)->acex_coi);
						if (ex)
						{
							functionComposition = true;
						}
					}
				}
				need_new = true;
			}
			new_ch.push_back((*it)->acex_coi);
		}

//		 we cannot comment out the following 7 lines => it leads to a wrong result (return SAT for UNSAT probs)
//		 this is because of a literal, (prop$next = (~~)) & (~~) & prop$next(prop$next is later dropped)
//		 that is produced without the following 7 lines.
//		 Instead, (~~) should be produced!
//		 during PME generalization, (prop$next = (~~)) sometimes is chosen as one of literals in an UNSAT core,
//		 but (prop$next = true) which is important literal (should be added) is missing, because it is in the
//		 formula used during PME (this is a very rough and vague explanation. I'm going to update this later.)
//		if((((op_type == OpInst::Eq) || (op_type == OpInst::NotEq)) && all_ch_size_one == true))
//		{
//			e->acex_coi = NumInst::create(eVal, e->get_size());
//			// do nothing
//		}
//		else
		{
//			if (functionComposition)
//			{
//				rel = 0;
//			}

			if (need_new)
			{
				rel = e->apply_children(new_ch);

				int rVal = rel->get_bval();
				if (false && rVal != INVALID_SVAL)
				{
					if (rVal != eVal)
					{
						cout << "e  : " << *e << " (val: " << eVal << ")" << endl;
						cout << "rel: " << *rel << " (val: " << rVal << ")" << endl;
					}
//#ifndef ABSTRACTION_COURSE
					assert(rVal == eVal);
//#endif
				}
				else
				{
					rel->set_bval(eVal);
				}
			}
			else
			{
				rel = e;
			}
		}
	}
	else if (op_concat)
	{
		InstL new_ch;
		const InstL* ch = e->get_children();
		assert(ch != 0);
		bool need_new = false;

		//cout << "op_concat" << endl;
		bool all_ch_size_one = true;
		for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it)
		{
			if ((*it)->get_size() == 1)
			{
				evaluate_abstract_destination(mode, *it, bin_pre, nextMap);
				if ((*it)->acex_coi->acex_fc)
				{
					functionComposition = true;
				}
			}
			else
			{
				all_ch_size_one = false;
				evaluate_abstract_destination_term(mode, *it, bin_pre, nextMap);
				if ((*it)->acex_coi->acex_fc)
				{
					functionComposition = true;
				}
			}

			if (*it != (*it)->acex_coi)
			{
				if (ufFlag)
				{
					if (functionComposition == false && (*it)->acex_coi->get_type() == Op)
					{
						OpInst* op = OpInst::as((*it)->acex_coi);
						assert(op);
						if (op->get_euf_func_name() != "0")
						{
							functionComposition = true;
						}
					}
					else
					{
						ExInst* ex = ExInst::as((*it)->acex_coi);
						if (ex)
						{
							functionComposition = true;
						}
					}
				}
				need_new = true;
			}
			new_ch.push_back((*it)->acex_coi);
		}

//		if (functionComposition)
//		{
//			rel = 0;
//		}

		if (need_new)
		{
			rel = e->apply_children(new_ch);

			int rVal = rel->get_bval();
			if (false && rVal != INVALID_SVAL)
			{
				if (rVal != eVal)
				{
					cout << "e  : " << *e << " (val: " << eVal << ")" << endl;
					cout << "rel: " << *rel << " (val: " << rVal << ")" << endl;
				}
//#ifndef ABSTRACTION_COURSE
				assert(rVal == eVal);
//#endif
			}
			else
			{
				rel->set_bval(eVal);
			}
		}
		else
		{
			rel = e;
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
			evaluate_abstract_destination(mode, *(ch->begin()), bin_pre, nextMap);
			break;
		case OpInst::LogAnd:
		case OpInst::LogOr: {
			for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it)
			{
				if (mode == 1)
				{
					evaluate_abstract_destination(mode, *it, bin_pre, nextMap);
				}
				else
				{
					int itVal = (*it)->get_bval();
					if ((eVal != controlling(op_type)) || (itVal == controlling(op_type)))
						evaluate_abstract_destination(mode, *it, bin_pre, nextMap);
					if ((eVal == controlling(op_type)) && (itVal == controlling(op_type)))
							break;

				}
			}
		}break;
		case OpInst::Ternary: {
			InstL::const_iterator it = ch->begin();
			Inst* if_e = *(it++);
			Inst* then_e = *(it++);
			Inst* else_e = *(it++);
			evaluate_abstract_destination(mode, if_e, bin_pre, nextMap);

			int ifVal = if_e->get_bval();
			if (mode == 1)
			{
				evaluate_abstract_destination(mode, else_e, bin_pre, nextMap);
				evaluate_abstract_destination(mode, then_e, bin_pre, nextMap);

				if (ifVal == 0) {
					e->acex_coi = else_e->acex_coi;
				} else if (ifVal == 1) {
					e->acex_coi = then_e->acex_coi;
				} else {
					assert(0);
				}
			}
			else
			{
				if (ifVal == 0) {
					evaluate_abstract_destination(mode, else_e, bin_pre, nextMap);
					e->acex_coi = else_e->acex_coi;
				} else if (ifVal == 1) {
					evaluate_abstract_destination(mode, then_e, bin_pre, nextMap);
					e->acex_coi = then_e->acex_coi;
				} else {
					assert(0);
				}
			}
		}break;
		default:
			assert(0);
		}
	}

	if (!e->acex_coi)
	{
		// We should put this code before rel is negated
		if (rel)
		{
			e->acex_coi = rel;
		}
		else
		{
			e->acex_coi = e;
		}
	}

	if (functionComposition)
		e->acex_coi->acex_fc = true;

	if (e_orig != e)
	{
		e_orig->acex_coi = e->acex_coi;
		AVR_LOG(9, 1, "[EvalD] simplified: " << *e_orig << " -> " << *(e->acex_coi) << endl);
	}

	if (rel)
	{
		if (eVal == 0)
		{
			rel = OpInst::create(OpInst::LogNot, rel);
			rel->set_bval(1);
		}
		if (rel == NumInst::create(0,1, SORT()))
		{
			cout << "Error inserting in c$: " << *rel << " [@ " << _trace_depth << " for " << *e << " ]" << endl;
			assert(0);
		}
		int rVal = rel->get_bval();
		assert(rVal == 1);
	}

//	if (mode != 3)
//		assert(functionComposition == false);

	if (is_redundant(rel))
		rel = 0;

	if (rel)
	{
		if (rel->find_next())
		{
			AVR_LOG(9, 5, "No insert: " << " [ for " << *e << " ]_" << ufFlag << "_" << functionComposition << endl);
		}
		else
		{
			if (rel != NumInst::create(1, 1, SORT()))
			{
#ifdef REACH_ADD_PATH_CONSTRAINTS
				if (bin_pre == _abViol.pathConstraints)
					num_path_constraints++;
#endif

				if ((mode != 3) || (!functionComposition))
				{
					bin_pre.push_back(rel);
					AVR_LOG(9, 1, "Inserting in _viol$: " << *rel << " [ for " << *e << " ]_" << ufFlag << "_" << functionComposition << endl);

#ifdef REACH_ADD_PATH_CONSTRAINTS
					if (bin_pre == _abViol.pathConstraints)
						num_path_constraints_taken++;
#endif
				}
#ifdef LIMIT_WLP_USING_FCLEVEL
				else
				{
					if (rel->fcLevel <= _allowed_funcLevel)
					{
						bin_pre.push_back(rel);
						AVR_LOG(9, 5, "Inserting in _viol$: " << *rel << " [ for " << *e << " ]_" << ufFlag << "_" << functionComposition << endl);

						if (bin_pre == _abViol.pathConstraints)
							num_path_constraints_taken++;
					}
				}
#endif
			}
			else
			{
				AVR_LOG(9, 5, "No insert: " << " [ for " << *e << " ]_" << ufFlag << "_" << functionComposition << endl);
			}
		}
	}
	else
	{
		AVR_LOG(9, 5, "No insert: " << " [ for " << *e << " ]_" << ufFlag << "_" << functionComposition << endl);
	}
	AVR_LOG(9, 2, "[EvalD] e: " << *e << " -> " << *(e->acex_coi) << endl);
}


void Reach::evaluate_abstract_destination_term(int mode, Inst*e, InstL& bin_pre, InstToInstM& nextMap)
{
	assert(e != 0);
	if (e->get_visit())
	{
	}
	e->set_visit();
	AVR_LOG(9, 4, "[EvalD]: " << *e << endl);

	mpz_class* eVal = e->get_ival();

	bool apply_on_children = false;

	Inst* e_orig = e;
//#ifdef INTERPRET_EX_CC
//	OpInst* op = OpInst::as(e);
//	if (op)
//	{
//		e = op->t_simple;
//		if (e->get_ival() != eVal)
//		{
//			cout << *e_orig << " = " << eVal << endl;
//			cout << *e << " = " << e->get_ival() << endl;
//
//			cout << endl;
//			for (auto& c: *(e_orig->get_children()))
//			{
//				if (c->get_size() == 1)
//					cout << "\t" << *c << " = " << c->get_bval() << endl;
//				else
//					cout << "\t" << *c << " = " << c->get_ival() << endl;
//			}
//
//			cout << endl;
//			for (auto& c: *(e->get_children()))
//			{
//				if (c->get_size() == 1)
//					cout << "\t" << *c << " = " << c->get_bval() << endl;
//				else
//					cout << "\t" << *c << " = " << c->get_ival() << endl;
//			}
//		}
//		assert(e->get_ival() == eVal);
//	}
//#endif

	e->acex_coi = e;

	switch (e->get_type())
	{
	case Sig:
	{
		SigInst* sig = SigInst::as(e);
		assert(sig);
		string sigName = sig->get_name();
		size_t nameLength = sigName.length();
		if (nameLength > 5)
		{
			if (sigName.substr(nameLength - 5, 5) == "$next")
			{
				InstToInstM::iterator mit = nextMap.find(e);
				if (mit != nextMap.end())
				{
					e->acex_coi = (*mit).second;
				}
				else
				{
					e->acex_coi = e;
				}
			}
			else
				e->acex_coi = e;
		}
		else
			e->acex_coi = e;
	}break;
	case Const:
	{
		assert(0);
	}break;
	case Num:
	{
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
			evaluate_abstract_destination(mode, if_e, bin_pre, nextMap);

			int ifVal = if_e->get_bval();
			if (mode == 1)
			{
				evaluate_abstract_destination_term(mode, else_e, bin_pre, nextMap);
				evaluate_abstract_destination_term(mode, then_e, bin_pre, nextMap);

				if (ifVal == 0) {
					e->acex_coi = else_e->acex_coi;
				} else if (ifVal == 1) {
					e->acex_coi = then_e->acex_coi;
				} else
					assert(0);
			}
			else
			{
				if (ifVal == 0) {
					evaluate_abstract_destination_term(mode, else_e, bin_pre, nextMap);
					e->acex_coi = else_e->acex_coi;
				} else if (ifVal == 1) {
					evaluate_abstract_destination_term(mode, then_e, bin_pre, nextMap);
					e->acex_coi = then_e->acex_coi;
				} else
					assert(0);
			}
		}
		else
		{
#ifdef ABSTRACTION_COURSE
			if (Inst::check_if_uf_black(e) == VALID)
#endif
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
		const InstL* ch = e->get_children();
		assert(ch != 0);
		InstL new_ch;
		bool need_new = false;
		bool functionComposition = false;

		for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it)
		{
			if ((*it)->get_size() == 1)
			{
				evaluate_abstract_destination(mode, *it, bin_pre, nextMap);
			}
			else
			{
				evaluate_abstract_destination_term(mode, *it, bin_pre, nextMap);
			}

			if ((*it)->acex_coi == 0)
			{
				functionComposition = true;
			}

			if (*it != (*it)->acex_coi)
			{
				if (mode == 3)
				{
					if (functionComposition == false && (*it)->acex_coi->get_type() == Op)
					{
						OpInst* op = OpInst::as((*it)->acex_coi);
						assert(op);
						if (op->get_euf_func_name() != "0")
						{
							functionComposition = true;
						}
					}
					else
					{
						ExInst* ex = ExInst::as((*it)->acex_coi);
						if (ex)
						{
							functionComposition = true;
						}
					}
				}
//				OpInst* opCh = OpInst::as(*it);
//				if (opCh && opCh->get_op() == OpInst::Ternary)
//				{
//					new_ch.push_back(*it);
//				}
//				else
				{
					new_ch.push_back((*it)->acex_coi);
					need_new = true;
				}
			}
			else
				new_ch.push_back(*it);
		}

		if (need_new)
		{
			e->acex_coi = e->apply_children(new_ch);

			mpz_class* eaVal = e->acex_coi->get_ival();
			if (false && eaVal != INVALID_SMPZ)
			{
				if (*eaVal != *eVal)
				{
					cout << "e      : " << *e << " (val: " << eVal << ")" << endl;
					cout << "e->acex: " << *(e->acex_coi) << " (val: " << eaVal << ")" << endl;
//					cout << "e invalid: " << Inst::check_v_important(e) << endl;
//					cout << "eacex invalid: " << Inst::check_v_important(e->acex_coi) << endl;
				}
//#ifndef ABSTRACTION_COURSE
				assert(*eaVal == *eVal);
//#endif
			}
			else
			{
				e->acex_coi->set_ival(eVal);
			}
		}

		if (functionComposition)
		{
			e->acex_coi->acex_fc = true;
		}
	}
	else
	{
		// leave it as ""itself"
	}

	if (mode != 3)
	{
//		assert(e->acex_coi != 0);
		mpz_class* eaVal = e->acex_coi->get_ival();
		assert(eaVal != INVALID_SMPZ);
//		if (eaVal != eVal)
//		{
//			cout << "e      : " << *e << " (val: " << eVal << ")" << endl;
////			for (auto& c: *(e->get_children()))
////				cout << "\t" << *c << " (val: " << c->get_bval() << ")" << endl;
//			cout << "e->acex: " << *(e->acex_coi) << " (val: " << eaVal << ")" << endl;
////			for (auto& c: *(e->acex_coi->get_children()))
////				cout << "\t" << *c << " (val: " << c->get_bval() << ")" << endl;
////			cout << OpInst::as(e)->get_op() << endl;
//			cout << e->get_ival() << endl;
//			cout << e->acex_coi->get_ival() << endl;
//		}

//#ifndef ABSTRACTION_COURSE
//		assert(*eVal == *eaVal);
//#endif
	}

	if (e_orig != e)
	{
		e_orig->acex_coi = e->acex_coi;
		AVR_LOG(9, 1, "[EvalD] simplified: " << *e_orig << " -> " << *e << endl);
	}

	if (e->acex_coi)
	{
		AVR_LOG(9, 5, "[EvalD]: " << *e << " Ans: " << *(e->acex_coi) << endl);
	}
	else
	{
		AVR_LOG(9, 5, "[EvalD]: " << *e << " Ans: " << 0 << endl);
	}
	AVR_LOG(9, 2, "[EvalD] e: " << *e << " -> " << *(e->acex_coi) << endl);
}


/// Mode = 1 (evaluating regular (reg1$next == ...) && (reg1$next == ...) ...)
/// Mode = 2 (evaluating other cube constraints (contains only present state regs, inputs, constants or numbers))
void Reach::evaluate_simulation_relation(int mode, Inst*e, SIMULATION_POSITION& pre, SIMULATION_POSITION& next, bool& stuck, bool init_visit)
{
	_simeval_depth++;
	OpInst::OpType op_type = OpInst::Unknown;

	if (init_visit) {
		Inst::init_visit();
	}

	assert(e != 0);
	if (e->get_visit())
	{
		_simeval_depth--;
		return;
	}
	e->set_visit();
	assert(e->get_size() == 1);

	AVR_LOG(14, 9, "[SimEval]: " << *e << " (" << e->get_bval() << ")" << endl);

	// TODO temporary fix for the next state function, "reg_reset$next = 1"
	// With wn_simplify_const_pred enabled, "reg_reset$next = 1" is simplified as "reg_reset$next"
	// However, m_sn[reg_reset$next] still is a NumInst, 1'b1.
	// Therefore, eval_formula(2, 1'b1) is called due to the codes below "if (_m_sn.find(e) != _m_sn.end()) {"
	// As 1'b1 was not in T (omitted during simplification), its cex_val and cex_mpz  also have not been initialized
	// Here, I temporarily assign the fields, but I should fix this problem properly later.
	NumInst *num_temp = NumInst::as(e);
	if(num_temp)
	{
		if(e->get_size() == 1)
		{
			if(num_temp->get_num() == 0)
				e->set_bval(0);
			else
				e->set_bval(1);
		}
	}

	int eVal = e->get_bval();

	if((e->get_size() == 1) && (!(eVal == 1 || eVal == 0)))
	{
		cout << "e->cex_mpz: " << e->get_size() << "'d";
		cout << "e->val: " << eVal << endl;
		cout << "e: " << *e << endl;
		assert(0);
	}

	// resulting relation to add to viol
	Inst* rel = 0;
	e->acex_coi = 0;

	bool intpd = false;
	bool call_eval_term = false;
	switch (e->get_type()) {
	case Sig:
	{
		InstToInstM::iterator vit = pre.val.find(e);
		if (vit != pre.val.end())
		{
			rel = (*vit).second;

			int rVal = rel->get_bval();
			if (false && rVal != INVALID_SVAL)
			{
				if (rVal != eVal)
				{
					cout << "e  : " << *e << " (val: " << eVal << ")" << endl;
					cout << "rel: " << *rel << " (val: " << rVal << ")" << endl;
				}
				assert(rVal == eVal);
			}
			else
			{
				rel->set_bval(eVal);
			}
			cext.add(pre.sIdx, e, (*vit).second, false);


			if (rel->childrenInfo[CONST] && !rel->find_sig()) {
				AVR_LOG(14, 7, "[EvalS] e: " << *e << " -> " << *rel << endl);
				rel->add_parent(e, pre.sIdx);
			}
		}
		else
		{
			InstToInstM::iterator nit = next.inp2Const.find(e);
			if (nit != next.inp2Const.end())
			{
				rel = (*nit).second;

				int rVal = rel->get_bval();
				if (false && rVal != INVALID_SVAL)
				{
					if (rVal != eVal)
					{
						cout << "e  : " << *e << " (val: " << eVal << ")" << endl;
						cout << "rel: " << *rel << " (val: " << rVal << ")" << endl;
					}
					assert(rVal == eVal);
				}
				else
				{
					rel->set_bval(eVal);
				}
			}
			else if (Inst::_s_inp.find(e) != Inst::_s_inp.end())
			{
				stringstream cName;
				int sz = e->get_size();
				cName << e->get_sort().sort2str() << "_" << sz << "'d*_" << ConstInst::hm_ConstInst.size();
				Inst* c = ConstInst::create(cName.str(), sz, e, pre.sIdx, e->get_sort());
				cext.add(pre.sIdx, e, c, true);
				c->set_bval(eVal);
				/// Aman TODO: Optimize here
				next.inp2Const[e] = c;
				rel = c;

				int rVal = rel->get_bval();
				if (false && rVal != INVALID_SVAL)
				{
					if (rVal != eVal)
					{
						cout << "e  : " << *e << " (val: " << eVal << ")" << endl;
						cout << "rel: " << *rel << " (val: " << rVal << ")" << endl;
					}
					assert(rVal == eVal);
				}
				else
				{
					rel->set_bval(eVal);
				}
			}
			else
			{
				InstToInstM::iterator mit = Inst::_m_next_input_pre.find(e);
				if (mit != Inst::_m_next_input_pre.end()) {
//					rel = (*mit).second;
				}
				else {
					if (!Inst::has_trelation(e)) {
						cout << *e << endl;
					}
					assert(Inst::has_trelation(e));
				}
				rel = e;
			}
		}
	}break;
	case Wire:
	{
		WireInst* w = WireInst::as(e);
		if (w->is_connected(WireInst::get_connect_key()))
		{
			Inst* port = w->get_port();
			evaluate_simulation_relation(mode, port, pre, next, stuck);
	//		if (port != port->acex_coi)
				e->acex_coi = port->acex_coi;
	//		else
	//			e->acex_coi = e;
		}
	}break;
	case Const:
	{
		rel = e;
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
			call_eval_term = true;
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
		InstL new_ch;
		const InstL* ch = e->get_children();
		assert(ch != 0);
		bool need_new = false;
		bool all_ch_size_one = true;

		for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it)
		{
			if ((*it)->get_size() == 1)
			{
				evaluate_simulation_relation(mode, *it, pre, next, stuck);
			}
			else
			{
				all_ch_size_one = false;
				evaluate_simulation_term(mode, *it, pre, next, stuck);
			}
			new_ch.push_back((*it)->acex_coi);
			need_new = need_new || (*it != (*it)->acex_coi);
		}

//		 we cannot comment out the following 7 lines => it leads to a wrong result (return SAT for UNSAT probs)
//		 this is because of a literal, (prop$next = (~~)) & (~~) & prop$next(prop$next is later dropped)
//		 that is produced without the following 7 lines.
//		 Instead, (~~) should be produced!
//		 during PME generalization, (prop$next = (~~)) sometimes is chosen as one of literals in an UNSAT core,
//		 but (prop$next = true) which is important literal (should be added) is missing, because it is in the
//		 formula used during PME (this is a very rough and vague explanation. I'm going to update this later.)
		if((((op_type == OpInst::Eq) || (op_type == OpInst::NotEq)) && all_ch_size_one == true))
		{
			e->acex_coi = NumInst::create(eVal, e->get_size(), e->get_sort());
			// do nothing
		}
		else
		{
			if (need_new)
			{
				rel = e->apply_children(new_ch);

				int rVal = rel->get_bval();
				if (false && rVal != INVALID_SVAL)
				{
					if (rVal != eVal)
					{
						cout << "e  : " << *e << " (val: " << eVal << ")" << endl;
						cout << "rel: " << *rel << " (val: " << rVal << ")" << endl;
					}
					assert(rVal == eVal);
				}
				else
				{
					rel->set_bval(eVal);
				}

				if (rel->childrenInfo[CONST] && !rel->find_sig()) {
					OpInst* op = OpInst::as(e);
					if (op && op->get_euf_func_name() != "0") {
						AVR_LOG(14, 7, "[EvalS] e: " << *e << " -> " << *rel << endl);
//						rel->add_parent(e, pre.sIdx);
						Inst* w = op->get_wire();
						if (w)
							rel->add_parent(w, pre.sIdx);
						else
							rel->add_parent(e, pre.sIdx);
					}
				}
			}
			else
			{
				rel = e;
			}
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
			evaluate_simulation_relation(mode, *(ch->begin()), pre, next, stuck);
			break;
		case OpInst::LogAnd:
		case OpInst::LogOr: {
			for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it)
			{
				if (eVal == controlling(op_type))
				{
					int itVal = (*it)->get_bval();
					if (itVal == controlling(op_type))
					{
						evaluate_simulation_relation(mode, *it, pre, next, stuck);
						break;
					}
				}
				else
				{
					evaluate_simulation_relation(mode, *it, pre, next, stuck);
				}
			}
		}break;
		case OpInst::Ternary: {
			InstL::const_iterator it = ch->begin();
			Inst* if_e = *(it++);
			Inst* then_e = *(it++);
			Inst* else_e = *(it++);
			evaluate_simulation_relation(mode, if_e, pre, next, stuck);

			int ifVal = if_e->get_bval();
			if (ifVal == 0) {
				evaluate_simulation_relation(mode, else_e, pre, next, stuck);
				e->acex_coi = else_e->acex_coi;
			} else if (ifVal == 1) {
				evaluate_simulation_relation(mode, then_e, pre, next, stuck);
				e->acex_coi = then_e->acex_coi;
			} else {
				assert(0);
			}
		}break;
		default:
			assert(0);
		}
	}

	if (!e->acex_coi)
	{
		// We should put this code befor rel is negated
		if (rel)
		{
			e->acex_coi = rel;
		}
		else
		{
			e->acex_coi = e;
		}
	}

	if (rel)
	{
		if (eVal == 0)
		{
			rel = OpInst::create(OpInst::LogNot, rel);
			rel->set_bval(1);
		}
		if (rel == NumInst::create(0,1, SORT()))
		{
			cout << "Error inserting in c$: " << *rel << " [@ " << _trace_depth << " for " << *e << " ]" << endl;
			assert(0);
		}
		int rVal = rel->get_bval();
		if (rVal != 1)
		{
			cout << "Error inserting in c$: " << *rel << " [@ " << _trace_depth << " for " << *e << " ]" << endl;
			cout << rVal << endl;
		}

		assert(rVal == 1);

#ifdef SIM_SIMPLIFY_CONSTANT_RELATIONS
		if (!(rel->childrenInfo[SIG] || rel->childrenInfo[CONST]))
			rel = NumInst::create(rel->cex_mpz, rel->get_size());
#endif
	}

	if (is_redundant(rel))
		rel = 0;

	if (mode == 1)
	{
		if (rel)
		{
			if (rel->find_next())
			{
        if (find_pre(rel)) {
          AVR_LOG(15, 0, "\t(error: unexpected relation with both pre & next)\t"
              << *rel << " (derived from " << *e << ")" << endl);
          assert(0);
        }

			  Inst* tmp2 = Inst::all_next2pre(rel);
			  Inst::init_visit2();
			  Inst* tmp = add_missing_wires(tmp2);
			  tmp = tmp->get_port();
			  bool done = false;

				OpInst* op = OpInst::as(tmp);
				if (op && op->get_op() == OpInst::Eq)
				{
					Inst* lhs = op->get_children()->front();
					Inst* rhs = op->get_children()->back();
					assert(lhs && rhs);
//					if (lhs->get_size() <= 1)
//					{
//						cout << *rel << endl;
//					}
//					assert(lhs->get_size() > 1);
					if (!SigInst::as(lhs))
					{
//						assert (SigInst::as(rhs));
						/// Swap lhs and rhs
						Inst* tmp;
						tmp = lhs;
						lhs = rhs;
						rhs = tmp;
					}

					if (lhs->get_type() == Sig &&
							!rhs->childrenInfo[SIG] &&
							Inst::_s_reg.find(lhs) != Inst::_s_reg.end()) {

						/// TODO: Below search can be pushed inside the following if-if, when next.s not needed
						InstToInstM::iterator mit = Inst::_m_pre_to_next.find(lhs);
						assert(mit != Inst::_m_pre_to_next.end());
						Inst* sig = (*mit).second;

						mpz_class* sigVal = sig->get_ival();
						next.s[lhs] = (sigVal);

						OpInst* opRhs = OpInst::as(rhs);
						if (opRhs)
						{
							if (!rhs->childrenInfo[CONST]) {
								if (rhs->get_sort_type() == bvtype || rhs->get_sort_type() == inttype)
								{
									rhs = NumInst::create(*sigVal, sig->get_size(), rhs->get_sort());
									tmp = OpInst::create(OpInst::Eq, lhs, rhs);
									AVR_LOG(14, 5, "(actual) Inserting in c$: " << *tmp << " [@ " << _simeval_depth << " for " << *e << " ]" << endl);
								}
							}
						}

//					if (lhs->get_sort_type() == arraytype) {
//						NumInst* num = NumInst::as(rhs);
//						if (num) {
//							assert(0);
//
//							long long val = num->get_num();
//
//							SORT sort = lhs->get_sort();
//							int width = sort.width;
//							int size = sort.size;
//
////						cout << *lhs << " -> " << *rhs << endl;
//							InstL args;
//							args.push_back(NumInst::create(width, 32));
//							args.push_back(NumInst::create(0, size));
//							Inst* newRhs = OpInst::create(OpInst::ArrayConst, args, lhs->get_size(), true, NULL, sort);
//
////						Inst* newRhs = pre.val[lhs];
////						assert(newRhs);
////						cout << "here: " << *newRhs << endl;
////						cout << newRhs->get_ival()->get_str(2) << endl;
//
//							if (val != 0)
//							{
//								string sval = Solver::val_to_str(val, num->get_size());
//								for (int i = 0; i < pow(2, width); i++) {
//									string segment = sval.substr(0, size);
//									sval.erase(0, size);
//									Inst* valInst = NumInst::create(segment, size, 2);
//									if (NumInst::as(valInst)->get_num() != 0)
//									{
//										InstL argsTmp;
//										argsTmp.push_back(newRhs);
//										argsTmp.push_back(NumInst::create(i, width));
//										argsTmp.push_back(valInst);
//
//										newRhs = OpInst::create(OpInst::ArrayStore, argsTmp, lhs->get_size(), true, NULL, sort);
//									}
//								}
//							}
//
//							rhs = newRhs;
////							rhs = try_wired_form(rhs);
//						}
//					}
						assert(lhs->get_sort() == rhs->get_sort());

						next.val[lhs] = rhs;
						next.sigs.insert(lhs);
						collect_constants(rhs, next.consts, true);

						AVR_LOG(14, 5, "Inserting in v$: " << *rel << " [@ " << _simeval_depth << " for " << *e << " ]" << endl);

						if (stuck)
						{
							InstToInstM::iterator pit = pre.val.find(lhs);
							if (pit != pre.val.end())
							{
								if ((*pit).second != rhs)
									stuck = false;
							}
							else
								stuck = false;
						}

						done = true;
					}
				}
				else
				{
					Inst* lhs;
					Inst* rhs;
					SigInst* sig = SigInst::as(tmp);
					if (sig &&
							Inst::_s_reg.find(sig) != Inst::_s_reg.end()) {
						assert(sig->get_size() == 1);
						lhs = sig;
						rhs = NumInst::create(1, 1, SORT());
						done = true;
					}
					else
					{
						OpInst* op = OpInst::as(tmp);
						if (op) {
							if (op->get_op() == OpInst::LogNot) {
								lhs = op->get_children()->front();
								SigInst* sig = SigInst::as(lhs);
								if (sig &&
										Inst::_s_reg.find(sig) != Inst::_s_reg.end()) {
									rhs = NumInst::create(0, 1, SORT());
									done = true;
								}
							}
						}
					}
					if (done) {
						next.val[lhs] = rhs;
						next.s[lhs] = NumInst::as(rhs)->get_mpz();
						next.sigs.insert(lhs);

						AVR_LOG(14, 5, "Inserting in v$: " << *rel << " [@ " << _simeval_depth << " for " << *e << " ]" << endl);

						if (stuck)
						{
							InstToInstM::iterator pit = pre.val.find(lhs);
							if (pit != pre.val.end())
							{
								if ((*pit).second != rhs)
									stuck = false;
							}
							else
								stuck = false;
						}
					}

//					next.pConditions.push_back(tmp);
//					AVR_LOG(9, 2, "Inserting in p$: " << *rel << " [@ " << _simeval_depth << " for " << *e << " ]" << endl);
//
//					if (stuck)
//					{
//						InstL::iterator pit = find(pre.pConditions.begin(), pre.pConditions.end(), tmp);
//						if (pit == pre.pConditions.end())
//								stuck = false;
//					}
				}

//				if (!done)
				{
//					cout << "tmp: " << *tmp << endl;
					next.postConditions.push_back(tmp);
					collect_sig(tmp, next.sigs, true);
					collect_constants(tmp, next.consts, true);

					AVR_LOG(14, 5, "Inserting in post$: " << *rel << " [@ " << _simeval_depth << " for " << *e << " ]" << endl);

					if (stuck)
					{
						InstL::iterator pit = find(pre.postConditions.begin(), pre.postConditions.end(), tmp);
						if (pit == pre.postConditions.end())
						{
							stuck = false;
						}
					}
				}
			}
			else
			{
				Inst* newCondition = NULL;
				if (!rel->childrenInfo[SIG])
				{
					newCondition = rel;
				}
				else if (find_limited_sigs(rel, next.inp2Const))
				{
					newCondition = replace_with_constant(rel, next.inp2Const, pre.sIdx);
					assert(0);
				}
				else {
					assert(0);
				}

				if (newCondition != NULL && newCondition->childrenInfo[CONST])
				{
					next.cConditions.insert(newCondition);
					collect_constants(newCondition, next.consts, true);
					AVR_LOG(14, 5, "Inserting in c$: " << *rel << " [@ " << _simeval_depth << " for " << *e << " ]" << endl);

					if (stuck)
					{
						InstS::iterator pit = find(pre.cConditions.begin(), pre.cConditions.end(), newCondition);
						if (pit == pre.cConditions.end())
								stuck = false;
					}
				}
				else
				{
					AVR_LOG(14, 9, "No insert: " << " [@ " << _simeval_depth << " for " << *e << " ]" << endl);
				}
			}
		}
		else
		{
			AVR_LOG(14, 9, "No insert: " << " [@ " << _simeval_depth << " for " << *e << " ]" << endl);
		}
	}
	else if (mode == 2)
	{
		if (rel)
		{
			Inst* newCondition = NULL;
			if (!rel->childrenInfo[SIG])
			{
				newCondition = rel;
			}
			else if (find_limited_sigs(rel, next.inp2Const))
			{
				newCondition = replace_with_constant(rel, next.inp2Const, pre.sIdx);
				assert(0);
			}
			else {
				assert(0);
			}

			if (newCondition != NULL && newCondition->childrenInfo[CONST])
			{
				next.cConditions.insert(newCondition);
				collect_constants(newCondition, next.consts, true);
				AVR_LOG(14, 5, "Inserting in c$: " << *rel << " [@ " << _simeval_depth << " for " << *e << " ]" << endl);

				if (stuck)
				{
					InstS::iterator pit = find(pre.cConditions.begin(), pre.cConditions.end(), newCondition);
					if (pit == pre.cConditions.end())
							stuck = false;
				}
			}
			else
			{
				AVR_LOG(14, 9, "No insert: " << " [in mode = 2 for " << *e << " ]" << endl);
			}
		}
		else
		{
			AVR_LOG(14, 9, "No insert: " << " [in mode = 2 for " << *e << " ]" << endl);
		}
	}

//	if (e->acex_coi->get_type() == Const) {
//		AVR_LOG(14, 0, "[EvalS] e: " << *e << " -> " << *(e->acex_coi) << endl);
//	}

	AVR_LOG(14, 9, "[EvalS] e: " << *e << " -> " << *(e->acex_coi) << endl);
	_simeval_depth--;
}


void Reach::evaluate_simulation_term(int mode, Inst*e, SIMULATION_POSITION& pre, SIMULATION_POSITION& next, bool& stuck)
{
	_simeval_depth++;
	assert(e != 0);
	if (e->get_visit())
	{
		if (e->acex_coi == 0)
		{
			cout << *e << "  " << e->get_id() << endl;
			assert(0);
		}
		_simeval_depth--;
		return;
	}
	e->set_visit();
	AVR_LOG(14, 9, "[SimEval]: " << *e << endl);

	mpz_class* eVal = e->get_ival();



	bool apply_on_children = false;

	e->acex_coi = e;

	mpz_class* eaVal = e->acex_coi->get_ival();

	switch (e->get_type())
	{
	case Sig:
	{
		InstToInstM::iterator vit = pre.val.find(e);
		if (vit != pre.val.end())
		{
			e->acex_coi = (*vit).second;
			eaVal = e->acex_coi->get_ival();
			if (false && eaVal != INVALID_SMPZ)
			{
				if (*eaVal != *eVal)
				{
					cout << "e      : " << *e << " (val: " << *eVal << ")" << endl;
					cout << "e->acex: " << *(e->acex_coi) << " (val: " << *eaVal << ")" << endl;
				}
				assert(*eaVal == *eVal);
			}
			else
			{
				e->acex_coi->set_ival(eVal);
				eaVal = eVal;
			}
			cext.add(pre.sIdx, e, (*vit).second, false);

			if (e->acex_coi->childrenInfo[CONST] && !e->acex_coi->find_sig()) {
				AVR_LOG(14, 7, "[EvalS] e: " << *e << " -> " << *(e->acex_coi) << endl);
				e->acex_coi->add_parent(e, pre.sIdx);
			}
		}
		else
		{
			InstToInstM::iterator nit = next.inp2Const.find(e);
			if (nit != next.inp2Const.end())
			{
				e->acex_coi = (*nit).second;
				eaVal = e->acex_coi->get_ival();
				if (false && eaVal != INVALID_SMPZ)
				{
					if (*eaVal != *eVal)
					{
						cout << "e      : " << *e << " (val: " << eVal << ")" << endl;
						cout << "e->acex: " << *(e->acex_coi) << " (val: " << eaVal << ")" << endl;
					}
					assert(*eaVal == *eVal);
				}
				else
				{
					e->acex_coi->set_ival(eVal);
					eaVal = eVal;
				}
			}
			else if (Inst::_s_inp.find(e) != Inst::_s_inp.end())
			{
				stringstream cName;
				int sz = e->get_size();
				cName << e->get_sort().sort2str() << "_" << sz << "'d*_" << ConstInst::hm_ConstInst.size();
				Inst* c = ConstInst::create(cName.str(), sz, e, pre.sIdx, e->get_sort());
				cext.add(pre.sIdx, e, c, true);
				c->set_ival(eVal);
				next.inp2Const[e] = c;
				e->acex_coi = c;
				eaVal = e->acex_coi->get_ival();
				if (false && eaVal != INVALID_SMPZ)
				{
					if (*eaVal != *eVal)
					{
						cout << "e      : " << *e << " (val: " << eVal << ")" << endl;
						cout << "e->acex: " << *(e->acex_coi) << " (val: " << eaVal << ")" << endl;
					}
					assert(*eaVal == *eVal);
				}
				else
				{
					e->acex_coi->set_ival(eVal);
					eaVal = eVal;
				}
			}
			else
			{
				InstToInstM::iterator mit = Inst::_m_next_input_pre.find(e);
				if (mit != Inst::_m_next_input_pre.end()) {
//					e->acex_coi = (*mit).second;
				}
				else {
					if (!Inst::has_trelation(e)) {
						cout << *e << endl;
					}
					assert(Inst::has_trelation(e));
				}
			}
		}
	}break;
	case Wire:
	{
		WireInst* w = WireInst::as(e);

		if (w->is_connected(WireInst::get_connect_key()))
		{

			Inst* port = w->get_port();
			evaluate_simulation_term(mode, port, pre, next, stuck);
	//		if (port != port->acex_coi)
				e->acex_coi = port->acex_coi;
	//		else
	//			e->acex_coi = e;
	//		eaVal = e->acex_coi->get_ival();
		}
	}break;
	case Const:
	{
		// leave it as "itself"
	}break;
	case Num:
	{
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
			evaluate_simulation_relation(mode, if_e, pre, next, stuck);

			int ifVal = if_e->get_bval();
			if (ifVal == 0) {
				evaluate_simulation_term(mode, else_e, pre, next, stuck);
				e->acex_coi = else_e->acex_coi;
			} else if (ifVal == 1) {
				evaluate_simulation_term(mode, then_e, pre, next, stuck);
				e->acex_coi = then_e->acex_coi;
			} else
				assert(0);

			eaVal = e->acex_coi->get_ival();

		} else
			apply_on_children = true;
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
		const InstL* ch = e->get_children();
		assert(ch != 0);
		InstL new_ch;
		bool need_new = false;

		for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it) {
			if ((*it)->get_size() == 1)
			{
				evaluate_simulation_relation(mode, *it, pre, next, stuck);
			}
			else
			{
				evaluate_simulation_term(mode, *it, pre, next, stuck);
			}
			new_ch.push_back((*it)->acex_coi);
			need_new = need_new || (*it != (*it)->acex_coi);
		}
		if (need_new)
		{
			e->acex_coi = e->apply_children(new_ch);

			eaVal = e->acex_coi->get_ival();
			if (false && eaVal != INVALID_SMPZ)
			{
				if (*eaVal != *eVal)
				{
					cout << "newCh: " << new_ch << endl;
					cout << "e      : " << *e << " (val: " << *eVal << ")" << endl;
					cout << "e->acex: " << *(e->acex_coi) << " (val: " << *eaVal << ")" << endl;
				}
				assert(*eaVal == *eVal);
			}
			else
			{
				e->acex_coi->set_ival(eVal);
				eaVal = eVal;
			}

			if (e->acex_coi->childrenInfo[CONST] && !e->acex_coi->find_sig()) {
				OpInst* op = OpInst::as(e);
				if (op && op->get_euf_func_name() != "0") {
					AVR_LOG(14, 7, "[EvalS] e: " << *e << " -> " << *(e->acex_coi) << endl);
//					e->acex_coi->add_parent(e, pre.sIdx);
					Inst* w = op->get_wire();
					if (w)
						e->acex_coi->add_parent(w, pre.sIdx);
					else
						e->acex_coi->add_parent(e, pre.sIdx);
				}
			}
		}
	}
	else
	{
		// leave it as ""itself"
	}

	assert(e->acex_coi != 0);

	if (eVal == INVALID_SMPZ)
	{
		cout << "e: " << *e << "  " << eVal << endl;
		cout << "ea: " << *(e->acex_coi) << "  " << eaVal << endl;
	}
	assert(eVal != INVALID_SMPZ);

	if (eaVal == INVALID_SMPZ)
	{
		cout << "e: " << *e << "  " << eVal << endl;
		cout << "ea: " << *(e->acex_coi) << "  " << eaVal << endl;
	}
	assert(eaVal != INVALID_SMPZ);

	if (*eVal != *eaVal)
	{
		cout << "e: " << eVal << endl;
		cout << "ea: " << eaVal << endl;
		cout << "e: " << *eVal << endl;
		cout << "ea: " << *eaVal << endl;
		cout << "e: " << *e << "  " << eVal << endl;
		cout << "ea: " << *(e->acex_coi) << "  " << eaVal << endl;
	}
//	assert(*eVal == *eaVal);

#ifdef SIM_SIMPLIFY_CONSTANT_RELATIONS
		if (!(e->acex_coi->childrenInfo[SIG] || e->acex_coi->childrenInfo[CONST]))
			e->acex_coi = NumInst::create(e->acex_coi->cex_mpz, e->acex_coi->get_size());
#endif

//	if (e->acex_coi->get_type() == Const) {
//		AVR_LOG(14, 0, "[EvalS] e: " << *e << " -> " << *(e->acex_coi) << endl);
//	}

	AVR_LOG(14, 9, "[EvalS] e: " << *e << " -> " << *(e->acex_coi) << endl);
	_simeval_depth--;
}

Inst* Reach::evaluate_generalize_relation(Inst*e, InstL& viol, bool init_visit)
{
	OpInst::OpType op_type = OpInst::Unknown;

	if (init_visit) {
		Inst::init_visit();
	}

	assert(e != 0);
	if (e->get_visit())
	{
		return e->acex_coi;
	}
	e->set_visit();
	assert(e->get_size() == 1);

	// TODO temporary fix for the next state function, "reg_reset$next = 1"
	// With wn_simplify_const_pred enabled, "reg_reset$next = 1" is simplified as "reg_reset$next"
	// However, m_sn[reg_reset$next] still is a NumInst, 1'b1.
	// Therefore, eval_formula(2, 1'b1) is called due to the codes below "if (_m_sn.find(e) != _m_sn.end()) {"
	// As 1'b1 was not in T (omitted during simplification), its cex_val and cex_mpz  also have not been initialized
	// Here, I temporarily assign the fields, but I should fix this problem properly later.
	NumInst *num_temp = NumInst::as(e);
	if(num_temp)
	{
		if(e->get_size() == 1)
		{
			if(num_temp->get_num() == 0)
				e->set_bval(0);
			else
				e->set_bval(1);
		}
	}

	int eVal = e->get_bval();

	AVR_LOG(9, 1, "[EvalG]: " << *e << endl);

	// resulting relation to add to viol
	Inst* rel = 0;
	e->acex_coi = e;

	bool intpd = false;
	bool call_eval_term = false;

	switch (e->get_type()) {
	case Sig:
	{
		if (eVal != INVALID_SVAL)
			e->acex_coi = NumInst::create(eVal, 1, SORT());
		else
			e->acex_coi = e;
		rel = e;
	}break;
	case Wire:
	{
		WireInst* w = WireInst::as(e);
		Inst* port = w->get_port();
		evaluate_generalize_relation(port, viol);
		if (port->acex_coi != port)
			e->acex_coi = port->acex_coi;
		else
			e->acex_coi = e;
	}break;
	case Const:
	{
		assert(0);
	}break;
	case Num: {

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
		{
			call_eval_term = true;
		}
	}break;
	case Mem:
	default:
		assert(0);
	}

	if (intpd)
	{
		assert(e->get_type() == Op);
		const InstL* ch = e->get_children();
		assert(ch != 0);

		bool gotVal = false;
		switch (op_type)
		{
		case OpInst::LogNot:
		{
			Inst* child = *(ch->begin());
			evaluate_generalize_relation(child, viol);
			int itVal = child->get_bval();
			if (itVal == 1)
			{
				eVal = 0;
				gotVal = true;
			}
			else if (itVal == 0)
			{
				eVal = 1;
				gotVal = true;
			}

			if (!gotVal)
				call_eval_term = true;
			else
			{
				e->set_bval(eVal);
				e->acex_coi = OpInst::create(OpInst::LogNot, child->acex_coi);
			}
		}
			break;
		case OpInst::LogAnd:
		case OpInst::LogOr: {
			for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it)
			{
				int itVal = (*it)->get_bval();
				eVal = itVal;
				if (itVal == controlling(op_type))
				{
					e->acex_coi = *it;
					gotVal = true;
					rel = 0;
					break;
				}
			}
			if (!gotVal)
				call_eval_term = true;
		}break;
		case OpInst::Ternary: {
			InstL::const_iterator it = ch->begin();
			Inst* if_e = *(it++);
			Inst* then_e = *(it++);
			Inst* else_e = *(it++);
			evaluate_generalize_relation(if_e, viol);

			int ifVal = if_e->get_bval();
			if (ifVal == 0) {
				evaluate_generalize_relation(else_e, viol);
				e->acex_coi = else_e->acex_coi;
			} else if (ifVal == 1) {
				evaluate_generalize_relation(then_e, viol);
				e->acex_coi = then_e->acex_coi;
			} else {
				evaluate_generalize_relation(else_e, viol);
				evaluate_generalize_relation(then_e, viol);

				bool need_new = false;
				InstL new_ch;
				if (else_e != else_e->acex_coi)
				{
					need_new = true;
				}
				if (then_e != then_e->acex_coi)
				{
					need_new = true;
				}
				new_ch.push_back(if_e->acex_coi);
				new_ch.push_back(then_e->acex_coi);
				new_ch.push_back(else_e->acex_coi);

				if (need_new)
				{
					Inst* newTve = e->apply_children(new_ch);
					e->acex_coi = newTve;
				}
				else
				{
					e->acex_coi = e;
				}
			}
			eVal = e->acex_coi->get_bval();
		}break;
		default:
			assert(0);
		}
	}

	if (call_eval_term)
	{
		InstL new_ch;
		const InstL* ch = e->get_children();
		assert(ch != 0);
		bool need_new = false;
		bool all_ch_size_one = true;

		for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it)
		{
			if ((*it)->get_size() == 1)
			{
				evaluate_generalize_relation(*it, viol);
			}
			else
			{
				all_ch_size_one = false;
				evaluate_generalize_term(*it, viol);
			}

			if (*it != (*it)->acex_coi)
			{
				need_new = true;
			}
			new_ch.push_back((*it)->acex_coi);
		}

		if (need_new)
		{
			Inst* newTve = e->apply_children(new_ch);
			e->acex_coi = newTve;
			rel = newTve;
		}
		else
		{
			e->acex_coi = e;
			rel = e;
		}
	}

	if (!e->acex_coi)
	{
		assert(0);
	}

	if (rel)
		cout << "rel: " << *rel << endl;

	AVR_LOG(9, 1, "[EvalG] e: " << *e << " -> " << *(e->acex_coi) << endl);

	return e->acex_coi;
}

void Reach::evaluate_generalize_term(Inst*e, InstL& viol)
{
	assert(e != 0);
	if (e->get_visit())
		return;
	e->set_visit();

	AVR_LOG(9, 1, "[EvalG]: " << *e << endl);

	bool apply_on_children = false;

	e->acex_coi = e;

	switch (e->get_type())
	{
	case Sig:
	{
		// leave it as "itself"
	}break;
	case Wire:
	{
		WireInst* w = WireInst::as(e);
		Inst* port = w->get_port();
		evaluate_generalize_term(port, viol);
		if (port->acex_coi != port)
			e->acex_coi = port->acex_coi;
		else
			e->acex_coi = e;
	}break;
	case Const:
	{
		assert(0);
	}break;
	case Num:
	{
		// leave it as "itself"
	}break;
	case Op:
	{
		OpInst* op = OpInst::as(e);
		assert(op != 0);
		OpInst::OpType t = op->get_op();
		if (t == OpInst::Ternary)
		{
			const InstL* ch = e->get_children();
			assert(ch != 0);
			InstL::const_iterator it = ch->begin();
			Inst* if_e = *(it++);
			Inst* then_e = *(it++);
			Inst* else_e = *(it++);
			evaluate_generalize_relation(if_e, viol);

			int ifVal = if_e->get_bval();
			if (ifVal == 0) {
				evaluate_generalize_term(else_e, viol);
				e->acex_coi = else_e->acex_coi;
			} else if (ifVal == 1) {
				evaluate_generalize_term(then_e, viol);
				e->acex_coi = then_e->acex_coi;
			} else
				e->acex_coi = e;
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
		const InstL* ch = e->get_children();
		assert(ch != 0);
		InstL new_ch;
		bool need_new = false;

		for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it)
		{
			if ((*it)->get_size() == 1)
			{
				evaluate_generalize_relation(*it, viol);
			}
			else
			{
				evaluate_generalize_term(*it, viol);
			}

			if (*it != (*it)->acex_coi)
			{
				new_ch.push_back((*it)->acex_coi);
				need_new = true;
			}
			else
				new_ch.push_back(*it);
		}

		if (need_new)
		{
			e->acex_coi = e->apply_children(new_ch);
//			mpz_class eaVal = e->acex_coi->get_ival();
//			e->acex_coi->set_ival(eVal);
		}
	}
	else
	{
		// leave it as ""itself"
	}

	assert(e->acex_coi);

	AVR_LOG(9, 1, "[EvalG] e: " << *e << " -> " << *(e->acex_coi) << endl);
}


/// Aman
/// mode = 1, Explore complete COI
/// else, explore relevant COI
#ifdef	FIND_SUB_EXPRESSION
void Reach::evaluate_relation(int mode, Inst*e)
{
	OpInst::OpType op_type = OpInst::Unknown;
	assert(e != 0);
	if (e->get_visit())
	{
		return;
	}
	e->set_visit();
	assert(e->get_size() == 1);

	// TODO temporary fix for the next state function, "reg_reset$next = 1"
	// With wn_simplify_const_pred enabled, "reg_reset$next = 1" is simplified as "reg_reset$next"
	// However, m_sn[reg_reset$next] still is a NumInst, 1'b1.
	// Therefore, eval_formula(2, 1'b1) is called due to the codes below "if (_m_sn.find(e) != _m_sn.end()) {"
	// As 1'b1 was not in T (omitted during simplification), its cex_val and cex_mpz  also have not been initialized
	// Here, I temporarily assign the fields, but I should fix this problem properly later.
	NumInst *num_temp = NumInst::as(e);
	if(num_temp)
	{
		if(e->get_size() == 1)
		{
			if(num_temp->get_num() == 0)
				e->set_bval(0);
			else
				e->set_bval(1);
		}
	}

	int eVal = e->get_bval();

	if((e->get_size() == 1) && (!(eVal == 1 || eVal == 0)))
	{
		cout << "e->cex_mpz: " << e->get_size() << "'d";
		cout << "e->val: " << eVal << endl;
		cout << "e: " << *e << endl;
		assert(0);
	}

	if (!(eVal == 1 || eVal == 0))
	{
		cout << "e->cex_mpz: " << e->get_size() << "'d";
		cout << "e->val: " << eVal << endl;
		cout << "e: " << *e << endl;
		assert(0);
	}

	AVR_LOG(9, 4, "[EvalP]: " << *e << endl);

	e->subs_coi = e;

	bool intpd = false;
	bool call_eval_term = false;
	switch (e->get_type()) {
	case Sig:
	{
	}break;
	case Wire:
	{
		WireInst* w = WireInst::as(e);
		Inst* port = w->get_port();
		evaluate_relation(mode, port);
		e->subs_coi = port->subs_coi;
		OpInst* op_port = OpInst::as(port);
		if (op_port)
		{
			w->set_sliceVal();
		}
		else
			assert(0);
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
		InstL new_ch;
		const InstL* ch = e->get_children();
		assert(ch != 0);
		bool need_new = false;
		bool all_ch_size_one = true;

		for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it)
		{
			if ((*it)->get_size() == 1)
			{
				evaluate_relation(mode, *it);
			}
			else
			{
				evaluate_term(mode, *it);
				all_ch_size_one = false;
			}
			new_ch.push_back((*it)->subs_coi);
			need_new = need_new || (*it != (*it)->subs_coi);
		}


		if((((op_type == OpInst::Eq) || (op_type == OpInst::NotEq)) && all_ch_size_one == true))
		{
			e->subs_coi = NumInst::create(eVal, e->get_size());
			// do nothing
		}
		else
		{
			if (need_new)
			{
				e->subs_coi = e->apply_children(new_ch);

				int rVal = e->subs_coi->get_bval();
				if (rVal != INVALID_SVAL)
				{
					if (rVal != eVal)
					{
						cout << "e  : " << *e << " (val: " << eVal << ")" << endl;
						cout << "eSub: " << *e->subs_coi << " (val: " << rVal << ")" << endl;
					}
					assert(rVal == eVal);
				}
				else
				{
					e->subs_coi->set_bval(eVal);
				}
			}
		}
	}
	else if (intpd)
	{
		assert(e->get_type() == Op);
		const InstL* ch = e->get_children();
		assert(ch != 0);

		e->subs_coi = NumInst::create(eVal, e->get_size());

		switch (op_type)
		{
		case OpInst::LogNot:
			evaluate_relation(mode, *(ch->begin()));
      if (ch->front() != ch->front()->subs_coi)
      {
        InstL new_ch;
        new_ch.push_back(ch->front()->subs_coi);
        e->subs_coi = e->apply_children(new_ch);

        int rVal = e->subs_coi->get_bval();
        if (rVal != INVALID_SVAL)
        {
          if (rVal != eVal)
          {
            cout << "e  : " << *e << " (val: " << eVal << ")" << endl;
            cout << "eSub: " << *e->subs_coi << " (val: " << rVal << ")" << endl;
          }
          assert(rVal == eVal);
        }
        else
        {
          e->subs_coi->set_bval(eVal);
        }
      }
			break;
		case OpInst::LogAnd:
		case OpInst::LogOr: {
			for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it)
			{
				if (mode == 1)
				{
					evaluate_relation(mode, *it);
				}
				else
				{
					int itVal = (*it)->get_bval();

					if (eVal == controlling(op_type))
					{
						if (itVal == controlling(op_type))
						{
							evaluate_relation(mode, *it);
							break;
						}
					}
					else
					{
						evaluate_relation(mode, *it);
					}
				}
			}
		}break;
		case OpInst::Ternary: {
			InstL::const_iterator it = ch->begin();
			Inst* if_e = *(it++);
			Inst* then_e = *(it++);
			Inst* else_e = *(it++);
			evaluate_relation(mode, if_e);

			int ifVal = if_e->get_bval();
			if (mode == 1)
			{
				evaluate_relation(mode, else_e);
				evaluate_relation(mode, then_e);

				if (ifVal == 0) {
					e->subs_coi = else_e->subs_coi;
				} else if (ifVal == 1) {
					e->subs_coi = then_e->subs_coi;
				} else {
					assert(0);
				}
			}
			else
			{
				if (ifVal == 0) {
					evaluate_relation(mode, else_e);
					e->subs_coi = else_e->subs_coi;
				} else if (ifVal == 1) {
					evaluate_relation(mode, then_e);
					e->subs_coi = then_e->subs_coi;
				} else {
					assert(0);
				}
			}
		}break;
		default:
			assert(0);
		}
	}

	if (e != e->subs_coi) {
	  int eVal = e->get_bval();
    int esVal = e->subs_coi->get_bval();
	  if (esVal == INVALID_SVAL)
	    e->subs_coi->set_bval(eVal);
	  else
	    assert(eVal == esVal);
	}

	AVR_LOG(9, 2, "[EvalP] e: " << *e << " -> " << *(e->subs_coi) << ")" << endl);
}

void Reach::evaluate_term(int mode, Inst*e)
{
	assert(e != 0);
	if (e->get_visit())
	{
		return;
	}
	e->set_visit();
	AVR_LOG(9, 4, "[Eval]: " << *e << endl);

	mpz_class* eVal = e->get_ival();
	assert(eVal != INVALID_SMPZ);

	e->subs_coi = e;
	mpz_class* eaValSub = e->subs_coi->get_ival();

	bool apply_on_children = false;

	switch (e->get_type())
	{
	case Sig:
	{
		// leave it as "itself"
	}break;
	case Wire:
	{
		WireInst* w = WireInst::as(e);
		Inst* port = w->get_port();
		evaluate_term(mode, port);
		e->subs_coi = port->subs_coi;
		OpInst* op_port = OpInst::as(port);
		if (op_port)
			w->set_sliceVal();
		else
			assert(0);
	}break;
	case Const:
	{
		assert(0);
	}break;
	case Num:
	{
		// leave it as "itself"
	}break;
	case Op:
	{
		OpInst* op = OpInst::as(e);
		assert(op != 0);
		OpInst::OpType t = op->get_op();

//		Inst* wc = op->get_wire();

		if (t == OpInst::Ternary) {
			const InstL* ch = e->get_children();
			assert(ch != 0);
			InstL::const_iterator it = ch->begin();
			Inst* if_e = *(it++);
			Inst* then_e = *(it++);
			Inst* else_e = *(it++);
			evaluate_relation(mode, if_e);

			int ifVal = if_e->get_bval();
			if (mode == 1)
			{
				evaluate_term(mode, else_e);
				evaluate_term(mode, then_e);

				if (ifVal == 0) {
					e->subs_coi = else_e->subs_coi;
				} else if (ifVal == 1) {
					e->subs_coi = then_e->subs_coi;
				} else
					assert(0);
			}
			else
			{
				if (ifVal == 0) {
					evaluate_term(mode, else_e);
					e->subs_coi = else_e->subs_coi;
				} else if (ifVal == 1) {
					evaluate_term(mode, then_e);
					e->subs_coi = then_e->subs_coi;
				} else
					assert(0);
			}
			eaValSub = e->subs_coi->get_ival();

//			if (!wc) {
//			  cout << "Error: " << *op << " has no wire" << endl;
//			}
//			assert(wc);
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

		const InstL* ch = e->get_children();
		assert(ch != 0);
		InstL new_ch;
		bool need_new = false;

		for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it)
		{
			if ((*it)->get_size() == 1)
			{
				evaluate_relation(mode, *it);
			}
			else
			{
				evaluate_term(mode, *it);
			}
			new_ch.push_back((*it)->subs_coi);
			need_new = need_new || (*it != (*it)->subs_coi);
		}
		if (need_new)
		{
			e->subs_coi = e->apply_children(new_ch);

			eaValSub = e->subs_coi->get_ival();
			if (eaValSub != INVALID_SMPZ)
			{
				if (*eaValSub != *eVal)
				{
					cout << "newCh: " << new_ch << endl;
					cout << "e      : " << *e << " (val: " << eVal << ")" << endl;
					cout << "e->subs_coi: " << *(e->subs_coi) << " (val: " << eaValSub << ")" << endl;
				}
				assert(*eaValSub == *eVal);
			}
			else
			{
				e->subs_coi->set_ival(eVal);
				eaValSub = eVal;
			}
		}
	}
	else
	{
		// leave it as ""itself"
	}


  assert(eaValSub != INVALID_SMPZ);
  if (*eVal != *eaValSub) {
    cout << *e << "\t: " << *eVal << endl;
    cout << *(e->subs_coi) << "\t: " << *eaValSub << endl;
  }
	assert(*eVal == *eaValSub);

	AVR_LOG(9, 2, "[EvalP] e: " << *e << " -> " << *(e->subs_coi) << ")" << endl);
}
#endif

/// Simplify refinement
Inst* Reach::reduce_relation(Inst* top)
{
	if (top->get_visit())
	{
		return top->get_reduceEval();
	}
	top->set_visit();

	Inst* reduced = top;
	long long reducedVal = top->get_reduceVal();

	const InstL* ch = top->get_children();
	if (ch)
	{
		InstL new_ch;
		bool need_new = false;

		for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it)
		{
			Inst* newCh = reduce_relation((*it));
			if (newCh != (*it))
				need_new = true;
			new_ch.push_back(newCh);
		}
		if (need_new)
		{
			bool done = false;
			OpInst* op = OpInst::as(top);
			if (op)
			{
				switch(op->get_op())
				{
				case OpInst::Eq:
				{
					Inst* lhs = new_ch.front();
					Inst* rhs = new_ch.back();
					if (lhs == rhs)
					{
						done = true;
						reduced = NumInst::create(1,1, SORT());
					}
				}
				break;
				case OpInst::NotEq:
				{
#ifdef ASSERT_DISTINCT_NUMBERS
					Inst* lhs = new_ch.front();
					Inst* rhs = new_ch.back();
					if (lhs->get_type() == Num && rhs->get_type() == Num)
					{
						done = true;
						if (lhs == rhs)
							reduced = NumInst::create(0,1, SORT());
						else
							reduced = NumInst::create(1,1, SORT());
					}
#endif
				}
				break;
				case OpInst::LogAnd:
				{
					bool allTrue = true;
					for(InstL::iterator cit = new_ch.begin(); cit != new_ch.end();)
					{
						Inst* child = *cit;
						if (child == NumInst::create(1, 1, SORT()))
						{
							cit = new_ch.erase(cit);
						}
						else if (child == NumInst::create(0, 1, SORT()))
						{
							done = true;
							reduced = NumInst::create(0,1, SORT());
							break;
						}
						else
						{
							allTrue &= (child->get_reduceVal() == 1);
							cit++;
						}
					}
					if (new_ch.empty())
					{
						done = true;
						reduced = NumInst::create(1,1, SORT());
					}
					if (!done && allTrue)
						reducedVal = 1;
				}
				break;
				case OpInst::LogOr:
				{
					bool allFalse = true;
					for(InstL::iterator cit = new_ch.begin(); cit != new_ch.end();)
					{
						Inst* child = *cit;
						if (child == NumInst::create(0, 1, SORT()))
							cit = new_ch.erase(cit);
						else if (child == NumInst::create(1, 1, SORT()))
						{
							done = true;
							reduced = NumInst::create(1,1, SORT());
							break;
						}
						else
						{
							allFalse &= (child->get_reduceVal() == 0);
							cit++;
						}
					}
					if (new_ch.empty())
					{
						done = true;
						reduced = NumInst::create(0,1, SORT());
					}
					if (!done && allFalse)
						reducedVal = 0;
				}
				break;
				case OpInst::Ternary:
				{
					InstL::iterator cit = new_ch.begin();
					Inst* cond = *cit;
					cit++;
					Inst* thn = *cit;
					cit++;
					Inst* els = *cit;

					if (cond == NumInst::create(1, 1, SORT()) || cond->get_reduceVal() == 1)
					{
						done = true;
						reduced = thn;
					}
					else if (cond == NumInst::create(0, 1, SORT()) || cond->get_reduceVal() == 0)
					{
						done = true;
						reduced = els;
					}
					else if (thn == els)
					{
						done = true;
						reduced = thn;
					}
				}
				break;
				}
			}
			if (!done)
			{
				if (new_ch.empty())
				{
					cout << *top << " became empty" << endl;
				}
				reduced = top->apply_children(new_ch);
			}
		}
	}
	else
	{
		if(!top->get_reduceEval(Inst::get_reduceKey()))
		{
			if(top->get_type() == Sig)
			{
				Inst* rhs = Inst::fetch_trelation_eq(top);
				if (rhs != NULL)
				{
					if (rhs->get_visit())
					{
						reduced = rhs->get_reduceEval();
						if (reducedVal == -1)
						{
							reducedVal = rhs->get_reduceVal();
						}
					}
				}
			}
		}
		else
		{
			reduced = top->get_reduceEval();
		}
	}

	if (reduced == NULL)
	{
		cout << "No exp for " << *top << endl;
	}
	assert(reduced != NULL);
	if (reducedVal != -1)
		reduced->set_reduceVal(reducedVal);
	top->set_reduceEval(reduced);

//	AVR_LOG(9, 0, "[RedR]: " << *top << " becomes " << *top->get_reduceEval() << " (val: " << top->get_reduceEval()->get_reduceVal() << " )" << endl);
	return top->get_reduceEval();
}

/// Simplify refinement
Inst* Reach::reduce_relation_sim(Inst* top, InstToInstM& eqMap)
{
	if (top->get_visit())
	{
		return top->get_reduceEval();
	}
	top->set_visit();

	Inst* reduced = top;

	const InstL* ch = top->get_children();
	if (ch)
	{
		InstL new_ch;
		bool need_new = false;

		for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it)
		{
			Inst* newCh = reduce_relation_sim((*it), eqMap);
			if (newCh != (*it))
				need_new = true;
			new_ch.push_back(newCh);
		}
		if (need_new)
		{
			bool done = false;
			OpInst* op = OpInst::as(top);
			if (op)
			{
				switch(op->get_op())
				{
				case OpInst::Eq:
				{
					Inst* lhs = new_ch.front();
					Inst* rhs = new_ch.back();
					if (lhs == rhs)
					{
						done = true;
						reduced = NumInst::create(1,1, SORT());
					}
				}
				break;
				case OpInst::NotEq:
				{
#ifdef ASSERT_DISTINCT_NUMBERS
					Inst* lhs = new_ch.front();
					Inst* rhs = new_ch.back();
					if (lhs->get_type() == Num && rhs->get_type() == Num)
					{
						done = true;
						if (lhs == rhs)
							reduced = NumInst::create(0,1, SORT());
						else
							reduced = NumInst::create(1,1, SORT());
					}
#endif
				}
				break;
				case OpInst::LogAnd:
				{
					for(InstL::iterator cit = new_ch.begin(); cit != new_ch.end();)
					{
						Inst* child = *cit;
						if (child == NumInst::create(1, 1, SORT()))
						{
							cit = new_ch.erase(cit);
						}
						else if (child == NumInst::create(0, 1, SORT()))
						{
							done = true;
							reduced = NumInst::create(0,1, SORT());
							break;
						}
						else
						{
							cit++;
						}
					}
					if (new_ch.empty())
					{
						done = true;
						reduced = NumInst::create(1,1, SORT());
					}
				}
				break;
				case OpInst::LogOr:
				{
					for(InstL::iterator cit = new_ch.begin(); cit != new_ch.end();)
					{
						Inst* child = *cit;
						if (child == NumInst::create(0, 1, SORT()))
							cit = new_ch.erase(cit);
						else if (child == NumInst::create(1, 1, SORT()))
						{
							done = true;
							reduced = NumInst::create(1,1, SORT());
							break;
						}
						else
						{
							cit++;
						}
					}
					if (new_ch.empty())
					{
						done = true;
						reduced = NumInst::create(0,1, SORT());
					}
				}
				break;
				case OpInst::Ternary:
				{
					InstL::iterator cit = new_ch.begin();
					Inst* cond = *cit;
					cit++;
					Inst* thn = *cit;
					cit++;
					Inst* els = *cit;

					if (cond == NumInst::create(1, 1, SORT()))
					{
						done = true;
						reduced = thn;
					}
					else if (cond == NumInst::create(0, 1, SORT()))
					{
						done = true;
						reduced = els;
					}
					else if (thn == els)
					{
						done = true;
						reduced = thn;
					}
				}
				break;
				default:
					// do nothing
					;
				}
			}
			if (!done)
			{
				if (new_ch.empty())
				{
					cout << *top << " became empty" << endl;
				}
				reduced = top->apply_children(new_ch);
//				reduced = reduced->get_simple();
			}
		}
		OpInst* op = OpInst::as(reduced);
		if (op)
		{
			switch(op->get_op())
			{
			case OpInst::Concat:
			{
				InstL suffix = (*reduced->get_children());
				InstL prefix;
				bool done = false;
				while(1)
				{
					Inst* child = suffix.back();
					suffix.pop_back();
					prefix.push_front(child);

					if (!suffix.empty())
					{
						Inst* remaining = OpInst::create(OpInst::Concat, suffix);
//						Inst* remainingRed = reduce_relation_sim(remaining, eqMap);
						Inst* remainingRed = remaining->get_reduceEval();
						if (remainingRed != NULL && remainingRed != remaining)
						{
							prefix.push_front(remainingRed);
							reduced = OpInst::create(OpInst::Concat, prefix);
//							reduced = reduced->get_simple();
							done = true;
						}
					}
					else
						break;
				}
				if (!done)
				{
					while(1)
					{
						Inst* child = prefix.front();
						prefix.pop_front();
						suffix.push_back(child);

						if (!prefix.empty())
						{
							Inst* remaining = OpInst::create(OpInst::Concat, prefix);
//							Inst* remainingRed = reduce_relation_sim(remaining, eqMap);
							Inst* remainingRed = remaining->get_reduceEval();
							if (remainingRed != NULL && remainingRed != remaining)
							{
								suffix.push_back(remainingRed);
								reduced = OpInst::create(OpInst::Concat, suffix);
//								reduced = reduced->get_simple();
								done = true;
//								cout << "\t(temporary assert added to identify rare case)" << endl;
//								assert(0);
							}
						}
						else
							break;
					}
				}

				reduced = reduced->t_simple;
			}
			break;
			case OpInst::Extract:
			{

			}
			break;
			default:
				// do nothing
				;
			}
		}
	}
	if (reduced->childrenInfo[CONST])
	{
		InstToInstM::iterator mit = eqMap.find(reduced);
		if (mit != eqMap.end())
		{
			AVR_LOG(9, 2, "[RedR]: found " << *reduced << " in map)" << endl);
			reduced = (*mit).second;
		}
		else
		{
			Inst* reduced2 = top->get_reduceEval();
			if (reduced2 != NULL)
			{
				reduced = reduced2;
			}
		}
	}

	top->set_reduceEval(reduced);

	AVR_LOG(9, 1, "[RedR]: " << *top << " becomes " << *top->get_reduceEval() << " )" << endl);
	return top->get_reduceEval();
}

/// END

}
