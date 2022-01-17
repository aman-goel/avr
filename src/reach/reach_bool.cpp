/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


/*
 * reach_bool.cpp
 *
 *  Created on: Jan 13, 2020
 *      Author: rock
 */

#include "reach_bool.h"

Inst* true_gate() {
	return NumInst::create(1, 1, SORT());
}
Inst* false_gate() {
	return NumInst::create(0, 1, SORT());
}
Inst* not_gate(Inst* A) {
	if (A == true_gate())
		return false_gate();
	else if (A == false_gate())
		return true_gate();
	else
		return OpInst::create(OpInst::LogNot, A);
}
Inst* and_gate(Inst* A, Inst* B, bool inverter = false) {
	if (A == B)
		return inverter ? not_gate(A) : A;
	return OpInst::create(OpInst::LogAnd, A, B);
}
Inst* nand_gate(Inst* A, Inst* B) {
	return and_gate(A, B, true);
}
Inst* or_gate(Inst* A, Inst* B, bool inverter = false) {
//	return inverter ? and_gate(not_gate(A), not_gate(B)) : nand_gate(not_gate(A), not_gate(B));
	if (A == B)
		return inverter ? not_gate(A) : A;
	return OpInst::create(OpInst::LogOr, A, B);
}
Inst* nor_gate(Inst* A, Inst* B) {
	return or_gate(A, B, true);
}
Inst* xor_gate(Inst* A, Inst* B) {
	return nor_gate(and_gate(A, B), nor_gate(A, B));
}
Inst* xnor_gate(Inst* A, Inst* B) {
	return or_gate(and_gate(A, B), nor_gate(A, B));
}
Inst* mux_gate(Inst* A, Inst* B, Inst* S) {
	if (A == B)
		return A;
	return or_gate(and_gate(A, not_gate(S)), and_gate(B, S));
}
Inst* eq_gate(Inst* A, Inst* B) {
	if (A == B)
		return true_gate();
	return xnor_gate(A, B);
}
Inst* gt_gate(Inst* A, Inst* B) {
	if (A == B)
		return false_gate();
	return and_gate(A, not_gate(B));
}

Inst* and_gate(InstL& L) {
//	Inst* O = L.front();
//	L.pop_front();
//	while(!L.empty()) {
//		Inst* A = L.front();
//		L.pop_front();
//		O = and_gate(O, A);
//	}
//	return O;
	return OpInst::create(OpInst::LogAnd, L);
}
Inst* or_gate(InstL& L) {
//	Inst* O = L.front();
//	L.pop_front();
//	while(!L.empty()) {
//		Inst* A = L.front();
//		L.pop_front();
//		O = or_gate(O, A);
//	}
//	return O;
	return OpInst::create(OpInst::LogOr, L);
}
Inst* xor_gate(InstL& args) {
	assert(args.size() == 2);
	return xor_gate(args.front(), args.back());
}
Inst* simple_gate(InstL& args, OpInst::OpType opt, bool complement) {
	Inst* arg;
	switch(opt) {
	case OpInst::LogAnd:
		arg = and_gate(args);
		break;
	case OpInst::LogOr:
		arg = or_gate(args);
		break;
	case OpInst::LogXor:
		arg = xor_gate(args);
		break;
	default:
		assert(0);
	}
	if (complement)
		arg = not_gate(arg);
	return arg;
}

Inst* get_uge(InstV& a, InstV& b, int i) {
	// - assert (a[i] > b[i]) or ((a[i] = b[i]) and (bvuge a[i-1 ... 0] b[i-1 ... 0]))
	assert(i < a.size());

	Inst* or1 = gt_gate(a[i], b[i]);
	Inst* and1 = eq_gate(a[i], b[i]);
	if (i == 0) {
		return or_gate(or1, and1);
	}
	else {
		Inst* and2 = get_uge(a, b, i-1);
		return or_gate(or1, and_gate(and1, and2));
	}
}
Inst* get_sge(InstV& a, InstV& b) {
	int n = a.size();
	// n must be greater than 1
	assert(n > 1);
	n--;

  // (a[n...0] >= b[n...0]) is (b[n] > a[n]) or (a[n] = b[n] and (bvuge a[n-1...0] b[n-1...0]))
	Inst* or1 = gt_gate(b[n], a[n]);
	Inst* and1 = eq_gate(a[n], b[n]);
	Inst* and2 = get_uge(a, b, n-1);
	return or_gate(or1, and_gate(and1, and2));
}


void w2b_extract(OpInst* node) {
	ExInst* nodex = ExInst::as(node);
	assert(nodex);

	Inst* argw = nodex->get_exp();
	unsigned hi = nodex->get_hi();
	unsigned lo = nodex->get_lo();

	InstV& argb = argw->word2bool();
	assert(argb.size() < hi);

	for (int i = lo; i <= hi; i++) {
		node->w2b.push_back(argb[i]);
	}
	assert(node->w2b.size() == node->get_size());
}

void w2b_concat(OpInst* node) {
	for (auto& argw: *node->get_children()) {
		InstV& argb = argw->word2bool();
		for (auto& arg: argb)
			node->w2b.push_back(arg);
	}
	assert(node->w2b.size() == node->get_size());
}

void w2b_extend(OpInst* node, bool sign) {
	Inst* argw = node->get_children()->front();
	InstV& argb = argw->word2bool();
	Inst* ext = sign ? argb.back() : false_gate();
	for (auto& arg: argb)
		node->w2b.push_back(arg);
	assert(node->w2b.size() <= node->get_size());
	while(node->w2b.size() < node->get_size())
		node->w2b.push_back(ext);
	assert(node->w2b.size() == node->get_size());
}

void w2b_not(OpInst* node) {
	Inst* argw = node->get_children()->front();
	InstV& argb = argw->word2bool();
	for (auto& arg: argb) {
		node->w2b.push_back(not_gate(arg));
	}
	assert(node->w2b.size() == node->get_size());
}

void w2b_simple(OpInst* node, OpInst::OpType opt, bool complement) {
	list<InstV*> allb;
	for (auto& argw: *node->get_children()) {
		InstV& argb = argw->word2bool();
		allb.push_back(&argb);
	}
	for (int i = 0; i < node->get_size(); i++) {
		InstL argList;
		for (auto& argb_p: allb) {
			argList.push_back((*argb_p)[i]);
		}
		Inst* arg = simple_gate(argList, opt, complement);
		node->w2b.push_back(arg);
	}
	assert(node->w2b.size() == node->get_size());
}

void w2b_reduce(OpInst* node, OpInst::OpType opt, bool complement) {
	Inst* argw = node->get_children()->front();
	InstV& argb = argw->word2bool();

	InstL argList;
	for (auto& arg: argb)
		argList.push_back(arg);
	Inst* arg = simple_gate(argList, opt, complement);
	node->w2b.push_back(arg);
}

void w2b_neq(OpInst* node, bool complement) {
	Inst* argwL = node->get_children()->front();
	Inst* argwR = node->get_children()->back();
	InstV& argbL = argwL->word2bool();
	InstV& argbR = argwR->word2bool();

	InstL argList;
	for (int i = 0; i < argbL.size(); i++) {
		Inst* arg = xor_gate(argbL[i], argbR[i]);
		argList.push_back(arg);
	}
	Inst* argb = or_gate(argList);
	if (complement)
		argb = not_gate(argb);
	node->w2b.push_back(argb);
	assert(node->w2b.size() == node->get_size());
}

void w2b_ternary(OpInst* node) {
	InstL::const_iterator cit = node->get_children()->begin();
	Inst* argwC = (*cit);
	cit++;
	Inst* argwT = (*cit);
	cit++;
	Inst* argwE = (*cit);
	InstV& argbT = argwT->word2bool();
	InstV& argbE = argwE->word2bool();

	InstL argList;
	for (int i = 0; i < argbT.size(); i++) {
		Inst* arg = mux_gate(argbT[i], argbE[i], argwC);
		argList.push_back(arg);
	}
	Inst* argb = and_gate(argList);
	node->w2b.push_back(argb);
	assert(node->w2b.size() == node->get_size());
}

void w2b_ge(OpInst* node, OpInst::OpType opt, bool sign) {
	Inst* argwL = node->get_children()->front();
	Inst* argwR = node->get_children()->back();
	InstV& argbL = argwL->word2bool();
	InstV& argbR = argwR->word2bool();

	bool swap = false;
	bool complement = false;
	switch(opt) {
	case OpInst::SLe:
	case OpInst::Le:
//		(a < b) := !(a >= b)
		complement = true;
		break;
	case OpInst::SLeEq:
	case OpInst::LeEq:
//		(a <= b) := (b >= a)
		swap = true;
		break;
	case OpInst::SGr:
	case OpInst::Gr:
//		(a > b) := !(a <= b) := !(b >= a)
		swap = true;
		complement = true;
		break;
	case OpInst::SGrEq:
	case OpInst::GrEq:
		break;
	default:
		assert(0);
	}

	Inst* argb;
	if (!sign)
		argb = swap ? get_uge(argbR, argbL, argwR->get_size() - 1) :
									get_uge(argbL, argbR, argwL->get_size() - 1);
	else
		argb = swap ? get_sge(argbR, argbL) :
									get_sge(argbL, argbR);
	if (complement)
		argb = not_gate(argb);
	node->w2b.push_back(argb);
	assert(node->w2b.size() == node->get_size());
}

InstV& SigInst::word2bool() {
	if (!w2b.empty()) {
		return w2b;
	}

	if(m_size == 1) {
		w2b.push_back(this);
	}
	else {
		for(int i = 0; i < m_size; ++i) {
			ostringstream oss;
			oss << m_name << "$" << i;
			Inst* bi = SigInst::create(oss.str(), 1, SORT());
			w2b.push_back(bi);
		}
	}
	return w2b;
}

InstV& NumInst::word2bool() {
	if (!w2b.empty()) {
		return w2b;
	}

	if(m_size == 1) {
		w2b.push_back(this);
	}
	else {
		string snum = m_mpz.get_str(2);
		for (int i = 0; i < m_size; i++) {
			Inst* bi;
			if (i < snum.length() && snum[i] == '1')
				bi = true_gate();
			else
				bi = false_gate();
			w2b.push_back(bi);
		}
	}
	return w2b;
}

InstV& WireInst::word2bool() {
	return get_port()->word2bool();
}

InstV& ConstInst::word2bool() {
	if (!w2b.empty()) {
		return w2b;
	}

	if(m_size == 1) {
		w2b.push_back(this);
	}
	else {
		for(int i = 0; i < m_size; ++i) {
			ostringstream oss;
			oss << m_name << "$" << i;
			Inst* bi = ConstInst::create(oss.str(), 1, m_parent.first, m_parent.second, SORT());
			w2b.push_back(bi);
		}
	}
	return w2b;
}

InstV& OpInst::word2bool() {
	if (!w2b.empty()) {
		return w2b;
	}
	bool done = false;

	switch (m_op) {
		case Extract:
			w2b_extract(this);
			done = true;
			break;
		case Concat:
			w2b_concat(this);
			done = true;
			break;
		case Zext:
			w2b_extend(this, false);
			done = true;
			break;
		case Sext:
			w2b_extend(this, false);
			done = true;
			break;
		case LogNot:
		case BitWiseNot:
			w2b_not(this);
			done = true;
			break;
		case LogAnd:
		case BitWiseAnd:
			w2b_simple(this, LogAnd, false);
			done = true;
			break;
		case LogOr:
		case BitWiseOr:
			w2b_simple(this, LogOr, false);
			done = true;
			break;
		case LogXor:
		case BitWiseXor:
			w2b_simple(this, LogXor, false);
			done = true;
			break;
		case LogNand:
		case BitWiseNand:
			w2b_simple(this, LogAnd, true);
			done = true;
			break;
		case LogNor:
		case BitWiseNor:
			w2b_simple(this, LogOr, true);
			done = true;
			break;
		case LogXNor:
		case BitWiseXNor:
			w2b_simple(this, LogXor, true);
			done = true;
			break;
		case Eq:
			w2b_neq(this, true);
			done = true;
			break;
		case NotEq:
			w2b_neq(this, false);
			done = true;
			break;
		case Ternary:
			w2b_ternary(this);
			done = true;
			break;
		case ReductionAnd:
			w2b_reduce(this, LogAnd, false);
			done = true;
			break;
		case ReductionOr:
			w2b_reduce(this, LogOr, false);
			done = true;
			break;
		case ReductionXor:
			w2b_reduce(this, LogXor, false);
			done = true;
			break;
		case ReductionNand:
			w2b_reduce(this, LogAnd, true);
			done = true;
			break;
		case ReductionNor:
			w2b_reduce(this, LogOr, true);
			done = true;
			break;
		case ReductionXNor:
			w2b_reduce(this, LogXor, true);
			done = true;
			break;
		case Minus:
			break;
		case Le:
		case LeEq:
		case Gr:
		case GrEq:
			w2b_ge(this, m_op, false);
			done = true;
			break;
		case SLe:
		case SLeEq:
		case SGr:
		case SGrEq:
			w2b_ge(this, m_op, true);
			done = true;
			break;
		case AddC:
		case Add:
		case Sub:
		case Mult:
		case Div:
		case SDiv:
		case Rem:
		case SRem:
		case SMod:
			break;
		case ShiftL:
		case ShiftR:
		case AShiftR:
		case AShiftL:
			break;
		case RotateL:
		case RotateR:
			break;
		case VShiftL:
		case VShiftR:
		case VAShiftL:
		case VAShiftR:
		case VRotateL:
		case VRotateR:
		case VEx:
			break;
		case ArrayConst:
		case ArraySelect:
		case ArrayStore:
			break;
		case IntAdd:
		case IntSub:
		case IntMult:
		case IntDiv:
		case IntFloor:
		case IntLe:
		case IntLeEq:
		case IntGr:
		case IntGrEq:
		case IntMod:
		case IntMinus:
		case Unknown:
		case Future:
			assert(0 && "unexpected word2bool conversion");
			break;
		default:
			cout << "unknown operation: " << op2str(m_op) << endl;
			assert(0);
	}
	if (!done)
		assert(0 && "not implemented");

	return w2b;
}

InstV& ExInst::word2bool() {
	if (!w2b.empty()) {
		return w2b;
	}
	w2b_extract(this);
	return w2b;
}

InstV& MemInst::word2bool() {
	assert(0 && "not implemented");
}
InstV& UFInst::word2bool() {
	assert(0 && "not implemented");
}
InstV& LambdaInst::word2bool() {
	assert(0 && "not implemented");
}
InstV& ArrayInst::word2bool() {
	assert(0 && "not implemented");
}


//InstV& all_word2bool(Inst* wn) {
//	if (not wn->word2bool.empty()) {
//		return wn->word2bool;
//	}
//
//	InstV& bn = wn->word2bool;
//
//}

