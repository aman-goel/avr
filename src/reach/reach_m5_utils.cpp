/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


/*
 * reach_m5_utils.cpp
 *
 *  Created on: Feb 13, 2019
 *      Author: rock
 */

#include "reach_m5_utils.h"

#ifdef _M5

#include <cstdlib>
#include <fstream>
#include <cmath>
#include <csignal>
#include <pthread.h>
#include <functional>

using namespace std;

namespace _m5 {

string name(msat_term t, bool skip = true)
{
	if (skip)
		return "id" + to_string(msat_term_id(t));

	char* sp = msat_term_repr(t);
  string s = string(sp);
  msat_free(sp);
  return s;
}

Inst* VmtFrontend::traverse_node(msat_term t) {
	map< msat_term, Inst* >::iterator mit = processed.find(t);
	if (mit != processed.end()) {
		return (*mit).second;
	}

	size_t narg = msat_term_arity(t);
	InstL args;
	for (size_t i = 0; i < narg; i++) {
		msat_term arg = msat_term_get_arg(t, i);
		args.push_back(traverse_node(arg));
	}

	Inst* inst = process_node(t, args);
	processed[t] = inst;
	return inst;
}

Inst* VmtFrontend::process_node(msat_term t, InstL& args) {
	NODE_INFO info;

	info.term = t;

  info.tag = msat_decl_get_tag(get_env(), msat_term_get_decl(t));
  get_node(info, args);

//  vmt_log("processed: " << info);
  return info.node;
}

void VmtFrontend::get_node(NODE_INFO& info, InstL& args) {
	Inst* node = NULL;
	msat_type type;
	size_t sz = 0;
	type = msat_term_get_type(info.term);
	SORT sort = get_node_type(type);
	sz = sort.sz;

//	char* sp = msat_type_repr(type);
//	vmt_log("type " << sp << " in node " << name(info.term) << endl);
//	msat_free(sp);

	OpInst::OpType opt = OpInst::Unknown;
	bool done = false;
	bool cansort = false;
	bool usesz = false;

	switch(info.tag) {
	case MSAT_TAG_ERROR:
		break;
	case MSAT_TAG_UNKNOWN:
		assert(args.size() == 0);
		if (msat_term_is_number(get_env(), info.term)) {
			mpq_t m;
			mpq_init(m);
			if (!msat_term_to_number(get_env(), info.term, m)) {
				string snum = string(mpq_get_str(NULL, 2, m));
				node = NumInst::create(snum, sz, 2, sort);
			}
			else {
				vmt_loge("unable to convert to a number in node " << name(info.term));
			}
		}
		else {
			node = process_sig(info, sz, sort);
		}
		done = true;
		break;
	case MSAT_TAG_TRUE:/**< the Boolean constant True */
		assert(sz == 1);
		node = NumInst::create(1, 1, SORT());
		done = true;
		break;
	case MSAT_TAG_FALSE:/**< the Boolean constant False */
		assert(sz == 1);
		node = NumInst::create(0, 1, SORT());
		done = true;
		break;
	case MSAT_TAG_AND:/**< the AND Boolean connective */
		assert(sz == 1);
		assert(args.size() > 1);
		opt = OpInst::LogAnd;
		break;
	case MSAT_TAG_OR:/**< the OR Boolean connective */
		assert(sz == 1);
		assert(args.size() > 1);
		opt = OpInst::LogOr;
		break;
	case MSAT_TAG_NOT:/**< the NOT Boolean connective */
		assert(sz == 1);
		assert(args.size() == 1);
		opt = OpInst::LogNot;
		break;
	case MSAT_TAG_IFF:/**< the IFF Boolean connective */
		assert(sz == 1);
		assert(args.size() == 2);
		opt = OpInst::Eq;
		break;
	case MSAT_TAG_EQ:/**< equality */
		assert(args.size() == 2);
		assert(args.front()->get_size() == args.back()->get_size());
		opt = OpInst::Eq;
		break;
	case MSAT_TAG_ITE:/**< term-level if-then-else */
		assert(args.size() == 3);
		assert(args.front()->get_size() == 1);
		{
			Inst* cond = args.front();
			args.pop_front();
			Inst* the = args.front();
			args.pop_front();
			Inst* els = args.front();
			args.pop_front();
			assert(the->get_size() == els->get_size());
			assert(the->get_size() == sz);

			if (the == els)
				node = the;
			else {
				if (sz == 1 && the->get_type() == Num && els->get_type() == Num) {
					if (the == NumInst::create(1, 1, SORT())) {
						assert(els == NumInst::create(0, 1, SORT()));
						node = cond;
					}
					else {
						assert(the == NumInst::create(0, 1, SORT()));
						assert(els == NumInst::create(1, 1, SORT()));
						node = OpInst::create(OpInst::LogNot, cond);
					}
				}
				else {
					node = OpInst::create(OpInst::Ternary, cond, the, els);
				}
			}
		}
		done = true;
		break;
	case MSAT_TAG_BV_CONCAT:/**< BV concatenation */
		assert(args.size() > 1);
		reverse(args.begin(), args.end());
		opt = OpInst::Concat;
		break;
	case MSAT_TAG_BV_EXTRACT:/**< BV selection */
		{
			assert(args.size() == 1);
			size_t hi = 0;
			size_t lo = 0;
			if (msat_term_is_bv_extract(get_env(), info.term, &hi, &lo)) {
				node = ExInst::create(args.front(), hi, lo);
			}
			else {
				vmt_loge("unable to get extract node " << name(info.term));
			}
		}
		done = true;
		break;
	case MSAT_TAG_BV_NOT:/**< BV bitwise not */
		assert(args.size() == 1);
		assert(args.front()->get_size() == sz);
		opt = OpInst::BitWiseNot;
		break;
	case MSAT_TAG_BV_AND:/**< BV bitwise and */
		assert(args.size() == 2);
		assert(args.front()->get_size() == args.back()->get_size());
		opt = OpInst::BitWiseAnd;
		cansort = true;
		break;
	case MSAT_TAG_BV_OR:/**< BV bitwise or */
		assert(args.size() == 2);
		assert(args.front()->get_size() == args.back()->get_size());
		opt = OpInst::BitWiseOr;
		cansort = true;
		break;
	case MSAT_TAG_BV_XOR:/**< BV bitwise xor */
		assert(args.size() == 2);
		assert(args.front()->get_size() == args.back()->get_size());
		opt = OpInst::BitWiseXor;
		cansort = true;
		break;
	case MSAT_TAG_BV_ULT:/**< BV unsigned < */
		assert(args.size() == 2);
		assert(args.front()->get_size() == args.back()->get_size());
		opt = OpInst::Le;
		break;
	case MSAT_TAG_BV_SLT:/**< BV signed < */
		assert(args.size() == 2);
		assert(args.front()->get_size() == args.back()->get_size());
		opt = OpInst::SLe;
		break;
	case MSAT_TAG_BV_ULE:/**< BV unsigned <= */
		assert(args.size() == 2);
		assert(args.front()->get_size() == args.back()->get_size());
		opt = OpInst::LeEq;
		break;
	case MSAT_TAG_BV_SLE:/**< BV signed < */
		assert(args.size() == 2);
		assert(args.front()->get_size() == args.back()->get_size());
		opt = OpInst::SLeEq;
		break;
	case MSAT_TAG_BV_COMP:/**< BV bit comparison */
		vmt_loge("operation with tag " << info.tag << " not supported in node " << name(info.term));
		break;
	case MSAT_TAG_BV_NEG:/**< BV unary minus */
		assert(args.size() == 1);
		assert(args.front()->get_size() == sz);
		opt = OpInst::Minus;
		break;
	case MSAT_TAG_BV_ADD:/**< BV addition */
		assert(args.size() == 2);
		assert(args.front()->get_size() == args.back()->get_size());
		{
			Inst* arg1 = args.front();
			if (OpInst::as(arg1) && OpInst::as(arg1)->get_op() == OpInst::Minus) {
				Inst* arg2 = args.back();
				args.clear();
				swap (arg1, arg2);
				args.push_back(arg1);
				args.push_back(arg2);
			}
			opt = OpInst::Add;
			cansort = true;
		}
		break;
	case MSAT_TAG_BV_SUB:/**< BV subtraction */
		assert(args.size() == 2);
		assert(args.front()->get_size() == args.back()->get_size());
		opt = OpInst::Sub;
		break;
	case MSAT_TAG_BV_MUL:/**< BV multiplication */
		assert(args.size() == 2);
		assert(args.front()->get_size() == args.back()->get_size());
		opt = OpInst::Mult;
		cansort = true;
		usesz = true;
		break;
	case MSAT_TAG_BV_UDIV:/**< BV unsigned division */
		assert(args.size() == 2);
		assert(args.front()->get_size() == args.back()->get_size());
		opt = OpInst::Div;
		usesz = true;
		break;
	case MSAT_TAG_BV_SDIV:/**< BV signed division */
		assert(args.size() == 2);
		assert(args.front()->get_size() == args.back()->get_size());
		opt = OpInst::SDiv;
		usesz = true;
		break;
	case MSAT_TAG_BV_UREM:/**< BV unsigned remainder */
		assert(args.size() == 2);
		assert(args.front()->get_size() == args.back()->get_size());
		opt = OpInst::Rem;
		usesz = true;
		break;
	case MSAT_TAG_BV_SREM:/**< BV signed remainder */
		assert(args.size() == 2);
		assert(args.front()->get_size() == args.back()->get_size());
		opt = OpInst::SRem;
		usesz = true;
		break;
	case MSAT_TAG_BV_LSHL:/**< BV logical left shift */
		assert(args.size() == 2);
		opt = OpInst::ShiftL;
		usesz = true;
		break;
	case MSAT_TAG_BV_LSHR:/**< BV logical right shift */
		assert(args.size() == 2);
		opt = OpInst::ShiftR;
		usesz = true;
		break;
	case MSAT_TAG_BV_ASHR:/**< BV arithmetic right shift */
		assert(args.size() == 2);
		opt = OpInst::AShiftR;
		usesz = true;
		break;
	case MSAT_TAG_BV_ROL:/**< BV rotate left */
		assert(args.size() == 2);
		opt = OpInst::RotateL;
		usesz = true;
		break;
	case MSAT_TAG_BV_ROR:/**< BV rotate right */
		assert(args.size() == 2);
		opt = OpInst::RotateR;
		usesz = true;
		break;
	case MSAT_TAG_BV_ZEXT:/**< BV zero extension */
		{
			assert(args.size() == 1);
			size_t amount = 0;
			if (msat_term_is_bv_zext(get_env(), info.term, &amount)) {
				Inst* num = NumInst::create(0, amount, SORT());
				args.push_back(num);

				node = OpInst::create(OpInst::Concat, args);
			}
			else {
				vmt_loge("unable to get zero extend amount for node " << name(info.term));
			}
		}
		done = true;
		break;
	case MSAT_TAG_BV_SEXT:/**< BV sign extension */
		{
			assert(args.size() == 1);
			size_t amount = 0;
			if (msat_term_is_bv_sext(get_env(), info.term, &amount)) {

	//			Inst* num = NumInst::create(0, amount);
	//			constants.insert(num);
	//			args.push_back(num);
	//			vmt_logw("ignoring signedness, interpreting as unsigned operation for node " << name(info.term));

				Inst* arg1 = args.front();
				Inst* ex = ExInst::create(arg1, (arg1->get_size() - 1), (arg1->get_size() - 1));
				for (int i = 0; i < amount; i++)
					args.push_back(ex);

				node = OpInst::create(OpInst::Concat, args);
			}
			else {
				vmt_loge("unable to get sign extend amount for node " << name(info.term));
			}
		}
		done = true;
		break;
	case MSAT_TAG_ARRAY_CONST:/**< Constant array, array = arrayconst (width, value) */
	{
		assert(args.size() == 1);
		assert(sort.args.size() == 2);
		unsigned width = sort.args.front().sz;
		assert(width > 0);
		Inst* init_val = args.front();
		assert(init_val->get_type() == Num);
		mpz_class* value = NumInst::as(init_val)->get_mpz();
		args.clear();

		args.push_back(NumInst::create(width, 32, SORT()));
		args.push_back(NumInst::create(*value, sz, SORT()));
		opt = OpInst::ArrayConst;
		node = OpInst::create(opt, args, sz, true, NULL, sort);
		done = true;
	}
		break;
	case MSAT_TAG_ARRAY_READ:/**< Array read/select operation, value = arrayselect(array, addr)*/
		assert(args.size() == 2);
		opt = OpInst::ArraySelect;
		node = OpInst::create(opt, args, sz, true, NULL);
		done = true;
		break;
	case MSAT_TAG_ARRAY_WRITE:/**< Array write/store operation, array = arraystore (array, addr, value) */
	{
		assert(args.size() == 3);
		assert(sort.args.size() == 2);
		opt = OpInst::ArrayStore;
		node = OpInst::create(opt, args, sz, true, NULL, sort);
		done = true;
	}
		break;
	case MSAT_TAG_PLUS:/**< arithmetic addition */
		assert(args.size() == 2);
		assert(args.front()->get_sort() == args.back()->get_sort());
		{
			bool doswap = false;
			Inst* arg1 = args.front();
			if (OpInst::as(arg1) && OpInst::as(arg1)->get_op() == OpInst::IntMinus)
				doswap = true;
			else if (NumInst::as(arg1) && NumInst::as(arg1)->get_num() < 0)
				doswap = true;
			if (doswap) {
				Inst* arg2 = args.back();
				args.clear();
				swap (arg1, arg2);
				args.push_back(arg1);
				args.push_back(arg2);
			}

			Inst* arg2 = args.back();
			if (OpInst::as(arg2) && OpInst::as(arg2)->get_op() == OpInst::IntMinus) {
				args.pop_back();
				args.push_back(arg2->get_children()->front());
				opt = OpInst::IntSub;
			}
			else {
				opt = OpInst::IntAdd;
				cansort = true;
			}
		}
		break;
	case MSAT_TAG_TIMES:/**< arithmetic multiplication */
		assert(args.size() == 2);
		assert(args.front()->get_sort() == args.back()->get_sort());
		{
			Inst* arg1 = args.front();
			if (NumInst::as(arg1) && NumInst::as(arg1)->get_num() < 0) {
				Inst* arg2 = args.back();
				args.clear();
				swap (arg1, arg2);
				args.push_back(arg1);
				args.push_back(arg2);
			}
			Inst* arg2 = args.back();
			if (NumInst::as(arg2) && NumInst::as(arg2)->get_num() == -1) {
				args.pop_back();
				opt = OpInst::IntMinus;
			}
			else {
				opt = OpInst::IntMult;
				cansort = true;
			}
		}
		break;
	case MSAT_TAG_DIVIDE:/**< arithmetic division */
		assert(args.size() == 2);
		assert(args.front()->get_sort() == args.back()->get_sort());
		opt = OpInst::IntDiv;
		break;
	case MSAT_TAG_FLOOR:/**< floor function */
		assert(args.size() == 1);
		assert(args.front()->get_sort_type() == inttype);
		opt = OpInst::IntFloor;
		break;
	case MSAT_TAG_LEQ:/**< arithmetic <= */
		assert(args.size() == 2);
		assert(args.front()->get_sort() == args.back()->get_sort());
		opt = OpInst::IntLeEq;
		break;
	case MSAT_TAG_INT_MOD_CONGR:/**< integer modular congruence */
		assert(args.size() == 2);
		assert(args.front()->get_sort() == args.back()->get_sort());
		opt = OpInst::IntMod;
		vmt_loge("found integer modulo congruence for node " << name(info.term));
		break;
	case MSAT_TAG_FP_EQ:/**< FP IEEE equality */
	case MSAT_TAG_FP_LT:/**< FP < */
	case MSAT_TAG_FP_LE:/**< FP <= */
	case MSAT_TAG_FP_NEG:/**< FP unary minus */
	case MSAT_TAG_FP_ADD:/**< FP addition */
	case MSAT_TAG_FP_SUB:/**< FP subtraction */
	case MSAT_TAG_FP_MUL:/**< FP multiplication */
	case MSAT_TAG_FP_DIV:/**< FP division */
	case MSAT_TAG_FP_SQRT:/**< FP square root */
	case MSAT_TAG_FP_ABS:/**< FP absolute value */
	case MSAT_TAG_FP_MIN:/**< FP min */
	case MSAT_TAG_FP_MAX:/**< FP max */
	case MSAT_TAG_FP_CAST:/**< FP format conversion */
	case MSAT_TAG_FP_ROUND_TO_INT:/**< FP round to integer */
	case MSAT_TAG_FP_FROM_SBV:/**< FP conversion from a signed BV */
	case MSAT_TAG_FP_FROM_UBV:/**< FP conversion from an unsigned BV */
	case MSAT_TAG_FP_TO_BV:/**< FP conversion to BV */
	case MSAT_TAG_FP_AS_IEEEBV:/**< FP as IEEE BV (access to the bits) */
	case MSAT_TAG_FP_ISNAN:/**< FP check for NaN */
	case MSAT_TAG_FP_ISINF:/**< FP check for infinity */
	case MSAT_TAG_FP_ISZERO:/**< FP check for zero */
	case MSAT_TAG_FP_ISSUBNORMAL:/**< FP check for subnormal */
	case MSAT_TAG_FP_ISNORMAL:/**< FP check for normal */
	case MSAT_TAG_FP_ISNEG:/**< FP check for negative */
	case MSAT_TAG_FP_ISPOS:/**< FP check for positive */
	case MSAT_TAG_FP_FROM_IEEEBV:/**< FP conversion from IEEE BV */
		vmt_loge("operation with tag " << info.tag << " not supported in node " << name(info.term));
		break;
	case MSAT_TAG_INT_FROM_UBV:/**< Unsigned BV -> INT conversion */
	case MSAT_TAG_INT_FROM_SBV:/**< Signed BV -> INT conversion */
	case MSAT_TAG_INT_TO_BV:/**< INT -> BV conversion */
		vmt_loge("operation with tag " << info.tag << " not supported in node " << name(info.term));
		break;
	default:
		vmt_loge("unrecognized MathSAT tag " << info.tag << " for node " << name(info.term));
	}

	if (!done) {
//		if (cansort)
//			args.sort(compare());
		if (usesz)
			node = OpInst::create(opt, args, sz);
		else
			node = OpInst::create(opt, args);
	}

	if (!node) {
		vmt_loge("processing failed for node " << name(info.term));
	}
	if (node->get_size() != sz) {
		vmt_loge("output size different for " << *node << " (expected: " << sz << ", got " << node->get_size());
	}

	info.node = node;
}

SORT VmtFrontend::get_node_type(msat_type& type) {
	SORT sort;
	size_t sz = 0;

	if (msat_is_bool_type(get_env(), type)) {
		sort.type = bvtype;
		sort.sz = 1;
	}
	else if (msat_is_bv_type(get_env(), type, &sz)) {
		sort.type = bvtype;
		sort.sz = sz;
	}
	else if (msat_is_integer_type(get_env(), type)) {
		sort.type = inttype;
		sort.sz = INT_SZ;
	}
	else {
		msat_type typeD;
		msat_type typeR;

		if (msat_is_array_type(get_env(), type, &typeD, &typeR)) {
			sort.type = arraytype;
			SORT domain = get_node_type(typeD);
			SORT range = get_node_type(typeR);
			sort.args.push_back(domain);
			sort.args.push_back(range);
			sort.sz = range.sz;
		}
		else {
			char* sp = msat_type_repr(type);
			vmt_loge("unsupported type " << sp);
			msat_free(sp);
		}
	}
	return sort;
}

Inst* VmtFrontend::process_sig(NODE_INFO& info, int sz, SORT sort) {
	Inst* node = NULL;

	if (msat_term_is_constant(get_env(), info.term)) {
		string n = name(info.term, false);
		if (Solver::m_nameToInst.find(n) != Solver::m_nameToInst.end()) {
			node = Solver::m_nameToInst[n];
		}
		else {
			assert(0);
		}
	}
	else {
		assert(0);
	}

	vmt_logv("constant node: " << *node << " " << node->get_sort().sort2str() << endl);
	return node;
}


}

#endif




