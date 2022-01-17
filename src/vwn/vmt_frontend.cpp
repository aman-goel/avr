/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


/*
 * vmt_parser.cpp
 *
 *  Created on: Sep 29, 2018
 *      Author: rock
 */


#include "vmt_frontend.h"

using namespace std;

namespace vmt
{

void VmtFrontend::help() {
	//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
	vmt_log("\n");
	vmt_log("    read_vmt [filename]\n");
	vmt_log("\n");
	vmt_log("Reads the design in a 'vmt' file. (The VMT format is an extension of \n");
	vmt_log("the SMT-LIBv2 (SMT2 for short) format to represent symbolic transition systems.\n");
	vmt_log("(https://es-static.fbk.eu/tools/nuxmv/index.php?n=Languages.VMT)\n");
	vmt_log("\n");
	vmt_log("Note: The frontend is similar to one used in ic3ia (https://es-static.fbk.eu/people\n");
	vmt_log("/griggio/ic3ia/index.html) and requires MathSAT (http://mathsat.fbk.eu/)\n");
	vmt_log("\n");
}


void VmtFrontend::execute() {
	traverse_system();
//	print_system();
}


void VmtFrontend::print_system() {
	vmt_log('\n');

	vmt_log("(states)" << endl);
	for (auto& v: states) {
		vmt_log('\t' << *v.second << " of type " << v.second->get_sort().sort2str() << endl);
	}
	vmt_log('\n');

	vmt_log("(next states)" << endl);
	for (auto& v: next_states) {
		vmt_log('\t' << *v << " of type " << v->get_sort().sort2str() << endl);
	}
	vmt_log('\n');

	vmt_log("(initial states)" << endl);
	for (auto& v: map_init) {
		vmt_log('\t' << *v.first << " = " << *v.second << endl);
	}
	vmt_log('\n');

	vmt_log("(transition relation)" << endl);
	for (auto& v: map_net_op) {
		vmt_log('\t' << *v.first << " = " << *v.second << endl);
	}
	vmt_log('\n');

	vmt_log("(properties)" << endl);
	for (auto& v: properties) {
		vmt_log('\t' << *v << endl);
	}
	vmt_log('\n');

	vmt_log("(assumptions)" << endl);
	for (auto& v: assumptions) {
		vmt_log('\t' << *v << " = " << *map_net_op[v] << endl);
	}
	vmt_log('\n');
}


void VmtFrontend::traverse_system() {
	for (auto& s: statevars())
		traverse_node(s);
	for (auto& s: nextstatevars())
		traverse_node(s);
	for (auto& s: inputvars())
		traverse_node(s);

	Inst* instI = traverse_node(init());
	add_inits(instI);

	Inst* instT = traverse_node(trans());
	add_trans(instT);

	InstL instP;
	for (auto& p: props())
		instP.push_back(traverse_node(p));
	add_props(instP);
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

  gate_names[info.node] = gate_name(t);

//  vmt_log("processed: " << info);
  return info.node;
};


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
//	bool sortbool = false;

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
				bool negate = false;
//				if (snum[0] == '-') {
////					cout << snum << endl;
//					negate = true;
//					snum = snum.substr(1);
//				}
				node = NumInst::create(snum, sz, 2, sort);
				assert(node->get_sort() == sort);
				constants.insert(node);
				if (negate)
					node = OpInst::create(OpInst::IntMinus, node);
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
		node = NumInst::create(1, 1);
		done = true;
		break;
	case MSAT_TAG_FALSE:/**< the Boolean constant False */
		assert(sz == 1);
		node = NumInst::create(0, 1);
		done = true;
		break;
	case MSAT_TAG_AND:/**< the AND Boolean connective */
		assert(sz == 1);
		assert(args.size() > 1);
		opt = OpInst::LogAnd;
		{
			InstL newArgs;
			for (auto& v: args) {
				OpInst* opv = OpInst::as(v);
				if (opv && opv->get_op() == OpInst::LogAnd) {
					for (InstL::const_iterator cit = v->get_children()->begin(); cit != v->get_children()->end(); cit++)
						newArgs.push_back(*cit);
				}
				else
					newArgs.push_back(v);
			}
			newArgs.swap(args);
		}
//		sortbool = true;

//		{
//			// (a11 | a12) & (a21 | a22) -> ()
//			if (args.size() >= 2) {
//				InstL::const_iterator it = args.begin();
//				OpInst* a1 = OpInst::as(*it);
//				it++;
//				OpInst* a2 = OpInst::as(*it);
//				if (a1 && a2 && a1->get_op() == OpInst::LogOr && a2->get_op() == OpInst::LogOr) {
//					if ((a1->get_children()->size() == 2) && (a2->get_children()->size() == 2)) {
//						Inst* a11 = a1->get_children()->front();
//						Inst* a12 = a1->get_children()->back();
//						Inst* a21 = a2->get_children()->front();
//						Inst* a22 = a2->get_children()->back();
//
//						Inst* a21N = OpInst::create(OpInst::LogNot, a21);
//						Inst* a22N = OpInst::create(OpInst::LogNot, a22);
//						if (a12 == a21N || a12 == a21) {
//							swap(a11, a12);
//						}
//						else if (a12 == a22N || a12 == a22) {
//							swap(a11, a12);
//							swap(a21, a22);
//						}
//
//						Inst* a11N = OpInst::create(OpInst::LogNot, a11);
//						if (a11 == a21) {
//							cout << "entering1" << endl;
//
//							// (a11 | a12) & (a11 | a22) -> (a11 | (a12 & a22))
//							args.pop_front();
//							args.pop_front();
//							args.push_front(OpInst::create(OpInst::LogAnd, a12, a22));
//							args.push_front(a11);
//							opt = OpInst::LogOr;
//						}
//						else if (a11N == a21) {
//							cout << "entering2" << endl;
//
//							// (a11 | a12) & (!a11 | a22) -> ((a11 & a22) | (!a11 & a12))
//							cout << "changing &: " << args << endl;
//							args.pop_front();
//							args.pop_front();
//							args.push_front(OpInst::create(OpInst::LogAnd, a11N, a12));
//							args.push_front(OpInst::create(OpInst::LogAnd, a11, a22));
//							opt = OpInst::LogOr;
//							cout << "to |: " << args << endl;
//						}
//					}
//				}
//			}
//		}
		break;
	case MSAT_TAG_OR:/**< the OR Boolean connective */
		assert(sz == 1);
		assert(args.size() > 1);
		{
			InstL newArgs;
			for (auto& v: args) {
				OpInst* opv = OpInst::as(v);
				if (opv && opv->get_op() == OpInst::LogOr) {
					for (InstL::const_iterator cit = v->get_children()->begin(); cit != v->get_children()->end(); cit++)
						newArgs.push_back(*cit);
				}
				else
					newArgs.push_back(v);
			}
			newArgs.swap(args);
		}
		opt = OpInst::LogOr;
//		sortbool = true;
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
//		sortbool = true;
		break;
	case MSAT_TAG_EQ:/**< equality */
		assert(args.size() == 2);
		assert(args.front()->get_size() == args.back()->get_size());
		opt = OpInst::Eq;
//		sortbool = true;
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
					if (the == NumInst::create(1, 1)) {
						assert(els == NumInst::create(0, 1));
						node = cond;
					}
					else {
						assert(the == NumInst::create(0, 1));
						assert(els == NumInst::create(1, 1));
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

				Inst* num = NumInst::create(0, amount);
				constants.insert(num);
				args.push_back(num);
				node = OpInst::create(OpInst::Concat, args);

//				Inst* num = NumInst::create(amount, amount + args.front()->get_size());
//				constants.insert(num);
//				args.push_back(num);
//				node = OpInst::create(OpInst::Zext, args);
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
				Inst* num = NumInst::create(amount, amount + args.front()->get_size());
				constants.insert(num);
				args.push_back(num);

				node = OpInst::create(OpInst::Sext, args);
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

		args.push_back(NumInst::create(width, 32));
		args.push_back(NumInst::create(sz, 32));
		args.push_back(NumInst::create(*value, sz));
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
		unsigned width = sort.args.front().sz;
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
			else if (NumInst::as(arg2) && NumInst::as(arg2)->get_num() < 0) {
				args.pop_back();
				string snum = NumInst::as(arg2)->get_mpz()->get_str(10);
				assert (snum[0] == '-');
				snum = snum.substr(1);
				Inst* new_arg2 = NumInst::create(snum, arg2->get_size(), 10, arg2->get_sort());
				args.push_back(new_arg2);
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
//		if (sortbool)
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


string VmtFrontend::gate_name(msat_term t) {
	string s = to_string(msat_term_id(t));
	s = VMT_NAME_PREFIX + s;
	return s;
}


void VmtFrontend::sanitize_name(string& n) {
	n.erase(remove(n.begin(), n.end(), '\"'), n.end());
	replace(n.begin(), n.end(), '#', '.');

	string ext = "__AT0";
	size_t nlen = n.length();
	size_t elen = ext.length();

	if (nlen > elen) {
		bool  matched = true;
		for (int i = 0; i < elen; i++) {
			if (n[nlen - elen + i] != ext[i]) {
				matched = false;
				break;
			}
		}
		if (matched)
			n.erase(nlen - elen);
	}
	assert(n.length() > 0);
	if (n[0] == '_')
		n.erase(0, 1);
}


Inst* VmtFrontend::process_sig(NODE_INFO& info, int sz, SORT sort) {
	Inst* node = NULL;
	string type = "?";
	if (is_statevar(info.term)) {
	  string n = name(info.term, false);
	  sanitize_name(n);
		node = SigInst::create(n, sz, sort);
		states[n] = node;
		type = "reg";
	}
	else if (is_nextstatevar(info.term)) {
		msat_term pre = cur(info.term);
	  string n = name(pre, false);
	  sanitize_name(n);
		Inst* preI = SigInst::create(n, sz, sort);
	  n += NEXT_SUFFIX;
		node = SigInst::create(n, sz, sort);
		next_states.push_back(node);

		unordered_map< Inst*, Inst* >::const_iterator mit = state_next2pre.find(node);
		if (mit != state_next2pre.end()) {
			vmt_loge("found multiple pre state attached to next state " << *node << " (pre- " << *state_next2pre[node] << " and " << *preI);
		}
		state_next2pre[node] = preI;
		type = "nextreg";
	}
	else if (is_inputvar(info.term)) {
	  string n = name(info.term, false);
	  sanitize_name(n);
		node = SigInst::create(n, sz, sort);
		inputs.insert(node);
		type = "input";
	}
	else {
		vmt_loge("unknown signal in node " << name(info.term, false));
	}

	SigInst* sig = SigInst::as(node);
	assert(sig);

	vmt_logv("adding sig: " << *node << " of type " << type << " " << node->get_sort().sort2str() << endl);
	return node;
}


void VmtFrontend::add_inits(Inst* instI) {
//	vmt_logv("init: " << *instI << endl);
	InstToInstM l;
	flatten_and_init(instI, l);

	bool simpleT = true;
	for (auto& v: l) {
		SigInst* sig = SigInst::as(v.first);
		if (!sig) {
			simpleT = false;
			vmt_logw("expected init relation: " << *v.first << " = " << *v.second);
		}
		else {
			if (states.find(sig->get_name()) == states.end()) {
				vmt_loge("expected state variable in initial state condition for " << *v.first);
			}
		}

		InstToInstM::iterator mit = map_init.find(v.first);
		if (mit != map_init.end()) {
			if (v.second != (*mit).second) {
				vmt_loge("conflicting repeated initial value for state " << *v.first);
			}
		}
		else {
			NumInst* num = NumInst::as(v.second);
//			if (!num) {
//				vmt_loge("expected number in initial state condition for " << *v.first << ", got " << *v.second);
//			}
			map_init[v.first] = v.second;
			vmt_logv("adding init: [" << *v.first << "] = " << *v.second << endl);
		}
	}

	if (!simpleT && Config::g_split_signals) {
		Config::g_split_signals = false;
		vmt_logw("detected complex init relation, disabling split optimization");
	}
}


void VmtFrontend::add_trans(Inst* instT) {
	string name = "assume_" + to_string(assumptions.size() + 1);
	Inst* assume = SigInst::create(name, 1, SORT());
	map_net_op[assume] = instT;
	assumptions.push_back(assume);

	vector < pair< Inst*, Inst* > > l;

	InstL allOr;
	flatten_or(instT, allOr);
	cout << "found total " << allOr.size() << " relations in T" << endl;
	list< TRANS_DATA > data;

	if (allOr.size() == 1) {
		InstL allAnd;
		flatten_and(allOr.front(), allAnd);
		bool changed = false;
		for (InstL::iterator cit = allAnd.begin(); cit != allAnd.end();) {
			Inst* v = (*cit);
			if (!v->find_next()) {
				vmt_log("found assumption: " << *v << "\n");
				string n = "assume_" + to_string(assumptions.size() + 1);
				Inst* lhs = SigInst::create(n, 1, SORT());
				map_net_op[lhs] = v;
				assumptions.push_back(lhs);
				cit = allAnd.erase(cit);
				changed = true;
			}
			else {
				cit++;
			}
		}
		if (changed) {
			allOr.pop_front();
			allOr.push_front(OpInst::create(OpInst::LogAnd, allAnd));
		}
	}

	int count = 0;
	bool fcond = false;
	bool simpleT = true;
	for (auto& inst: allOr) {
		vmt_logv("\n[" << ++count << "]" << endl);
		vmt_logv("\t-> " << *inst << endl);

		TRANS_DATA l;
		InstL ndone;
		InstS nextSigs;
		collect_next_sigs(inst, nextSigs, true);
		flatten_and_trans(inst, l, ndone);

//		vmt_log("---------------------------------------------------------" << endl);
//		vmt_log("\t-> " << *inst << endl);
//		vmt_log("cond: " << l.cond << endl);
//		vmt_log("cond_rem: " << l.cond_rem << endl);
//		for (auto& v: l.t) {
//			vmt_log("\ttran: [" << *v.first << "] = " << *v.second << endl);
//		}
//		for (auto& lhs: ndone) {
//			vmt_log("ndone: " << *lhs << endl);
//		}
//		vmt_log("---------------------------------------------------------" << endl);

		for (auto& lhs: ndone) {
			InstToInstM::iterator mit = l.t.find(lhs);
			Inst* rhs;
			do {
				assert(mit != l.t.end());
				rhs = (*mit).second;
				if (!rhs->find_next())
					break;
				mit = l.t.find(rhs);
			} while (mit != l.t.end());
			assert (rhs);
			if (rhs->find_next()) {
				vmt_logwv("unable to resolve trans relation for " << *lhs << " = " << *rhs);
				l.cond_rem.push_back(OpInst::create(OpInst::Eq, lhs, rhs));
//				assert(0);
			}
			else {
				if (l.t.find(lhs) != l.t.end()) {
					vmt_logw("repeated relation for " << *lhs << ", related to " << *l.t[lhs] << " and " << *rhs);
					l.cond.push_back(OpInst::create(OpInst::Eq, l.t[lhs], rhs));
				}
				else
					l.t[lhs] = rhs;
			}
		}

		for (auto& v: nextSigs) {
			if (l.t.find(v) == l.t.end()) {
				l.t[v] = v;
				simpleT = false;
			}
		}

		InstToInstM cache;
		for (auto& v: l.cond_rem) {
			Inst* tve = v;
//			if (tve->find_next()) {
//				tve = substitute(tve, l.t, cache);
//			}
			l.cond.push_back(tve);
		}
		l.cond_rem.clear();
		data.push_back(l);

		if (!l.cond.empty()) {
			fcond = true;

			vmt_logv("cond: " << l.cond << endl);
			for (auto& v: l.t) {
				vmt_logv("\ttran: [" << *v.first << "] = " << *v.second << endl);
			}

			for (auto& v: l.cond) {
				if (v->find_next()) {
					vmt_logwv("unable to eliminate next relation in cond- " << *v);
					simpleT = false;
				}
			}
		}
	}
//	if (!top_ca.empty()) {
//		if (fassume) {
//			vmt_loge("found relation of type- cond -> assume ^ next = f(pre)");
//
////			string n = "assume_" + to_string(assumptions.size() + 1);
////			Inst* lhs = SigInst::create(n, 1);
////			Inst* rhs = OpInst::create(OpInst::LogOr, top_ca);
////			map_net_op[lhs] = rhs;
////			assumptions.push_back(lhs);
//		}
//		else {
//			vmt_logw("found relation of type- cond -> next = f(pre)");
//		}
//	}

	InstToListPairM mapT;
	for (auto& d: data) {
		Inst* cond = NULL;
		if (!d.cond.empty())
			cond = OpInst::create(OpInst::LogAnd, d.cond);

		for (auto& v: d.t) {
			SigInst* sig = SigInst::as(v.first);
			if (!sig) {
				vmt_loge("expected signal for " << *v.first);
			}
			if (find(next_states.begin(), next_states.end(), sig) == next_states.end()) {
	//			cout << "next states: " << next_states << endl;
				vmt_loge("expected next state variable in transition relation for " << *sig);
			}
			assert(v.first->get_size() == v.second->get_size());

			if (v.second->find_next()) {
				assert(!simpleT);
				if (v.second == sig && d.cond.empty()) {
					vmt_loge("unexpected next state variable without condition in right of transition relation for " << *sig << " = " << *v.second);
				}
			}

			InstToListPairM::iterator mit = mapT.find(v.first);
			if (mit != mapT.end()) {
				(*mit).second.push_back(make_pair(cond, v.second));
			}
			else {
				mapT[v.first].push_back(make_pair(cond, v.second));
			}
		}
	}

	for (auto& m: mapT) {
		Inst* lhs = m.first;
		Inst* rhs;
		unordered_map< Inst*, Inst* >::const_iterator mit = state_next2pre.find(lhs);
		if (mit != state_next2pre.end()) {
			rhs = state_next2pre[lhs];
		}
		else {
			vmt_loge("unable to find pre version of next state " << *lhs);
		}

		list< pair< Inst*, Inst* > >& rhsT = m.second;
		for (list< pair< Inst*, Inst* > >::reverse_iterator rit = rhsT.rbegin(); rit != rhsT.rend(); rit++) {
			Inst* cond = (*rit).first;
			Inst* t = (*rit).second;
			if (cond == NULL) {
				rhs = t;
				assert(rhsT.size() == 1);
			}
			else {
				rhs = OpInst::create(OpInst::Ternary, cond, t, rhs);
			}
		}

		InstToInstM::iterator mit2 = map_net_op.find(lhs);
		if (mit2 != map_net_op.end()) {
			vmt_loge("conflicting repeated trans relation for node " << *lhs);
		}
		else {
			map_net_op[lhs] = rhs;
			vmt_logv("adding trans: " << *lhs << " = " << *rhs << endl);
		}
	}

	if (!simpleT && Config::g_split_signals) {
		Config::g_split_signals = false;
		vmt_logw("detected complex transition relation, disabling split optimization");
	}

	// erase next states with no cones
	for(InstL::iterator lit = next_states.begin(); lit != next_states.end();){
		if (map_net_op.find(*lit) == map_net_op.end()) {
			Inst* pre = state_next2pre[*lit];
			assert(pre);
			lit = next_states.erase(lit);
			SigInst* sig = SigInst::as(pre);
			assert(sig);
			states.erase(sig->get_name());
		}
		else
			lit++;
	}

//	assert(simpleT);
}


void VmtFrontend::add_props(InstL& instP) {
//	vmt_logv("properties: " << instP << endl);
	if (instP.empty()) {
		vmt_loge("no property specified");
	}

	for (auto& rhs: instP) {
		string name = VMT_PROP_PREFIX + to_string(properties.size());
		Inst* p = SigInst::create(name, 1, SORT());
		properties.push_back(p);
//		if (rhs->get_type() == Sig) {
//			string n = SigInst::as(rhs)->get_name() + NEXT_SUFFIX;
//			Inst* nextSig = SigInst::create(n, rhs->get_size());
//			InstToInstM::iterator mit = map_net_op.find(nextSig);
//			if (mit != map_net_op.end()) {
//				vmt_logv("prop: replacing " << *rhs << " with " << *(*mit).second << endl);
//				rhs = (*mit).second;
//			}
//		}
		map_net_op[p] = rhs;
	}

	if (instP.size() == 1) {
		Inst* prop = instP.front();
		NumInst* np = NumInst::as(prop);
		if (np) {
			vmt_loge("property trivially equals " << *np);
		}
	}
}


void VmtFrontend::flatten_and_init(Inst* inst, InstToInstM& l) {
	OpInst* op = OpInst::as(inst);
	if (op) {
		if (op->get_op() == OpInst::LogAnd) {
			const InstL* ch = op->get_children();
			assert (ch);
			for (auto& c: *ch) {
					flatten_and_init(c, l);
			}
		}
		else if (op->get_op() == OpInst::Eq) {
			const InstL* ch = op->get_children();
			assert (ch);
			assert(ch->size() == 2);

			Inst* lhs = ch->front();
			Inst* rhs = ch->back();
			SigInst* sig = SigInst::as(lhs);
			if (!sig)
				swap(lhs, rhs);
			sig = SigInst::as(lhs);
			if (sig) {
				if (inputs.find(sig) != inputs.end()) {
					swap(lhs, rhs);
				}
				else if (SigInst::as(rhs) &&
									find(next_states.begin(), next_states.end(), rhs) != next_states.end()) {
					swap(lhs, rhs);
				}
			}
			vmt_logvv("init- adding flatten: " << *lhs << " with " << *rhs << endl);
			if (l.find(lhs) != l.end()) {
				vmt_logw("init- repeated relation for: " << *lhs << " with " << *l[lhs] << " and " << *rhs);
				flatten_and_init(OpInst::create(OpInst::Eq, l[lhs], rhs), l);
			}
			else
				l[lhs] = rhs;
		}
		else if (op->get_op() == OpInst::LogNot) {
			const InstL* ch = op->get_children();
			assert (ch);

			Inst* lhs = ch->front();
			assert(lhs->get_size() == 1);
			Inst* rhs = NumInst::create(0, 1);
			if (l.find(lhs) != l.end()) {
				vmt_logw("init- repeated relation for: " << *lhs << " with " << *l[lhs] << " and " << *rhs);
				flatten_and_init(OpInst::create(OpInst::Eq, l[lhs], rhs), l);
			}
			else
				l[lhs] = rhs;
		}
		else {
			assert(inst->get_size() == 1);
			Inst* rhs = NumInst::create(1, 1);
			if (l.find(inst) != l.end()) {
				vmt_logw("init- repeated relation for: " << *inst << " with " << *l[inst] << " and " << *rhs);
				flatten_and_init(OpInst::create(OpInst::Eq, l[inst], rhs), l);
			}
			else
				l[inst] = rhs;
		}
	}
	else {
		NumInst* num = NumInst::as(inst);
		if (num) {
			if (num->get_num() != 1) {
				vmt_loge("init- unexpected relation in node " << *inst);
			}
		}
		else {
			assert(inst->get_size() == 1);
			Inst* rhs = NumInst::create(1, 1);
			if (l.find(inst) != l.end()) {
				vmt_logw("init- repeated relation for: " << *inst << " with " << *l[inst] << " and " << *rhs);
				flatten_and_init(OpInst::create(OpInst::Eq, l[inst], rhs), l);
			}
			else
				l[inst] = rhs;
		}
	}
}


void VmtFrontend::flatten_and_trans(Inst* inst, TRANS_DATA& l, InstL& ndone) {
	OpInst* op = OpInst::as(inst);
	if (op) {
		if (op->get_op() == OpInst::LogAnd) {
			const InstL* ch = op->get_children();
			assert (ch);
			for (auto& c: *ch) {
				if (!c->find_next())
					l.cond.push_back(c);
				else
					flatten_and_trans(c, l, ndone);
			}
		}
		else if (op->get_op() == OpInst::Eq) {
			const InstL* ch = op->get_children();
			assert (ch);
			assert(ch->size() == 2);

			Inst* lhs = ch->front();
			Inst* rhs = ch->back();
			SigInst* sig = SigInst::as(lhs);
			if (!sig)
				swap(lhs, rhs);
			sig = SigInst::as(lhs);
			if (!sig) {
				vmt_logwv("trans- unexpected relation in node " << *inst);
				l.cond_rem.push_back(inst);
				return;
			}
			assert(sig);
			if (inputs.find(sig) != inputs.end()) {
				swap(lhs, rhs);
				sig = SigInst::as(lhs);
				if (!sig) {
					vmt_logwv("trans- unexpected relation in node " << *inst);
					l.cond_rem.push_back(inst);
					return;
				}
				assert (inputs.find(sig) == inputs.end());
			}
			else if (SigInst::as(rhs) && rhs->find_next()) {
				swap(lhs, rhs);
				sig = SigInst::as(lhs);
				assert(sig);
			}
			assert(SigInst::as(lhs) && lhs->find_next());
			vmt_logvv("trans- adding flatten: " << *lhs << " with " << *rhs << endl);

			if (rhs->find_next()) {
				vmt_logwv("trans- unexpected relation in node " << *inst);
				l.cond_rem.push_back(inst);
				return;

//				SigInst* sig = SigInst::as(rhs);
//				if (!sig) {
//				}
//				else
//					ndone.push_back(lhs);
			}

			if (l.t.find(lhs) != l.t.end()) {
				vmt_logw("repeated relation for " << *lhs << ", related to " << *l.t[lhs] << " and " << *rhs);
				l.cond.push_back(OpInst::create(OpInst::Eq, l.t[lhs], rhs));
			}
			else
				l.t[lhs] = rhs;
		}
		else if (op->get_op() == OpInst::LogNot) {
			const InstL* ch = op->get_children();
			assert (ch);

			SigInst* sig = SigInst::as(ch->front());
			if (!sig) {
				vmt_logwv("trans- unexpected relation in node " << *inst);
				l.cond_rem.push_back(inst);
				return;
			}
			assert(sig->get_size() == 1);

			Inst* rhs = NumInst::create(0, 1);
			if (l.t.find(sig) != l.t.end()) {
				vmt_logw("repeated relation for " << *sig << ", related to " << *l.t[sig] << " and " << *rhs);
				l.cond.push_back(OpInst::create(OpInst::Eq, l.t[sig], rhs));
			}
			else
				l.t[sig] = rhs;
		}
		else {
			vmt_logwv("trans- unexpected relation in node " << *inst);
			l.cond_rem.push_back(inst);
			return;
		}
	}
	else {
		SigInst* sig = SigInst::as(inst);
		if (!sig) {
			vmt_logwv("trans- unexpected relation in node " << *inst);
			l.cond_rem.push_back(inst);
			return;
		}
		assert(sig->get_size() == 1);

		Inst* rhs = NumInst::create(1, 1);
		if (l.t.find(sig) != l.t.end()) {
			vmt_logw("repeated relation for " << *sig << ", related to " << *l.t[sig] << " and " << *rhs);
			l.cond.push_back(OpInst::create(OpInst::Eq, l.t[sig], rhs));
		}
		else
			l.t[sig] = rhs;
	}
}


void VmtFrontend::flatten_or(Inst* inst, InstL& l) {
	OpInst* op = OpInst::as(inst);
	if (op) {
		if (op->get_op() == OpInst::LogOr) {
			const InstL* ch = op->get_children();
			assert (ch);
			for (auto& c: *ch)
				flatten_or(c, l);
			return;
		}
	}
	l.push_back(inst);
}


void VmtFrontend::flatten_and(Inst* inst, InstL& l) {
	OpInst* op = OpInst::as(inst);
	if (op) {
		if (op->get_op() == OpInst::LogAnd) {
			const InstL* ch = op->get_children();
			assert (ch);
			for (auto& c: *ch)
				flatten_and(c, l);
			return;
		}
	}
	l.push_back(inst);
}


void VmtFrontend::collect_next_sigs(Inst* inst, InstS& l, bool init_visit) {
	if (init_visit) {
		Inst::init_visit2();
	}
	if (inst->get_visit2()) {
		return;
	}
	inst->set_visit2();

	const InstL* ch = inst->get_children();
	if (ch) {
		for (auto& c: *ch)
			collect_next_sigs(c, l, false);
	}
	else if (inst->get_type() == Sig) {
		if (inst->find_next()) {
			assert(state_next2pre.find(inst) != state_next2pre.end());
			l.insert(inst);
		}
	}
}


Inst* VmtFrontend::substitute(Inst* ve, InstToInstM& m, InstToInstM& cache) {
	if (!ve->find_next())
		return ve;

	InstToInstM::iterator cit = cache.find(ve);
	if (cit != cache.end())
		return (*cit).second;

	InstToInstM::iterator mit = m.find(ve);
	if (mit != m.end())
		return (*mit).second;

	Inst* topRet = ve;

	InstL newCh;
	const InstL* ch = topRet->get_children();
	if (ch) {
		bool apply = false;
		for (auto& c: (*ch)) {
			Inst* newC = substitute(c, m, cache);
			newCh.push_back(newC);
			if (newC != c)
				apply = true;
		}
		if (apply) {
			topRet = ve->apply_children(newCh);
		}
	}
	cache[ve] = topRet;
	return topRet;
}


}


