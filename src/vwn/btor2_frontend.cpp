/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


/*
 * btor2_frontend.cpp
 *
 *  Created on: Sep 3, 2019
 *      Author: rock
 */


#include "btor2_frontend.h"

using namespace std;

namespace bt2
{

void Btor2Frontend::help() {
	//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
	btor2_log("\n");
	btor2_log("    read_btor2 [filename]\n");
	btor2_log("\n");
	btor2_log("Reads the design in a 'btor2' file.\n");
	btor2_log("(https://http://fmv.jku.at/cav18-btor2)\n");
	btor2_log("\n");
}


void Btor2Frontend::execute() {
	reset();
	traverse_system();
//	post_process();
//	print_system();
}


void Btor2Frontend::reset() {
	nodeList.clear();
	id2line.clear();
	id2sort.clear();
	processed.clear();
}


void Btor2Frontend::print_system() {
	btor2_log('\n');

	btor2_log("(states)" << endl);
	for (auto& v: states) {
		btor2_log('\t' << *v.second << " of type " << v.second->get_sort().sort2str() << endl);
	}
	btor2_log('\n');

	btor2_log("(next states)" << endl);
	for (auto& v: next_states) {
		btor2_log('\t' << *v << " of type " << v->get_sort().sort2str() << endl);
	}
	btor2_log('\n');

	btor2_log("(initial states)" << endl);
	for (auto& v: map_init) {
		btor2_log('\t' << *v.first << " = " << *v.second << endl);
	}
	btor2_log('\n');

	btor2_log("(transition relation)" << endl);
	for (auto& v: map_net_op) {
		btor2_log('\t' << *v.first << " = " << *v.second << endl);
	}
	btor2_log('\n');

	btor2_log("(properties)" << endl);
	for (auto& v: properties) {
		btor2_log('\t' << *v << endl);
	}
	btor2_log('\n');

	btor2_log("(assumptions)" << endl);
	for (auto& v: assumptions) {
		btor2_log('\t' << *v << " = " << *map_net_op[v] << endl);
	}
	btor2_log('\n');
}


void Btor2Frontend::post_process() {
	for (auto& v: states) {
		Inst* lhs = v.second;
		if (lhs->get_sort_type() == bvtype) {
			InstToInstM::iterator mit = map_init.find(lhs);
			if (mit == map_init.end()) {
				Inst* rhs = NumInst::create(0, lhs->get_size());
				map_init[lhs] = rhs;
				btor2_logv("adding forced init: [" << *lhs << "] = " << *rhs << endl);
			}
		}
	}
}


void Btor2Frontend::traverse_system() {
	if (reader == NULL) {
		btor2_loge("btor2 reader not set, exiting");
	}

	Btor2LineIterator it;
	Btor2Line* l;
	uint32_t j;
	btor2_log("\t(starting interpreting btor2 model)\n");
	it = btor2parser_iter_init (reader);
	while ((l = btor2parser_iter_next (&it))) {
		if (id2line.find(l->id) != id2line.end()) {
			btor2_loge("Line for id " << l->id << " already present");
		}
		id2line[l->id] = *l;

		if (l->tag == BTOR2_TAG_sort) {
			if (id2sort.find(l->id) != id2sort.end()) {
				btor2_loge("Sort for id " << l->id << " already present");
			}
			id2sort[l->id] = get_node_type(l->id);
		}
		else
			nodeList.push_back(l->id);
	}
	btor2_log("\t(finished interpreting btor2 model)\n");
	btor2_log("\t(parsed system with " << "?" << " state variables)\n");

	for (auto& id: nodeList)
		traverse_node(id);
}


Inst* Btor2Frontend::traverse_node(int64_t nid) {
	map< int64_t, Inst* >::iterator mit = processed.find(nid);
	if (mit != processed.end()) {
		return (*mit).second;
	}

	int64_t id = nid;
	bool negate = false;
	if (id < 0) {
		negate = true;
		id = -id;

		map< int64_t, Inst* >::iterator mit2 = processed.find(id);
		if (mit2 != processed.end()) {
			Inst* inst = OpInst::create(OpInst::LogNot, (*mit2).second);
			processed[nid] = inst;
			return inst;
		}
	}

	Btor2Line& t = get_line(id);
	size_t narg = t.nargs;
	InstL args;
	for (size_t i = 0; i < narg; i++) {
		int64_t argi = t.args[i];
		args.push_back(traverse_node(argi));
	}

	Inst* inst = process_node(t, args);
	processed[id] = inst;

	if (negate) {
		assert(inst->get_size() == 1);
		inst = OpInst::create(OpInst::LogNot, inst);
		processed[nid] = inst;
	}
	return inst;
}


Inst* Btor2Frontend::process_node(Btor2Line& t, InstL& args) {
	NODE_INFO info;
	info.id = t.id;
	get_node(info, args);
  gate_names[info.node] = gate_name(t);

  btor2_logv("\t\tprocessed: " << info << "\n");
  return info.node;
};


Btor2Line& Btor2Frontend::get_line(int64_t id) {
	map< int64_t, Btor2Line >::iterator mit = id2line.find(id);
	if (mit == id2line.end()) {
		btor2_loge("no line found for id " << id);
	}
	return (*mit).second;
}


string Btor2Frontend::print_id(int64_t id) {
	Btor2Line& t = get_line(id);
	ostringstream out;
	out << "->  " << t.id << " " << t.name << " tag: " << t.tag
			 << " init: " << t.init << " next: " << t.next
//			 << " const: " << string(t.constant) << " symbol: " << string(t.symbol)
			 << " nargs: " << t.nargs << " ch: ";
	for (int i = 0; i < t.nargs; i++)
		out << t.args[i] << " ";
	return out.str();
}


SORT Btor2Frontend::get_node_type(int64_t sid) {
	map< int64_t, SORT >::iterator mit = id2sort.find(sid);
	if (mit != id2sort.end())
		return (*mit).second;
	Btor2Line& t = get_line(sid);
	Btor2Sort& type = t.sort;
	SORT sort;

	switch (type.tag) {
		case BTOR2_TAG_SORT_bitvec: {
			sort.type = bvtype;
			sort.sz = type.bitvec.width;
		} break;
		case BTOR2_TAG_SORT_array: {
			sort.type = arraytype;
			SORT domain = get_node_type(type.array.index);
			SORT range = get_node_type(type.array.element);
			sort.args.push_back(domain);
			sort.args.push_back(range);
			sort.sz = range.sz;
		} break;
		default:
			btor2_loge("invalid sort encountered");
	}

	id2sort[sid] = sort;
	return sort;
}


Inst* Btor2Frontend::get_state(Btor2Line& t, int sz, SORT sort) {
	Inst* node = NULL;
	string n = "_s" + to_string(states.size()) + "_";
	n += name(t, false);
	sanitize_name(n);
	node = SigInst::create(n, sz, sort);
	states[n] = node;

	SigInst* sig = SigInst::as(node);
	assert(sig);

	btor2_logv("adding sig: " << *node << " of type reg " << node->get_sort().sort2str() << endl);
	return node;
}


Inst* Btor2Frontend::get_input(Btor2Line& t, int sz, SORT sort) {
	Inst* node = NULL;
	string n = "_i" + to_string(inputs.size()) + "_";
	n += name(t, false);
	sanitize_name(n);
	node = SigInst::create(n, sz, sort);
	inputs.insert(node);

	SigInst* sig = SigInst::as(node);
	assert(sig);

	btor2_logv("adding sig: " << *node << " of type inp " << node->get_sort().sort2str() << endl);
	return node;
}


Inst* Btor2Frontend::get_init(Btor2Line& t, int sz, SORT sort, InstL& args) {
	if (args.size() != 2) {
		btor2_loge("expecting init condition with 2 arguments, got " << args.size());
	}

	Inst* lhs = args.front();
	Inst* rhs = args.back();
	SigInst* sig = SigInst::as(lhs);
	if (!sig) {
		btor2_loge("expecting init condition with argument 1 as signal, got " << *lhs);
	}
	else {
		if (states.find(sig->get_name()) == states.end()) {
			btor2_loge("expecting init condition argument 1 to be a state, got " << *lhs);
		}
	}

	SORT lhs_t = lhs->get_sort();
	SORT rhs_t = rhs->get_sort();
	if (lhs_t != rhs_t) {
		bool done = false;
		if (lhs_t.type == arraytype) {
			if (*lhs->get_sort_range() == rhs_t) {
				unsigned width = lhs->get_sort_domain()->sz;
				assert(width > 0);
				Inst* init_val = rhs;
				assert(init_val->get_type() == Num);
				mpz_class* value = NumInst::as(init_val)->get_mpz();

				InstL args;
				args.push_back(NumInst::create(width, 32));
				args.push_back(NumInst::create(sz, 32));
				args.push_back(NumInst::create(*value, sz));
				rhs = OpInst::create(OpInst::ArrayConst, args);
				done = true;
			}
		}
		if (!done) {
			btor2_loge("sort mismatch in init " << *lhs << " = " << *rhs);
		}
	}

	InstToInstM::iterator mit = map_init.find(lhs);
	if (mit != map_init.end()) {
		if (rhs != (*mit).second) {
			btor2_loge("conflicting repeated initial value for state " << *lhs);
		}
	}
	else {
		NumInst* num = NumInst::as(rhs);
//			if (!num) {
//				btor2_loge("expected number in initial state condition for " << *lhs << ", got " << *rhs);
//			}
		map_init[lhs] = rhs;
		btor2_logv("adding init: [" << *lhs << "] = " << *rhs << endl);
	}

	return rhs;
}


Inst* Btor2Frontend::get_next(Btor2Line& t, int sz, SORT sort, InstL& args) {
	if (args.size() != 2) {
		btor2_loge("expecting trans condition with 2 arguments, got " << args.size());
	}

	Inst* lhs = args.front();
	Inst* rhs = args.back();
	SigInst* sig = SigInst::as(lhs);
	if (!sig) {
		btor2_loge("expecting trans condition with argument 1 as signal, got " << *lhs);
	}
	else {
		if (states.find(sig->get_name()) == states.end()) {
			btor2_loge("expecting trans condition argument 1 to be a state, got " << *lhs);
		}
	}

	string next = sig->get_name() + NEXT_SUFFIX;
	Inst* sigNext = SigInst::create(next, sig->get_size(), sig->get_sort());
	next_states.push_back(sigNext);
	assert (state_next2pre.find(sigNext) == state_next2pre.end());
	state_next2pre[sigNext] = sig;

	map_net_op[sigNext] = rhs;
	btor2_logv("adding trans: " << *sigNext << " = " << *rhs << "\n");

	return sigNext;
}


Inst* Btor2Frontend::get_bad(Btor2Line& t, int sz, SORT sort, InstL& args) {
	if (args.size() != 1) {
		btor2_loge("expecting bad condition with 1 argument, got " << args.size());
	}

	Inst* propNeg = args.front();
	Inst* prop = OpInst::create(OpInst::LogNot, propNeg);

	string n = "_p" + to_string(properties.size()) + "_";
	n += name(t, false);
	Inst* p = SigInst::create(n, 1, SORT());
	properties.push_back(p);
	map_net_op[p] = prop;

	btor2_logv("adding prop: " << *prop << "\n");
	return propNeg;
}


Inst* Btor2Frontend::get_constraint(Btor2Line& t, int sz, SORT sort, InstL& args) {
	if (args.size() != 1) {
		btor2_loge("expecting constraint condition with 1 argument, got " << args.size());
	}

	Inst* a = args.front();
	string n = "assume_" + name(t, false);
	Inst* p = SigInst::create(n, 1, SORT());
	assumptions.push_back(p);
	map_net_op[p] = a;

	btor2_logv("adding prop: " << *a << "\n");
	return a;
}


Inst* Btor2Frontend::get_output(Btor2Line& t, InstL& args) {
	if (args.size() != 1) {
		btor2_loge("expecting output condition with 1 argument, got " << args.size());
	}

	return args.front();
}


void Btor2Frontend::get_node(NODE_INFO& info, InstL& args) {
	int64_t id = info.id;
	assert(id > 0);

	bool done = false;
	Inst* node = NULL;
	Btor2Line& t = get_line(id);
//	btor2_log("\t\t(Line " << print_id(info.id) << ")\n");
	SORT sort;
	size_t sz = 0;
	switch(t.tag) {
	case BTOR2_TAG_output: {
		node = get_output(t, args);
		done = true;
		sort = node->get_sort();
	} break;
	case BTOR2_TAG_constraint:
	case BTOR2_TAG_bad: {
		sort.type = bvtype;
		sort.sz = 1;
	} break;
	default:
		sort = get_node_type(t.sort.id);
	}
	sz = sort.sz;
	btor2_logvv("\t\t(Line " << print_id(id) << " has sort " << sort.sort2str() << ")\n");
//	return;

	OpInst::OpType opt = OpInst::Unknown;
	bool cansort = false;
	bool usesz = false;
//	bool sortbool = false;

	switch(t.tag) {
	case BTOR2_TAG_add: {
		assert(args.size() == 2);
		assert(args.front()->get_size() == args.back()->get_size());
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
	} break;
	case BTOR2_TAG_and: {
		assert(args.size() == 2);
		assert(args.front()->get_size() == args.back()->get_size());
		if (sz == 1) {
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
		}
		else {
			opt = OpInst::BitWiseAnd;
			cansort = true;
		}
	} break;
	case BTOR2_TAG_bad: {
		node = get_bad(t, sz, sort, args);
		done = true;
	} break;
	case BTOR2_TAG_concat: {
		assert(args.size() > 1);
		reverse(args.begin(), args.end());
		opt = OpInst::Concat;
	} break;
	case BTOR2_TAG_const: {
		string snum(t.constant);
		node = NumInst::create(snum, sz, 2, sort);
//		{
//			string numstr = NumInst::as(node)->get_mpz()->get_str(2);
//			if (numstr != snum) {
//				btor2_loge("number error: gave " << snum << ", got " << numstr);
//			}
//		}
		constants.insert(node);
		done = true;
	} break;
	case BTOR2_TAG_constraint: {
		node = get_constraint(t, sz, sort, args);
		done = true;
	} break;
	case BTOR2_TAG_constd: {
		string snum(t.constant);
		node = NumInst::create(snum, sz, 10, sort);
//		{
//			string numstr = NumInst::as(node)->get_mpz()->get_str(10);
//			if (numstr != snum) {
//				btor2_loge("number error: gave " << snum << ", got " << numstr);
//			}
//		}
		constants.insert(node);
		done = true;
	} break;
	case BTOR2_TAG_consth: {
		string snum(t.constant);
		node = NumInst::create(snum, sz, 16, sort);
//		{
//			string numstr = NumInst::as(node)->get_mpz()->get_str(16);
//			if (numstr != snum) {
//				btor2_loge("number error: gave " << snum << ", got " << numstr);
//			}
//		}
		constants.insert(node);
		done = true;
	} break;
	case BTOR2_TAG_dec: {
		assert(args.size() == 1);
		Inst* num1 = NumInst::create(1, sz);
		args.push_back(num1);
		assert(args.front()->get_size() == args.back()->get_size());
		opt = OpInst::Sub;
	} break;
	case BTOR2_TAG_eq: {
		assert(args.size() == 2);
		assert(args.front()->get_size() == args.back()->get_size());
		opt = OpInst::Eq;
//		sortbool = true;
	} break;
	case BTOR2_TAG_fair: {
		btor2_loge("unsupported: " << t.name);
	} break;
	case BTOR2_TAG_iff: {
		assert(args.size() == 2);
		assert(args.front()->get_size() == args.back()->get_size());
		assert(args.front()->get_size() == 1);
		opt = OpInst::Eq;
//		sortbool = true;
	} break;
	case BTOR2_TAG_implies: {
		assert(args.size() == 2);
		assert(args.front()->get_size() == args.back()->get_size());
		assert(args.front()->get_size() == 1);

		Inst* arg1 = args.front();
		Inst* arg2 = args.back();
		args.clear();
		args.push_back(OpInst::create(OpInst::LogNot, arg1));
		args.push_back(arg2);
		opt = OpInst::LogOr;
//		sortbool = true;
	} break;
	case BTOR2_TAG_inc: {
		assert(args.size() == 1);
		Inst* num1 = NumInst::create(1, sz);
		args.push_back(num1);
		assert(args.front()->get_size() == args.back()->get_size());
		opt = OpInst::Add;
	} break;
	case BTOR2_TAG_init: {
		node = get_init(t, sz, sort, args);
		done = true;
	} break;
	case BTOR2_TAG_input: {
		node = get_input(t, sz, sort);
		done = true;
	} break;
	case BTOR2_TAG_ite: {
		assert(args.size() == 3);
		assert(args.front()->get_size() == 1);

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
		done = true;
	} break;
	case BTOR2_TAG_justice: {
		btor2_loge("unsupported: " << t.name);
	} break;
	case BTOR2_TAG_mul: {
		assert(args.size() == 2);
		assert(args.front()->get_size() == args.back()->get_size());
		opt = OpInst::Mult;
		cansort = true;
		usesz = true;
	} break;
	case BTOR2_TAG_nand: {
		assert(args.size() == 2);
		assert(args.front()->get_size() == args.back()->get_size());
		if (sz == 1) {
			opt = OpInst::LogNand;
		}
		else {
			opt = OpInst::BitWiseNand;
			cansort = true;
		}
	} break;
	case BTOR2_TAG_neq: {
		assert(args.size() == 2);
		assert(args.front()->get_size() == args.back()->get_size());
		opt = OpInst::NotEq;
//		sortbool = true;
	} break;
	case BTOR2_TAG_neg: {
		assert(args.size() == 1);
		assert(args.front()->get_size() == sz);
		opt = OpInst::Minus;
	} break;
	case BTOR2_TAG_next: {
		node = get_next(t, sz, sort, args);
		done = true;
	} break;
	case BTOR2_TAG_nor: {
		assert(args.size() == 2);
		assert(args.front()->get_size() == args.back()->get_size());
		if (sz == 1) {
			opt = OpInst::LogNor;
		}
		else {
			opt = OpInst::BitWiseNor;
			cansort = true;
		}
	} break;
	case BTOR2_TAG_not: {
		assert(args.size() == 1);
		if (sz == 1) {
			opt = OpInst::LogNot;
		}
		else {
			opt = OpInst::BitWiseNot;
		}
	} break;
	case BTOR2_TAG_one: {
		if (sort.type == bvtype) {
			node = NumInst::create(1, sz);
			done = true;
		}
		else {
			btor2_loge("unsupported: " << t.name);
		}
	} break;
	case BTOR2_TAG_ones: {
		if (sort.type == bvtype) {
			string snum(sz, '1');
			node = NumInst::create(snum, sz, 2);
			done = true;
		}
		else {
			btor2_loge("unsupported: " << t.name);
		}
	} break;
	case BTOR2_TAG_or: {
		assert(args.size() == 2);
		assert(args.front()->get_size() == args.back()->get_size());
		if (sz == 1) {
			opt = OpInst::LogOr;
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
		}
		else {
			opt = OpInst::BitWiseOr;
			cansort = true;
		}
	} break;
	case BTOR2_TAG_output: {
		done = true;
	} break;
	case BTOR2_TAG_read: {
		assert(args.size() == 2);
		assert(args.front()->get_sort_type() == arraytype);
		opt = OpInst::ArraySelect;
		node = OpInst::create(opt, args, sz, true, NULL);
		done = true;
		break;
	} break;
	case BTOR2_TAG_redand: {
		assert(args.size() == 1);
		opt = OpInst::ReductionAnd;
	} break;
	case BTOR2_TAG_redor: {
		assert(args.size() == 1);
		opt = OpInst::ReductionOr;
	} break;
	case BTOR2_TAG_redxor: {
		assert(args.size() == 1);
		opt = OpInst::ReductionXor;
	} break;
	case BTOR2_TAG_rol: {
		assert(args.size() == 2);
		assert(args.front()->get_size() == args.back()->get_size());
		opt = OpInst::RotateL;
	} break;
	case BTOR2_TAG_ror: {
		assert(args.size() == 2);
		assert(args.front()->get_size() == args.back()->get_size());
		opt = OpInst::RotateR;
	} break;
	case BTOR2_TAG_saddo: {
		assert(sort.sz == 1);
		assert(args.size() == 2);
		assert(args.front()->get_size() == args.back()->get_size());
		Inst* arg1 = args.front();
		Inst* arg2 = args.back();
		if (OpInst::as(arg1) && OpInst::as(arg1)->get_op() == OpInst::Minus) {
			swap (arg1, arg2);
		}
		int width = arg1->get_size();
		Inst* sign_arg1 = ExInst::create(arg1, width - 1, width - 1);
		Inst* sign_arg2 = ExInst::create(arg2, width - 1, width - 1);
		Inst* add = OpInst::create(OpInst::Add, arg1, arg2);
		Inst* sign_result = ExInst::create(add, width - 1, width - 1);
		Inst* or1;
		{
			InstL args_tmp;
			args_tmp.push_back(sign_arg1);
			args_tmp.push_back(sign_arg2);
			args_tmp.push_back(OpInst::create(OpInst::LogNot, sign_result));
			or1 = OpInst::create(OpInst::LogAnd, args_tmp);
		}
		Inst* or2;
		{
			InstL args_tmp;
			args_tmp.push_back(OpInst::create(OpInst::LogNot, sign_arg1));
			args_tmp.push_back(OpInst::create(OpInst::LogNot, sign_arg2));
			args_tmp.push_back(sign_result);
			or2 = OpInst::create(OpInst::LogAnd, args_tmp);
		}
		node = OpInst::create(OpInst::LogOr, or1, or2);
		done = true;
//		cout << "node: " << *node << endl;
	} break;
	case BTOR2_TAG_sdiv: {
		assert(args.size() == 2);
		assert(args.front()->get_size() == args.back()->get_size());
		opt = OpInst::SDiv;
		usesz = true;
	} break;
	case BTOR2_TAG_sdivo: {
		assert(sort.sz == 1);
		assert(args.size() == 2);
		assert(args.front()->get_size() == args.back()->get_size());
		Inst* arg1 = args.front();
		Inst* arg2 = args.back();
		int argsz = arg1->get_size();

		string min(argsz, '0');
		min[0] = '1';
		string ones(argsz, '1');
		Inst* v_min = NumInst::create(min, argsz, 2);
		Inst* v_ones = NumInst::create(ones, argsz, 2);

		InstL arg_tmp;
		arg_tmp.push_back(OpInst::create(OpInst::Eq, arg1, v_min));
		arg_tmp.push_back(OpInst::create(OpInst::Eq, arg2, v_ones));

		node = OpInst::create(OpInst::LogAnd, arg_tmp);
		done = true;
//		cout << "node: " << *node << endl;
	} break;
	case BTOR2_TAG_sext: {
		assert(args.size() == 1);
		size_t amount = t.args[1];
		if (amount == 0)
			node = args.front();
		else {
			Inst* num = NumInst::create(amount, amount + args.front()->get_size());
			constants.insert(num);
			args.push_back(num);
			node = OpInst::create(OpInst::Sext, args);
		}
		done = true;
	} break;
	case BTOR2_TAG_sgt: {
		assert(args.size() == 2);
		assert(args.front()->get_size() == args.back()->get_size());
		opt = OpInst::SGr;
	} break;
	case BTOR2_TAG_sgte: {
		assert(args.size() == 2);
		assert(args.front()->get_size() == args.back()->get_size());
		opt = OpInst::SGrEq;
	} break;
	case BTOR2_TAG_slice: {
		assert(args.size() == 1);
		size_t hi = t.args[1];
		size_t lo = t.args[2];
//		cout << "hi: " << hi << " lo: " << lo << endl;
		assert(hi >= lo);
		node = ExInst::create(args.front(), hi, lo);
		done = true;
	} break;
	case BTOR2_TAG_sll: {
		assert(args.size() == 2);
		opt = OpInst::ShiftL;
		usesz = true;
	} break;
	case BTOR2_TAG_slt: {
		assert(args.size() == 2);
		assert(args.front()->get_size() == args.back()->get_size());
		opt = OpInst::SLe;
	} break;
	case BTOR2_TAG_slte: {
		assert(args.size() == 2);
		assert(args.front()->get_size() == args.back()->get_size());
		opt = OpInst::SLeEq;
	} break;
	case BTOR2_TAG_sort: {
		btor2_loge("unsupported: " << t.name);
	} break;
	case BTOR2_TAG_smod: {
		assert(args.size() == 2);
		assert(args.front()->get_sort() == args.back()->get_sort());
		opt = OpInst::SMod;
	} break;
	case BTOR2_TAG_smulo: {
		assert(sort.sz == 1);
		assert(args.size() == 2);
		assert(args.front()->get_size() == args.back()->get_size());
		int argsz = args.front()->get_size();
		node = OpInst::create(OpInst::Mult, args, 2*argsz);
		Inst* sign = ExInst::create(node, argsz - 1, argsz - 1);
		node = ExInst::create(node, node->get_size() - 1, argsz);

		string zeros(argsz, '0');
		string ones(argsz, '1');
		Inst* v_zeros = NumInst::create(zeros, argsz, 2);
		Inst* v_ones = NumInst::create(ones, argsz, 2);

		Inst* ite = OpInst::create(OpInst::Ternary, sign, v_ones, v_zeros);
		node = OpInst::create(OpInst::NotEq, node, ite);
		done = true;
//		cout << "node: " << *node << endl;
	} break;
	case BTOR2_TAG_sra: {
		assert(args.size() == 2);
		opt = OpInst::AShiftR;
		usesz = true;
	} break;
	case BTOR2_TAG_srem: {
		assert(args.size() == 2);
		assert(args.front()->get_sort() == args.back()->get_sort());
		opt = OpInst::SRem;
	} break;
	case BTOR2_TAG_srl: {
		assert(args.size() == 2);
		opt = OpInst::ShiftR;
		usesz = true;
	} break;
	case BTOR2_TAG_ssubo: {
		assert(sort.sz == 1);
		assert(args.size() == 2);
		assert(args.front()->get_size() == args.back()->get_size());
		Inst* arg1 = args.front();
		Inst* arg2 = args.back();
		int width = arg1->get_size();
		Inst* sign_arg1 = ExInst::create(arg1, width - 1, width - 1);
		Inst* sign_arg2 = ExInst::create(arg2, width - 1, width - 1);
		Inst* sub = OpInst::create(OpInst::Sub, arg1, arg2);
		Inst* sign_result = ExInst::create(sub, width - 1, width - 1);
		Inst* or1;
		{
			InstL args_tmp;
			args_tmp.push_back(OpInst::create(OpInst::LogNot, sign_arg1));
			args_tmp.push_back(sign_arg2);
			args_tmp.push_back(sign_result);
			or1 = OpInst::create(OpInst::LogAnd, args_tmp);
		}
		Inst* or2;
		{
			InstL args_tmp;
			args_tmp.push_back(sign_arg1);
			args_tmp.push_back(OpInst::create(OpInst::LogNot, sign_arg2));
			args_tmp.push_back(OpInst::create(OpInst::LogNot, sign_result));
			or2 = OpInst::create(OpInst::LogAnd, args_tmp);
		}
		node = OpInst::create(OpInst::LogOr, or1, or2);
		done = true;
//		cout << "node: " << *node << endl;
	} break;
	case BTOR2_TAG_state: {
		node = get_state(t, sz, sort);
		done = true;
	} break;
	case BTOR2_TAG_sub: {
		assert(args.size() == 2);
		assert(args.front()->get_size() == args.back()->get_size());
		opt = OpInst::Sub;
	} break;
	case BTOR2_TAG_uaddo: {
		assert(sort.sz == 1);
		assert(args.size() == 2);
		assert(args.front()->get_size() == args.back()->get_size());
		Inst* arg1 = args.front();
		Inst* arg2 = args.back();
		if (OpInst::as(arg1) && OpInst::as(arg1)->get_op() == OpInst::Minus) {
			swap (arg1, arg2);
		}
		arg1 = extend(arg1, 0, 1);
		arg2 = extend(arg2, 0, 1);
		node = OpInst::create(OpInst::Add, arg1, arg2);
		node = ExInst::create(node, node->get_size() - 1, node->get_size() - 1);
		done = true;
//		cout << "node: " << *node << endl;
	} break;
	case BTOR2_TAG_udiv: {
		assert(args.size() == 2);
		assert(args.front()->get_size() == args.back()->get_size());
		opt = OpInst::Div;
		usesz = true;
	} break;
	case BTOR2_TAG_uext: {
		assert(args.size() == 1);
		size_t amount = t.args[1];
		if (amount == 0)
			node = args.front();
		else {
			assert(amount > 0);
			Inst* num = NumInst::create(0, amount);
			constants.insert(num);
			args.push_back(num);
			node = OpInst::create(OpInst::Concat, args);

//			Inst* num = NumInst::create(amount, amount + args.front()->get_size());
//			constants.insert(num);
//			args.push_back(num);
//			node = OpInst::create(OpInst::Zext, args);
		}
		done = true;
	} break;
	case BTOR2_TAG_ugt: {
		assert(args.size() == 2);
		assert(args.front()->get_size() == args.back()->get_size());
		opt = OpInst::Gr;
	} break;
	case BTOR2_TAG_ugte: {
		assert(args.size() == 2);
		assert(args.front()->get_size() == args.back()->get_size());
		opt = OpInst::GrEq;
	} break;
	case BTOR2_TAG_ult: {
		assert(args.size() == 2);
		assert(args.front()->get_size() == args.back()->get_size());
		opt = OpInst::Le;
	} break;
	case BTOR2_TAG_ulte: {
		assert(args.size() == 2);
		assert(args.front()->get_size() == args.back()->get_size());
		opt = OpInst::LeEq;
	} break;
	case BTOR2_TAG_umulo: {
		assert(sort.sz == 1);
		assert(args.size() == 2);
		assert(args.front()->get_size() == args.back()->get_size());
		int argsz = args.front()->get_size();
		node = OpInst::create(OpInst::Mult, args, 2*argsz);
		node = ExInst::create(node, node->get_size() - 1, argsz);
		node = OpInst::create(OpInst::NotEq, node, NumInst::create(0, argsz));
		done = true;
//		cout << "node: " << *node << endl;
	} break;
	case BTOR2_TAG_urem: {
		assert(args.size() == 2);
		assert(args.front()->get_sort() == args.back()->get_sort());
		opt = OpInst::Rem;
	} break;
	case BTOR2_TAG_usubo: {
		assert(sort.sz == 1);
		assert(args.size() == 2);
		assert(args.front()->get_size() == args.back()->get_size());
		Inst* arg1 = args.front();
		Inst* arg2 = args.back();
		arg1 = extend(arg1, 0, 1);
		arg2 = extend(arg2, 0, 1);
		node = OpInst::create(OpInst::Sub, arg1, arg2);
		node = ExInst::create(node, node->get_size() - 1, node->get_size() - 1);
		done = true;
//		cout << "node: " << *node << endl;
	} break;
	case BTOR2_TAG_write: {
		assert(args.size() == 3);
		assert(sort.args.size() == 2);
		opt = OpInst::ArrayStore;
		node = OpInst::create(opt, args, sz, true, NULL, sort);
		done = true;
	} break;
	case BTOR2_TAG_xnor: {
		assert(args.size() == 2);
		assert(args.front()->get_size() == args.back()->get_size());
		if (sz == 1) {
			opt = OpInst::LogXNor;
		}
		else {
			opt = OpInst::BitWiseXNor;
			cansort = true;
		}
	} break;
	case BTOR2_TAG_xor: {
		assert(args.size() == 2);
		assert(args.front()->get_size() == args.back()->get_size());
		if (sz == 1) {
			opt = OpInst::LogXor;
		}
		else {
			opt = OpInst::BitWiseXor;
			cansort = true;
		}
	} break;
	case BTOR2_TAG_zero: {
		if (sort.type == bvtype) {
			node = NumInst::create(0, sz);
			done = true;
		}
		else {
			btor2_loge("unsupported: " << t.name);
		}
	} break;
//	case MSAT_TAG_TRUE:/**< the Boolean constant True */
//		assert(sz == 1);
//		node = NumInst::create(1, 1);
//		done = true;
//		break;
//	case MSAT_TAG_FALSE:/**< the Boolean constant False */
//		assert(sz == 1);
//		node = NumInst::create(0, 1);
//		done = true;
//		break;
//	case MSAT_TAG_OR:/**< the OR Boolean connective */
//		assert(sz == 1);
//		assert(args.size() > 1);
//		{
//			InstL newArgs;
//			for (auto& v: args) {
//				OpInst* opv = OpInst::as(v);
//				if (opv && opv->get_op() == OpInst::LogOr) {
//					for (InstL::const_iterator cit = v->get_children()->begin(); cit != v->get_children()->end(); cit++)
//						newArgs.push_back(*cit);
//				}
//				else
//					newArgs.push_back(v);
//			}
//			newArgs.swap(args);
//		}
//		opt = OpInst::LogOr;
////		sortbool = true;
//		break;
//	case MSAT_TAG_NOT:/**< the NOT Boolean connective */
//		assert(sz == 1);
//		assert(args.size() == 1);
//		opt = OpInst::LogNot;
//		break;
//	case MSAT_TAG_IFF:/**< the IFF Boolean connective */
//		assert(sz == 1);
//		assert(args.size() == 2);
//		opt = OpInst::Eq;
////		sortbool = true;
//		break;
//	case MSAT_TAG_EQ:/**< equality */
//		assert(args.size() == 2);
//		assert(args.front()->get_size() == args.back()->get_size());
//		opt = OpInst::Eq;
////		sortbool = true;
//		break;
//	case MSAT_TAG_ITE:/**< term-level if-then-else */
//		assert(args.size() == 3);
//		assert(args.front()->get_size() == 1);
//		{
//			Inst* cond = args.front();
//			args.pop_front();
//			Inst* the = args.front();
//			args.pop_front();
//			Inst* els = args.front();
//			args.pop_front();
//			assert(the->get_size() == els->get_size());
//			assert(the->get_size() == sz);
//
//			if (the == els)
//				node = the;
//			else {
//				if (sz == 1 && the->get_type() == Num && els->get_type() == Num) {
//					if (the == NumInst::create(1, 1)) {
//						assert(els == NumInst::create(0, 1));
//						node = cond;
//					}
//					else {
//						assert(the == NumInst::create(0, 1));
//						assert(els == NumInst::create(1, 1));
//						node = OpInst::create(OpInst::LogNot, cond);
//					}
//				}
//				else {
//					node = OpInst::create(OpInst::Ternary, cond, the, els);
//				}
//			}
//		}
//		done = true;
//		break;
//	case MSAT_TAG_BV_EXTRACT:/**< BV selection */
//		{
//			assert(args.size() == 1);
//			size_t hi = 0;
//			size_t lo = 0;
//			if (msat_term_is_bv_extract(get_env(), t, &hi, &lo)) {
//				node = ExInst::create(args.front(), hi, lo);
//			}
//			else {
//				btor2_loge("unable to get extract node " << name(t));
//			}
//		}
//		done = true;
//		break;
//	case MSAT_TAG_BV_NOT:/**< BV bitwise not */
//		assert(args.size() == 1);
//		assert(args.front()->get_size() == sz);
//		opt = OpInst::BitWiseNot;
//		break;
//	case MSAT_TAG_BV_OR:/**< BV bitwise or */
//		assert(args.size() == 2);
//		assert(args.front()->get_size() == args.back()->get_size());
//		opt = OpInst::BitWiseOr;
//		cansort = true;
//		break;
//	case MSAT_TAG_BV_XOR:/**< BV bitwise xor */
//		assert(args.size() == 2);
//		assert(args.front()->get_size() == args.back()->get_size());
//		opt = OpInst::BitWiseXor;
//		cansort = true;
//		break;
//	case MSAT_TAG_BV_ULT:/**< BV unsigned < */
//		assert(args.size() == 2);
//		assert(args.front()->get_size() == args.back()->get_size());
//		opt = OpInst::Le;
//		break;
//	case MSAT_TAG_BV_SLT:/**< BV signed < */
//		assert(args.size() == 2);
//		assert(args.front()->get_size() == args.back()->get_size());
//		opt = OpInst::SLe;
//		break;
//	case MSAT_TAG_BV_ULE:/**< BV unsigned <= */
//		assert(args.size() == 2);
//		assert(args.front()->get_size() == args.back()->get_size());
//		opt = OpInst::LeEq;
//		break;
//	case MSAT_TAG_BV_SLE:/**< BV signed < */
//		assert(args.size() == 2);
//		assert(args.front()->get_size() == args.back()->get_size());
//		opt = OpInst::SLeEq;
//		break;
//	case MSAT_TAG_BV_COMP:/**< BV bit comparison */
//		btor2_loge("operation with tag " << info.tag << " not supported in node " << name(t));
//		break;
//	case MSAT_TAG_BV_NEG:/**< BV unary minus */
//		assert(args.size() == 1);
//		assert(args.front()->get_size() == sz);
//		opt = OpInst::Minus;
//		break;
//	case MSAT_TAG_BV_SUB:/**< BV subtraction */
//		assert(args.size() == 2);
//		assert(args.front()->get_size() == args.back()->get_size());
//		opt = OpInst::Sub;
//		break;
//	case MSAT_TAG_BV_MUL:/**< BV multiplication */
//		assert(args.size() == 2);
//		assert(args.front()->get_size() == args.back()->get_size());
//		opt = OpInst::Mult;
//		cansort = true;
//		usesz = true;
//		break;
//	case MSAT_TAG_BV_UDIV:/**< BV unsigned division */
//		assert(args.size() == 2);
//		assert(args.front()->get_size() == args.back()->get_size());
//		opt = OpInst::Div;
//		usesz = true;
//		break;
//	case MSAT_TAG_BV_SDIV:/**< BV signed division */
//		assert(args.size() == 2);
//		assert(args.front()->get_size() == args.back()->get_size());
//		opt = OpInst::SDiv;
//		usesz = true;
//		break;
//	case MSAT_TAG_BV_UREM:/**< BV unsigned remainder */
//		assert(args.size() == 2);
//		assert(args.front()->get_size() == args.back()->get_size());
//		opt = OpInst::Mod;
//		usesz = true;
//		break;
//	case MSAT_TAG_BV_SREM:/**< BV signed remainder */
//		assert(args.size() == 2);
//		assert(args.front()->get_size() == args.back()->get_size());
//		opt = OpInst::SMod;
//		usesz = true;
//		break;
//	case MSAT_TAG_BV_LSHL:/**< BV logical left shift */
//		assert(args.size() == 2);
//		opt = OpInst::ShiftL;
//		usesz = true;
//		break;
//	case MSAT_TAG_BV_LSHR:/**< BV logical right shift */
//		assert(args.size() == 2);
//		opt = OpInst::ShiftR;
//		usesz = true;
//		break;
//	case MSAT_TAG_BV_ASHR:/**< BV arithmetic right shift */
//		assert(args.size() == 2);
//		opt = OpInst::AShiftR;
//		usesz = true;
//		break;
//	case MSAT_TAG_BV_ROL:/**< BV rotate left */
//		assert(args.size() == 2);
//		opt = OpInst::RotateL;
//		usesz = true;
//		break;
//	case MSAT_TAG_BV_ROR:/**< BV rotate right */
//		assert(args.size() == 2);
//		opt = OpInst::RotateR;
//		usesz = true;
//		break;
//	case MSAT_TAG_BV_ZEXT:/**< BV zero extension */
//		{
//			assert(args.size() == 1);
//			size_t amount = 0;
//			if (msat_term_is_bv_zext(get_env(), t, &amount)) {
//
//				Inst* num = NumInst::create(0, amount);
//				constants.insert(num);
//				args.push_back(num);
//				node = OpInst::create(OpInst::Concat, args);
//
////				Inst* num = NumInst::create(amount, amount + args.front()->get_size());
////				constants.insert(num);
////				args.push_back(num);
////				node = OpInst::create(OpInst::Zext, args);
//			}
//			else {
//				btor2_loge("unable to get zero extend amount for node " << name(t));
//			}
//		}
//		done = true;
//		break;
//	case MSAT_TAG_BV_SEXT:/**< BV sign extension */
//		{
//			assert(args.size() == 1);
//			size_t amount = 0;
//			if (msat_term_is_bv_sext(get_env(), t, &amount)) {
//				Inst* num = NumInst::create(amount, amount + args.front()->get_size());
//				constants.insert(num);
//				args.push_back(num);
//
//				node = OpInst::create(OpInst::Sext, args);
//			}
//			else {
//				btor2_loge("unable to get sign extend amount for node " << name(t));
//			}
//		}
//		done = true;
//		break;
//	case MSAT_TAG_ARRAY_CONST:/**< Constant array, array = arrayconst (width, value) */
//	{
//		assert(args.size() == 1);
//		assert(sort.args.size() == 2);
//		unsigned width = sort.args.front().sz;
//		assert(width > 0);
//		Inst* init_val = args.front();
//		assert(init_val->get_type() == Num);
//		mpz_class* value = NumInst::as(init_val)->get_mpz();
//		args.clear();
//
//		args.push_back(NumInst::create(width, 32));
//		args.push_back(NumInst::create(*value, sz));
//		opt = OpInst::ArrayConst;
//		node = OpInst::create(opt, args, sz, true, NULL, sort);
//		done = true;
//	}
//		break;
//	case MSAT_TAG_ARRAY_READ:/**< Array read/select operation, value = arrayselect(array, addr)*/
//		assert(args.size() == 2);
//		opt = OpInst::ArraySelect;
//		node = OpInst::create(opt, args, sz, true, NULL);
//		done = true;
//		break;
//	case MSAT_TAG_ARRAY_WRITE:/**< Array write/store operation, array = arraystore (array, addr, value) */
//	{
//		assert(args.size() == 3);
//		assert(sort.args.size() == 2);
//		unsigned width = sort.args.front().sz;
//		opt = OpInst::ArrayStore;
//		node = OpInst::create(opt, args, sz, true, NULL, sort);
//		done = true;
//	}
//		break;
//	case MSAT_TAG_PLUS:/**< arithmetic addition */
//		assert(args.size() == 2);
//		assert(args.front()->get_sort() == args.back()->get_sort());
//		{
//			bool doswap = false;
//			Inst* arg1 = args.front();
//			if (OpInst::as(arg1) && OpInst::as(arg1)->get_op() == OpInst::IntMinus)
//				doswap = true;
//			else if (NumInst::as(arg1) && NumInst::as(arg1)->get_num() < 0)
//				doswap = true;
//			if (doswap) {
//				Inst* arg2 = args.back();
//				args.clear();
//				swap (arg1, arg2);
//				args.push_back(arg1);
//				args.push_back(arg2);
//			}
//
//			Inst* arg2 = args.back();
//			if (OpInst::as(arg2) && OpInst::as(arg2)->get_op() == OpInst::IntMinus) {
//				args.pop_back();
//				args.push_back(arg2->get_children()->front());
//				opt = OpInst::IntSub;
//			}
//			else if (NumInst::as(arg2) && NumInst::as(arg2)->get_num() < 0) {
//				args.pop_back();
//				string snum = NumInst::as(arg2)->get_mpz()->get_str(10);
//				assert (snum[0] == '-');
//				snum = snum.substr(1);
//				Inst* new_arg2 = NumInst::create(snum, arg2->get_size(), 10, arg2->get_sort());
//				args.push_back(new_arg2);
//				opt = OpInst::IntSub;
//			}
//			else {
//				opt = OpInst::IntAdd;
//				cansort = true;
//			}
//		}
//		break;
//	case MSAT_TAG_TIMES:/**< arithmetic multiplication */
//		assert(args.size() == 2);
//		assert(args.front()->get_sort() == args.back()->get_sort());
//		{
//			Inst* arg1 = args.front();
//			if (NumInst::as(arg1) && NumInst::as(arg1)->get_num() < 0) {
//				Inst* arg2 = args.back();
//				args.clear();
//				swap (arg1, arg2);
//				args.push_back(arg1);
//				args.push_back(arg2);
//			}
//			Inst* arg2 = args.back();
//			if (NumInst::as(arg2) && NumInst::as(arg2)->get_num() == -1) {
//				args.pop_back();
//				opt = OpInst::IntMinus;
//			}
//			else {
//				opt = OpInst::IntMult;
//				cansort = true;
//			}
//		}
//		break;
//	case MSAT_TAG_DIVIDE:/**< arithmetic division */
//		assert(args.size() == 2);
//		assert(args.front()->get_sort() == args.back()->get_sort());
//		opt = OpInst::IntDiv;
//		break;
//	case MSAT_TAG_FLOOR:/**< floor function */
//		assert(args.size() == 1);
//		assert(args.front()->get_sort_type() == inttype);
//		opt = OpInst::IntFloor;
//		break;
//	case MSAT_TAG_LEQ:/**< arithmetic <= */
//		assert(args.size() == 2);
//		assert(args.front()->get_sort() == args.back()->get_sort());
//		opt = OpInst::IntLeEq;
//		break;
//	case MSAT_TAG_INT_MOD_CONGR:/**< integer modular congruence */
//		assert(args.size() == 2);
//		assert(args.front()->get_sort() == args.back()->get_sort());
//		opt = OpInst::IntMod;
//		btor2_loge("found integer modulo congruence for node " << name(t));
//		break;
//	case MSAT_TAG_FP_EQ:/**< FP IEEE equality */
//	case MSAT_TAG_FP_LT:/**< FP < */
//	case MSAT_TAG_FP_LE:/**< FP <= */
//	case MSAT_TAG_FP_NEG:/**< FP unary minus */
//	case MSAT_TAG_FP_ADD:/**< FP addition */
//	case MSAT_TAG_FP_SUB:/**< FP subtraction */
//	case MSAT_TAG_FP_MUL:/**< FP multiplication */
//	case MSAT_TAG_FP_DIV:/**< FP division */
//	case MSAT_TAG_FP_SQRT:/**< FP square root */
//	case MSAT_TAG_FP_ABS:/**< FP absolute value */
//	case MSAT_TAG_FP_MIN:/**< FP min */
//	case MSAT_TAG_FP_MAX:/**< FP max */
//	case MSAT_TAG_FP_CAST:/**< FP format conversion */
//	case MSAT_TAG_FP_ROUND_TO_INT:/**< FP round to integer */
//	case MSAT_TAG_FP_FROM_SBV:/**< FP conversion from a signed BV */
//	case MSAT_TAG_FP_FROM_UBV:/**< FP conversion from an unsigned BV */
//	case MSAT_TAG_FP_TO_BV:/**< FP conversion to BV */
//	case MSAT_TAG_FP_AS_IEEEBV:/**< FP as IEEE BV (access to the bits) */
//	case MSAT_TAG_FP_ISNAN:/**< FP check for NaN */
//	case MSAT_TAG_FP_ISINF:/**< FP check for infinity */
//	case MSAT_TAG_FP_ISZERO:/**< FP check for zero */
//	case MSAT_TAG_FP_ISSUBNORMAL:/**< FP check for subnormal */
//	case MSAT_TAG_FP_ISNORMAL:/**< FP check for normal */
//	case MSAT_TAG_FP_ISNEG:/**< FP check for negative */
//	case MSAT_TAG_FP_ISPOS:/**< FP check for positive */
//	case MSAT_TAG_FP_FROM_IEEEBV:/**< FP conversion from IEEE BV */
//		btor2_loge("operation with tag " << info.tag << " not supported in node " << name(t));
//		break;
//	case MSAT_TAG_INT_FROM_UBV:/**< Unsigned BV -> INT conversion */
//	case MSAT_TAG_INT_FROM_SBV:/**< Signed BV -> INT conversion */
//	case MSAT_TAG_INT_TO_BV:/**< INT -> BV conversion */
//		btor2_loge("operation with tag " << info.tag << " not supported in node " << name(t));
//		break;
	default:
		btor2_loge("unrecognized BTOR2 tag " << t.tag << " for node " << name(t));
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
		btor2_loge("processing failed for node " << name(t));
	}
	if (node->get_size() != sz) {
		btor2_loge("output size different for " << *node << " i.e. " << name(t) << " (expected: " << sz << ", got " << node->get_size());
	}

	info.node = node;
}


string Btor2Frontend::gate_name(Btor2Line& t) {
	string s = to_string(t.id);
	s = BTOR2_NAME_PREFIX + s;
	return s;
}


void Btor2Frontend::sanitize_name(string& n) {
	n.erase(remove(n.begin(), n.end(), '\"'), n.end());
	replace(n.begin(), n.end(), '#', '.');

	assert(n.length() > 0);
}


Inst* Btor2Frontend::extend(Inst* v, int value, int amount) {
	Inst* num = NumInst::create(value, amount);
	InstL args_tmp;
	args_tmp.push_back(v);
	args_tmp.push_back(num);
	return OpInst::create(OpInst::Concat, args_tmp);
}


}




