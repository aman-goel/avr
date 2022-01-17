/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


/*
 * wif_frontend.cpp
 *
 *  Created on: May 15, 2019
 *      Author: amangoel
 */


#include "wif_frontend.h"



namespace _wif {


void WifFrontend::help() {
	//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
	wif_log("\n");
	wif_log("    read_wif [filename]\n");
	wif_log("\n");
	wif_log("Reads the design in a WIF file. \n");
	wif_log("\t(WIF format is JasperGold Word-level Interface format)\n");
	wif_log("\n");
}

void WifFrontend::execute() {
	traverse_system();
//	print_system();
}

void WifFrontend::print_system() {
	wif_log('\n');

	wif_log("(states)" << endl);
	for (auto& v: states) {
		wif_log('\t' << *v.second << " of type " << v.second->get_sort().sort2str() << endl);
	}
	wif_log('\n');

	wif_log("(next states)" << endl);
	for (auto& v: next_states) {
		wif_log('\t' << *v << " of type " << v->get_sort().sort2str() << endl);
	}
	wif_log('\n');

	wif_log("(initial states)" << endl);
	for (auto& v: map_init) {
		wif_log('\t' << *v.first << " = " << *v.second << endl);
	}
	wif_log('\n');

	wif_log("(transition relation)" << endl);
	for (auto& v: map_net_op) {
		wif_log('\t' << *v.first << " = " << *v.second << endl);
	}
	wif_log('\n');

	wif_log("(properties)" << endl);
	for (auto& v: properties) {
		wif_log('\t' << *v << endl);
	}
	wif_log('\n');

	wif_log("(assumptions)" << endl);
	for (auto& v: assumptions) {
		wif_log('\t' << *v << " = " << *map_net_op[v] << endl);
	}
	wif_log('\n');
}

void WifFrontend::traverse_system() {
	list < pair < string, Inst* > > instP, outP;
	InstL instA;

//	for (auto& r: roots)
//		cout << "(root) " << r->print() << endl;
//	for (auto& n: nodes) {
//		cout << "(node) " << n.print() << endl;
//		for (auto& arg: n.args)
//			cout << "\t\t" << arg->print() << endl;
//	}

	for (auto& p: safetychecks) {
		instP.push_back(make_pair(p.first, traverse_node(*(p.second))));
	}

	for (auto& p: assumes)
		instA.push_back(traverse_node(*p));
	add_assumes(instA);

	process_delay();

	add_props(instP, outP);
	if (Config::g_single_property) {
		bool found = false;
		pair< string, Inst* > singleP;
		for (auto& p: outP) {
			if (endsWith(p.first, config->get_arg(SELECT_PROPERTY))) {
				if (found) {
					wif_logw("multiple checks matching with selected property " << config->get_arg(SELECT_PROPERTY));
					wif_logw("ignoring matched check " << p.first << " as property");
				}
				else {
					wif_log("\t(selecting matched check " << p.first << " as property)\n");
					found = true;
					singleP = p;
				}
			}
		}
		if (!found) {
			wif_loge("no check matches with property name " << config->get_arg(SELECT_PROPERTY));
//			wif_logw("no check matches with property name " << config->get_arg(SELECT_PROPERTY));
//			wif_logw("selecting all properties");
		}
		else {
			prop_ve = singleP.second;
		}
	}
}

Inst* WifFrontend::traverse_node(WifNode& t) {
	map< WifNode, Inst* >::iterator mit = processed.find(t);
	if (mit != processed.end()) {
		return (*mit).second;
	}

//	wif_log("traversing: " << t.print() << "\n");

	InstL args;
	for (auto& arg : t.args) {
		assert(arg);
		// don't process delay args yet
		if (t.type != wDelay)
			args.push_back(traverse_node(*arg));
	}

	Inst* inst = process_node(t, args);
	processed[t] = inst;
	return inst;
}

Inst* WifFrontend::process_node(WifNode& t, InstL& args) {
	string name = gate_name(t);
	Inst* inst;

	wif_logvv("processing: " << t.print() << " i.e. " << name << "\n");
	inst = get_node(t, args);
	gate_names[inst] = name;

	wif_logvv("processed: " << t.print() << " to " << *inst << "\n");
	assert(inst);
	return inst;
}

SORT WifFrontend::get_node_type(WifNode& t) {
	SORT sort;
	size_t sz = 0;

	assert(t.size > 0);
	sort.type = bvtype;
	sort.sz = t.size;

	return sort;
}

Inst* WifFrontend::get_node(WifNode& t, InstL& args) {
	Inst* node = NULL;
	size_t sz = 0;
	SORT sort = get_node_type(t);
	sz = sort.sz;

	OpInst::OpType opt = OpInst::Unknown;
	bool done = false;
	bool cansort = false;
	bool usesz = false;

	switch(t.type) {
	case wConst:
		node = NumInst::create(t.attr, sz, 10, sort);
		{
			string numstr = NumInst::as(node)->get_mpz()->get_str(10);
			if (numstr != t.attr) {
				wif_loge("number error: gave " << t.attr << ", got " << numstr);
			}
		}
		constants.insert(node);
		done = true;
		break;
	case wVar:
		assert(args.size() == 0);
		node = process_sig(t, args, sz, sort);
		done = true;
		break;
	case wDelay:
		assert(args.size() == 0);
		node = process_sig(t, args, sz, sort);
		done = true;
		break;
	case wIte:
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

			if (the == els || (cond == NumInst::create(1, 1)))
				node = the;
			else if (cond == NumInst::create(0, 1))
				node = els;
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
	case wNot:
		assert(args.size() == 1);
		if (sz == 1)
			opt = OpInst::LogNot;
		else {
			assert(args.front()->get_size() == sz);
			opt = OpInst::BitWiseNot;
		}
		break;
	case wAnd:
		assert(args.size() > 1);
		if (sz == 1) {
			opt = OpInst::LogAnd;
//			InstL newArgs;
//			for (auto& v: args) {
//				OpInst* opv = OpInst::as(v);
//				if (opv && opv->get_op() == OpInst::LogAnd) {
//					for (InstL::const_iterator cit = v->get_children()->begin(); cit != v->get_children()->end(); cit++)
//						newArgs.push_back(*cit);
//				}
//				else
//					newArgs.push_back(v);
//			}
//			newArgs.swap(args);
		}
		else {
			assert(args.size() == 2);
			assert(args.front()->get_size() == args.back()->get_size());
			opt = OpInst::BitWiseAnd;
			cansort = true;
		}
		break;
	case wAdd:
		assert(args.size() == 2);
		assert(args.front()->get_size() == args.back()->get_size());
		opt = OpInst::Add;
		cansort = true;
		break;
	case wSub:
		assert(args.size() == 2);
		assert(args.front()->get_size() == args.back()->get_size());
		opt = OpInst::Sub;
		break;
	case wMul:
		assert(args.size() == 2);
		assert(args.front()->get_size() == args.back()->get_size());
		opt = OpInst::Mult;
		cansort = true;
		usesz = true;
		break;
	case wDiv:
		assert(args.size() == 2);
		assert(args.front()->get_size() == args.back()->get_size());
		opt = OpInst::Div;
		usesz = true;
		break;
	case wSdiv:
		assert(args.size() == 2);
		assert(args.front()->get_size() == args.back()->get_size());
		opt = OpInst::SDiv;
		usesz = true;
		break;
	case wMod:
		assert(args.size() == 2);
		assert(args.front()->get_size() == args.back()->get_size());
		opt = OpInst::Rem;
		usesz = true;
		break;
	case wSmod:
		assert(args.size() == 2);
		assert(args.front()->get_size() == args.back()->get_size());
		opt = OpInst::SMod;
		usesz = true;
		break;
	case wSh:
	case wSsh:
		wif_loge("unsupported WIF op " << wifop_str[t.type] << " for node " << t.name);
		break;
	case wExt:
		{
			assert(args.size() == 1);
			Inst* arg = args.back();

			int finalsz = sz;
			int amount = finalsz - arg->get_size();
			if (amount == 0)
				node = arg;
			else {
				assert(amount > 0);

				Inst* num = NumInst::create(0, amount);
				constants.insert(num);
				args.push_back(num);
				node = OpInst::create(OpInst::Concat, args);

//				Inst* num = NumInst::create(amount, finalsz);
//				constants.insert(num);
//				args.push_back(num);
//
//				node = OpInst::create(OpInst::Zext, args);
			}
		}
		done = true;
		break;
	case wSext:
		{
			assert(args.size() == 1);
			Inst* arg = args.back();

			int finalsz = sz;
			int amount = finalsz - arg->get_size();
			if (amount == 0)
				node = arg;
			else {
				assert(amount > 0);

				Inst* sign = ExInst::create(arg, (arg->get_size() - 1), (arg->get_size() - 1));
				for (int i = 0; i < amount; i++)
					args.push_back(sign);
				node = OpInst::create(OpInst::Concat, args);

//				Inst* num = NumInst::create(0, finalsz);
//				constants.insert(num);
//				args.push_back(num);
//				node = OpInst::create(OpInst::Sext, args);
			}
		}
		done = true;
		break;
	case wBfe:
		{
			assert(args.size() == 1);
			Inst* exp = args.front();
			int lo = stoi(t.attr);
			assert(lo >= 0);
			node = ExInst::create(exp, lo + (sz - 1), lo);
		}
		done = true;
		break;
	case wCat:
		assert(args.size() > 1);
		reverse(args.begin(), args.end());
		opt = OpInst::Concat;
		break;
	case wSelect:
	case wUpdate:
		wif_loge("unsupported WIF op " << wifop_str[t.type] << " for node " << t.name);
		break;
	case wEq:
		assert(args.size() == 2);
		assert(args.front()->get_size() == args.back()->get_size());
		opt = OpInst::Eq;
		break;
	case wLe:
		assert(args.size() == 2);
		assert(args.front()->get_size() == args.back()->get_size());
		opt = OpInst::LeEq;
		break;
	case wSle:
		assert(args.size() == 2);
		assert(args.front()->get_size() == args.back()->get_size());
		opt = OpInst::SLeEq;
		break;
	case wLt:
		assert(args.size() == 2);
		assert(args.front()->get_size() == args.back()->get_size());
		opt = OpInst::Le;
		break;
	case wSlt:
		assert(args.size() == 2);
		assert(args.front()->get_size() == args.back()->get_size());
		opt = OpInst::SLe;
		break;
	case wShl:
		assert(args.size() == 2);
		opt = OpInst::ShiftL;
		usesz = true;
		break;
	case wShr:
		assert(args.size() == 2);
		opt = OpInst::ShiftR;
		usesz = true;
		break;
	case wSshr:
		assert(args.size() == 2);
		opt = OpInst::AShiftR;
		usesz = true;
		break;
	case wVec:
		wif_loge("unsupported WIF op " << wifop_str[t.type] << " for node " << t.name);
		break;
	case wPin:
		{
			assert(args.size() == 2);
			Inst* exp = args.front();
			args.pop_front();

			Inst* lsb = args.front();
			NumInst* nlsb = NumInst::as(lsb);

			if (nlsb) {
				int lo = nlsb->get_num();
				assert(lo >= 0);

				node = ExInst::create(exp, lo, lo);
			}
			else {
				wif_loge("unable to get extract node " << t.name);
			}
		}
		done = true;
		break;
	case wLut:
		wif_loge("unsupported WIF op " << wifop_str[t.type] << " for node " << t.name);
		break;
	case wRange:
		assert(args.size() == 3);
		{
			Inst* m = args.front();
			args.pop_front();
			Inst* l = args.front();
			args.pop_front();
			Inst* r = args.front();
			args.pop_front();

			assert(m->get_size() == l->get_size());
			assert(m->get_size() == r->get_size());

			InstL newArgs;
			newArgs.push_back(OpInst::create(OpInst::LeEq, l, m));
			newArgs.push_back(OpInst::create(OpInst::LeEq, m, r));

			node = OpInst::create(OpInst::LogAnd, newArgs);
		}
		done = true;
		break;
	case wSigned:
	case wUnsigned:
	case wDummy:
	case wOpMax:
		wif_loge("unsupported WIF op " << wifop_str[t.type] << " for node " << t.name);
		break;
	default:
		wif_loge("unrecognized WIF op " << wifop_str[t.type] << " for node " << t.name);
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
		wif_loge("processing failed for node " << t.name);
	}
	if (node->get_size() != sz) {
		wif_loge("output size different for " << *node << " (expected: " << sz << ", got " << node->get_size());
	}

	return node;
}

Inst* WifFrontend::process_sig(WifNode& t, InstL& args, int sz, SORT sort) {
	Inst* node = NULL;
	string type = "?";
	if (t.type == wDelay) {
		type = "reg";
		string pre = gate_name(t);
		node = SigInst::create(pre, sz, sort);
		states[pre] = node;
		delay_nodes.insert(t);
	}
	else {
		type = "inp";
		assert (t.type == wVar);
		string n = gate_name(t);
		node = SigInst::create(n, sz, sort);
		inputs.insert(node);
	}

	SigInst* sig = SigInst::as(node);
	assert(sig);

	wif_logv("adding sig: " << *node << " of type " << type << " " << node->get_sort().sort2str() << endl);
	return node;
}

void WifFrontend::process_delay() {
	for (auto& t: delay_nodes) {
		assert (t.args.size() == 2);
		map< WifNode, Inst* >::iterator mit = processed.find(t);
		assert (mit != processed.end());
		Inst* node = (*mit).second;

		WifNode* ti = t.args.front();
		Inst* initR = traverse_node(*ti);
		if (initR->get_type() != Num) {
			wif_logwv("detected complex initial condition: " << *node << " = " << *initR);
		}
		map_init[node] = initR;
		wif_logv("adding init: [" << *node << "] = " << *initR << "\n");

		string next = SigInst::as(node)->get_name() + NEXT_SUFFIX;
		Inst* nodeNext = SigInst::create(next, node->get_size(), node->get_sort());
		next_states.push_back(nodeNext);
		assert (state_next2pre.find(nodeNext) == state_next2pre.end());
		state_next2pre[nodeNext] = node;

		WifNode* tr = t.args.back();
		Inst* transR = traverse_node(*tr);
		map_net_op[nodeNext] = transR;
		wif_logv("adding trans: " << *nodeNext << " = " << *transR << "\n");

//		if (transR->get_type() == Op && OpInst::as(transR)->get_op() == OpInst::Ternary) {
//			InstL::const_iterator cit = transR->get_children()->begin();
//			cit++;
//			map_net_op[nodeNext] = (*cit);
//		}
	}
}

string WifFrontend::gate_name(WifNode& t) {
	if (t.name != "")
		return t.name;
	else {
		string s = to_string(t.id);
		s = WIF_NAME_PREFIX + s;
		return s;
	}
}

void WifFrontend::add_props(list < pair < string, Inst* > >& instP, list < pair < string, Inst* > >& outP) {
	wif_logvv("properties: \n");
	for (auto& p: instP) {
		wif_logvv("\t" << p.first << ": " << *p.second << "\n");
	}
	if (instP.empty()) {
		wif_loge("no property specified");
	}

	for (auto& rhs: instP) {
		string name = rhs.first;
		if (name == "")
			name = WIF_NAME_PREFIX + to_string(properties.size());
		Inst* p = SigInst::create(name, 1, SORT());
		properties.push_back(p);
		map_net_op[p] = rhs.second;
		outP.push_back(make_pair(rhs.first, p));
	}

	if (instP.size() == 1) {
		Inst* prop = instP.front().second;
		NumInst* np = NumInst::as(prop);
		if (np) {
			wif_logw("property trivially equals " << *np);
		}
	}
}

void WifFrontend::add_assumes(InstL& instA) {
	for (auto& rhs: instA) {
		NumInst* np = NumInst::as(rhs);
		if (np) {
			if (np == NumInst::create(1, 1))
				continue;
			else {
				wif_loge("assumption equals " << *np);
			}
		}

		wif_logv("\t(adding assumption: " << *rhs << ")\n");
		string name = "assume_" + to_string(assumptions.size());
		Inst* p = SigInst::create(name, 1, SORT());
		assumptions.push_back(p);
		map_net_op[p] = rhs;
	}
}

}

