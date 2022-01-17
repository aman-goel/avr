/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


/*
 * sal_frontend.cpp
 *
 *  Created on: Sep 4, 2017
 *      Author: rock
 */

#include <sal_frontend.h>
#include <iostream>

using namespace std;

namespace sal
{

const string SalFrontend::bv("bv");
const string SalFrontend::next("next.");
CellTypes SalFrontend::cell_factory;

void SalFrontend::help()
{
	//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
	sal_logh("\n");
	sal_logh("    read_sally [filename]\n");
	sal_logh("\n");
	sal_logh("Reads the design from a '.mcmt' file. (.mcmt is a text representation\n");
	sal_logh("of a sequential design in averroes/euforia's internal format.)\n");
	sal_logh("\n");
}

void SalFrontend::execute()
{
	sal_log("Executing Sally frontend.\n");
	sal_log("Input filename: " << filename << endl);

	process_design();
	print_design();
	post_process();
}

/**
 * Function for post processing the design
 */
void SalFrontend::post_process()
{
	assert(constants.empty());
	assert(states.empty());
	assert(inputs.empty());
	assert(map_init.empty());
	assert(properties.empty());

	for (auto& c: sal_constants)
		constants.insert(c.second);
	for (auto& c: sal_states)
		states.insert(c);
	for (auto& c: sal_inputs)
		inputs.insert(c.second);
	for (auto& c: sal_gates)
		gate_names.insert(make_pair(c.second, c.first));

	for (auto& c: sal_initial)
		map_init.insert(c);

	for (auto& c: sal_transition)
		next_states.push_back(c.first);

	int i = 0;
	for (auto& c: sal_property)
	{
		properties.push_back(c);
		i++;
	}

}

/**
 * Function for printing design equations
 */
void SalFrontend::print_design()
{
	sal_logp("constants:" << endl);
	for (auto& c: sal_constants)
		sal_logp("\t" << *c.second << endl);

	sal_logp("states:" << endl);
	for (auto& c: sal_states)
		sal_logp("\t" << *c.second << endl);

	sal_logp("inputs:" << endl);
	for (auto& c: sal_inputs)
		sal_logp("\t" << *c.second << endl);

	sal_logp("initial:" << endl);
	for (auto& c: sal_initial)
		sal_logp("\t" << *c.first << " = " << *c.second << endl);

	sal_logp("next:" << endl);
	for (auto& c: sal_transition)
		sal_logp("\t" << *c.first << " = " << *c.second << endl);

	sal_logp("property:" << endl);
	for (auto& c: sal_property)
		sal_logp("\t" << *c << endl);

	sal_logp("function blocks:" << endl);
	for (auto& c: map_net_op)
		sal_logp("\t" << *c.first << " = " << *c.second << endl);

	sal_logp(endl);
}

/**
 * Function for processing design to avr data structures
 */
void SalFrontend::process_design()
{
    sal_log("constant:" << endl);
    for (auto& binding : getConstant()) {
    	process_constant(binding);
    }

    sal_log("state:" << endl);
    for (auto& binding : getState()) {
    	process_state(binding);
    }

    sal_log("input:" << endl);
    for (auto& binding : getInput()) {
    	process_input(binding);
    }

    sal_log("gates:" << endl);
    for (auto& binding : getGates()) {
    	process_gate(binding);
    }

    sal_log("next:" << endl);
    for (auto& binding : getNext()) {
    	process_next(binding);
    }

    sal_log("init:" << endl);
    for (auto& binding : getInitial()) {
    	process_init(binding);
    }

    sal_log("property: " << endl);
    for (auto& binding : getProperty()) {
    	process_property(binding);
    }
	sal_log(endl);
}

/**
 * Function for processing a constant to avr data structures
 */
void SalFrontend::process_constant(const sexpr& s)
{
	sexpr::iterator it = s.begin();
	it++;

	auto word = *it++;
	auto name = word.copyVal();
	force_new(name, s);

	word = *it++;
	int num, sz;
	{
		auto sit = word.begin();

		auto token = *sit++;
		auto key = token.copyVal();
		assert(get_key(key) == $underscore);

		token = *sit++;
		key = token.copyVal();
		string numStr = key.substr(bv.size(), key.size() - bv.size());
		num = stoi(numStr);

		token = *sit++;
		string szStr = token.copyVal();
		sz = stoi(szStr);

		assert(sit == word.end());
	}
	assert(it == s.end());

	Inst* tve = NumInst::create(num, sz);
	sal_constants[name] = tve;

	sal_nodes[name] = tve;
	sal_log ("  constant: " << name << " " << *tve << endl);
}

/**
 * Function for processing a state variable to avr data structures
 */
void SalFrontend::process_state(const sexpr& s)
{
	sexpr::iterator it = s.begin();

	auto word = *it++;
	auto name = word.copyVal();
	force_new(name, s);

	int sz = read_size(*it++);
	assert(it == s.end());

	Inst* tve = SigInst::create(name, sz);
	sal_states[name] = tve;

	sal_nodes[name] = tve;
	sal_log ("  state: " << name << " " << *tve << endl);
}

/**
 * Function for processing an input variable to avr data structures
 */
void SalFrontend::process_input(const sexpr& s)
{
	sexpr::iterator it = s.begin();

	auto word = *it++;
	auto name = word.copyVal();
	force_new(name, s);

	int sz = read_size(*it++);
	assert(it == s.end());

	Inst* tve = SigInst::create(name, sz);
	sal_inputs[name] = tve;

	sal_nodes[name] = tve;
	sal_log ("  input: " << name << " " << *tve << endl);
}

/**
 * Function for processing a gate expression to avr data structures
 */
void SalFrontend::process_gate(const sexpr& s)
{
	sexpr::iterator it = s.begin();

	auto word = *it++;
	auto name = word.copyVal();
	force_new(name, s);

	word = *it++;
	int sz = read_size(word);

	word = *it++;
	Inst* rhs = process_expression(word, sz);

	Inst* wire = SigInst::create(name, sz);
	sal_gates[name] = rhs;

	sal_nodes[name] = wire;
	map_net_op[wire] = rhs;
	sal_log ("  gate: " << *wire << " " << *rhs << endl);
}

/**
 * Function for processing a next state expression to avr data structures
 */
void SalFrontend::process_next(const sexpr& s)
{
	sexpr::iterator it = s.begin();

	auto word = *it++;
	auto key = word.copyVal();
	assert(get_key(key) == $eq);

	word = *it++;
	auto name = word.copyVal();
	force_new(name, s);

	string namePre = name.substr(next.size(), name.size() - next.size());

	auto preIt = sal_states.find(namePre);
	assert(preIt != sal_states.end());
	int sz = (*preIt).second->get_size();
	string nameNext = namePre + NEXT_SUFFIX;

	Inst* lhs = SigInst::create(nameNext, sz);

	word = *it++;
	Inst* rhs = process_expression(word, sz);

//	Inst* tve = OpInst::create(OpInst::Eq, lhs, rhs);
	sal_transition.insert(make_pair(lhs, rhs));

	map_net_op[lhs] = rhs;
	sal_log ("  next: " << *tve << endl);
}

/**
 * Function for processing an init expression to avr data structures
 */
void SalFrontend::process_init(const sexpr& s)
{
	Inst* tve = process_expression(s, 1);

	SigInst* sig = SigInst::as(tve);
	if (sig)
		sal_initial.insert(make_pair(sig, NumInst::create(1, 1)));
	else
	{
		OpInst* op = OpInst::as(tve);
		if (op)
		{
			if (op->get_op() == OpInst::LogNot)
			{
				Inst* sig = op->get_children()->front();
				assert(sig->get_type() == Sig);
				sal_initial.insert(make_pair(sig, NumInst::create(0, 1)));
			}
			else if (op->get_op() == OpInst::Eq)
			{
				Inst* sig = op->get_children()->front();
				Inst* num = op->get_children()->back();
				if (sig->get_type() != Sig)
					swap(sig, num);
				assert(sig->get_type() == Sig);
				assert(num->get_type() == Num);
				sal_initial.insert(make_pair(sig, num));
			}
			else
			{
				sal_loge("Error: in initial_states definition: " << *tve << " \texpected assignment of a constant value" << endl);
				assert(0);
			}
		}
		else
		{
			sal_loge("Error: in initial_states definition: " << *tve << " \texpected assignment of a constant value" << endl);
			assert(0);
		}
	}

	sal_log ("  initial: " << *tve << endl);
}

/**
 * Function for processing property expression to avr data structures
 */
void SalFrontend::process_property(const sexpr& s)
{
	Inst* tve = process_expression(s, 1);

	string propName;
	if (sal_property.empty())
		propName = config->get_arg(PROP_SIG_ARG);
	else
		propName = config->get_arg(PROP_SIG_ARG) + to_string(sal_property.size());

	Inst* wire = SigInst::create(propName, 1);
	sal_property.push_back(wire);

	map_net_op[wire] = tve;
	sal_log ("  property: " << *wire << ": " << *tve << endl);
}


Inst* SalFrontend::process_expression(const sexpr& s, int outSz)
{
	Inst* out;

	if (s.isValue())
	{
		auto valStr = s.copyVal();
		map<string, Inst*>::iterator mit = sal_nodes.find(valStr);
		if (mit == sal_nodes.end())
		{
			sal_loge("Error: in " << s.asString() << " \texpected " << valStr << " already defined by now" << endl);
			assert(0);
		}
		out = (*mit).second;

		if ((outSz != ANY_NUM) && (out->get_size() != outSz))
		{
			sal_loge("Error: in " << s.asString() << "\texpected operand of size " << outSz << ", operand " << valStr << " is of size " << out->get_size() << endl);
			assert(0);
		}

		return out;
	}
	assert(s.isList());

	sexpr::iterator it = s.begin();

	auto word = *it++;
	auto opStr = word.copyVal();
	CellType cell = cell_factory.get_sal_op(opStr);
	OpInst::OpType op = cell.get_op();

	vector<sexpr> inputExpr;
	while (it != s.end())
	{
		auto inpExpr = *it++;
		inputExpr.push_back(inpExpr);
	}
	int numInp = cell.get_num_input();
	if (numInp != ANY_NUM)
	{
		if (inputExpr.size() != numInp)
		{
			sal_loge("Error: in " << s.asString() << "\texpected " << numInp << " operands for " << opStr << ", got " << inputExpr.size() << endl);
			assert(0);
		}
	}

	int inpSz = get_input_size(cell, outSz);

	list<Inst*> inputs;
	int sumSz = 0;
	for (auto& inp: inputExpr)
	{
		Inst* input;

		if ((sumSz == 0) && (op == OpInst::Ternary))
			input = process_expression(inp, 1);
		else
			input = process_expression(inp, inpSz);

		if (inp.isList())
		{
			sal_loge("Error: in " << s.asString() << "\tnested expressions unsupported (currently)" << endl);
			assert(0);
		}

		inputs.push_back(input);
		sumSz += input->get_size();
	}
	out = OpInst::create(op, inputs);

	if (out->get_size() != outSz)
	{
		sal_loge("Error: in " << s.asString() << "\texpected output of size " << out->get_size() << endl);
		assert(0);
	}

	return out;
}

int SalFrontend::read_size(const sexpr& s)
{
	sexpr::iterator it = s.begin();

	auto word = *it++;
	auto key = word.copyVal();
	assert(get_key(key) == $underscore);

	word = *it++;
	key = word.copyVal();
	Sal_keyword type = get_key(key);

	int sz = 0;
	switch(type)
	{
	case $bool:	{	sz = 1;	}	break;
	case $bitvec: {
		word = *it++;
		string szStr = word.copyVal();
		sz = stoi(szStr);
	}	break;
	default:
		sal_loge("unable to get size in expression: " << s.asString() << endl);
		assert(0);
	}
	assert (it == s.end());

	return sz;
}

void SalFrontend::force_new(const string& name, const sexpr& s)
{
	if (sal_nodes.find(name) != sal_nodes.end())
	{
		sal_loge("Error: in " << s.asString() << " \trepeated definition of " << name << endl);
		assert(0);
	}
}

int SalFrontend::get_input_size(CellType& cell, int outSz)
{
	switch(cell.get_input_restrcition())
	{
	case $anysz:	return ANY_NUM;
	case $samesz:	return ANY_NUM;
	case $tersz:	return outSz;
	case $outsz:	return outSz;
	case $boolsz:	return 1;
	default:
		assert(0);
	}
}


/**
 * Function for setting special keywords
 */
void SalFrontend::set_keys(void)
{
	keyHash["_"] 		= $underscore;
	keyHash["BitVec"] 	= $bitvec;
	keyHash["Bool"] 	= $bool;
	keyHash["="] 		= $eq;
}

SalFrontend::Sal_keyword SalFrontend::get_key(string keyword)
{
	if (keyHash.find(keyword) == keyHash.end())
		return $unknown;
	return keyHash[keyword];
}

/**
 * Function for initialization of parser
 */
void SalParser::_init(void)
{
	try {
//		print();
	} catch (const parse_error& ex) {
		cerr << "PARSE ERROR: " << ex.what() << endl;
		sal_loge("Error encountered in input file: " << filename << endl;);
	}
}

}


