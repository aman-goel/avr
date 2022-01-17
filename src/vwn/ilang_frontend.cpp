/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


/*
 * ilang_frontend.cpp
 *
 *  Created on: Jun 6, 2017
 *      Author: rock
 */

#include "ilang_frontend.h"

namespace yos
{


const char IlangParser::specialChars[] = {'(', ')', ',', ';', '*'};
std::unordered_map <char, bool> IlangParser::specCharLibDir;

map<string, CellType> CellTypes::cell_types;
static CellTypes CellTemplates;

int IlangFrontend::wid = 0;
int IlangFrontend::cid = 0;

void IlangFrontend::help()
{
	//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
	yos_log("\n");
	yos_log("    read_ilang [filename]\n");
	yos_log("\n");
	yos_log("Reads the design in an 'ilang' file. (ilang is a text representation\n");
	yos_log("of a design in yosys's internal format.)\n");
	yos_log("\n");
	yos_log("Note: Design should be already elaborated and flattened using Yosys\n");
	yos_log("\n");
}

void IlangFrontend::execute()
{
	yos_log("Executing ILANG frontend.\n");
	yos_log("Input filename: " << filename << endl);
	bool status = read_design();

	if (!status)
	{
		yos_loge("failure encountered in input file: " << filename);
	}
	else
	{
		process_design();
		print_design();
	}
}

/**
 * Function for printing design equations
 */
void IlangFrontend::print_design()
{
	yos_log("---------------" << endl);
	yos_log("Clocks (unique)" << endl);
	yos_log("---------------" << endl);
	yos_log("  " << unique_clk.size() << endl);
	for (auto& c: unique_clk)
	{
		yos_log(c << endl);
	}
	yos_log(endl);
	yos_log("------------------------------------" << endl);
	yos_log("Next State / Combinational Equations" << endl);
	yos_log("------------------------------------" << endl);
	for (static InstToInstM::iterator i = map_net_op.begin(); i != map_net_op.end(); i++)
	{
		Inst* temp = (*i).second;
		string instType = "";
		switch(temp->get_type())
		{
		// Signal
		case Sig: instType = "Sig"; break;
		// Number
		case Num: instType = "Num"; break;
		// Operation
		case Op: instType = "Op"; break;
		// Extraction
		case Ex: instType = "Ex"; break;
		// Memory
		case Mem: instType = "Mem"; break;
		// UF
		case UF: instType = "UF"; break;

		// now, things that were used in software verification!
		// Lambda
		case Lambda: instType = "Lambda"; break;
		// Array. Can be equated to other arrays or to Lambdas!
//					case Array: instType = "Array"; break;
		default: instType = "-";
		}
		yos_log("(inst: " << setw(12) << left << map_inst_vinst[(*i).first] << " type: " << setw(6) << left << instType << ")\t");
		yos_log(setw(8) << left << *(*i).first << " = " << *(*i).second << endl);

//		OpInst* op = OpInst::as((*i).second);
//		if (op)
//		{
//			stringstream tmp;
//			tmp << *(*i).first;
//			op->set_v_name(tmp.str());
//		}
	}
	yos_log(endl);
}

/**
 * Function for processing design to avr data structures
 */
void IlangFrontend::process_design()
{
	for (auto& c: clock_names) {
		unique_clk.insert(c.second);
	}
	num_clock = unique_clk.size();

	for (int i = 0; i < wires.size(); i++)
	{
//		print_wire(wires[i]);
		process_wire(wires[i]);
	}
	for (int i = 0; i < cells.size(); i++)
	{
//		print_cell(cells[i]);
		process_cell(cells[i]);
	}

#ifdef ALLOW_EXPLICIT_INPUTS_ONLY
	for (auto& mit : map_sig)
	{
		Inst* sig = mit.second;
		if (s_inputs.find(sig) == s_inputs.end())
		{
			if (map_net_op.find(sig) == map_net_op.end())
			{
				Inst* pre = sig;
				SigInst* sigPre = SigInst::as(pre);
				assert(sigPre);
				string sigStr = sigPre->get_name();

				if (sigStr.substr(0,2) == WIRE_NAME_PREFIX)
				{
					yos_log ("Warning: Found redundant intermediate wire: " << *sig << ", skipping." << endl);
					num_warnings++;
					continue;
				}

				sigStr += "$next";
				Inst* sigNext = SigInst::create(sigStr, pre->get_size());

				if (map_net_op.find(sigNext) == map_net_op.end())
				{
					states[sigPre->get_name()] = sigPre;
					map_net_op[sigNext] = pre;
					map_inst_vinst[sigNext] = "-";
					next_states.push_back(sigNext);
					yos_log ("   creating ff (fixed): " << *sigNext << " <= " << *pre << endl);
				}
			}
		}
	}
#endif
}

/**
 * Function for processing a wire to avr data structures
 */
void IlangFrontend::process_wire(wire& w)
{
	string sig_name = get_wire_name(w);
	if (sig_name == config->get_arg(PROP_SIG_ARG)) {
		yos_logw("found reserved keyword " << sig_name << " as signal");
		sig_name += "$";
		yos_logw("renaming as " << sig_name);
	}

	Inst* sig;
	sig = SigInst::create(sig_name, w.size, SORT());

	if (Config::g_single_property && endsWith(sig_name, config->get_arg(SELECT_PROPERTY))) {
		if (prop_ve != NULL) {
			yos_logw("multiple signals matching with selected property " << config->get_arg(SELECT_PROPERTY));
			yos_logw("ignoring matched signal " << sig_name << " as property");
		}
		else
			prop_ve = sig;
	}

	map_sig[sig_name] = sig;

	m_wire2sig[w.name] = sig;

	if (w.init != "")
	{
		std::string s = w.init;
		std::string delimiter = "'";

		size_t pos = 0;
		std::string token;
		while ((pos = s.find(delimiter)) != std::string::npos)
		{
		    token = s.substr(0, pos);
		    s.erase(0, pos + delimiter.length());
		}
		if (token == "")
		{
			long long numVal = stoll(s);
			s = decimal2binary(numVal);
		}

//		cout << w.name << "  " << s << "  " << w.init << endl;

		for (int i = s.length(); i < w.size; i++)
			s = "0" + s;
		assert(s.length() == w.size);

		sig = SigInst::create(sig_name, w.size, SORT());
		if (w.size == 1)
		{
			if (s == "1")
			{
				initials.push_back(sig);
				map_init[sig] = NumInst::create(1, 1);
			}
			else
			{
				initials.push_back(OpInst::create(OpInst::LogNot, sig));
				map_init[sig] = NumInst::create(0, 1);
			}
		}
		else
		{
			Inst* num = NumInst::create(s, w.size, 2);
			constants.insert(num);
			initials.push_back(OpInst::create(OpInst::Eq, sig, num));
			map_init[sig] = num;
		}
		yos_log ("   init_cond: " << *(initials.back()) << endl);
	}

#ifdef ALLOW_EXPLICIT_INPUTS_ONLY
	if (w.type == "input")
	{
		s_inputs.insert(sig);
		yos_log ("   input: " << *sig << endl);
	}
#endif

//	log ("  Sig: " << *sig << " (sz: " << sig->get_size() << ")" << endl);
}

/**
 * Function for finding signal name from a wire
 */
string IlangFrontend::get_wire_name(wire& w)
{
	if (false && (w.name.at(0) == '\\'))
	{
		string tmp = w.name.substr(1);
		map_sig_user_defined[tmp] = true;
		return tmp;
	}
	else if (false && (w.name.at(0) == '$'))
	{
		string tmp = (WIRE_NAME_PREFIX + to_string(wid++));
		map_sig_user_defined[tmp] = false;
		return tmp;
	}
	else
	{
		map_sig_user_defined[w.name] = true;
		return w.name;
	}
}

/**
 * Function for converting a decimal number to binary string
 */
string IlangFrontend::decimal2binary(long long numVal)
{
	string numStr = "";
	while(1)
	{
		int div = numVal / 2;
		int rem = numVal % 2;
		numStr = ((rem == 0) ? "0" : "1") + numStr;
		if (div == 0)
			break;
		else
			numVal = div;
	}
	return numStr;
}

/**
 * Function for zero extending instance to bring to a given size
 */
Inst* IlangFrontend::zero_extend(Inst* tve, unsigned outSz)
{
	unsigned sz = tve->get_size();
	pair< Inst*, unsigned > p = make_pair(tve, outSz);
	PairUintToInstM::iterator mit = m_inst2zextend.find(p);
	if (mit != m_inst2zextend.end())
		return (*mit).second;

//	cout << *tve << "  " << sz << "  " << outSz << endl;
	assert(sz < outSz);
	Inst* newTve;
	NumInst* num = NumInst::as(tve);
	if (num)
	{
		string numStr = num->get_mpz()->get_str(2);
		for (unsigned i = numStr.length(); i < outSz; i++)
			numStr = "0" + numStr;
		assert(numStr.length() == outSz);
		newTve = NumInst::create(numStr, outSz, 2);
	}
	else
	{
		string numStr = "";
		for (unsigned i = sz; i < outSz; i++)
			numStr = "0" + numStr;
		Inst* zeroNum = NumInst::create(numStr, (outSz - sz), 2);
		InstL exps;
		exps.push_back(tve);
		exps.push_back(zeroNum);
		newTve = OpInst::create(OpInst::Concat, exps);
	}

	m_inst2zextend[p] = newTve;
	yos_log ("   zero-extending " << *tve << " to " << *newTve << endl);
	assert(newTve->get_size() == outSz);
	return newTve;
}

/**
/**
 * Function for processing a non-signal expression to avr data structures
 */
Inst* IlangFrontend::process_expr(string portStr)
{
	char firstC = portStr.at(0);
	if (firstC == '{')
		return process_concat(portStr);
	else if (isdigit(firstC))
		return process_const(portStr);
	else
		return process_extract(portStr);
}

/**
/**
 * Function for processing a constant number to avr data structures
 */
Inst* IlangFrontend::process_const(string portStr)
{
	map < string, Inst* >::iterator sit = m_wire2sig.find(portStr);
	if (sit != m_wire2sig.end())
		return (*sit).second;

	std::string s = portStr;
	std::string delimiter = "'";

	size_t pos = 0;
	std::string token = "";
	while ((pos = s.find(delimiter)) != std::string::npos)
	{
	    token = s.substr(0, pos);
	    s.erase(0, pos + delimiter.length());
	}
	int sz;
	if (token != "")
	{
		sz = stoi(token);
		assert(s.length() == sz);
	}
	else
	{
		long long numVal = stoll(s);
		s = decimal2binary(numVal);
		sz = s.length();
	}
	Inst* num = NumInst::create(s, sz, 2);
	constants.insert(num);
	m_wire2sig[portStr] = num;
	yos_log ("   creating num: " << *num << " from " << portStr << endl);
	return num;
}

/**
/**
 * Function for processing an extract expression to avr data structures
 */
Inst* IlangFrontend::process_extract(string portStr)
{
	map < string, Inst* >::iterator sit = m_wire2sig.find(portStr);
	if (sit != m_wire2sig.end())
		return (*sit).second;

	string s = portStr;
	std::string delimiter = ",[";

	size_t pos = 0;
	std::string sigName = "";
	int hi = -1, lo = -1;
	if ((pos = s.find(delimiter)) != std::string::npos)
	{
	    sigName = s.substr(0, pos);
	    s.erase(0, pos + delimiter.length());
	}

	std::string token = "";
	delimiter = ":";
	if ((pos = s.find(delimiter)) != std::string::npos)
	{
	    token = s.substr(0, pos);
	    hi = stoi(token);
	    s.erase(0, pos + delimiter.length());
	}

	delimiter = "]";
	if ((pos = s.find(delimiter)) != std::string::npos)
	{
	    token = s.substr(0, pos);
	    lo = stoi(token);
	    s.erase(0, pos + delimiter.length());
	}

	if (hi == -1)
		hi = lo;

	assert(hi >= lo);
	assert(lo >= 0);
	assert(sigName != "");

	sit = m_wire2sig.find(sigName);
	if (sit == m_wire2sig.end())
		yos_loge ("unable to create extract (from port expr): " << portStr);

	Inst* ex = ExInst::create((*sit).second, hi, lo);
	m_wire2sig[portStr] = ex;
	yos_log ("   creating extract (from port expr): " << *ex << endl);
	return ex;
}

/**
/**
 * Function for processing a concat expression to avr data structures
 */
Inst* IlangFrontend::process_concat(string portStr)
{
	map < string, Inst* >::iterator sit = m_wire2sig.find(portStr);
	if (sit != m_wire2sig.end())
		return (*sit).second;

	string s = portStr;
	char *cstr = new char[s.length() + 1];
	strcpy(cstr, s.c_str());
	const char* delimiter = ",{}";

	InstL exps;
	char * pch;
	std::string sigName = "";
	pch = strtok (cstr, delimiter);
	while (pch != NULL)
	{
		if (pch[0] == '[')
		{
			exps.push_front(process_extract(sigName + "," + pch));
			sigName = "";
		}
		else
		{
			if (sigName != "")
			{
				map < string, Inst* >::iterator sit = m_wire2sig.find(sigName);
				if (sit != m_wire2sig.end())
					exps.push_front((*sit).second);
				else
					exps.push_front(process_const(sigName));
			}
			sigName = pch;
		}
		pch = strtok (NULL, delimiter);
	}
	delete [] cstr;

	if (sigName != "")
	{
		map < string, Inst* >::iterator sit = m_wire2sig.find(sigName);
		if (sit != m_wire2sig.end())
			exps.push_front((*sit).second);
		else
			exps.push_front(process_const(sigName));
	}

	Inst* cc = OpInst::create(OpInst::Concat, exps);
	m_wire2sig[portStr] = cc;
	yos_log ("   creating concat (from port expr): " << *cc << endl);
	return cc;
}

/**
/**
 * Function for processing a cell to avr data structures
 */
void IlangFrontend::process_cell(Cell& c)
{
	string cell_name = get_cell_name(c);

	map< string, TypeHash>::iterator type_it = m_hash.find(c.type);
	if (type_it != m_hash.end())
	{
		TypeHash type = (*type_it).second;

		OpInst::OpType opt = OpInst::Unknown;
		InstL inputs, outputs;

		map<string, CellType>::iterator ctit = CellTypes::cell_types.find(c.type);
		assert(ctit != CellTypes::cell_types.end());
		CellType ct = (*ctit).second;
		unsigned maxIsz = 0;
		unsigned totalIsz = 0;
		unsigned outSize = 0;

		for (auto p : ct.params)
		{
			string portStr = c.params[p];
			map < string, Inst* >::iterator sit = m_wire2sig.find(portStr);
			Inst* tve;
			if (sit != m_wire2sig.end())
				tve = (*sit).second;
			else {
				tve = process_expr(portStr);
//				cout << c.src << " in " << portStr << " becomes " << *tve << endl;
			}
		}
		for (auto inp : ct.inputs)
		{
			string portStr = c.connects[inp];
			map < string, Inst* >::iterator sit = m_wire2sig.find(portStr);
			Inst* tve;
			if (sit != m_wire2sig.end())
				tve = (*sit).second;
			else
				tve = process_expr(portStr);

			if (!CellTypes::cell_is_memory(type)) {
				int sz = 0;
				string widthParam = inp + "_WIDTH";
				auto mit = c.params.find(widthParam);
				if (mit == c.params.end())
					mit = c.params.find("\\WIDTH");

				if (mit != c.params.end())
				{
					sz = stoi((*mit).second);
					if (tve->get_size() != sz) {
						if (tve->get_size() > sz) {
							yos_logw("input width (" << tve->get_size() << ") is more than given width (" << sz
									<< ") for input " << *tve << " in cell " << c.name);
	//						assert(0);
						}
						else
							tve = zero_extend(tve, sz);
					}
				}
			}
//			cout << "inp: " <<  *tve << "  " << tve->get_size() << endl;

			inputs.push_back(tve);
			if (tve->get_size() > maxIsz)
				maxIsz = tve->get_size();
			totalIsz += tve->get_size();
		}
		assert(inputs.size() > 0);
//		cout << c.name << endl;
		assert(maxIsz > 0);

		for (auto out : ct.outputs)
		{
			string portStr = c.connects[out];
			map < string, Inst* >::iterator sit = m_wire2sig.find(portStr);
			Inst* tve;
			if (sit != m_wire2sig.end())
				tve = (*sit).second;
			else
				tve = process_expr(portStr);

			int sz = 0;
			string widthParam = out + "_WIDTH";
			auto mit = c.params.find(widthParam);
			if (mit == c.params.end())
				mit = c.params.find("\\WIDTH");

			if (mit != c.params.end())
			{
				sz = stoi((*mit).second);
				if (tve->get_size() != sz)
					tve = zero_extend(tve, sz);
			}
			outputs.push_back(tve);
		}

		/// Hack for assert blocks
		if (type == $assert)
			outputs.push_back(NumInst::create(1,1));
		else if (type == $assume)
			outputs.push_back(NumInst::create(1,1));
		else if (type == $meminit)
			outputs.push_back(NumInst::create(1,1));
		else if (type == $memwr)
			outputs.push_back(NumInst::create(1,1));

		if (outputs.size() != 1)
		{
			yos_loge("more than one output for cell " << c.name);
		}
		assert(outputs.size() == 1);
		if (outSize <= 0)
		{
			outSize = outputs.front()->get_size();
			if (type == $concat)
			{
				if (outSize != totalIsz)
				{
					cout << outSize << "  " << totalIsz << endl;
					cout << c.name << endl;
				}
				assert (outSize == totalIsz);
			}
		}
		assert(outSize > 0);

		bool isBool = (outSize == 1) ? true : false;
//		bool isBool = ((outputs.size() == 1) && (outputs.back()->get_size() == 1)) ? true : false;

		bool isFf = false;
		bool isBuf = false;
		bool isInv = false;
		bool isEx = false;

		bool inpExtend = false;
#ifdef ZERO_EXTEND_OPERATIONS
		bool outExtend = false;
#endif
		bool unitSz = false;
		bool useOutsz = false;

		switch (type)
		{
			case $assert:
			{
        Inst* rhs;
        rhs = m_wire2sig[c.connects["\\A"]];
        assert(rhs->get_size() == 1);
//        if (rhs == prop_ve)
//          return;

			  Inst* prop;
				{
					wire w;
					w.name = config->get_arg(PROP_SIG_ARG) + to_string(properties.size() + 1);
					w.size = 1;
					w.src = c.src;
					w.type = "output";
					wires.push_back(w);
					process_wire(w);
					prop = m_wire2sig[w.name];
					properties.push_back(prop);

					yos_log("Found multiple assert blocks" << endl);
				}
				assert(prop);
				outputs.clear();
				outputs.push_back(prop);

				inputs.clear();
				Inst* cond;
				cond = m_wire2sig[c.connects["\\EN"]];
				assert(cond->get_size() == 1);

				if (cond != NumInst::create(1,1))
				{
					Inst* then;
					then = m_wire2sig[c.connects["\\A"]];
					Inst* el;
					el = NumInst::create(1,1);

					assert(then->get_size() == 1);
					assert(el->get_size() == 1);

					inputs.push_back(cond);
					inputs.push_back(then);
					inputs.push_back(el);
					opt = OpInst::Ternary;
				}
				else
				{
					Inst* rhs;
					rhs = m_wire2sig[c.connects["\\A"]];
					assert(rhs->get_size() == 1);
					inputs.push_back(rhs);

					isBuf = true;
				}
			}	break;
			case $assume:
			{
        Inst* rhs;
        rhs = m_wire2sig[c.connects["\\A"]];
        assert(rhs->get_size() == 1);

			  Inst* prop;
				{
					wire w;
					w.name = "assume_" + to_string(assumptions.size() + 1);
					w.size = 1;
					w.src = c.src;
					w.type = "output";
					wires.push_back(w);
					process_wire(w);
					prop = m_wire2sig[w.name];
					assumptions.push_back(prop);

					yos_log("Found assume block" << endl);
				}
				assert(prop);
				outputs.clear();
				outputs.push_back(prop);

				inputs.clear();
				Inst* cond;
				cond = m_wire2sig[c.connects["\\EN"]];
				assert(cond->get_size() == 1);

				if (cond != NumInst::create(1,1))
				{
					Inst* then;
					then = m_wire2sig[c.connects["\\A"]];
					Inst* el;
					el = NumInst::create(1,1);

					assert(then->get_size() == 1);
					assert(el->get_size() == 1);

					inputs.push_back(cond);
					inputs.push_back(then);
					inputs.push_back(el);
					opt = OpInst::Ternary;
				}
				else
				{
					Inst* rhs;
					rhs = m_wire2sig[c.connects["\\A"]];
					assert(rhs->get_size() == 1);
					inputs.push_back(rhs);

					isBuf = true;
				}
			}	break;
			// Unary
			case $not:
			{
				if (isBool)
					unitSz = true;
				else
				{
					useOutsz = true;
#ifdef ZERO_EXTEND_OPERATIONS
					outExtend = true;
#endif
				}
				opt = isBool ? OpInst::LogNot : OpInst::BitWiseNot;
			}
			break;
			case $logic_not:
			case $_NOT_:
				unitSz = true;
				opt = OpInst::LogNot;	break;
			case $neg:
				opt = OpInst::Minus;	break;
			case $reduce_and:
			  if (inputs.front()->get_size() == 1)
          isBuf = true;
				opt = OpInst::ReductionAnd;	break;
			case $reduce_bool:
			case $reduce_or:
        if (inputs.front()->get_size() == 1)
          isBuf = true;
				opt = OpInst::ReductionOr;	break;
			case $reduce_xor:
				opt = OpInst::ReductionXor;	break;
			case $reduce_xnor:
				opt = OpInst::ReductionXNor;	break;
			case $pos:
				isBuf = true;	break;
			case $slice:
				isEx = true;	break;
			case $lut:
			case $sop:
				yos_loge("cell type " << c.type << " not supported. Found in cell defined at " << c.src);
				break;

			// Binary
			case $logic_and:
			case $_AND_:
				unitSz = true;
				opt = OpInst::LogAnd;	break;
			case $logic_or:
			case $_OR_:
				unitSz = true;
				opt = OpInst::LogOr;	break;
			case $eq:
			case $eqx:
				inpExtend = true;
				opt = OpInst::Eq;	break;
			case $ne:
			case $nex:
				inpExtend = true;
				opt = OpInst::NotEq;	break;
			case $lt:
#ifdef ZERO_EXTEND_OPERATIONS
				inpExtend = true;
#endif
				opt = OpInst::Le;	break;
			case $le:
#ifdef ZERO_EXTEND_OPERATIONS
				inpExtend = true;
#endif
				opt = OpInst::LeEq;	break;
			case $gt:
#ifdef ZERO_EXTEND_OPERATIONS
				inpExtend = true;
#endif
				opt = OpInst::Gr;	break;
			case $ge:
#ifdef ZERO_EXTEND_OPERATIONS
				inpExtend = true;
#endif
				opt = OpInst::GrEq;	break;
			case $_XOR_:
				unitSz = true;
				opt = OpInst::LogXor;	break;
			case $_XNOR_:
				unitSz = true;
				opt = OpInst::LogXNor;	break;
			case $or:
				if (isBool)
					unitSz = true;
				else
				{
					useOutsz = true;
#ifdef ZERO_EXTEND_OPERATIONS
					outExtend = true;
#endif
				}
				opt = isBool ? OpInst::LogOr : OpInst::BitWiseOr;	break;
			case $and:
				if (isBool)
					unitSz = true;
				else
				{
					useOutsz = true;
#ifdef ZERO_EXTEND_OPERATIONS
					outExtend = true;
#endif
				}
				opt = isBool ? OpInst::LogAnd : OpInst::BitWiseAnd;	break;
			case $xor:
				if (isBool)
					unitSz = true;
				else
				{
					useOutsz = true;
#ifdef ZERO_EXTEND_OPERATIONS
					outExtend = true;
#endif
				}
				opt = isBool ? OpInst::LogXor : OpInst::BitWiseXor;	break;
			case $xnor:
				if (isBool)
					unitSz = true;
				else
				{
					useOutsz = true;
#ifdef ZERO_EXTEND_OPERATIONS
					outExtend = true;
#endif
				}
				opt = isBool ? OpInst::LogXNor : OpInst::BitWiseXNor;	break;
			case $add:
				useOutsz = true;
#ifdef ZERO_EXTEND_OPERATIONS
				outExtend = true;
#endif
				opt = OpInst::Add;	break;
			case $sub:
				useOutsz = true;
#ifdef ZERO_EXTEND_OPERATIONS
				outExtend = true;
#endif
				opt = OpInst::Sub;	break;
			case $mul:
				useOutsz = true;
				opt = OpInst::Mult;	break;

			case $div:
				useOutsz = true;
				opt = OpInst::Div;	break;
			case $mod:
				useOutsz = true;
				opt = OpInst::Rem;	break;

			case $concat:
//				useOutsz = true;
				opt = OpInst::Concat;	break;
			case $sshl:
			case $shl:
			{
				useOutsz = true;
#ifdef ZERO_EXTEND_OPERATIONS
//				inpExtend = true;
	#ifdef OUTPUT_EXTEND_SHIFT_OPERATIONS
				outExtend = true;
	#endif
#endif

#ifdef ZERO_EXTEND_OPERATIONS
				outExtend = true;
#endif
				Inst* op2;
				op2 = m_wire2sig[c.connects["\\B"]];
				if (NumInst::as(op2))
					opt = OpInst::ShiftL;
				else
					opt = OpInst::ShiftL;

#ifdef YOSYS_REPLACE_SHIFT_WITH_ADD
				yos_log("replacing <<< with + for " << c.name << endl);
				opt = OpInst::Add;
#endif
			}
				break;

			case $sshr:
			case $shr:
			{
				useOutsz = true;
#ifdef ZERO_EXTEND_OPERATIONS
//				inpExtend = true;
	#ifdef OUTPUT_EXTEND_SHIFT_OPERATIONS
			outExtend = true;
	#endif
#endif

#ifdef ZERO_EXTEND_OPERATIONS
				outExtend = true;
#endif
				Inst* op2;
				op2 = m_wire2sig[c.connects["\\B"]];
				if (NumInst::as(op2))
					opt = OpInst::ShiftR;
				else
					opt = OpInst::ShiftR;

#ifdef YOSYS_REPLACE_SHIFT_WITH_ADD
				yos_log("replacing >>> with + for " << c.name << endl);
				opt = OpInst::Add;
#endif
			}
				break;

			case $shift:
			case $shiftx:
//			case $eqx:
//			case $nex:
			case $pow:
			case $macc:
				yos_loge("cell type " << c.type << " not supported. Found in cell defined at " << c.src);
				break;

			case $mux:
			case $_MUX_:
				inputs.clear();
				Inst* cond;
				cond = m_wire2sig[c.connects["\\S"]];
				Inst* then;
				then = m_wire2sig[c.connects["\\B"]];
				Inst* el;
				el = m_wire2sig[c.connects["\\A"]];

				assert(cond->get_size() == 1);
				if (then->get_size() < outSize)
					then = zero_extend(then, outSize);
				if (el->get_size() < outSize)
					el = zero_extend(el, outSize);

				inputs.push_back(cond);
				inputs.push_back(then);
				inputs.push_back(el);
				opt = OpInst::Ternary;	break;

			case $pmux:
			case $lcu:
			case $alu:
			case $fa:
			case $tribuf:
				yos_loge("cell type " << c.type << " not supported. Found in cell defined at " << c.src);
				break;

			/// Internal memory cells
			case $ff:
				c.connects[get_clock_name(type)] = "1'x";
				// fall through intended
			case $dff:
			case $_DFF_P_:
			case $_DFF_N_:
				isFf = true;	break;
			case $adff:
				yos_logw("modelling async flop as synchronous. Found in cell " << c.name << " defined at " << c.src);
				isFf = true;	break;
			case $meminit:
			case $memrd:
			case $memwr:
				process_memory(c);
				return;
				break;
			case $dffsr:
			case $sr:
			case $dffe:
			case $dlatch:
			case $dlatchsr:
			case $mem:
			case $fsm:
				yos_loge("cell type " << c.type << " not supported. Found in cell " << c.name << " defined at " << c.src);
				break;

			/// Standard cells
			case $_BUF_:
				isBuf = true;	break;
			case $_NAND_:
				unitSz = true;
				isInv = true;
				opt = OpInst::LogAnd;	break;
			case $_NOR_:
				unitSz = true;
				isInv = true;
				opt = OpInst::LogOr;	break;
			case $_ANDNOT_:
			case $_ORNOT_:
				unitSz = true;
				inputs.clear();
				inputs.push_back(m_wire2sig[c.connects["\\A"]]);
				Inst* port_b;
				port_b = m_wire2sig[c.connects["\\B"]];
				assert(port_b->get_size() == 1);
				inputs.push_back(OpInst::create(OpInst::LogNot, port_b));
				opt = (type == $_ANDNOT_) ? OpInst::LogAnd : OpInst::LogOr;
				break;

			case $_MUX4_:
			case $_MUX8_:
			case $_MUX16_:
			case $_AOI3_:
			case $_OAI3_:
			case $_AOI4_:
			case $_OAI4_:
			case $_TBUF_:
				yos_loge("cell type " << c.type << " not supported. Found in cell " << c.name << " defined at " << c.src);
				break;
			default:
				yos_loge("cell type " << c.type << " not supported. Found in cell " << c.name << " defined at " << c.src);
				break;
		}

		if (isFf)
		{
			Inst* out = m_wire2sig[c.connects["\\D"]];
			Inst* clk = m_wire2sig[c.connects[get_clock_name(type)]];

			if (type == $adff) {
				Inst* arst = m_wire2sig[c.connects["\\ARST"]];
				Inst* arst_polarity = m_wire2sig[c.params["\\ARST_POLARITY"]];
				Inst* arst_value = m_wire2sig[c.params["\\ARST_VALUE"]];

				assert(arst && arst_polarity && arst_value);
				assert(arst->get_size() == 1);
				assert(arst_polarity->get_size() == 1);
				assert(arst_polarity->get_type() == Num);

				if (arst_polarity == NumInst::create(0, 1))
					arst = OpInst::create(OpInst::LogNot, arst);
				out = OpInst::create(OpInst::Ternary, arst, arst_value, out);
			}

			Inst* pre = outputs.back();
			SigInst* sigPre = SigInst::as(pre);

			Inst* sigNext;
			bool appendCellName = false;
			if (sigPre)
			{
				string sigStr = sigPre->get_name();
				Inst* sigTmp = SigInst::create(sigStr, sigPre->get_size(), SORT());
				states[sigStr] = sigTmp;
				sigStr += "$next";
				sigNext = SigInst::create(sigStr, out->get_size(), SORT());

				string clk_str = c.connects[get_clock_name(type)];
				if (!startsWith(clk_str, "1'")) {
					Inst* clk = m_wire2sig[clk_str];
					SigInst* sigClk = SigInst::as(clk);
					assert(sigClk);
					if (num_clock > 1)
						out = OpInst::create(OpInst::Ternary, sigClk, out, sigPre);
				}
			}
			else
			{
				ExInst* ex_op = ExInst::as(pre);
				if (ex_op)
				{
					unsigned hi = ex_op->get_hi();
					unsigned lo = ex_op->get_lo();

					Inst* exp = ex_op->get_exp();
					unsigned sz = exp->get_size();

					sigPre = SigInst::as(exp);
					assert(sigPre);

					string sigStr = sigPre->get_name();
					Inst* sigTmp = SigInst::create(sigStr, sigPre->get_size(), SORT());
					states[sigStr] = sigTmp;
					sigStr += "$next";
					sigNext = SigInst::create(sigStr, sigPre->get_size(), SORT());

					string clk_str = c.connects[get_clock_name(type)];
					if (!startsWith(clk_str, "1'")) {
						Inst* clk = m_wire2sig[clk_str];
						SigInst* sigClk = SigInst::as(clk);
						assert(sigClk);
						if (num_clock > 1)
							out = OpInst::create(OpInst::Ternary, sigClk, out, ExInst::create(sigPre, hi, lo));
					}

					InstToInstM::iterator mit = map_net_op.find(sigNext);
					if (mit != map_net_op.end())
					{
						Inst* tve = (*mit).second;
						OpInst* op_tve = OpInst::as(tve);
						assert(op_tve);
						assert(op_tve->get_op() == OpInst::Concat);

						const InstL* ch = op_tve->get_children();
						assert (ch);
						unsigned s_loc = 0, e_loc = 0;
						InstL exps;
						bool replaceFlag = false;
						for (InstL::const_iterator cit = ch->begin(); cit != ch->end(); ++cit)
						{
							Inst *tve = *cit;
							unsigned size = tve->get_size();
							s_loc = e_loc;
							e_loc += size;
							if (s_loc == lo)
							{
								replaceFlag = true;
								exps.push_back(out);
								unsigned remSz = e_loc - (hi + 1);
								if (remSz > 0)
									exps.push_back(NumInst::create(0, remSz));
							}
							else if (!replaceFlag && (e_loc > hi))
							{
								replaceFlag = true;
								unsigned remSz = lo - s_loc;
								if (remSz > 0)
									exps.push_back(NumInst::create(0, remSz));
								exps.push_back(out);
								remSz = e_loc - (hi + 1);
								if (remSz > 0)
									exps.push_back(NumInst::create(0, remSz));
							}
							else
								exps.push_back(tve);
						}
						if (!replaceFlag)
						{
							cout << "Error at " << c.name << endl;
							cout << *tve << endl;
						}
						assert(replaceFlag);

						Inst* tmp = OpInst::create(OpInst::Concat, exps);
						out = tmp;
						appendCellName = true;
						yos_log ("   replacing zero padded concat to " << *tmp << " for cell: " << c.name << endl);
					}
					else
					{
						InstL exps;
						if (lo > 0)
							exps.push_back(NumInst::create(0, lo));

						exps.push_back(out);

						if (hi < (sz - 1))
							exps.push_back(NumInst::create(0, (sz - 1 - hi)));

						Inst* tmp = OpInst::create(OpInst::Concat, exps);
						out = tmp;
						yos_log ("   creating zero padded concat " << *tmp << " for cell: " << c.name << endl);
					}
				}
				else
				{
					yos_loge ("in " << *pre << " for cell: " << c.name);
				}
			}
			map_net_op[sigNext] = out;
			if (appendCellName)
			{
				map_inst_vinst[sigNext] += (", " + cell_name);
				yos_log ("   updating ff: " << *sigNext << " <= " << *out << endl);
			}
			else
			{
				map_inst_vinst[sigNext] = cell_name;
				next_states.push_back(sigNext);
				yos_log ("   creating ff: " << *sigNext << " <= " << *out << endl);
			}
		}
		else
		{
			Inst* out = outputs.back();
			if (isBuf)
			{
				Inst* inp = inputs.back();
				if (inp->get_size() != outSize)
					inp = zero_extend(inp, outSize);
				if (out->get_size() != outSize)
					out = zero_extend(out, outSize);
				map_net_op[out] = inp;
			}
			else if (isEx)
			{
				Inst* inp = inputs.back();
				SigInst* out_sig = SigInst::as(out);
				assert(out_sig);
				assert (out->get_size() == outSize);

				int offset = 0;
				for (auto p : c.params)
				{
					if ((p.first == "\\OFFSET"))
					{
						offset = stoi(p.second);
						break;
					}
				}
				unsigned lo = (unsigned) offset;
				unsigned hi = lo + outSize - 1;
				assert(lo >= 0);
				assert(hi >= lo);
				Inst* exCell = ExInst::create(inp, hi, lo);
				assert (exCell->get_size() == outSize);

				map_net_op[out] = exCell;
				map_inst_vinst[out] = cell_name;
				SigInst* outSig = SigInst::as(out);
				if (outSig)
					gate_names[exCell] = outSig->get_name();

				yos_log ("   creating extract: " << *exCell << endl);
			}
			else
			{
				assert(opt != OpInst::Unknown);

#ifdef ZERO_EXTEND_OPERATIONS
				if (outExtend)
				{
					for (auto& inp : inputs)
					{
						if (inp->get_size() < outSize)
						{
							yos_log(c.name << endl);
							inp = zero_extend(inp, outSize);
						}
						else
						{
							inp = ExInst::create(inp, (outSize - 1), 0);
						}
					}
				}
				else
				{
#endif
				if (inpExtend)
				{
					for (auto& inp : inputs)
					{
						if (inp->get_size() != maxIsz)
						{
							inp = zero_extend(inp, maxIsz);
							yos_logw ("comparison of operands of different bit in cell " << c.name << ", zero extending");
//							num_warnings++;
						}
					}
				}
#ifdef ZERO_EXTEND_OPERATIONS
				}
#endif
				if (unitSz)
				{
					for (auto& inp : inputs)
					{
						unsigned sz = inp->get_size();
						if (sz != 1)
						{
							inp = OpInst::create(OpInst::NotEq, inp, NumInst::create(0, sz));
							yos_logw ("logical operation on multi-bit operands in cell " << c.name);
							num_warnings++;
						}
					}
				}

				Inst* opCell;

				if (useOutsz)
					opCell = OpInst::create(opt, inputs, outSize);
				else
					opCell = OpInst::create(opt, inputs);

				if (isInv)
				{
					assert(opCell->get_size() == 1);
					opCell = OpInst::create(OpInst::LogNot, opCell);
				}

				if (opCell->get_size() != outSize)
				{
					cout << c.name << endl;
					cout << *opCell << endl;
					cout << opCell->get_size() << endl;
					cout << outSize << endl;
				}
				assert (opCell->get_size() == outSize);
				assert (out->get_size() == outSize);

				if (type == $concat)
					yos_log ("   creating concat: " << *opCell << endl);

				SigInst* out_sig = SigInst::as(out);
				if (out_sig)
				{
					map_net_op[out] = opCell;
					map_inst_vinst[out] = cell_name;
					SigInst* outSig = SigInst::as(out);
					if (outSig)
						gate_names[opCell] = outSig->get_name();
				}
				else
				{
					ExInst* ex_op = ExInst::as(out);
					if (ex_op)
					{
						unsigned hi = ex_op->get_hi();
						unsigned lo = ex_op->get_lo();

						Inst* exp = ex_op->get_exp();
						assert(SigInst::as(exp));
						unsigned sz = exp->get_size();

						InstToInstM::iterator mit = map_net_op.find(exp);
						if (mit != map_net_op.end())
						{
							Inst* tve = (*mit).second;
							OpInst* op_tve = OpInst::as(tve);
							if (!op_tve)
							{
								cout << *exp << endl;
							}
							assert(op_tve);
              if (op_tve->get_op() != OpInst::Concat)
              {
                cout << "cell " << c.name << " at " << c.src << "\t" << get_cell_name(c) << endl;
                cout << *op_tve << endl;
              }
							assert(op_tve->get_op() == OpInst::Concat);

							const InstL* ch = op_tve->get_children();
							assert (ch);
							unsigned s_loc = 0, e_loc = 0;
							InstL exps;
							bool replaceFlag = false;
							for (InstL::const_iterator cit = ch->begin(); cit != ch->end(); ++cit)
							{
								Inst *tve = *cit;
								unsigned size = tve->get_size();
								s_loc = e_loc;
								e_loc += size;
								if (s_loc == lo)
								{
									replaceFlag = true;
									exps.push_back(opCell);
									unsigned remSz = e_loc - (hi + 1);
									if (remSz > 0)
										exps.push_back(NumInst::create(0, remSz));
								}
								else if (!replaceFlag && (e_loc > hi))
								{
									replaceFlag = true;
									unsigned remSz = lo - s_loc;
									if (remSz > 0)
										exps.push_back(NumInst::create(0, remSz));
									exps.push_back(opCell);
									remSz = e_loc - (hi + 1);
									if (remSz > 0)
										exps.push_back(NumInst::create(0, remSz));
								}
								else
									exps.push_back(tve);
							}
							if (!replaceFlag)
							{
								cout << "Error at " << c.name << endl;
								cout << *tve << endl;
							}
							assert(replaceFlag);

							Inst* tmp = OpInst::create(OpInst::Concat, exps, 0, false);
							map_net_op[exp] = tmp;
							map_inst_vinst[exp] += (", " + cell_name);
							SigInst* outSig = SigInst::as(exp);
							if (outSig)
								gate_names[tmp] = outSig->get_name();

							yos_log ("   replacing zero padded concat to " << *tmp << " for cell: " << c.name << endl);
						}
						else
						{
							InstL exps;
							if (lo > 0)
								exps.push_back(NumInst::create(0, lo));

							exps.push_back(opCell);

							if (hi < (sz - 1))
								exps.push_back(NumInst::create(0, (sz - 1 - hi)));

							Inst* tmp = OpInst::create(OpInst::Concat, exps, 0, false);
							map_net_op[exp] = tmp;
							map_inst_vinst[exp] = cell_name;
							SigInst* outSig = SigInst::as(exp);
							if (outSig)
								gate_names[tmp] = outSig->get_name();

							yos_log ("   creating zero padded concat " << *tmp << " for cell: " << c.name << endl);
						}
					}
					else
					{
						OpInst* out_op = OpInst::as(out);
						assert(out_op);
//						if (out_op->get_op() != OpInst::Concat)
//						{
//							cout << c.name << endl;
//							cout << *out_op << endl;
//						}
						assert(out_op->get_op() == OpInst::Concat);
						const InstL* chs = out_op->get_children();
						unsigned offset = 0;
						for (InstL::const_iterator cit = chs->begin(); cit != chs->end(); cit++)
						{
							Inst* tve = *cit;
							unsigned sz = tve->get_size();
							unsigned lo = offset;
							unsigned hi = lo + sz - 1;
							Inst* exCell = ExInst::create(opCell, hi, lo);
							yos_log ("   creating extract (for output port): " << *exCell << endl);
							assert (tve->get_size() == exCell->get_size());

							map_net_op[tve] = exCell;
							map_inst_vinst[tve] = cell_name;
							SigInst* outSig = SigInst::as(tve);
							if (outSig)
								gate_names[exCell] = outSig->get_name();

							offset = hi + 1;

							if (tve->get_type() != Sig)
							{
								yos_logw ("back cone of " << *tve << " can possibly get skipped in cell " << c.name);
								num_warnings++;
							}
						}
						assert(offset == outSize);
					}
				}

			}
		}
	}
	else
	{
		yos_loge("unable to find cell type " << c.type);
	}
}

void IlangFrontend::process_memory(Cell& c) {
	map< string, TypeHash>::iterator type_it = m_hash.find(c.type);
	assert (type_it != m_hash.end());
	TypeHash type = (*type_it).second;

	switch (type) {
	case $meminit:
	case $memrd:
	case $memwr:
		break;
	default:
		yos_loge("unable to process memory element in cell " << c.name << " defined at " << c.src);
	}
	yos_logw("possibly using imprecise timing model for memory elements");

  _resFile << "i-has-memory:\t" << "true" << endl;

	SORT sort;
	sort.type = arraytype;
	auto mit = c.params.find("\\ABITS");
	if (mit == c.params.end())
		yos_loge("unable to find address width in cell " << c.name << " defined at " << c.src);
	unsigned width = stoi((*mit).second);
	assert(width > 0);
	sort.args.push_back(SORT(width));

	mit = c.params.find("\\WIDTH");
	if (mit == c.params.end())
		yos_loge("unable to find width in cell " << c.name << " defined at " << c.src);
	unsigned size = stoi((*mit).second);
	assert(size > 0);
	sort.args.push_back(SORT(size));

	unsigned sz = size;
	assert(sz > 0);

	mit = c.params.find("\\MEMID");
	if (mit == c.params.end())
		yos_loge("unable to find memid in cell " << c.name << " defined at " << c.src);
	string portStr = (*mit).second;
	if (portStr.find("\\") == 0)
		portStr.erase(0, 2);

	Inst* pre;
	map < string, Inst* >::iterator sit = m_wire2sig.find(portStr);
	if (sit != m_wire2sig.end())
		pre = (*sit).second;
	else
		pre = SigInst::create(portStr, sz, sort);

	assert(pre->get_size() == sz);
	assert(pre->get_sort() == sort);

	switch (type) {
	case $meminit: {
		InstL args;
		Inst* init_val = m_wire2sig[c.connects["\\DATA"]];
		assert(init_val);
		assert(init_val->get_type() == Num);
		mpz_class* value = NumInst::as(init_val)->get_mpz();

		args.push_back(NumInst::create(width, 32));
		args.push_back(NumInst::create(size, 32));
		args.push_back(NumInst::create(*value, size));
		Inst* rhs = OpInst::create(OpInst::ArrayConst, args);
		initials.push_back(OpInst::create(OpInst::Eq, pre, rhs));
		map_init[pre] = rhs;
		assert (rhs->get_size() == pre->get_size());
		yos_log ("   $memrd: " << *pre << " -> " << *rhs << endl);
		if (value->get_ui() != 0)
			yos_logw("initializing memory to a non-zero value, in cell " << c.name << " defined at " << c.src);
	} break;
	case $memrd: {
		InstL args;
		args.push_back(pre);
		args.push_back(m_wire2sig[c.connects["\\ADDR"]]);

		Inst* rhs = OpInst::create(OpInst::ArraySelect, args);
		string en_str = c.connects["\\EN"];
		if (en_str != "1'x") {
			yos_logw("ignoring control signal in cell " << c.name << " defined at " << c.src);
//			Inst* en = process_expr(en_str);
//			en = ExInst::create(en, 0, 0);
//			if (en->get_size() != 1) {
//			}
		}
		Inst* out = m_wire2sig[c.connects["\\DATA"]];
		SigInst* out_sig = SigInst::as(out);
		assert(out_sig);
		assert (out->get_size() == size);
		map_net_op[out] = rhs;
		yos_log ("   $memrd: " << *out << " -> " << *rhs << endl);
	} break;
	case $memwr: {
		SigInst* sigPre = SigInst::as(pre);
		assert(sigPre);
		assert(sigPre->get_size() == sz);
		Inst* sigNext;
		string sigStr = sigPre->get_name();
		states[sigStr] = sigPre;
		sigStr += "$next";
		sigNext = SigInst::create(sigStr, sz, sort);
		assert(sigNext->get_size() == sz);
		assert(sigNext->get_sort() == sigPre->get_sort());
		Inst* inp;
		auto mit = map_net_op.find(sigNext);
		if (mit == map_net_op.end())
			inp = sigPre;
		else {
//			yos_logw("assuming each memory write is mutually exclusive");
//
//			Inst* ter = (*mit).second;
//			assert(ter->get_type() == Op);
//			assert(OpInst::as(ter)->get_op() == OpInst::Ternary);
//			InstL::const_iterator cit = ter->get_children()->begin();
//			cit++;
//			inp = (*cit);
			inp = (*mit).second;
		}
		InstL args;
		args.push_back(inp);
		args.push_back(m_wire2sig[c.connects["\\ADDR"]]);
		args.push_back(m_wire2sig[c.connects["\\DATA"]]);
		Inst* rhs = OpInst::create(OpInst::ArrayStore, args);
		string en_str = c.connects["\\EN"];
		if (en_str != "1'x") {
			Inst* en = process_expr(en_str);
			if (en->get_size() != 1) {
				yos_logw("ignoring higher order bits for control signal in cell " << c.name);
				en = ExInst::create(en, 0, 0);
			}
			rhs = OpInst::create(OpInst::Ternary, en, rhs, inp);
		}

		string clk_str = c.connects[get_clock_name(type)];
		if (clk_str != "1'x") {
			Inst* clk = m_wire2sig[clk_str];
			SigInst* sigClk = SigInst::as(clk);
			assert(sigClk);
			if (num_clock > 1) {
				rhs = OpInst::create(OpInst::Ternary, sigClk, rhs, sigPre);
				yos_logw("redundant clock muxes possible with multiple memory writes");
			}
		}

		map_net_op[sigNext] = rhs;
		map_inst_vinst[sigNext] = get_cell_name(c);
		next_states.push_back(sigNext);
		yos_log ("   $memwr: " << *sigNext << " -> " << *rhs << endl);
	} break;
	default:
		yos_loge("cell type " << c.type << " not supported. Found in cell defined at " << c.src);
		break;
	}
}

string IlangFrontend::get_clock_name(TypeHash type) {
	switch(type) {
	case $_DFF_P_:
	case $_DFF_N_:
		return "\\C";
	default:
		return "\\CLK";
	}
}

/**
 * Function for finding cell name from a cell
 */
string IlangFrontend::get_cell_name(Cell& c)
{
	return ("f_" + to_string(cid++));
//	return c.name;
}

/**
 * Function for parsing the input file and storing information in internal format
 */
bool IlangFrontend::read_design()
{
	_init();

	deque<string> tokens ;
	bool valid = read_line_as_tokens (is, tokens, false);
	while(valid)
	{
//		for (auto i = 0; i < tokens.size(); i++)
//		{
//			cout << "[" << i << "] " << tokens[i] << endl;
//		}

		if(tokens[0]== "attribute")
		{
			bool status = read_attribute(tokens);
			if (!status)	return false;
		}
		else if(tokens[0]== "wire")
		{
			bool status = read_wire(tokens);
			if (!status)	return false;
		}
		else if(tokens[0]== "cell")
		{
			bool status = read_cell(tokens);
			if (!status)	return false;
		}
		else if(tokens[0]== "connect")
		{
			bool status = read_connect_sig(tokens);
			if (!status)	return false;
		}
		else if(tokens[0]== "module")
		{
			// Do nothing
		}
		else if(tokens[0]== "end")
		{
			// Do nothing
		}
		else if(tokens[0]== "memory")
		{
			// Do nothing
		}
		else
		{
			yos_log("skipping line starting with unknown start keyword: " << tokens[0] << endl);
			// Do nothing
		}
		valid=read_line_as_tokens (is, tokens, false) ;
	}
	_close();
	return true;
}

/**
 * Function for processing attribute
 */
bool IlangFrontend::read_attribute(deque < string >& tokens)
{
//	log("Reading attribute" << endl);
	if (tokens[1] == "\\src")
	{
		assert(tokens.size() == 3);
		src = tokens[2];
	}
	else if (tokens[1] == "\\init")
	{
		assert(tokens.size() == 3);
		init = tokens[2];
	}
	return true;
}

/**
 * Function for processing wire
 */
bool IlangFrontend::read_wire(deque < string >& tokens)
{
//	log("Reading wire" << endl);
	wire w;
	w.src = src;
	w.init = init;

	src = "";
	init = "";

	int idx = 1;

	if (tokens[idx] == "width")
	{
		idx++;
		w.size = std::stoi(tokens[idx]);
		idx++;
	}
	else
	{
		w.size = 1;
	}

	int offset = -1;
	if (tokens[idx] == "offset")
	{
		idx++;
		offset = std::stoi(tokens[idx]);
		idx++;
		if (offset > 0)
		{
			yos_loge("offsets in wire not supported. Found in wire defined at " << w.src);
		}
	}

	if (tokens[idx] == "upto")
	{
		yos_loge("reversed wires not supported. Found in wire defined at " << w.src);
	}

	if (tokens[idx] == "input")
	{
		w.type = "input";
		idx += 2;
	}
	else if (tokens[idx] == "output")
	{
		w.type = "output";
		idx += 2;
	}

	w.name = tokens[idx];
	for (int i = (idx + 1); i < tokens.size(); i++)
		w.name += "_" + tokens[i];

	wires.push_back(w);

	if (offset != -1)
	{
		yos_logw ("ignoring offset for wire " << w.name);
		num_warnings++;
	}
//	print_wire(w);

	return true;
}

/**
 * Function for processing cell
 */
bool IlangFrontend::read_cell(deque < string >& tokens)
{
//	log("Reading cell" << endl);
	assert(tokens.size() == 3);

	Cell c;
	c.src = src;
	c.type = tokens[1];
	c.name = tokens[2];

	src = "";
	init = "";

	bool valid = read_line_as_tokens (is, tokens, false);
	while(valid)
	{
//		for (auto i = 0; i < tokens.size(); i++)
//		{
//			cout << "[" << i << "] " << tokens[i] << endl;
//		}

		if(tokens[0]== "parameter")
		{
			bool status = read_parameter(c, tokens);
			if (!status)	return false;
		}
		else if(tokens[0]== "connect")
		{
			bool status = read_connect(c, tokens);
			if (!status)	return false;
		}
		else if(tokens[0]== "end")
		{
			break;
		}
		else
		{
			assert(0);
		}
		valid=read_line_as_tokens (is, tokens, false) ;
	}
	assert(valid);
	cells.push_back(c);
//	print_cell(c);

	return true;
}

/**
 * Function for processing cell parameter
 */
bool IlangFrontend::read_parameter(Cell& cell, deque < string >& tokens)
{
//	log("Reading cell parameter" << endl);
	assert(tokens.size() == 3);
	cell.params[tokens[1]] = tokens[2];
	return true;
}

/**
 * Function for processing cell connection
 */
bool IlangFrontend::read_connect(Cell& cell, deque < string >& tokens)
{
//	log("Reading cell connect" << endl);

	string rhs = tokens[2];
	for (int i = 3; i < tokens.size(); i++)
		rhs += "," + tokens[i];
	cell.connects[tokens[1]] = rhs;
	if (tokens[1] == get_clock_name(cell.type) && !startsWith(rhs, "1'"))
		clock_names.insert(make_pair(rhs, rhs));
	return true;
}

/**
 * Function for processing wire connection
 */
bool IlangFrontend::read_connect_sig(deque < string >& tokens)
{
//	yos_log("Reading wire connect" << endl);

	Cell c;
	c.src = "global";
	c.type = "$_BUF_";
	c.name = "connect";

	string lhs = "";
	string rhs = "";
	bool onLhs = true;
	bool onCc = false;
	int i = 1;
	while (i < tokens.size()) {
		if (onLhs) {
			if (lhs == "") {
				lhs = tokens[i];
				if (tokens[i][0] == '{')
					onCc = true;
				else if (tokens[i + 1][0] == '[') {
					lhs += "," + tokens[i + 1];
					i++;
					onLhs = false;
				}
				else
					onLhs = false;
			}
			else if (onCc) {
				lhs += "," + tokens[i];
				if (tokens[i][tokens[i].size() - 1] == '}') {
					onCc = false;
					onLhs = false;
				}
			}
		}
		else {
			if (rhs == "")
				rhs = tokens[i];
			else
				rhs += "," + tokens[i];
			}
		i++;
	}
	c.connects["\\Y"] = lhs;
	c.connects["\\A"] = rhs;
	cells.push_back(c);

	if (clock_names.find(lhs) != clock_names.end()) {
		clock_union(lhs, rhs);
//		cout << "clk " << lhs << " " << clock_names[lhs] << " to " << rhs << " " << clock_names[rhs] << endl;
	}
	if (clock_names.find(rhs) != clock_names.end()) {
		clock_union(lhs, rhs);
//		cout << "clk " << lhs << " " << clock_names[lhs] << " to " << rhs << " " << clock_names[rhs] << endl;
	}


//	print_cell(c);
	return true;
}

// Naive implementation of find for clocks
string IlangFrontend::clock_find(string i)
{
	map< string, string >::iterator mit = clock_names.find(i);
	if (mit == clock_names.end()) {
  	clock_names[i] = i;
		return i;
  }
	else if ((*mit).second == i)
			return i;
	return clock_find(clock_names[i]);
}

// Naive implementation of union for clocks
void IlangFrontend::clock_union(string x, string y)
{
	string xset = clock_find(x);
	string yset = clock_find(y);
	clock_names[xset] = yset;
}

/**
 * Function for printing wire details
 */
void IlangFrontend::print_wire(wire& w)
{
	yos_log("  (wire)  t: " << w.type << " n: " << w.name << " sz: " << w.size << " src: " << w.src << " init: " << w.init << endl);
}

/**
 * Function for printing cell details
 */
void IlangFrontend::print_cell(Cell& c)
{
	yos_log("  (cell)  t: " << c.type << " n: " << c.name << " src: " << c.src << endl);
	for (auto& pi : c.params)
		yos_log("    param: " << pi.first << " v: " << pi.second << endl);
	for (auto& ci : c.connects)
		yos_log("    port: " << ci.first << " c: " << ci.second << endl);
}

/**
 * Function for initialization of parser
 */
void IlangParser::_init(void)
{
	for (int i=0; i < (int)sizeof(specialChars); ++i)
		specCharLibDir[specialChars[i]] = true;
	return;
}

/**
 * Function to close and free input file stream
 */
void IlangParser::_close(void)
{
//	free(is);
	is.close();
	return;
}

/**
 * \param is Input .ilang file stream
 * \param tokens Set of words in a line (separated by specified delimiters)
 * \param includeSpecialChars Flag to indicate if special characters to be included
 * \result Returns true if tokens is not empty
 *
 * Reads from the input stream and splits a line into a set of words separated by delimiters
 */
bool IlangParser::read_line_as_tokens (istream& is, deque<string>& tokens, bool includeSpecialChars )
{
	tokens.clear();
	string line;
	std::getline (is, line);

	while (is && tokens.empty())
	{
		string token = "" ;
		for (int i = 0; i < (int)line.size(); ++i)
		{
			char currChar = line[i];
			bool isSpecialChar = specCharLibDir[currChar];
			if (std::isspace (currChar) || isSpecialChar)
			{
				if (!token.empty())
				{
					// Add the current token to the list of tokens
					tokens.push_back(token);
					token.clear();
				}
				if (includeSpecialChars && isSpecialChar)
				{
					tokens.push_back(string(1, currChar));
				}
			}
			else
			{
				// Add the char to the current token
				token.push_back(currChar);
			}
		}
		if (!token.empty())
			tokens.push_back(token);

		// Previous line read was empty. Read the next one.
		if (tokens.empty())
			std::getline (is, line);
	}
	return !tokens.empty();
}


}

