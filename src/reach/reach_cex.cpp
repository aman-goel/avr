/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


/*
 * reach_cex.cpp
 *
 *  Created on: Sep 21, 2018
 *      Author: rock
 */

#include "reach_cex.h"

namespace reach
{

InstToIntM CEX::m_instId = InstToIntM();

void CEX::add (int st, Inst* inp, Inst* con, bool isinput) {
	CEX_NODE c;
	c.step = st;
	c.input = inp;
	c.constant = con;
	c.isinput = isinput;
	cex.push_back(c);
}

void CEX::reset () {
	cex.clear();
	CEX::m_instId.clear();
}

void CEX::print (ofstream& out, int length, InstL& propList) {
	vector < pair< InstToMpzM, InstToMpzM> > statev;
	statev.resize(length+1);

	out << "sat" << "\n";
	out << "b" << get_bad_id(propList) << "\n";
	for (auto& c: cex) {
		int idx = c.step;
		if (backward)
			idx = (length - c.step - 1);
		assert(idx >= 0);
		assert(idx <= length);
		c.isinput &= is_input(c.input);

		InstToMpzM::iterator mit;
		if (c.isinput) {
			mit = statev[idx].first.find(c.input);
			if (mit != statev[idx].first.end()) {
				AVR_LOG(8, 0, "(warning: cex repeated value for input: " << *c.input << ")" << endl);
			}
		}
		else {
			mit = statev[idx].second.find(c.input);
			if (mit != statev[idx].second.end()) {
				AVR_LOG(8, 0, "(warning: cex repeated value for state: " << *c.input << ")" << endl);
			}
		}

		if (c.isinput) {
			if (length != 0) {
				ConstInst* con = ConstInst::as(c.constant);
				assert(con);
			}
		}

		if (c.constant->get_size() != 1) {
			mpz_class* val = c.constant->get_ival();
			if (val != INVALID_SMPZ) {
				if (c.isinput)
					statev[idx].first[c.input] = *val;
				else
					statev[idx].second[c.input] = *val;
			}
			else {
				AVR_LOG(8, 0, "(warning: cex unexpected value for constant: " << *c.constant <<  " (value ptr: " << val << "))" << endl);
			}
		}
		else {
			int val = c.constant->get_bval();
			if (val == 1) {
				if (c.isinput)
					statev[idx].first[c.input] =  mpz_class("1", 10);
				else
					statev[idx].second[c.input] =  mpz_class("1", 10);
			}
			else if (val == 0) {
				if (c.isinput)
					statev[idx].first[c.input] =  mpz_class("0", 10);
				else
					statev[idx].second[c.input] =  mpz_class("0", 10);
			}
			else {
				AVR_LOG(8, 0, "(warning: cex unexpected value for constant: " << *c.constant <<  " (value: " << val << "))" << endl);
			}
		}
	}

//	out << "Length: " << length << "\n\n";
	for (int i = 0; i <= length; i++) {
		if (i == 0)
		{
			process_step(out, statev[i].second, i, false);
//			out << "#" << i << "\n";
//			for (auto& m: statev[i].second) {
//				out << get_id(m.first) << " " << get_string(m.first, m.second) << " |" << *(m.first) << "|#" << i << "\n";
//			}
		}
		process_step(out, statev[i].first, i, true);
//		out << "@" << i << "\n";
//		for (auto& m: statev[i].first) {
//			out << get_id(m.first) << " " << get_string(m.first, m.second) << " |" << *(m.first) << "|@" << i << "\n";
//		}
	}
	out << "." << "\n";
}

void CEX::process_step(ofstream& out, InstToMpzM& inMap, int idx, bool isinput) {
	string label = "@";
	if (!isinput)
		label = "#";
	out << label << idx << "\n";

	map < int, list < pair < string, string > > > idMap;
	for (auto& m: inMap) {
		int id = get_id(m.first);
		string val = get_string(m.first, m.second);
		ostringstream tmp;
		tmp << *(m.first);
		string name = tmp.str();

		if (m.first->get_sort_type() == arraytype) {
			SORT* d = m.first->get_sort_domain();
			SORT* r = m.first->get_sort_range();
			assert(d->type == bvtype);
			assert(r->type == bvtype);
			int width = d->sz;
			int size = r->sz;
			int maxaddress = pow(2, width) - 1;
			for (int i = maxaddress; i >= 0; i--) {
				string data_str = val.substr(i*size, size);
				Inst* address = NumInst::create(maxaddress - i, width, SORT());
				mpz_class* valn = NumInst::as(address)->get_mpz();
				string addr_str = get_string(address, *valn);

				idMap[id].push_back(make_pair(name, "[" + addr_str + "] " + data_str));
			}
		}
		else
			idMap[id].push_back(make_pair(name, val));
	}
	for (auto& m: idMap) {
		int id = m.first;
		list < pair < string, string > >& rhs = m.second;
		if (id < 0 || rhs.size() == 1) {
			for (auto& entry: rhs)
				out << id << " " << entry.second << " |" << entry.first << "|" << label << idx << "\n";
		}
		else {
			assert (rhs.size() > 1);
			string name = rhs.front().first;
			int sz = -1;

			int pos = name.find_last_of("[");
			if (pos == string::npos) {
				for (auto& entry: rhs)
					out << id << " " << entry.second << " |" << entry.first << "|" << label << idx << "\n";
				continue;
			}

			string prefix = name.substr(0, pos - 1);

			pos = prefix.find_last_of("$");
			assert (pos != string::npos);
			sz = stoi(prefix.substr(pos+1));
			string signame = prefix.substr(0, pos);
			assert(sz > 0);

//			out << "prefix: " << prefix << " of sz " << sz << " with sig name " << signame << endl;
			string val(sz, '0');

			for (auto& entry: rhs) {
				string lhs = entry.first;
				string rhs = entry.second;
				pos = lhs.find_first_of(prefix);
				assert(pos == 0);

				string suffix = lhs.substr(pos + prefix.length() + 1);
				assert(suffix.length() > 0);
				assert(suffix[0] == '[');
				assert(suffix[suffix.length() - 1] == ']');
				suffix = suffix.substr(1, suffix.length() - 2);

				pos = suffix.find_first_of(":");
				int hi = stoi(suffix.substr(0, pos));
				int lo = stoi(suffix.substr(pos + 1));
				assert(hi < sz);
				assert(lo >= 0);
				assert(hi >= lo);

				int j = 0;
				for (int i = hi; i >= lo; i--, j++) {
					val[sz - i - 1] = rhs[j];
				}
//				out << "suffix: " << suffix << " hi: " << hi << " lo: " << lo << " rhs: " << rhs << " val: " << val << endl;
			}

			out << id << " " << val << " |" << signame << "|" << label << idx << "\n";
		}
	}
}

string CEX::get_string (Inst* lhs, mpz_class& val) {
	string s = val.get_str(2);
	str_extend(s, lhs->get_size());
	return s;
}

void CEX::str_extend (string& s, int sz) {
	int insz = s.length();
	for (int i = insz; i < sz; i++) {
		s = "0" + s;
	}
}

bool CEX::is_input(Inst* v) {
	SigInst* sig = SigInst::as(v);
	if (sig) {
		string name = sig->get_name();
		if (name.length() > 3) {
			if (name[0] == '_' && name[1] == 'i') {
				return true;
			}
		}
		if (Inst::_s_inp.find(sig) != Inst::_s_inp.end()) {
			return true;
		}
	}
	return false;
}

int CEX::get_id(Inst* v) {
	InstToIntM::iterator mit = m_instId.find(v);
	if (mit != m_instId.end())
		return (*mit).second;

	int res = -1;
	string name = "";
	SigInst* sig = SigInst::as(v);
	if (sig)
		name = sig->get_name();
	else {
		WireInst* w = WireInst::as(v);
		if (w)
			name = w->get_name();
	}
	if (name.length() > 3) {
		if (name[0] == '_') {
			string namesub = name.substr(2);
			int pos2 = namesub.find_first_of("_");
			namesub = namesub.substr(0, pos2);

			int pos = name.find_first_of("0123456789");
			if (pos != string::npos) {
				res = stoi(name.substr(pos));
			}
		}
	}
	m_instId[v] = res;
	return res;
}

bool CEX::is_failing(Inst* p, int valrhs) {
	int val = p->get_bval();
//	cout << "prop: " << *p << "\t" << val << endl;
	return (val == valrhs);
}

int CEX::get_bad_id(Inst* p) {
	if (p->find_next())
		p = Inst::all_next2pre(p);

	OpInst* op = OpInst::as(p);
	if (op) {
		Inst* w = op->get_wire();
		if (w != NULL)
			p = w;
	}
	int ret = get_id(p);
//	cout << "wire: " << *p << "\t" << ret << endl;
	return ret;
}

int CEX::get_bad_id(InstL& propList) {
	int ret = 0;
	if (propList.size() == 0)
		return 0;
	for (auto& p: propList) {
		bool failed = is_failing(p, 0);
		if (!failed) {
			Inst* pn = OpInst::create(OpInst::LogNot, p);
			failed = is_failing(pn, 1);
		}
		if (failed) {
			int id = get_bad_id(p);
//			cout << "id: " << *p << "\t" << id << endl;
			if (id != -1) {
				ret = id;
				break;
			}
		}
	}
	return ret;
}

}


