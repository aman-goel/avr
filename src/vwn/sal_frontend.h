/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


/*
 * sal_frontend.h
 *
 *  Created on: Sep 4, 2017
 *      Author: rock
 */

#ifndef SRC_VWN_SAL_FRONTEND_H_
#define SRC_VWN_SAL_FRONTEND_H_

#include <iostream>
#include <string>
#include <deque>

#include "eufabs_parser.hpp"
#include "sal_def.h"


extern InstS constants;// Stores all constants
extern map<string, Inst*> states;// map<current-register-name, Inst*>
extern InstS inputs;// Stores all constants

extern InstToInstM map_init;
extern InstL properties;
extern InstToInstM map_net_op;	// map_net_op[output] = input, was originally defined within derive_ITP()
extern InstL next_states;
extern Inst* prop_ve;
extern InstToStringM gate_names; // map to remember internal signal name

namespace sal
{

using namespace std;
using namespace eufabs;

class SalParser : public eufabs_parser
{
public:
	SalParser (string filename): eufabs_parser(filename), filename(filename)
	{
		_init();
	};

protected:
	string filename;

	void _init(void);

private:
} ;

class SalFrontend : public SalParser
{
public:
	void help();
	void execute();

	SalFrontend(string filename) : SalParser(filename)
	{
		set_keys();
	};

private:
	typedef enum {
		$underscore,
		$bitvec,
		$bool,
		$eq,
		$unknown
	} Sal_keyword;

	unordered_map<std::string, Sal_keyword> keyHash; // maps string keyword to Keyword
    map<string, Inst*> sal_nodes;

    map<string, Inst*> sal_constants;
    map<string, Inst*> sal_states;
    map<string, Inst*> sal_inputs;
    map<string, Inst*> sal_gates;

    InstToInstM sal_initial;
    InstToInstM sal_transition;
    list<Inst*> sal_property;

    static const string bv;
    static const string next;
    static CellTypes cell_factory;

	void post_process();
	void print_design();
	void process_design();

	void process_constant(const sexpr& s);
	void process_state(const sexpr& s);
	void process_input(const sexpr& s);
	void process_gate(const sexpr& s);
	void process_next(const sexpr& s);
	void process_init(const sexpr& s);
	void process_property(const sexpr& s);

	Inst* process_expression(const sexpr& s, int outSz);
	int read_size(const sexpr& s);
	void force_new(const string& name, const sexpr& s);
	int get_input_size(CellType& cell, int outSz);

	void set_keys(void);
	Sal_keyword get_key(string keyword);
} ;


}

#endif /* SRC_VWN_SAL_FRONTEND_H_ */
