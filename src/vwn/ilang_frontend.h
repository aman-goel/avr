/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


/*
 * ilang_frontend.h
 *
 *  Created on: Jun 6, 2017
 *      Author: rock
 */

#ifndef SRC_VWN_ILANG_FRONTEND_H_
#define SRC_VWN_ILANG_FRONTEND_H_

#include "ilang_celltypes.h"

// For Averroes
#include "avr_config.h"
#include "avr_word_netlist.h"


using namespace std;

extern int num_warnings;

extern InstToInstM map_net_op;	// map_net_op[output] = input, was originally defined within derive_ITP()
extern InstL initials;
extern map<string, Inst*> states;// map<current-register-name, Inst*>
extern InstS constants;// Stores all constants

extern 	map<string, Inst* > map_sig;
/// Map to find if a signal is user defined
extern map<string, bool> map_sig_user_defined;

/// Map to get verific instance name from an Inst
extern InstToStringM map_inst_vinst;

extern InstToStringM gate_names; // map to remember internal signal name

extern InstL next_states;
extern Inst *prop_ve;
extern InstL properties;
extern InstL assumptions;

extern InstToInstM map_init;
extern ofstream _resFile;
extern Config* config;


namespace yos
{

/// To be enabled when bit-blasting used
//#define YOSYS_REPLACE_SHIFT_WITH_ADD


#define ZERO_EXTEND_OPERATIONS

#ifdef ZERO_EXTEND_OPERATIONS
//	#define OUTPUT_EXTEND_SHIFT_OPERATIONS
#endif

#define WIRE_NAME_PREFIX "s$"

/// Below flag asserts that only primary input(s) are treated as input, converts undriven wires to state vars.
//#define ALLOW_EXPLICIT_INPUTS_ONLY

//#define yos_loge(expr)	cout << expr;

#define yos_log(expr)	  //cout << expr;
#define yos_logw(expr)	cout << "\t(warning: " << expr << ')' << endl;
#define yos_loge(expr)	{cout << "\t(error: " << expr << ')' << endl; \
												 assert(0);}


class IlangParser
{
public:
	IlangParser (string filename): is(filename.c_str()), filename(filename)
	{
	};

protected:
	ifstream is;                   ///< Input .timing file stream
	string filename;

	void _init(void);
	void _close (void);
	bool read_line_as_tokens (istream& is, deque < string >& tokens, bool includeSpecialChars = false );

private:
	static const char specialChars[];
	static std::unordered_map <char, bool> specCharLibDir;
} ;

class wire
{
public:
	string name;
	int size;
	string src;
	string init;
	string type;

	wire()
	{
		name = "";
		size = 1;
		src  = "";
		init = "";
		type = "";
	}
};

class Cell
{
public:
	string name;
	string type;
	string src;

	map < string, string > params;
	map < string, string > connects;

	Cell()
	{
		name = "";
		type = "";
		src  = "";
		params.clear();
		connects.clear();
	}
};

class IlangFrontend : public IlangParser
{
public:
	void help();
	void execute();

	IlangFrontend(string filename) : IlangParser(filename) { num_clock = 0; };

private:
	static int wid;
	static int cid;

	int num_clock;
	string src;
	string init;

	map< string, string > clock_names;
	set <string> unique_clk;

	deque < wire > wires;
	deque < Cell > cells;

	map < string, Inst* > m_wire2sig;
#ifdef ALLOW_EXPLICIT_INPUTS_ONLY
	InstS s_inputs;
#endif
	PairUintToInstM m_inst2zextend;

	void print_design();

	void process_design();
	void process_wire(wire& w);
	string get_wire_name(wire& w);
	void process_cell(Cell& c);
	string get_cell_name(Cell& c);
	Inst* process_expr(string portStr);
	Inst* process_const(string portStr);
	Inst* process_concat(string portStr);
	Inst* process_extract(string portStr);
	string decimal2binary(long long num);
	Inst* zero_extend(Inst* tve, unsigned outSz);
	void process_memory(Cell& cell);

	void clock_union(string x, string y);
	string clock_find(string i);
	string get_clock_name(TypeHash type);
	string get_clock_name(string type) {
		map< string, TypeHash>::iterator type_it = m_hash.find(type);
		if (type_it == m_hash.end()) {
			cout << "type: " << type << endl;
		}
		assert (type_it != m_hash.end());
		return get_clock_name((*type_it).second);
	}

	bool read_design();
	bool read_attribute(deque < string >& tokens);
	bool read_wire(deque < string >& tokens);
	bool read_cell(deque < string >& tokens);
	bool read_parameter(Cell& cell, deque < string >& tokens);
	bool read_connect(Cell& cell, deque < string >& tokens);
	bool read_connect_sig(deque < string >& tokens);

	void print_wire(wire& wire);
	void print_cell(Cell& cell);
} ;


}


#endif /* SRC_VWN_ILANG_FRONTEND_H_ */
