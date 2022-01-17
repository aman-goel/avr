/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


/*
 * init_pass.h
 *
 *  Created on: Nov 21, 2018
 *      Author: rock
 */

#ifndef SRC_VWN_INIT_PASS_H_
#define SRC_VWN_INIT_PASS_H_


#include <stdarg.h>
#include <string>
#include <iostream>
#include <vector>
#include <map>
#include <set>

#include <iostream>
#include <string>
#include <unordered_map>
#include <deque>
#include <algorithm>

// For Averroes
#include "avr_config.h"
#include "avr_word_netlist.h"


using namespace std;

extern int num_warnings;

extern map<string, Inst*> states;// map<current-register-name, Inst*>
extern InstS constants;// Stores all constants

extern 	map<string, Inst* > map_sig;

extern InstL next_states;

extern InstToInstM map_init;
extern Config* config;


namespace init
{

#define INIT_PREFIX1 "\\m"
#define INIT_PREFIX2 "\\"
#define INIT_SUFFIX ".out"

#define init_logcerr(expr)	cerr << "\t(" << expr << ')' << endl;
#define init_log(expr)	cout << expr;
#define init_logw(expr)	cout << "\t(warning: " << expr << ')' << endl;
#define init_loge(expr)	{cout << "\t(error: " << expr << ')' << endl; \
												 assert(0);}


class InitParser
{
public:
	void help();
	void execute();

	InitParser (string filename): is(filename.c_str()), filename(filename)
	{
	};

private:
	void print_init();
	void process_init();
	bool read_init();
	Inst* read_sig(deque < string >& tokens);
	Inst* read_num(deque < string >& tokens);

	void print_tokens(deque < string >& tokens);
	void _init(void);
	void _close (void);
	bool read_line_as_tokens (istream& is, deque < string >& tokens, bool includeSpecialChars = false );

	ifstream is;                   ///< Input .timing file stream
	string filename;

	static const char specialChars[];
	static std::unordered_map <char, bool> specCharLibDir;
} ;


}


#endif /* SRC_VWN_INIT_PASS_H_ */
