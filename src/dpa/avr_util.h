/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


#ifndef AVERROES_FLOW_UTILS_H__
#define AVERROES_FLOW_UTILS_H__

/* 
   utils.h
   Common utilities used in implementations
*/

#include <cassert>
#include <string>
#include <sstream>
#include <iostream>
#include <cmath>
#include <iostream>
#include <cstdlib>
#include <sys/time.h>
#include <sys/resource.h>

#include <iomanip>

using namespace std;

//TODO use inline function instead of MACRO
//verbosity
//0123456 <= debug loc
//default format:			11111111
// 									print level 0 and 1
//alternative format:	11000000 11000000 11000000 11000000 11000000 11000000 11000000 11000000
// 									print level 0 and 1
//	ex. to enable 0, 1, 3, put 11010000 to the debug level of a specific location

//	debug level (bit position)
//  0: minimal information (such as prop holds or not)
//	1: flow indication ( extending a frame, forward or backward propagation begins)
//	2: execution time
//	3: important cubes
//	4: less important cubes
//	5: dump formulas, csf, nsf, init, ...
//	6: intermediate data during the computation
//	7: temporary debugging info

//	debug level for "CONF", "SOLV", and "WN"
//  0: error
//  1: warning
//  2: info
//  3: debug

//	debug loc
//	0: pre processing
//	1: prop solve
//	2: block
//	3: forward propagation
//	4: data-path refinement
//	5: derive_ccext
//	6: ccext_block
//	7: containment_check
//	8: post processing
//	9: eval_formula, eval_term

extern string global_loc_tag[20];
extern int global_debug_level[20];

#ifdef ARM_RELEASE
	#define AVR_LOG(loc, level, expr) //
	#define AVR_LOG_NO_TAG(loc, level, expr) //
	#define AVR_COUT cout
#else
	#define AVR_LOG(loc, level, expr)\
		if(global_debug_level[loc] & (1 << level))\
			cout << "[" << global_loc_tag[loc] << "_" << level << "]    " << expr;

	#define AVR_LOG_NO_TAG(loc, level, expr)\
		if(global_debug_level[loc] & (1 << level))\
			cout << expr;
	#define AVR_COUT cout
#endif

#define INT32_MAX (2147483647)

double log_bell_number(int n);

long long Timevaldiff(struct timeval *starttime, struct timeval *finishtime);

string get_path_from_fname(string);
string remove_path_from_fname(string);

template <class F>
bool access_file(F& f,string s,bool fail_if_not_found = true){
	string name = s;
	f.open(name.c_str());
	if(!f.good()){
		AVR_COUT << "Could not access file: " << name << endl;
		if(fail_if_not_found)
			assert(0);
	}
	return f.good();
}


#endif
