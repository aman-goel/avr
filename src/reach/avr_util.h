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
#include <fstream>
#include <iomanip>

using namespace std;

//#define PERFORMANCE_NOPRINT

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

#define AVR_MAX INT32_MAX

extern string global_loc_tag[25];
extern int global_debug_level[25];

extern ofstream _outFile;
extern long long _totalTime;
extern int _numRefinements;

extern ofstream _resFile;
extern ofstream _refFile;
extern ofstream _expFile;
extern ofstream _prFile;

#ifdef PERFORMANCE_NOPRINT
#define AVR_REF(expr)
#else
#define AVR_REF(expr)\
	{\
		ostringstream str;\
		str << expr;\
		if (str.str().length() < 1000)\
		{\
			_refFile << expr;\
		}\
		else\
		{\
			_refFile << "\t(too large to print)" << endl;\
		}\
		str.clear();\
	}
#endif

//#define DUMP_SMT
#ifdef DUMP_SMT
	extern ofstream _smtFile;
	extern string _benchmark;
	extern bool _ufsHaveBool;
#endif

#ifdef ARM_RELEASE
	#define AVR_LOG(loc, level, expr) //
	#define AVR_LOG_NO_TAG(loc, level, expr) //
	#define AVR_COUT cout
#else
#ifdef DUMP_SMT
#define AVR_LOG(loc, level, expr)\
	if(global_debug_level[loc] & (1 << level))\
	{\
		if (loc == 16)\
		{\
			_smtFile << expr;\
		}\
		else if (loc != 15)\
		{\
			cout << "[" << global_loc_tag[loc] << "_" << level << "]    " << expr;\
		}\
		else\
		{\
			_outFile << expr;\
			cout << expr;\
		}\
	}
#else
#ifdef PERFORMANCE_NOPRINT
#define AVR_LOG(loc, level, expr)
#else
#define AVR_LOG(loc, level, expr)\
	if(global_debug_level[loc] & (1 << level))\
	{\
		if (loc != 15)\
		{\
			cout << "[" << global_loc_tag[loc] << "_" << level << "]    " << expr;\
		}\
		else\
		{\
			ostringstream str;\
			str << expr;\
			if (str.str().length() < 5000)\
			{\
				cout << expr;\
			}\
			else\
			{\
				cout << "\t(too large to print)" << endl;\
			}\
			str.clear();\
		}\
	}
#endif
#endif
//	ostringstream str;\
//	str << expr;\
//	{\
//		cout << expr;\
//	}\
//	str.clear();\
//	cout << expr;\

//		cout << "[" << global_loc_tag[loc] << "_" << level << "]    " << expr;

	#define AVR_LOG_NO_TAG(loc, level, expr)\
		if(global_debug_level[loc] & (1 << level))\
			cout << expr;
	#define AVR_COUT cout
#define AVR_FILE(expr)	outFile << expr;
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

struct TableFormat {
    int width;
    char fill;
    TableFormat(): width(12), fill(' ') {}
    template<typename T>
    TableFormat& operator<<(const T& data) {
        cout << data << setw(width) << setfill(fill);
        return *this;
    }
    TableFormat& operator<<(std::ostream&(*out)(std::ostream&)) {
        cout << out;
        return *this;
    }
};


template <typename T>
std::string to_string(const T& value) {
    std::stringstream ss;
    ss << value;
    return ss.str();
}


#define EXIT_HOLD				0
#define EXIT_VIOL				1
#define EXIT_HOLD_TRIV	2
#define EXIT_TIMEOUT		-1
#define EXIT_MEMOUT			-2
#define EXIT_ERROR			-3

#endif
