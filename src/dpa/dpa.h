/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


/*
 * dpa.h
 *
 *  Created on: Oct 17, 2016
 *      Author: rock
 */

#ifndef SRC_DPA_DPA_H_
#define SRC_DPA_DPA_H_

#include <algorithm>

// For Averroes
#include "avr_config.h"
#include "avr_word_netlist.h"


#define PRINT_DPA_RESULTS true
#define PRINT_DESIGN true
#define MOVED_TO_DPA false

#ifdef AVR_SPLIT_SIGNALS
//	#define PROPERTY_DIRECTED_SPLIT
#endif

#define AVOID_LARGE_PRINTING

//#define AVR_SPLIT_SIGNALS
//#define AVR_PARTIAL_BIT_BLAST

#ifdef AVR_PARTIAL_BIT_BLAST
//#define REMOVE_UNNECESSARY_CONCAT
#endif


// the simplification routine in Inst::create() converts the concatenation of extraction
// into identity. This conflicts with the routines in partial bit-blast functions

#if 0
// TODO enable 1175
//#define PATCH_FOR_154
//#define PATCH_FOR_C17

#define AVR_PARTIAL_BIT_BLAST
#define AVR_SPLIT_SIGNALS

//#define BIT_LEVEL_AVR
#elif 0
//			correct BL_AVR
#define PATCH_FOR_BIT_LEVEL_AVR
#define AVR_PARTIAL_BIT_BLAST
#else
//			original AVR
//#define AVR_PARTIAL_BIT_BLAST
//#define AVR_SPLIT_SIGNALS
//#define BIT_LEVEL_AVR
#endif

//#define DEBUG_DERIVE_PBBS
#define AVR_DUMP_DOT
//#define SEL_BIT_BLAST
#define L_MUXES_ERASE

using namespace std;

#if 0
	//#define DUMP_INFOS
	// cout in connect_vexprs()
	#define VWN_COUT_1(expr)	cout << "[CV] " << expr;
	// cout in derive_ITP()
	#define VWN_COUT_2(expr)	cout << "[ITP] " << expr;
	// cout in write_wn()
	#define VWN_COUT_3(expr)	cout << "[WN] " << expr;
	// dump I, T, P
	#define VWN_COUT_ITP(expr)	//cout << expr;
#else
	//#define DUMP_INFOS
	// cout in connect_vexprs()
	#define VWN_COUT_1(expr)	//cout << "[CV] " << expr;
	// cout in derive_ITP()
	#define VWN_COUT_2(expr)	//cout << "[ITP] " << expr;
	// cout in write_wn()
	#define VWN_COUT_3(expr)	//cout << "[WN] " << expr;
	// dump I, T, P
	#define VWN_COUT_ITP(expr)	//cout << expr;
	// cout by Aman
	#define DPA_COUT_A(expr)	//cout << "[A] " << expr;
//	#define DPA_COUT_A(expr)	cout << expr;
	// cout by Aman for output
	#define DPA_COUT_FILE(expr)	outFile << expr;
#endif

#define NEXT_SUFFIX "$next"
#define NEXT_SUFFIX_LENGTH 5

static Inst *ve_init;
static Inst *ve_model_nsf;
static Inst *ve_prop;
static Inst *ve_assume;

static Config* config;

struct mux{
	Inst *data;
	Inst *sel;
	Inst *out;
	Inst *root_data;
};

// struct Inst_comp {
//   bool operator() (Inst* lhs, Inst* rhs)
//   {return lhs->get_id()<rhs->get_id();}
// };

static list<mux> l_muxes;
static InstS s_sels;
static InstS s_data;
static InstToInstM map_init;

void collect_nsfs(Inst *top, InstL &vel_nsfs, bool init_visit = false);
int check_term_type(Inst *top);
bool derive_euf_func_list_2(Inst *top, bool init_visit);

void collect_cone(Inst *top, set<string> &s_reg_names, int& numCF, int& numUF, int& numEx, int& numCc, bool init_visit = false);

bool collect_inputs(Inst *top, InstS& regs, bool init_visit = false);

//map<string, InstL> _func_list;
//InstToStringM map_inst_euf;
//InstToStringM map_inst_inst_type;

InstS _s_reg; // set of registers in the design, used to filter out inputs later
// a kind of a map of (state_var, simplified nsf of it)
InstToInstM _m_sn; // simplified next,

InstS constants;// Stores all constants
InstS inputs;// Stores all constants



#endif /* SRC_DPA_DPA_H_ */
