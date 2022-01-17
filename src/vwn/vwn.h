/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


/*
 * vwn.h
 *
 *  Created on: Oct 11, 2016
 *      Author: rock
 */

#ifndef SRC_VWN_VWN_H_
#define SRC_VWN_VWN_H_

#include <algorithm>
#include <unordered_map>

#include "avr_config.h"
#include "avr_word_netlist.h"

#include "init_pass.h"
using namespace init;

#define PRINT_VWN_RESULTS true
#define MOVED_TO_DPA false

#define AVOID_LARGE_PRINTING


//	#define PROPERTY_DIRECTED_SPLIT
#define AVR_DUMP_DOT
#define L_MUXES_ERASE
//#define REPLACE_SHIFT_WITH_ADD
//#define REPLACE_SHIFT_WITH_MULT
//#define STUPID_CONCAT_SIMPL
//#define DEBUG_DUMP_MODEL
//#define DEBUG_DUMP_MODEL_USE_DOLLAR
//#define BUILD_STANDALONE

//#define BIT_LEVEL_AVR
#ifdef BIT_LEVEL_AVR
	#ifndef AVR_PARTIAL_BIT_BLAST
		#define AVR_PARTIAL_BIT_BLAST
	#endif
#endif


/// Frontends
#define ENABLE_YOS
//#define ENABLE_SAL
#define ENABLE_VMT
//#define ENABLE_JG
#define ENABLE_BTOR2


#ifdef ENABLE_YOS
	#include "ilang_frontend.h"
	using namespace yos;
#endif

#ifdef ENABLE_SAL
	#include "sal_frontend.h"
	using namespace sal;
#endif

#ifdef ENABLE_VMT
	#include "vmt_frontend.h"
	using namespace vmt;
#endif

#ifdef ENABLE_JG
	#include "wif_frontend.h"
	using namespace _wif;
#endif

#ifdef ENABLE_BTOR2
	#include "btor2_frontend.h"
	using namespace bt2;
#endif


using namespace std;

//#define DUMP_INFOS
// cout in connect_insts()
#define VWN_COUT_1(expr)	//cout << "[CV] " << expr;
// cout in derive_ITP()
#define VWN_COUT_2(expr)	//cout << "[ITP] " << expr;
// cout in write_wn()
#define VWN_COUT_3(expr)	//cout << "[WN] " << expr;
// dump I, T, P
#define VWN_COUT_ITP(expr)	//cout << expr;
// cout by Aman
//	#define VWN_COUT_A(expr)	cout << "[A] " << expr;
#define VWN_COUT_A(expr)	//cout << expr;
// cout by Aman for output
#define VWN_COUT_FILE(expr)	outFile << expr;

#define avr_logcerr(expr)	cerr << "\t(" << expr << ')' << endl;
#define avr_log(expr)	cout << "\t(" << expr << ')' << endl;
#define avr_logw(expr)	cout << "\t(warning: " << expr << ')' << endl;
#define avr_loge(expr)	cout << "\t(error: " << expr << ')' << endl; \
												assert(0);

#define AVR_WIRE_NAME_PREFIX "w$"
static int avr_wid = 0;

static Inst *ve_init;
static Inst *ve_model_nsf;
static Inst *ve_prop;
static Inst *ve_assume;

static int tsb = 0;
static int tsb_init = 0;

//static Config* config;

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
InstToInstM map_init;

//ofstream outFile;

InstToStringM gate_names; // map to remember internal signal name


void draw_graph(string fname, string sname, int depth);
void draw_cone(string fname, string sname);
void collect_cone(Inst *top, set<string> &s_reg_names, int& numCF, int& numUF, int& numEx, int& numCc, bool init_visit=false);

void compile_initial(bool allow_file_read);
void compile_transition(void);
void compile_property(void);
void compile_assumptions(void);

void derive_ITP(void);

//void print_header(void);
void print_summary(void);
void connect_all_instances(void);

InstToInstM transitions;
void finalize_ITP(void);

map<string, Inst*> states;// map<current-register-name, Inst*>

InstS inputs;// Stores all constants
InstS constants;// Stores all constants

#endif /* SRC_VWN_VWN_H_ */
