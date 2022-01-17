/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


/*
 * vmt_parser.h
 *
 *  Created on: Sep 29, 2018
 *      Author: rock
 */

#ifndef SRC_VWN_VMT_FRONTEND_H_
#define SRC_VWN_VMT_FRONTEND_H_

#include "vmt_parser.h"

// For Averroes
#include "avr_config.h"
#include "avr_word_netlist.h"

extern InstS constants;// Stores all constants
extern map<string, Inst*> states;// map<current-register-name, Inst*>
extern InstS inputs;// Stores all constants

extern InstToInstM map_init;
extern InstL properties;
extern InstL assumptions;
extern InstToInstM map_net_op;	// map_net_op[output] = input, was originally defined within derive_ITP()
extern InstL next_states;
extern Inst* prop_ve;
extern InstToStringM gate_names; // map to remember internal signal name

extern Config* config;

namespace vmt
{

#define VMT_NAME_PREFIX "v$"
#define VMT_PROP_PREFIX config->get_arg(PROP_SIG_ARG)



struct NODE_INFO {
	msat_term term;
	msat_symbol_tag tag;
	Inst* node;

	NODE_INFO() {
		tag = MSAT_TAG_ERROR;
		node = NULL;
	}
};

inline std::ostream &operator<<(std::ostream &out, NODE_INFO &l) {
	if (l.node != NULL)
//		out << "inst: " << *l.node << '\t' << l.name << '\n';
		out << "inst: " << *l.node << '\n';
	else
		out << "inst: " << "??" << '\t' << "tag:" << l.tag << '\n';
	return out;
}


struct TRANS_DATA {
	InstL cond;
	InstL cond_rem;
	InstToInstM t;

	TRANS_DATA() {
		cond.clear();
		cond_rem.clear();
		t.clear();
	}
	void swap(TRANS_DATA& lhs, TRANS_DATA& rhs) {
		std::swap(lhs.cond, rhs.cond);
		std::swap(lhs.cond_rem, rhs.cond_rem);
		std::swap(lhs.t, rhs.t);
	}
};

class VmtFrontend : public MsatParser
{
public:
	void help();
	void execute();

	VmtFrontend(string filename) : MsatParser(filename) { };

private:
	void print_system();
	void traverse_system();
	Inst* traverse_node(msat_term t);
	Inst* process_node(msat_term t, InstL& args);
  void get_node(NODE_INFO& info, InstL& args);
  SORT get_node_type(msat_type& type);
  Inst* process_sig(NODE_INFO& info, int sz, SORT sort);
  string gate_name(msat_term t);
  void sanitize_name(string& n);
  void add_inits(Inst* instI);
  void add_trans(Inst* instT);
  void add_props(InstL& instP);
  void flatten_and_init(Inst* inst, InstToInstM& l);
  void flatten_and_trans(Inst* inst, TRANS_DATA& l, InstL& ndone);
  void flatten_or(Inst* inst, InstL& l);
  void flatten_and(Inst* inst, InstL& l);
  void collect_next_sigs(Inst* inst, InstS& l, bool init_visit);
  Inst* substitute(Inst* ve, InstToInstM& m, InstToInstM& cache);

  map< msat_term, Inst* > processed;
  unordered_map<Inst*, Inst*> state_next2pre;
} ;


}



#endif /* SRC_VWN_VMT_FRONTEND_H_ */
