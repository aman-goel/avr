/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


/*
 * btor2_frontend.h
 *
 *  Created on: Sep 3, 2019
 *      Author: rock
 */

#ifndef SRC_VWN_BTOR2_FRONTEND_H_
#define SRC_VWN_BTOR2_FRONTEND_H_


#include "btor2_parser.h"

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

namespace bt2
{

#define BTOR2_NAME_PREFIX "b$"
#define BTOR2_PROP_PREFIX config->get_arg(PROP_SIG_ARG)



struct NODE_INFO {
	int64_t id;
	Inst* node;

	NODE_INFO() {
		node = NULL;
	}
};

inline std::ostream &operator<<(std::ostream &out, NODE_INFO &l) {
	if (l.node != NULL)
//		out << "inst: " << *l.node << '\t' << l.name << '\n';
		out << "inst: " << *l.node << '\n';
	else
		out << "inst: " << "??" << '\t' << "id: " << l.id << '\n';
	return out;
}


class Btor2Frontend : public Btor2_Parser
{
public:
	void help();
	void execute();

	Btor2Frontend(string filename) : Btor2_Parser(filename) { };

private:
	void reset();
	void print_system();
	void traverse_system();
	void post_process();
	Inst* traverse_node(int64_t nid);
	Inst* traverse_bad(int64_t nid);
	Inst* process_node(Btor2Line& t, InstL& args);
  void get_node(NODE_INFO& info, InstL& args);
  Inst* get_state(Btor2Line& t, int sz, SORT sort);
  Inst* get_input(Btor2Line& t, int sz, SORT sort);
  Inst* get_init(Btor2Line& t, int sz, SORT sort, InstL& args);
  Inst* get_next(Btor2Line& t, int sz, SORT sort, InstL& args);
  Inst* get_bad(Btor2Line& t, int sz, SORT sort, InstL& args);
  Inst* get_constraint(Btor2Line& t, int sz, SORT sort, InstL& args);
  Inst* get_output(Btor2Line& t, InstL& args);

  Btor2Line& get_line(int64_t id);
  string print_id(int64_t id);
  SORT get_node_type(int64_t sid);
  string gate_name(Btor2Line& t);
  void sanitize_name(string& n);
  Inst* extend(Inst* v, int value, int amount);

  list < int64_t > nodeList;
  map< int64_t, Btor2Line > id2line;
  map< int64_t, SORT > id2sort;
  map< int64_t, Inst* > processed;
	unordered_map<Inst*, Inst*> state_next2pre;
} ;


}



#endif /* SRC_VWN_BTOR2_FRONTEND_H_ */
