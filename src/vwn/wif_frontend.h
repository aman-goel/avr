/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


/*
 * wif_frontend.h
 *
 *  Created on: May 15, 2019
 *      Author: amangoel
 */

#ifndef SRC_VWN_WIF_FRONTEND_H_
#define SRC_VWN_WIF_FRONTEND_H_

#include "wif_parser.h"

// For Averroes
#include "avr_config.h"
#include "avr_word_netlist.h"

#include <unordered_map>


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

namespace _wif {

#define WIF_NAME_PREFIX "j$"
#define WIF_PROP_PREFIX config->get_arg(PROP_SIG_ARG)

class WifFrontend : public WifConvert {
  public:
	void help();
	void execute();

	WifFrontend(string filename, string options) : WifConvert(filename, options, config->get_arg(SELECT_PROPERTY)) { };

  private:
	void traverse_system();
	void print_system();

	Inst* traverse_node(WifNode& t);
	Inst* process_node(WifNode& t, InstL& args);
	void add_props(list < pair < string, Inst* > >& instP, list < pair < string, Inst* > >& outP);
	void add_assumes(InstL& instA);
	Inst* get_node(WifNode& t, InstL& args);
	string gate_name(WifNode& t);
	SORT get_node_type(WifNode& t);
	Inst* process_sig(WifNode& t, InstL& args, int sz, SORT sort);
	void process_delay();

	map< WifNode, Inst* > processed;
	set< WifNode > delay_nodes;
	unordered_map<Inst*, Inst*> state_next2pre;
};


}


#endif /* SRC_VWN_WIF_FRONTEND_H_ */
