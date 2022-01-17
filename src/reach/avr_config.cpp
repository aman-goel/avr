/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


#include "avr_config.h"

#include <fstream>
#include <sstream>
#include <cstdlib>

using namespace std;

bool Config::g_random = false;
int Config::g_ab_granularity = 0;
int Config::g_interpret_uf_max_width = 0;
int Config::g_minimize_inv_effort = 0;
string Config::g_abstraction_name = "";
int Config::g_interpolation = 0;
int Config::g_forward_check = 0;
int Config::g_fineness = 0;
int Config::g_lazy_assume = 0;

bool Config::g_uf_unordered = false;
bool Config::g_uf_mult_only = false;
bool Config::g_uf_no_bitwise = false;
bool Config::g_uf_no_sext = false;
bool Config::g_uf_no_shift = false;
string Config::g_print_dot = "0000000";
bool Config::g_print_witness = false;

bool Config::g_ab_interpret = false;
int Config::g_ab_interpret_limit = 0;
int Config::g_ab_interpret_excc = 0;
int Config::g_correctness_check = 1;

bool Config::g_bmc_en = false;
int Config::g_bmc_max_bound = 0;

bool Config::g_kind_en = false;

string Config::g_verbosity = "0";

bool Config::read_arg(ifstream&f,char*arg){
	while(f.getline(arg,2048)){
		string a = arg;
		if(a=="")
			continue;
		if(a.substr(0,2)=="//")
			continue;
		return true;
	}
	return false;
}

void Config::load_args(bool picky){
	
	// New arguments
#ifdef RANDOMNESS
	args.insert(make_pair(EN_RANDOM,make_pair("True",0)));
#else
	args.insert(make_pair(EN_RANDOM,make_pair("False",0)));
#endif
#ifdef ALLOW_INPUTS
	args.insert(make_pair(AB_GRANULARITY,make_pair("True",0)));
#else
	args.insert(make_pair(AB_GRANULARITY_ARG,make_pair(to_string(AB_GRANULARITY_DEFAULT),0)));
#endif
	args.insert(make_pair(EN_INTERPRET_UF_MAX_WIDTH,make_pair(to_string(INTERPRET_UF_MAX_WIDTH),0)));
	args.insert(make_pair(MININV_EFFORT,make_pair(to_string(MININV_DEFAULT),0)));
	args.insert(make_pair(ABSTRACTION_TYPE,make_pair(DEFAULT_ABSTRACT,0)));
	args.insert(make_pair(INTERPOLATION_ARG,make_pair(to_string(INTERPOLATION_DEFAULT),0)));
	args.insert(make_pair(FORWARDCHECK_ARG,make_pair(to_string(FORWARDCHECK_DEFAULT),0)));
	args.insert(make_pair(FINENESS_ARG,make_pair(to_string(FINENESS_DEFAULT),0)));
	args.insert(make_pair(LAZY_ASSUME_ARG,make_pair(to_string(LAZY_ASSUME_DEFAULT),0)));
	args.insert(make_pair(PRINT_SMT2_DESIGN,make_pair("False",0)));
	args.insert(make_pair(PRINT_WITNESS,make_pair("False",0)));
	args.insert(make_pair(PRINT_DOT,make_pair("0000000",0)));
	args.insert(make_pair(VERBOSITY,make_pair("0",0)));
	args.insert(make_pair(BMC_EN,make_pair("False",0)));
	args.insert(make_pair(KIND_EN,make_pair("False",0)));
	args.insert(make_pair(BMC_MAX_BOUND,make_pair(to_string(BMC_MAX_BOUND_DEFAULT),0)));


	// define "expectation" (mandatory/not, default value, etc.) for all the arguments.
	args.insert(make_pair(CLOCK_SIG_ARG,make_pair("",0)));
	args.insert(make_pair(CLOCK_MODEL_ARG,make_pair(CONFIG_INIT0_OSCILLATING,0)));
	args.insert(make_pair(TOP_MODULE_ARG,make_pair("",0)));  
	args.insert(make_pair(DESIGN_ARG,make_pair("",1)));  
	args.insert(make_pair(DESIGN_T_ARG,make_pair(CONFIG_VERILOG,0)));  
	args.insert(make_pair(PROP_ARG,make_pair("",0))); 
	args.insert(make_pair(PROP_T_ARG,make_pair(CONFIG_VERILOG,0)));  
	args.insert(make_pair(AUX_F_ARG,make_pair("",0)));  
	args.insert(make_pair(PROP_CYCLE_ARG,make_pair("",0)));  
	args.insert(make_pair(PROP_SIG_ARG,make_pair("property",0)));
	args.insert(make_pair(ALG_T_ARG,make_pair(CONFIG_AR,0)));
	args.insert(make_pair(ABST_MIN_T_ARG,make_pair(CONFIG_NONE,0)));
	args.insert(make_pair(CONC_MIN_T_ARG,make_pair(CONFIG_ALL_MUSES,0)));
	args.insert(make_pair(VERB_ARG,make_pair("1",0)));
	args.insert(make_pair(DUMP_MODEL_ARG,make_pair("",0)));
	args.insert(make_pair(DUMP_VIOL_ARG,make_pair("",0)));
	args.insert(make_pair(DUMP_REF_ARG,make_pair("",0)));
	args.insert(make_pair(DUMP_STATS_ARG,make_pair("",0)));
	args.insert(make_pair(INT_DEB_ARG,make_pair("0",0)));
	args.insert(make_pair(TRACE_SIGS_ARG,make_pair("",0)));
	args.insert(make_pair(SIM_SIGS_ARG,make_pair("",0)));
	args.insert(make_pair(MEM_MAP_ARG,make_pair("",0)));
	//  args.insert(make_pair(ABST_SOLVER_ARG,make_pair(CONFIG_YICES,0)));  
	args.insert(make_pair(ABST_SOLVER_ARG,make_pair(CONFIG_YICES_API,0)));  
	
	args.insert(make_pair(AVR_MEM_LIMIT_ARG,make_pair("0",0)));
	args.insert(make_pair(AVR_TIMEOUT_ARG,make_pair("0",0)));
	args.insert(make_pair(AVR_TO_CONCRETIZE_ARG,make_pair("none",0)));
	args.insert(make_pair(DUMP_DOT_ARG,make_pair("none",0)));
	args.insert(make_pair(DUMP_DOT_DEPTH_ARG,make_pair("0",0)));
	
	args.insert(make_pair(AVR_VERB_ARG,make_pair("0000000000",0)));
//	args.insert(make_pair(AVR_VERB_ARG,make_pair("11111111",0)));
	args.insert(make_pair(AVR_PROP_TIMEOUT_ARG,make_pair("0",0)));
	args.insert(make_pair(AVR_REACH_TIMEOUT_ARG,make_pair("0",0)));
	args.insert(make_pair(AVR_CORR_REGS_ARG,make_pair("off",0)));

	/// Aman - Below mode removed in Averroes 2.1
	args.insert(make_pair(AVR_NUM_REACH_SOLVER,make_pair("20",0)));
	/// END

	// AVR_DERIVE_EQ_MODE is a three digit integer, "abc"
	// a : 0 if no ordering, 1 if term -> bit ordering, 2 if bit -> term ordering
	// b : 1 if COI analysis is enabled
	// c : 1 if init comparison is enabled
	// For example, 210 means that bit-> term ordering with COI enabled
	args.insert(make_pair(AVR_DERIVE_EQ_MODE,make_pair("010",0)));
	// AVR_NEW_CLT_MODE = new_clt_mode
	// 0 : non calypto benchmarks
	// 1 : calypto default	- turn on partitioning and partial bitblasting
	// 2 : 154 series
	// 3 : c17 series
	args.insert(make_pair(AVR_NEW_CLT_MODE,make_pair("0",0)));
	
	args.insert(make_pair(ABST_LOGIC_ARG,make_pair(CONFIG_EUF,0)));  
	args.insert(make_pair(EXPERIMENT_ARG,make_pair("0",0)));
	args.insert(make_pair(EXPERIMENT_COI_ARG,make_pair("0",0)));
	args.insert(make_pair(CAMUS_TIMEOUT_ARG,make_pair("0",0)));
	args.insert(make_pair(CAMUS_GROUPS_ARG,make_pair("0",0)));
	args.insert(make_pair(CAMUS_GROUP_SIZE_ARG,make_pair("0",0)));
	args.insert(make_pair(CAMUS_MAX_MUSES_ARG,make_pair("200",0)));
	args.insert(make_pair(VARS_ABST_ARG,make_pair(CONFIG_INTS,0)));
	args.insert(make_pair(DUMP_DESIGN_MODELING_ARG,make_pair("",0)));
	args.insert(make_pair(DUMP_CEX_ARG,make_pair("",0)));
	args.insert(make_pair(TRUNCATE_RHS_ARG,make_pair("1",0)));
	args.insert(make_pair(EXTEND_RHS_ARG,make_pair("1",0)));
	args.insert(make_pair(ABST_BOUND_ARG,make_pair("0",0)));
	args.insert(make_pair(DUMP_DESIGN_WN_ARG,make_pair("",0)));
	
	args.insert(make_pair(DUMP_BLIF_ARG,make_pair("off",0)));
//	args.insert(make_pair(DUMP_BLIF_ARG,make_pair("on",0)));
	
	args.insert(make_pair(MAX_ITER_ARG,make_pair("0",0)));
	args.insert(make_pair(SIM_SIMPL_ARG,make_pair(CONFIG_ON,0)));
	args.insert(make_pair(DUMP_INIT_FORMULA_VERILOG_ARG,make_pair("",0)));
	args.insert(make_pair(DUMP_FINAL_FORMULA_VERILOG_ARG,make_pair("",0)));
	args.insert(make_pair(DUMP_INIT_FORMULA_UCLID_ARG,make_pair("",0)));
	args.insert(make_pair(DUMP_FINAL_FORMULA_UCLID_ARG,make_pair("",0)));
	args.insert(make_pair(LEMMA_DB_ARG,make_pair("",0)));
	#ifndef LIMITED_RELEASE1
	args.insert(make_pair(INTPD_CONCAT_EXTRACT_ARG,make_pair("",0)));
	args.insert(make_pair(INTPD_ALL_ARG,make_pair("",0)));
	args.insert(make_pair(REF_TYPE_ARG,make_pair(CONFIG_REF,0)));
	args.insert(make_pair(TEMPLATES_ARG,make_pair("0",0)));
	args.insert(make_pair(EXT_BV_SOLVER_ARG,make_pair("",0)));
	args.insert(make_pair(SHOW_CEX_ARG,make_pair("1",0)));
	args.insert(make_pair(UBADD_ARG,make_pair("0",0)));
	#endif
	
	ifstream config_f;
	access_file(config_f, working_dir + "/" + CONFIG_FILE_NAME);
	
	char arg[2048];
	while(read_arg(config_f,&arg[0])){
		string param = arg;
#ifndef ARM_RELEASE
		if(args.find(param)==args.end()){
//			cout<<"SKIP unknown argument "<<param<<" in config file!"<<endl;
//			continue;

//			AVR_COUT <<"Skipping unknown argument "<<param<<" in config file!"<<endl;

//			AVR_COUT <<"The allowed arguments are:"<<endl;
//			for(Args::iterator it = args.begin() , end_it = args.end(); it != end_it ; ++it){
//				AVR_COUT <<(*it).first;
//				if((*it).second.second)
//					AVR_COUT <<" (mandatory)";
//				AVR_COUT <<endl;
//			}
		}
#endif
		bool r = read_arg(config_f,&arg[0]);
		assert(r!=0);
		get_arg(param) = arg;
	}
	for(Args::iterator it = args.begin() , end_it = args.end(); it != end_it ; ++it){
		if(picky &&
			(*it).second.second &&
			(*it).second.first==""){
			AVR_COUT << "Config File is missing a mandatory argment: " << (*it).first << endl;
			assert(0);
		}
	}

	get_arg_val(EN_RANDOM, g_random);
	get_arg_val(AB_GRANULARITY_ARG, g_ab_granularity);
	get_arg_val(EN_INTERPRET_UF_MAX_WIDTH, g_interpret_uf_max_width);
	get_arg_val(MININV_EFFORT, g_minimize_inv_effort);
	get_arg_val(INTERPOLATION_ARG, g_interpolation);
	get_arg_val(FORWARDCHECK_ARG, g_forward_check);
	get_arg_val(FINENESS_ARG, g_fineness);
	get_arg_val(LAZY_ASSUME_ARG, g_lazy_assume);
	get_arg_val(BMC_EN, g_bmc_en);
	get_arg_val(KIND_EN, g_kind_en);
	get_arg_val(BMC_MAX_BOUND, g_bmc_max_bound);
	get_arg_val(PRINT_WITNESS, g_print_witness);

	g_abstraction_name = get_arg(ABSTRACTION_TYPE);
	set_abstraction(g_abstraction_name);

	string print_dot = get_arg(PRINT_DOT);
	for (int i = 0; i <= 6; i++) {
		if (i < print_dot.size())
			g_print_dot[i] = print_dot[i];
	}

// 	ostringstream out;
// 	out<<"arguments:"<<endl;
// 	for(Args::iterator it = args.begin() , end_it = args.end(); it != end_it ; ++it){
// 		out<<(*it).first<<" : "<<(*it).second.first<<endl;
// 	}
// 	out<<"-------------"<<endl<<endl;
}

void Config::set_abstraction(string& name) {
	g_ab_interpret_limit = 0;
	g_ab_interpret_excc = LEVEL_EXCC_DEFAULT;

	{
		if (name.find(NAME_UF_UNORDERED) != string::npos)
			g_uf_unordered = !g_uf_unordered;
		if (name.find(NAME_UF_MULT_ONLY) != string::npos)
			g_uf_mult_only = !g_uf_mult_only;
		if (name.find(NAME_UF_NO_BITWISE) != string::npos)
			g_uf_no_bitwise = !g_uf_no_bitwise;
		if (name.find(NAME_UF_NO_SEXT) != string::npos)
			g_uf_no_sext = !g_uf_no_sext;
		if (name.find(NAME_UF_NO_SHIFT) != string::npos)
			g_uf_no_shift = !g_uf_no_shift;
	}

	if (name.find(NAME_SAUF) != string::npos) {
		g_ab_interpret = false;
	}
	else if (name.find(NAME_SABV) != string::npos) {
		int pos1 = name.find(NAME_SABV);
		string namesub = name.substr(pos1);
		int pos2 = namesub.find_first_of("+");
		namesub = namesub.substr(0, pos2);
		g_ab_interpret = true;
		int pos = namesub.find_first_of("0123456789");
		if (pos != string::npos) {
			g_ab_interpret_limit = stoi(namesub.substr(pos));
		}
	}

	{
		int pos1 = name.find(NAME_EXCC);
		if (pos1 != string::npos) {
			string namesub = name.substr(pos1);
			int pos2 = namesub.find_first_of("+");
			namesub = namesub.substr(0, pos2);
			int pos = namesub.find_first_of("0123456789");
			if (pos != string::npos) {
				g_ab_interpret_excc = stoi(namesub.substr(pos));
			}
		}
	}

	if (g_uf_mult_only) {
		g_ab_interpret = true;
		g_ab_interpret_limit = 0;
		g_ab_interpret_excc = LEVEL_EXCC_ALL;
		g_uf_unordered = true;
	}

	cerr << "\t(abstraction: " << (g_ab_interpret?"sa":"sa+uf")
														 << (g_ab_interpret_limit == 0?"":to_string(g_ab_interpret_limit))
														 << ((g_ab_interpret_excc != LEVEL_EXCC_DEFAULT)?"+ec"+to_string(g_ab_interpret_excc):"")
														 << (g_fineness != FINENESS_DEFAULT?"+l"+to_string(g_fineness):"")
														 << (g_uf_unordered?"+unordered":"")
														 << (g_uf_mult_only?"+mult":"")
														 << (g_uf_no_bitwise?"+nobitwise":"")
														 << (g_uf_no_sext?"+nosignex":"")
														 << (g_uf_no_shift?"+noshift":"")
														 << ")" << endl;
}

void Config::dump_args(ostream& out){
	out<<"CONFIGURATION:"<<endl;
	out<<"************************************************"<<endl;
	for(Args::iterator it = args.begin() , end_it = args.end(); it != end_it ; ++it){
		out<<(*it).first<<" = "<<(*it).second.first<<endl;
	}
	out<<"************************************************"<<endl;
}


void Config::get_arg_val(string arg, bool& orig) {
	if (get_arg(arg) == "True")
		orig = true;
	else if (get_arg(arg) == "False")
		orig = false;
	else {
		AVR_COUT <<"\t(unknown argument value for "<< arg <<", expected True/False)"<<endl;
		AVR_COUT <<"\t(assuming default value: "<< orig <<")"<<endl;
		assert(0);
	}
}

void Config::get_arg_val(string arg, int& orig) {
	int val = orig;
	stringstream ss;
	ss << get_arg(arg);
	ss >> val;

	if(!(ss.fail())) {
		orig = val;
		if (arg == AB_GRANULARITY_ARG) {
			if (orig > AB_GRANULARITY_MAX) {
				AVR_COUT <<"\t(argument "<< arg <<" expected to be atmax " << AB_GRANULARITY_MAX << ", assuming max)"<<endl;
				orig = AB_GRANULARITY_MAX;
			}
			if (orig < AB_GRANULARITY_NONE) {
				AVR_COUT <<"\t(argument "<< arg <<" expected to be at least " << AB_GRANULARITY_NONE << ", assuming min)"<<endl;
				orig = AB_GRANULARITY_NONE;
			}
			else if (orig < 0) {
				AVR_COUT <<"\t(argument "<< arg <<" expected to be positive, assuming 0)"<<endl;
				orig = 0;
			}
		}
		else if (arg == MININV_EFFORT) {
			if (orig > MININV_BV_SLOW) {
				AVR_COUT <<"\t(argument "<< arg <<" expected to be atmax " << MININV_BV_SLOW << ", assuming max)"<<endl;
				orig = MININV_BV_SLOW;
			}
			else if (orig < MININV_NONE) {
				AVR_COUT <<"\t(argument "<< arg <<" expected to be positive, assuming " << MININV_NONE << ")" <<endl;
				orig = MININV_NONE;
			}
		}
		else if (arg == INTERPOLATION_ARG) {
			if (orig > INTERPOLATION_MAX) {
				AVR_COUT <<"\t(argument "<< arg <<" expected to be atmax " << INTERPOLATION_MAX << ", assuming max)"<<endl;
				orig = INTERPOLATION_MAX;
			}
			else if (orig < INTERPOLATION_NONE) {
				AVR_COUT <<"\t(argument "<< arg <<" expected to be positive, assuming " << INTERPOLATION_NONE << ")" <<endl;
				orig = INTERPOLATION_NONE;
			}
		}
		else if (arg == FORWARDCHECK_ARG) {
			if (orig > FORWARDCHECK_MAX) {
				AVR_COUT <<"\t(argument "<< arg <<" expected to be atmax " << FORWARDCHECK_MAX << ", assuming max)"<<endl;
				orig = FORWARDCHECK_MAX;
			}
			else if (orig < FORWARDCHECK_NONE) {
				AVR_COUT <<"\t(argument "<< arg <<" expected to be positive, assuming " << FORWARDCHECK_NONE << ")" <<endl;
				orig = FORWARDCHECK_NONE;
			}
		}
		else if (arg == FINENESS_ARG) {
			if (orig > FINENESS_MAX) {
				AVR_COUT <<"\t(argument "<< arg <<" expected to be atmax " << FINENESS_MAX << ", assuming max)"<<endl;
				orig = FINENESS_MAX;
			}
			if (orig < FINENESS_NONE) {
				AVR_COUT <<"\t(argument "<< arg <<" expected to be at least " << FINENESS_NONE << ", assuming min)"<<endl;
				orig = FINENESS_NONE;
			}
		}
		else if (arg == LAZY_ASSUME_ARG) {
			if (orig > LAZY_ASSUME_MAX) {
				AVR_COUT <<"\t(argument "<< arg <<" expected to be atmax " << LAZY_ASSUME_MAX << ", assuming max)"<<endl;
				orig = LAZY_ASSUME_MAX;
			}
			if (orig < LAZY_ASSUME_NONE) {
				AVR_COUT <<"\t(argument "<< arg <<" expected to be at least " << LAZY_ASSUME_NONE << ", assuming min)"<<endl;
				orig = LAZY_ASSUME_NONE;
			}
		}
		else if (arg == BMC_MAX_BOUND) {
			if (orig < 0) {
				AVR_COUT <<"\t(argument "<< arg <<" expected to be positive, assuming 0)"<<endl;
				orig = 0;
			}
		}
	}
	else {
		AVR_COUT <<"\t(unknown argument value for "<< arg <<", expected int)"<<endl;
		AVR_COUT <<"\t(assuming default value: "<< orig <<")"<<endl;
		assert(0);
	}
}
