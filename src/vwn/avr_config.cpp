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
bool Config::g_split_signals = true;
bool Config::g_single_property = false;

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
#ifdef AVR_SPLIT_SIGNALS
	args.insert(make_pair(EN_SPLIT_SIGNALS,make_pair("True",0)));
#else
	args.insert(make_pair(EN_SPLIT_SIGNALS,make_pair("False",0)));
#endif
	args.insert(make_pair(SELECT_PROPERTY,make_pair("-",0)));
	args.insert(make_pair(JG_PREPROCESS,make_pair("-",0)));
	args.insert(make_pair(INIT_FILE,make_pair("-",0)));
	args.insert(make_pair(SELECT_FRONTEND,make_pair(DEFAULT_FRONTEND,0)));


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
	args.insert(make_pair(AVR_NUM_REACH_SOLVER,make_pair("20",0)));
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
//	args.insert(make_pair(AVR_NEW_CLT_MODE,make_pair("1",0)));
	
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
			continue;
			AVR_COUT <<"Unknown argument "<<param<<" in config file!"<<endl;
			AVR_COUT <<"The allowed arguments are:"<<endl;
			for(Args::iterator it = args.begin() , end_it = args.end(); it != end_it ; ++it){
				AVR_COUT <<(*it).first;
				if((*it).second.second)
					AVR_COUT <<" (mandatory)";
				AVR_COUT <<endl;
			}
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
			AVR_COUT << "Config File is missing a mandatory argument: " << (*it).first << endl;
			assert(0);
		}
	}

	get_arg_val(EN_RANDOM, g_random);
	get_arg_val(EN_SPLIT_SIGNALS, g_split_signals);
	g_single_property = (get_arg(SELECT_PROPERTY) != "-");

// 	ostringstream out;
// 	out<<"arguments:"<<endl;
// 	for(Args::iterator it = args.begin() , end_it = args.end(); it != end_it ; ++it){
// 		out<<(*it).first<<" : "<<(*it).second.first<<endl;
// 	}
// 	out<<"-------------"<<endl<<endl;
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

