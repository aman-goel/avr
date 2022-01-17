/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


#include "reach_core.h"

using namespace std;

long long _totalTime;
int _numRefinements = 0;

ofstream _resFile;
ofstream _refFile;
//ofstream _expFile;
ofstream _prFile;
string _benchmark;
bool _ufsHaveBool;

#ifdef DUMP_SMT
	ofstream _smtFile;
#endif


int main(int argc, char*argv[]) {
//	cout << "Running reach" << endl;

	using namespace reach;

	argc-- , argv++;
	if(argc!=2){
	AVR_COUT << "Syntax: reach "<<"<word_dir> <bin_dir>"<<endl;
		return 1;
	}
	Config config(argv[0],argv[1]);
	config.load_args();
	Reach reach(&config);
	Inst::config = &config;

	_totalTime = 0;
	_numRefinements = 0;

	string tmp = remove_path_from_fname(argv[0]);
	_benchmark = tmp.substr(tmp.find("work_") + 5);

	string fname_reach = config.get_working_dir() + "/" + _benchmark + ".results";
	_resFile.open(fname_reach.c_str(), std::ofstream::app);

	string fname_ref = config.get_working_dir() + "/data/refs.txt";
	_refFile.open(fname_ref.c_str(), std::ofstream::out);
	_refFile << "(benchmark) " << _benchmark << "\n" << endl;

//	string fname_exp = config.get_working_dir() + "/data/design.txt";
//	_expFile.open(fname_exp.c_str(), std::ofstream::app);


#ifdef DUMP_SMT
	_ufsHaveBool = false;

	string fname_smt = "../smt_queries/" + _benchmark + ".smt2";
	_smtFile.open(fname_smt.c_str());

	cout << _benchmark << endl << endl;

	_smtFile << "(set-logic QF_UF)" << endl;
	_smtFile << "(set-info :name: " << _benchmark << " (copyright: University of Michigan))" << endl;
	_smtFile << "(set-info :smt-lib-version: 2.0)" << endl;
	_smtFile << "(set-info :category: crafted)" << endl;
	_smtFile << "(declare-sort U 0)" << endl << endl;
#endif

// 	cout<<endl;
// 	cout<<"\tAverroes - University of Michigan, Ann Arbor"<<endl;
// 	cout<<"\tVersion: "<< AVERROES_VERSION << " (preliminary version)" <<endl<<endl;
// 	//config.dump_args(cout);
// 	//  yices_set_verbosity(100);
// 	cout<<endl<<"Averroes started..."<<endl<<endl;


	string fname_pr = config.get_working_dir() + "/" + "result.pr";
	_prFile.open(fname_pr.c_str(), std::ofstream::app);


	//#########		MAIN FUNCTION		#########//
	reach.init_flow();
	reach.read_wn();
	//assert(0);
	if(config.get_arg(DUMP_BLIF_ARG) == "on"){
		reach.write_blif_file();
    reach.delete_solvers();
	}else{
		int ret = reach.verify();
		reach.delete_solvers();

		reach.dump_execution_time(ret);

		if (!y2_API::y2_solvers.empty()) {
			cout << "\n\t(warning: cleanup error)\t #y2_solvers: " << y2_API::y2_solvers.size() << endl;
//			for (auto& s: y2_API::y2_solvers)
//				cout << "id: " << s.first << endl;
		}
	}
	_resFile.close();
	_refFile.close();
//	_expFile.close();
	_prFile.close();

	return 0;
}
