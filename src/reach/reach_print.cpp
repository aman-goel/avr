/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


/*
 * reach_print.cpp
 *
 *  Created on: Oct 2, 2019
 *      Author: rock
 */

#include "reach_core.h"
#include <execinfo.h>	// to dump call stacks (backtrace, backtrace_symbols)


namespace reach
{

void Reach::print_design_smt2() {
#ifdef PRINT_DESIGN_SMT2
  bool print_ = false;
  _config->get_arg_val(PRINT_SMT2_DESIGN, print_);
  if (print_) {
		string tmp_ = _config->get_working_dir() + "/tmp.smt2";
		ofstream out_;
		out_.open(tmp_.c_str());
		m5_API print_solver(_concrete_mapper, AVR_BV_IDX, false, prt);

		out_ << "\n; initial state\n";
		out_ << "(define-fun .init () Bool (! \n";
		print_solver.print_expression(_conjunct_init, out_);
		out_ << " :init true))\n";

		vector <string> trans;
		trans.push_back(".T");

		out_ << "\n; transition relation main\n";
		out_ << "(define-fun .T () Bool \n";
		print_solver.print_expression(_conjunct_nsf, out_);
		out_ << ")\n";

		if (!_assumptions.empty()) {
			InstL conjunct_assume;
			for (auto& v: _assumptions)
				conjunct_assume.push_back(v);

			trans.push_back(".A");
			out_ << "\n; assumptions\n";
			out_ << "(define-fun .A () Bool \n";
			print_solver.print_expression(conjunct_assume, out_);
			out_ << ")\n";

			InstL conjunct_assumeNext;
			for (auto& v: _assumptions) {
				if (!v->find_next()) {
					Inst* vNext = Inst::all_pre2next(v);
					conjunct_assumeNext.push_back(vNext);
				}
			}
			if (!conjunct_assumeNext.empty()) {
				trans.push_back(".A_next");
				out_ << "\n; assumptions next\n";
				out_ << "(define-fun .A_next () Bool \n";
				print_solver.print_expression(conjunct_assumeNext, out_);
				out_ << ")\n";
			}
		}
		out_ << "\n; transition relation\n";
		out_ << "(define-fun .trans () Bool (! \n";
		out_ << "(and \n";
		for (auto& s: trans)
			out_ << "\t" << s << "\n";
		out_ << ")\n";
		out_ << " :trans true))\n";

	  Inst* p = _ve_model;
	  OpInst* op = OpInst::as(_ve_model);
	  if (op && op->get_op() == OpInst::Eq) {
	  	p = op->get_children()->back();
	  }
		out_ << "\n; property expression\n";
		out_ << "(define-fun .prop () Bool \n";
		print_solver.print_expression(p, out_);
		out_ << ")\n";

	  p = _ve_model_next;
	  op = OpInst::as(_ve_model_next);
	  if (op && op->get_op() == OpInst::Eq) {
	  	p = op->get_children()->back();
	  }
		out_ << "\n; property next expression\n";
		out_ << "(define-fun .prop_next () Bool \n";
		print_solver.print_expression(p, out_);
		out_ << ")\n";

		out_ << "\n; property\n";
		out_ << "(define-fun property () Bool (! \n";
		out_ << "\t.prop\n";
		out_ << " :invar-property 0))\n";

		out_ << "\n; property next\n";
		out_ << "(define-fun property$next () Bool\n";
		out_ << "\t.prop_next\n";
		out_ << ")\n";

//
//		out_ << "\n; property_next\n";
//		out_ << "(define-fun .property_next () Bool \n";
//		out_ << "\t" << print_solver.print_name(_ve_prop_next_eq_1) << "\n";
//		out_ << ")\n";

//		out_ << "\n(assert .prop)\n";

		out_.close();

		string fname_ = _config->get_working_dir() + "/design.smt2";
		out_.open(fname_.c_str());
		out_ << "; printed by " << msat_get_version() << "\n";
		out_ << "\n (set-logic ALL)\n";

		out_ << "\n; state variables\n";
		for (auto& v: Inst::_s_reg) {
			Inst* vNext = Inst::all_pre2next(v);
			string vName = print_solver.print_name(v);
			string vNextName = print_solver.print_name(vNext);
			if (vName != "")
				out_ << "(declare-fun " << vName << " () " << v->get_sort().sort2smt2str() << ")\n";
			if (vNextName != "")
				out_ << "(declare-fun " << vNextName << " () " << vNext->get_sort().sort2smt2str() << ")\n";
			if (vName != "" && vNextName != "")
				out_ << "(define-fun ." << vName << " () " << v->get_sort().sort2smt2str() <<
				" (! " << vName << " :next " << vNextName << "))\n";
		}

		out_ << "\n; input variables\n";
		for (auto& v: Inst::_s_inp) {
			if (v == _ve_prop_eq_1)
				continue;
			Inst* vNext = Inst::all_pre2next(v);
			string vName = print_solver.print_name(v);
			string vNextName = print_solver.print_name(vNext);
			if (vName != "") {
				out_ << "(declare-fun " << vName << " () " << v->get_sort().sort2smt2str() << ")\n";
			}
			if (vNextName != "") {
				out_ << "(declare-fun " << vNextName << " () " << vNext->get_sort().sort2smt2str() << ")\n";
			}
		}

		ifstream tmp_file(tmp_);
		out_ << tmp_file.rdbuf();
		tmp_file.close();
		std::remove(tmp_.c_str());

		out_.close();
  }
#endif
}

void Reach::print_design_btor2() {
	return;

//#ifdef PRINT_DESIGN_BTOR2
//  bool print_ = false;
//  _config->get_arg_val(PRINT_SMT2_DESIGN, print_);
//  if (print_) {
//		string tmp_ = _config->get_working_dir() + "/tmp.btor2";
//		FILE* out_;
//		out_ = fopen(tmp_.c_str(), "w");
//    if (!out_) {
//        assert(0);
//    }
//		bt_API print_solver(_concrete_mapper, AVR_BV_IDX, false, prt);
//
//		print_solver.print_expression(_conjunct_init, out_);
//		fclose(out_);
//  }
//#endif
}


}

