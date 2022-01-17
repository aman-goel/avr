/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


/*
 * reach_bmc.cpp
 *
 *  Created on: Oct 10, 2019
 *      Author: rock
 */


#include "reach_core.h"

namespace reach
{

void Reach::bmc_init() {
	bm.safe_bound = -1;
	if (Config::g_print_witness)
		bm.solv_c = new_conc_solver(true, AVR_BV_IDX, mdl);
	else
		bm.solv_c = new_conc_solver(true, AVR_BV_IDX);
	bm.solv_c->assert_all_wire_constraints();

#ifdef BMC_ABSTRACT
	bm.use_abstract = true;
  if (Config::g_ab_interpret && (Config::g_ab_interpret_limit == 0))
  	bm.use_abstract = false;
  if (bm.use_abstract) {
		bm.solv_a = new SOLVER_AB(_abstract_mapper, AVR_EXTRA_IDX, true, cti);
		bm.solv_a->assert_all_wire_constraints();
  }
#endif
}

int Reach::bmc_run(int kmax) {
	int result = EXIT_ERROR;
	bmc_init();
	AVR_LOG(20, 1, "(starting bmc upto max bound " << kmax << ")\n");

  struct rusage usage;
  struct timeval end_time;
  long long time_diff;

	int step = 0;
	bool first = true;
	Inst::init_visit3();


	InstL conjunct_init;
	AVR_LOG(20, 5, "(asserting I)\n");
	conjunct_init.push_back(unroll_to(_ve_init, step, step + 1));
	conjunct_init.push_back(unroll_to(_ve_assume_orig, step, step + 1));
	bm.dest = unroll_to(_ve_model, step, step + 1);
	conjunct_init.push_back(bm.dest);
	bm.solv_c->s_assert(conjunct_init);
#ifdef BMC_ABSTRACT
  if (bm.use_abstract) {
  	bm.solv_a->s_assert(conjunct_init);
  }
#endif
	AVR_LOG(20, 7, "(asserting " << conjunct_init << "\n");

	while (step < kmax) {
		InstL conjunct_step, conjunct_per;
		if (first) {
			AVR_LOG(20, 5, "(asserting !P" << step << ")\n");
			conjunct_step.push_back(unroll_to(_ve_prop_eq_0, step, step + 1));
			first = false;
		}
		else {
			AVR_LOG(20, 5, "(asserting T" << step << ")\n");
			conjunct_per.push_back(unroll_to(_ve_model_nsf, step, step + 1));

			step++;
			_cext_idx.push_back(step);
			Inst::init_visit3();

			bm.dest = unroll_to(_ve_model, step, step + 1);
			conjunct_per.push_back(bm.dest);
			conjunct_per.push_back(unroll_to(_ve_assume_orig, step, step + 1));
			bm.solv_c->s_assert(conjunct_per);
#ifdef BMC_ABSTRACT
		  if (bm.use_abstract) {
				bm.solv_a->s_assert(conjunct_per);
		  }
#endif
			AVR_LOG(20, 7, "(asserting " << conjunct_per << "\n");

			AVR_LOG(20, 5, "(asserting !P" << step << ")\n");
			conjunct_step.push_back(unroll_to(_ve_prop_eq_0, step, step + 1));
		}

#ifdef BMC_ABSTRACT
		int step_res_a = AVR_QTO;
	  if (bm.use_abstract) {
			bm.solv_a->s_assert_retractable(conjunct_step);
			step_res_a = bm.solv_a->s_check_assume(BV_QUERY_TIMEOUT, true);
			bm.solv_a->s_retract_assertions();
	  }
	  if (step_res_a == AVR_QUSAT) {
			AVR_LOG(20, 1, "(abstract step " << step << " is UNSAT)" << endl);
			bm.safe_bound = step;
	  }
	  else
#endif
	  {
#ifdef BMC_ABSTRACT
	    if (bm.use_abstract) {
				AVR_LOG(20, 1, "(abstract step " << step << " is SAT)" << endl);
				AVR_LOG(20, 1, "(disabling abstract mode)" << endl);
#ifdef PRINT_FRAME_SUMMARY
				cerr << "\t(bmc: abstract mode disabled at step " << step << ")" << endl;
#endif
	  		delete static_cast<SOLVER_AB*>(bm.solv_a);
		  	bm.use_abstract = false;
	    }
#endif

			bm.solv_c->s_assert_retractable(conjunct_step);
			AVR_LOG(20, 7, "(assuming " << conjunct_step << "\n");
			int step_res = bm.solv_c->s_check_assume(BV_QUERY_TIMEOUT, true);

			if (step_res == AVR_QSAT) {
				AVR_LOG(20, 1, "(step " << step << " is SAT)" << endl);
				result = EXIT_VIOL;
				cext.backward = false;

				if (Config::g_print_witness) {
					retrieve_cex_val(bm.dest, bm.solv_c, false, true, false);
					for (auto& v: cext.cex) {
						retrieve_cex_val(v.constant, bm.solv_c, false, false, false);
					}
				}

				cout << "(bmc: found cex at step " << step << ")\n";
#ifdef PRINT_FRAME_SUMMARY
				cerr << "\t(bmc: found cex at step " << step << ")" << endl;
#endif
				break;
			}
			else if (step_res == AVR_QUSAT) {
				AVR_LOG(20, 1, "(step " << step << " is UNSAT)" << endl);
				AVR_LOG(20, 5, "(retracting !P" << step << ")\n");
				bm.solv_c->s_retract_assertions();
				bm.safe_bound = step;
			}
			else {
				AVR_LOG(20, 1, "(step " << step << " is UNKNOWN)" << endl);
				result = EXIT_ERROR;
				break;
			}
	  }

		if (step == kmax) {
			AVR_LOG(20, 1, "(reached max bound " << kmax << ")\n");

			cout << "(bmc: safe till step " << bm.safe_bound << ")" << endl;
#ifdef PRINT_FRAME_SUMMARY
			cerr << "\t(bmc: safe till step " << bm.safe_bound << ")" << endl;
#endif
			break;
		}

		if (step % 5 == 0) {
		  getrusage(RUSAGE_SELF, &usage);
		  timeradd(&usage.ru_utime, &usage.ru_stime, &end_time);
		  time_diff = Timevaldiff(&_start_time, &end_time);
		  int elapsed_time = ((double)time_diff / 1000000);

			cout << "  " << elapsed_time << "s\t(bmc: safe till step " << bm.safe_bound << ")" << endl;
#ifdef PRINT_FRAME_SUMMARY
			cerr << "  " << elapsed_time << "s\t(bmc: safe till step " << bm.safe_bound << ")" << endl;
#endif
		}
	}
	AVR_LOG(20, 1, "(bmc: done)" << endl);
#ifdef BMC_ABSTRACT
  if (bm.use_abstract) {
		delete static_cast<SOLVER_AB*>(bm.solv_a);
  }
#endif
	return result;
}

void Reach::kind_init() {
	bm.safe_bound = -1;
	if (Config::g_print_witness)
		bm.solv_c = new_conc_solver(true, AVR_BV_IDX, mdl);
	else
		bm.solv_c = new_conc_solver(true, AVR_BV_IDX);
	bm.solv_c->assert_all_wire_constraints();
}

int Reach::kind_run(int kmax) {
	int result = EXIT_ERROR;
	kind_init();
	AVR_LOG(20, 1, "(starting kind upto max bound " << kmax << ")\n");

  struct rusage usage;
  struct timeval end_time;
  long long time_diff;

	int step = 0;
	bool first = true;
	Inst::init_visit3();


	InstL conjunct_initC;
	Inst* tve_init;
	Inst* tve;

	tve_init = unroll_to(_ve_init, step, step + 1);

	tve = unroll_to(_ve_assume_orig, step, step + 1);
	conjunct_initC.push_back(tve);

	bm.dest = unroll_to(_ve_model, step, step + 1);
	conjunct_initC.push_back(bm.dest);

	bm.solv_c->s_assert(conjunct_initC);
	AVR_LOG(20, 8, "asserting: " << conjunct_initC << endl);

	while (step < kmax) {
		InstL conjunct_stepC, conjunct_stepA, conjunct_perC, conjunct_perA;
		if (first) {
			AVR_LOG(20, 5, "(init: asserting !P" << step << ")\n");
			tve = unroll_to(_ve_prop_eq_0, step, step + 1);
			conjunct_stepC.push_back(tve);
		}
		else {
			AVR_LOG(20, 5, "(conc: asserting P" << step << ")\n");
			tve = unroll_to(_ve_prop_eq_1, step, step + 1);
			conjunct_perC.push_back(tve);

			AVR_LOG(20, 5, "(asserting T" << step << ")\n");
			tve = unroll_to(_ve_model_nsf, step, step + 1);
			conjunct_perC.push_back(tve);

			step++;
			_cext_idx.push_back(step);
			Inst::init_visit3();

			bm.dest = unroll_to(_ve_model, step, step + 1);
			conjunct_perC.push_back(bm.dest);

			tve = unroll_to(_ve_assume_orig, step, step + 1);
			conjunct_perC.push_back(tve);

			bm.solv_c->s_assert(conjunct_perC);
			AVR_LOG(20, 8, "asserting: " << conjunct_perC << endl);

			AVR_LOG(20, 5, "(asserting !P" << step << ")\n");
			tve = unroll_to(_ve_prop_eq_0, step, step + 1);
			conjunct_stepC.push_back(tve);
		}

	  {
	  	AVR_LOG(20, 5, "(init: asserting I)\n");
	  	conjunct_stepC.push_back(tve_init);
			bm.solv_c->s_assert_retractable(conjunct_stepC);
			AVR_LOG(20, 8, "(assuming " << conjunct_stepC << "\n");
			int step_res = bm.solv_c->s_check_assume(BV_QUERY_TIMEOUT, true);

			if (step_res == AVR_QSAT) {
				AVR_LOG(20, 1, "(init: step " << step << " is SAT)" << endl);
				result = EXIT_VIOL;
				cext.backward = false;

				if (Config::g_print_witness) {
					retrieve_cex_val(bm.dest, bm.solv_c, false, true, false);
					for (auto& v: cext.cex) {
						retrieve_cex_val(v.constant, bm.solv_c, false, false, false);
					}
				}

				cout << "(init: found cex at step " << step << ")\n";
#ifdef PRINT_FRAME_SUMMARY
				cerr << "\t(init: found cex at step " << step << ")" << endl;
#endif
				break;
			}
			else if (step_res == AVR_QUSAT) {
				AVR_LOG(20, 1, "(init: step " << step << " is UNSAT)" << endl);
				AVR_LOG(20, 5, "(init: retracting !P" << step << ")\n");
				bm.solv_c->s_retract_assertions();
				bm.safe_bound = step;

				if (!first) {
					conjunct_stepC.pop_back();
					bm.solv_c->s_assert_retractable(conjunct_stepC);
					AVR_LOG(20, 8, "(conc: assuming " << conjunct_stepC << "\n");
					int step_resA = bm.solv_c->s_check_assume(BV_QUERY_TIMEOUT, true);

					if (step_resA == AVR_QUSAT) {
						AVR_LOG(20, 1, "(conc: step " << step << " is UNSAT)" << endl);
						result = EXIT_HOLD;

						cout << "(kind: inductive at step " << step << ")\n";
#ifdef PRINT_FRAME_SUMMARY
						cerr << "\t(kind: inductive at step " << step << ")" << endl;
#endif
//						bm.solv_c->print_constraints(20, 1);
//						bm.solv_c->print_query(0, ERROR, "error3");
//						assert(0);

						break;
					}
					else if (step_resA == AVR_QSAT) {
						AVR_LOG(20, 1, "(conc: step " << step << " is SAT)" << endl);
						AVR_LOG(20, 5, "(conc: retracting !P" << step << ")\n");

//						bm.solv_c->print_constraints(20, 1);
//						bm.solv_c->print_query(0, ERROR, "error3");
//						assert(0);

						bm.solv_c->s_retract_assertions();
					}
					else {
						AVR_LOG(20, 1, "(conc: step " << step << " is UNKNOWN)" << endl);
						result = EXIT_ERROR;
						break;
					}
				}
			}
			else {
				AVR_LOG(20, 1, "(init: step " << step << " is UNKNOWN)" << endl);
				result = EXIT_ERROR;
				break;
			}
	  }
		first = false;

		if (step == kmax) {
			AVR_LOG(20, 1, "(reached max bound " << kmax << ")\n");

			cout << "(kind: safe till step " << bm.safe_bound << ")" << endl;
#ifdef PRINT_FRAME_SUMMARY
			cerr << "\t(kind: safe till step " << bm.safe_bound << ")" << endl;
#endif
			break;
		}

		if (step % 5 == 0) {
		  getrusage(RUSAGE_SELF, &usage);
		  timeradd(&usage.ru_utime, &usage.ru_stime, &end_time);
		  time_diff = Timevaldiff(&_start_time, &end_time);
		  int elapsed_time = ((double)time_diff / 1000000);

			cout << "  " << elapsed_time << "s\t(kind: safe till step " << bm.safe_bound << ")" << endl;
#ifdef PRINT_FRAME_SUMMARY
			cerr << "  " << elapsed_time << "s\t(kind: safe till step " << bm.safe_bound << ")" << endl;
#endif
		}
	}
	AVR_LOG(20, 1, "(kind: done)" << endl);
	return result;
}

Inst* Reach::unroll_to(Inst* top, int u, int v, bool add_to_cex) {
	//	cout << "top: " << *top << endl;
  if (top->get_visit3()) {
  	return top->acex_coi;
  }
  top->set_visit3();

	Inst* topRet = top;

	const InstL* ch = top->get_children();
	if (ch) {
		InstL new_ch;
		bool need_new = false;
		for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it) {
			Inst* newCh = unroll_to((*it), u, v);
			if (newCh != (*it)) {
				need_new = true;
			}
			new_ch.push_back(newCh);
		}
		if (need_new) {
			topRet = top->apply_children(new_ch);
		}
	}
	else {
		SigInst* sig = SigInst::as(top);
		if (sig) {
			int step = u;
			bool isnext = sig->find_next();
			if (isnext) {
				step = v;
				Inst* pre = Inst::all_next2pre(sig);
				sig = SigInst::as(pre);
				assert(sig);
			}
			string name = sig->get_name();
			name += "@" + to_string(step);
			topRet = ConstInst::create(name, sig->get_size(), sig, step, sig->get_sort());
			if (add_to_cex && (!isnext)) {
				bool isinput = (Inst::_s_inp.find(sig) != Inst::_s_inp.end());
				if (isinput) {
					if (sig != _ve_prop_eq_1)
						cext.add(step, sig, topRet, true);
				}
				else
					cext.add(step, sig, topRet, false);
			}
		}
	}
//  cout << *top << " -> " << *topRet << endl;
	top->acex_coi = topRet;
	return topRet;
}

}

