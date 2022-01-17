/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


/*
 * reach_solve.cpp
 *
 *  Created on: Apr 12, 2018
 *      Author: rock
 */

#include "reach_core.h"
#include <execinfo.h> // to dump call stacks (backtrace, backtrace_symbols)

namespace reach
{


int Reach::solveRelative(int frameIdx, InstL& cube, int queryType, bool getModel, bool checkType) {
  assert(frameIdx < _reach_solvers.size());

  Solver* solver;
  if (checkType) {
#ifdef FRAME_SOLVER_MULTI
  	solver = _reach_solvers[frameIdx].solver1;
#else
  	solver = _reach_solvers[frameIdx].solver_main;
#endif
		assert(getModel);
		assert(queryType == br);

//		switch(queryType) {
//	//  case cti:
//	//    solver = _cti_solver;
//	//    break;
//		case br:
//			solver = _reach_solvers[frameIdx].solver1;
//			break;
//		default:
//			solver = _reach_solvers[frameIdx].solver2;
//			assert(!getModel);
//			break;
//		}
  }
  else {
		solver = _reach_solvers[frameIdx].solver_main;
		assert(!getModel);
  }

#ifdef REFRESH_FRAME_SOLVERS_QUERY
	_reach_solvers[frameIdx].numQ++;
#endif

  if (queryType == fp) {
    InstL forwarded;
    int qType = solver->queryType;
    solver->queryType = fp;
    solver->forward_propagation(AB_QUERY_TIMEOUT, frameIdx, forwarded, _cubes, this);
    solver->queryType = qType;
    for (auto& c: forwarded)
      update_inc_solvers(frameIdx+1, c);
    return 0;
  }

  solver->s_assert_retractable(cube);
  int result = solver->s_check_assume(AB_QUERY_TIMEOUT, getModel);

  switch(queryType) {
//  case cti:
//    solver->s_retract_assertions();
//    break;
  default:
    break;
  }
  return result;
}

void Reach::check_excc(ABSTRACT_REACH_VIOL& abViol, InstS& implications) {

  SOLUTION& s = abViol.generalized_s;
  InstToInstM& nextMap = abViol.nextMap;
//  print_solution(s, "checking partition");

  // Create maps for Ex/Cc values
  InstToMpzM exMap;
  InstToMpzM ccMap;
  map < int, map < mpz_class, Inst* > > numMap;
  for (InstL::iterator pit = s.predicates.begin(); pit != s.predicates.end(); pit++) {
    Inst* tve = (*pit)->get_port();
    if (tve->get_bval() == INVALID_SVAL) {
      cout << *tve << endl;
    }
    assert(tve->get_bval() != INVALID_SVAL);

    OpInst* op = OpInst::as(tve);
    if (op) {
      bool neg = false;
      if (op->get_op() == OpInst::LogNot) {
        tve = OpInst::create(OpInst::LogNot, tve)->get_port();
        assert(tve->get_bval() != INVALID_SVAL);

        op = OpInst::as(tve);
        neg = true;
      }
      if (op) {
        if (tve->get_type() == Ex)
          exMap[tve] = mpz_class(neg?0:1);
        else if (op->get_op() == OpInst::Concat)
          ccMap[tve] = mpz_class(neg?0:1);
      }
    }
  }
  for (auto& partition: s.partitions) {
    pair< int, SORT > sz = partition.first;
    for (auto& cell: partition.second) {
      for (InstL::iterator pit = cell.second.begin(); pit != cell.second.end(); pit++) {
        Inst* tve = (*pit)->get_port();
        assert(tve->get_ival() != INVALID_SMPZ);
        if (tve->get_type() == Num)
          numMap[sz.first].insert(make_pair(cell.first, tve));
        else {
          OpInst* op = OpInst::as(tve);
          if (op) {
            if (tve->get_type() == Ex)
              exMap[tve] = cell.first;
            else if (op->get_op() == OpInst::Concat)
              ccMap[tve] = cell.first;
          }
        }
      }
    }
  }

//  for (auto& m: numMap) {
//  	for (auto& n: m.second) {
//  		AVR_LOG(15, 0, "\t" << *n.second << " (v: " << n.first << ")" << endl);
//  	}
//  }
//  for (auto& n: exMap) {
//		AVR_LOG(15, 0, "\t" << *n.first << " (v: " << n.second << ")" << endl);
//  }
//  for (auto& n: ccMap) {
//		AVR_LOG(15, 0, "\t" << *n.first << " (v: " << n.second << ")" << endl);
//  }

  InstToPairInstM replaceMap;

  Inst::init_visit2();
  for (auto& v: exMap) {
//    AVR_LOG(15, 0, "ex: " << *(v.first) << " (v: " << v.second << ")" << endl);
    Inst* rhs = simplify_excc(v.first, numMap, nextMap);
    if (rhs != v.first) {
      mpz_class* rhsVal = INVALID_SMPZ;
      mpz_class valTmp;
      bool valid = false;
      if (rhs->get_size() == 1) {
        int bval = rhs->get_bval();
        if (bval == INVALID_SVAL) {
//          AVR_LOG(15, 0, *(v.first) << " -s-> " << *rhs << endl);
        }
        else {
        	valTmp = mpz_class(bval?1:0);
        	rhsVal = &valTmp;
          valid = true;
        }
      }
      else {
        mpz_class* ival = rhs->get_ival();
        if (ival == INVALID_SMPZ) {
//          AVR_LOG(15, 0, *(v.first) << " -s-> " << *rhs << endl);
        }
        else {
          rhsVal = ival;
          if (numMap[rhs->get_size()].find(*rhsVal) == numMap[rhs->get_size()].end())
            rhsVal = INVALID_SMPZ;
          else
            valid = true;
        }
      }
//      AVR_LOG(15, 0, "\trhsVal: " << (valid?rhsVal.get_str():"null") << endl);
      if (valid && v.second != (*rhsVal)) {
        replaceMap[v.first] = make_pair(v.first, rhs);
//        AVR_LOG(15, 0, "\tInserting: " << *(v.first) << endl);
      }
    }
//    AVR_LOG(15, 0, *(v.first) << " (v: " << v.second << ")" << " -s-> " << *rhs << endl);
  }
  for (auto& v: ccMap) {
//    AVR_LOG(15, 0, "cc: " << *(v.first) << " (v: " << v.second << ")" << endl);
    Inst* rhs = simplify_excc(v.first, numMap, nextMap);
    if (rhs != v.first) {
      mpz_class* rhsVal = INVALID_SMPZ;
      mpz_class valTmp;
      bool valid = false;
      if (rhs->get_size() == 1) {
        int bval = rhs->get_bval();
        if (bval == INVALID_SVAL) {
//          AVR_LOG(15, 0, *(v.first) << " -s-> " << *rhs << endl);
        }
        else {
          valTmp = mpz_class(bval?1:0);
          rhsVal = &valTmp;
          valid = true;
        }
      }
      else {
        mpz_class* ival = rhs->get_ival();
        if (ival == INVALID_SMPZ) {
//          AVR_LOG(15, 0, *(v.first) << " -s-> " << *rhs << endl);
        }
        else {
          rhsVal = ival;
          if (numMap[rhs->get_size()].find(*rhsVal) == numMap[rhs->get_size()].end())
            rhsVal = INVALID_SMPZ;
          else
            valid = true;
        }
      }
//      AVR_LOG(15, 0, "\trhsVal: " << (valid?rhsVal.get_str():"null") << endl);
      if (valid && v.second != (*rhsVal)) {
        replaceMap[v.first] = make_pair(v.first, rhs);
//        AVR_LOG(15, 0, "\tInserting: " << *(v.first) << endl);
      }
    }
//    AVR_LOG(15, 0, *(v.first) << " (v: " << v.second << ")" << " -s-> " << *rhs << endl);
  }

  Inst::init_visit2();
  for (auto& v: replaceMap) {
    Inst* lhs = replace_with_num_excc(v.first, numMap, nextMap);
    if (lhs != v.first) {
      v.second.first = lhs;
//      AVR_LOG(15, 0, *(v.first) << " -s-> " << *lhs << endl);
    }
//    assert(v.second.first != v.second.second);
    if (v.second.first != v.second.second) {
      Inst* eq = OpInst::create(OpInst::Eq, v.second.first, v.second.second);
//      if (!eq->childrenInfo[SIG])
        implications.insert(eq);
//      else {
//      }
    }
//    AVR_LOG(15, 0, *(v.first) << " -excc-> (" << *(v.second.first) << " == " << *(v.second.second) << ")" << endl);
  }
}

bool Reach::check_using_ufbv(InstL& cube)
{
	SOLVER_BV* fSolver = new SOLVER_BV(&_ufbv_mapper, AVR_EXTRA_IDX, false, regular);
  fSolver->stop_ex_cc_interpret();

  fSolver->s_assert(cube);
  int tmpResult = fSolver->s_check(AB_QUERY_TIMEOUT);
  if (tmpResult != AVR_QSAT)
  {
    assert(tmpResult == AVR_QUSAT);
    delete fSolver;
    return true;
  }
  delete fSolver;
  return false;
}

bool Reach::solvePartition(ABSTRACT_REACH_VIOL& abViol, string comment) {
#ifdef DISABLE_ABSTRACT_LEMMAS
	return true;
#endif

  bool result = true;
  InstS implications;
  check_excc(abViol, implications);
  if (!implications.empty()) {
    for (auto& nref: implications) {
      Inst* ref = OpInst::create(OpInst::LogNot, nref);
      if (check_if_global(ref)) {
        AVR_LOG(15, 0, "\n\t\t(global lemma: " << comment << ")" << endl);
        AVR_LOG(15, 2, "\t\t\t" << *nref << endl);

        add_refinement(nref, "ab");
        result = false;
      }
      else {
//        AVR_LOG(15, 0, "\t\t\t(lemma is not global)" << endl);
//        assert(0);
      }
    }
  }
  return result;
}

bool Reach::solveCube(InstL& cubeSub, InstL& cube, string comment) {
#ifdef DISABLE_ABSTRACT_LEMMAS
	return true;
#endif
	cout << "TODO: add support for unsatType here" << endl;
	assert(0);

	bool isSat = true;
  if (!cubeSub.empty()) {
    Inst* tve = OpInst::create(OpInst::LogAnd, cubeSub);
    if (check_if_global(tve)) {
      isSat = false;

#if 1
      BR_QUERY q;
      q.frameIdx = -1;
      for (auto& c: cubeSub)
        q.dest.insert(c);
      InstLL muses;
      SOLVER_AB tmpSolver(_abstract_mapper, AVR_EXTRA_IDX, true, regular);
      generalize_unsat_query(q, muses, &tmpSolver, &tmpSolver);
      assert(!muses.empty());
      for (auto& mus: muses) {
        Inst* ref = OpInst::create(OpInst::LogAnd, mus);
        Inst* nref = OpInst::create(OpInst::LogNot, ref);
        AVR_LOG(15, 0, "\n\t\t(global lemma: " << comment << ")" << endl);
        AVR_LOG(15, 2, "\t\t\t" << *nref << endl);
        add_refinement(nref, "ab");

        if (false)
        {
          BR_QUERY q2;
          q2.frameIdx = -1;
          SOLVER_AB tmpSolver(_abstract_mapper, AVR_EXTRA_IDX, true, regular);
          tmpSolver.s_assert(nref);
          for (auto& c: cube)
            q2.dest.insert(c);
          InstLL muses;
          generalize_unsat_query(q2, muses, &tmpSolver, &tmpSolver);
          assert(!muses.empty());
          for (auto& mus: muses) {
            Inst* ref2 = OpInst::create(OpInst::LogAnd, mus);
            Inst* nref2 = OpInst::create(OpInst::LogNot, ref2);
            AVR_LOG(15, 0, "\n\t\t(global lemma: " << comment << ")" << endl);
            add_refinement(nref2, "ab");
          }
        }
      }
#else
        BR_QUERY q;
        q.frameIdx = -1;
        SOLVER_AB tmpSolver(_abstract_mapper, AVR_EXTRA_IDX, true, regular);
        tmpSolver.s_assert(OpInst::create(OpInst::LogNot, tve));
        for (auto& c: cube)
          q.dest.insert(c);
        InstLL muses;
        generalize_unsat_query(q, muses, &tmpSolver, &tmpSolver);
        assert(!muses.empty());
        for (auto& mus: muses) {
          Inst* ref = OpInst::create(OpInst::LogAnd, mus);
          Inst* nref = OpInst::create(OpInst::LogNot, ref);
          AVR_LOG(15, 0, "\n\t\t(global lemma: " << comment << ")" << endl);
          AVR_LOG(15, 2, "\t\t\t" << *nref << endl);
          add_refinement(nref, "ab");
        }
#endif
    }
    else {
//      if (check_using_ufbv(cube)) {
//        AVR_LOG(15, 0, "\n\t\t(global lemma possible (ufbv): " << comment << ")" << endl);
//
//        z3_API* fSolver = new z3_API(&_ufbv_mapper, AVR_EXTRA_IDX, false, regular);
//        fSolver->stop_ex_cc_interpret();
//        InstLL muses;
//        fSolver->get_muses_2(AB_QUERY_TIMEOUT, cube, muses, num_scalls_sat_correctness, num_scalls_unsat_correctness, fSolver);
//        for (auto& mus: muses) {
//          Inst* ref = OpInst::create(OpInst::LogAnd, mus);
//          Inst* nref = OpInst::create(OpInst::LogNot, ref);
//          AVR_LOG(15, 0, "\n\t\t\t" << *nref << endl);
//        }
////        AVR_LOG(15, 0, cube << endl);
////        assert(0);
//      }
    }
  }
  return isSat;
}


bool Reach::solveBadDest() {
  InstL cubeBadSub, cubeBad;
  for (auto& c: _bad_cube.nextStateSubConstraints) {
    if (c->find_sig() && !c->find_next())
      continue;
    cubeBadSub.push_back(c);
  }
  for (auto& c: _bad_cube.nextStateConstraints) {
    if (c->find_sig() && !c->find_next())
      continue;
    cubeBad.push_back(c);
  }
  return solveCube(cubeBadSub, cubeBad, "cube in !P+");
}

void Reach::refineCube(ABSTRACT_CUBE cube, int idx) {
  InstL conjunct_q;
  InstL conjunct_hard;

  conjunct_q.push_back(cube.cube);

  AVR_LOG(4, 2, "Checking cube " << endl);
  AVR_LOG(4, 5, "C: " << conjunct_q);

  Inst *ve_q_wo_ref = OpInst::create(OpInst::LogAnd, conjunct_q);
//  for (InstL::iterator it3 = _negated_refs.begin(); it3 != _negated_refs.end(); ++it3)
//    conjunct_q.push_back(*it3);
//
//  Inst* ve_q = OpInst::create(OpInst::LogAnd, conjunct_q);
  _feas_sat_res = false;
  AVR_LOG(4, 1, "C: is " << (_sat_res ? "SAT" : "UNSAT") << endl);

#ifdef EXTRA_CHECKS
  if (_euf_solver){
    delete _euf_solver;
    _euf_solver = NULL;
  }
  _euf_solver = new z3_API(&_abstract_mapper, AVR_BASIS_IDX, false, false);

  _sat_res = _euf_solver->check_sat(ve_prop);
  //AVR_LOG(4, 2, "DP-R abst-level-solve, idx: " << idx << ", runtime: " << double(time_diff)/1000000 << endl);

  if (_sat_res)
#endif
  {
    AVR_LOG(15, 0, "\t\tSAT_c ? [ A[" << idx << "] ]: " );
    _new_refs.clear();
//          add_all_wires(ve_prop_wo_ref, dummyCube.relevantWires, true);
    refine(conjunct_hard, cube, ve_q_wo_ref, false);

//          dp_lemmas.push_back(_new_refs);
  }
#ifdef EXTRA_CHECKS
        else
        {
          AVR_LOG(4, 1, "C_bad is UNSAT ? (C is a violating cube)" << endl);
          dp_refinement_cleanup();
          /// Aman
      //    continue;
          // due to the DP lemmas from the (one-seg) feasibility check, this can be unsat.
          assert(0);
          /// END
        }
#endif
}

}

