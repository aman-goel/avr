/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


/*
 * reach_evaluate.h
 *
 *  Created on: Jan 22, 2018
 *      Author: rock
 */

#ifndef SRC_REACH_REACH_EVALUATE_H_
#define SRC_REACH_REACH_EVALUATE_H_


#include "reach_cube.h"
#include "reach_backend.h"

namespace reach
{
	class EVAL
	{
	public:
		EVAL(ABSTRACT_REACH_VIOL& inputBins, InstToInstM& inputMap, InstS& inputSet,
				InstS& inputSetNext, InstS& inputInp, InstS& inputInpNext, InstS& inputConst,
				set< string >& inputUFtype, Solver* inpSolver
//				, map< string, map < mpz_class, InstL > >& inputUFs
				)
		{
			bins = &inputBins;
			nextMap = &inputMap;
			relevantSet = &inputSet;
			relevantSetNext = &inputSetNext;
			relevantInp = &inputInp;
			relevantInpNext = &inputInpNext;
			relevantConst = &inputConst;
			relevantUFtype = &inputUFtype;
			solver = inpSolver;
//			relevantUFs = &inputUFs;
		}
		void change_bin(ABSTRACT_REACH_VIOL& inputBins)
		{
			bins = &inputBins;
		}
		void change_map(InstToInstM& inputMap)
		{
			nextMap = &inputMap;
		}
		void change_set(InstS& inputSet)
		{
			relevantSet = &inputSet;
		}
		void change_inp(InstS& inputInp)
		{
			relevantInp = &inputInp;
		}
		void print_all(int loc = 15, int level = 1) {
		  AVR_LOG(loc, level, "\t(projection set)     " << endl);
		  AVR_LOG(loc, level, "\t\t(next variables)   \t");
		  for (auto& v: *relevantSetNext) {
		    AVR_LOG(loc, level, *v << ", ");
		  }
		  AVR_LOG(loc, level, "\n");
		  AVR_LOG(loc, level, "\t\t(next inputs)      \t");
		  for (auto& v: *relevantInpNext) {
		    AVR_LOG(loc, level, *v << ", ");
		  }
		  AVR_LOG(loc, level, "\n");
		  AVR_LOG(loc, level, "\t\t(present variables)\t");
		  for (auto& v: *relevantSet) {
		    AVR_LOG(loc, level, *v << ", ");
		  }
		  AVR_LOG(loc, level, "\n");
		  AVR_LOG(loc, level, "\t\t(present inputs)   \t");
		  for (auto& v: *relevantInp) {
		    AVR_LOG(loc, level, *v << ", ");
		  }
		  AVR_LOG(loc, level, "\n");
		  AVR_LOG(loc, level, "\t\t(constants)     \t");
		  for (auto& v: *relevantConst) {
		    AVR_LOG(loc, level, *v << ", ");
		  }
		  AVR_LOG(loc, level, "\n");
		  AVR_LOG(loc, level, "\t\t(uf types)      \t");
		  for (auto& v: *relevantUFtype) {
		    AVR_LOG(loc, level, v << ", ");
		  }
		  AVR_LOG(loc, level, "\n");
//      AVR_LOG(15, 0, "\t\t(next cube)" << endl);
//      for (auto& c: bins->nextStateConstraints)
//        AVR_LOG(15, 0, "\t\t\t" << *c << endl);
//		  AVR_LOG(15, 0, "\t\t(main cube)" << endl);
//      for (auto& c: bins->mainConstraints)
//        AVR_LOG(15, 0, "\t\t\t" << *c << endl);
//      AVR_LOG(15, 0, "\t\t(next sub. cube)" << endl);
//      for (auto& c: bins->nextStateSubConstraints)
//        AVR_LOG(15, 0, "\t\t\t" << *c << endl);
//      AVR_LOG(15, 0, "\t\t(main sub cube)" << endl);
//      for (auto& c: bins->mainSubConstraints)
//        AVR_LOG(15, 0, "\t\t\t" << *c << endl);
      AVR_LOG(loc, level, endl);
		}
		void clear_all(void) {
		  bins->clear();
		  nextMap->clear();
		  relevantSet->clear();
		  relevantInp->clear();
		  relevantConst->clear();
		  relevantUFtype->clear();
		}

//		void clear_uf(void)
//		{
//			relevantUFs->clear();
//		}

		ABSTRACT_REACH_VIOL* bins;
		InstToInstM* nextMap;
		InstS* relevantSet;
		InstS* relevantSetNext;
		InstS* relevantInp;
		InstS* relevantInpNext;
		InstS* relevantConst;
		set< string >* relevantUFtype;
		Solver* solver;
//		map< string, map < mpz_class, InstL > >* relevantUFs;
	};

}




#endif /* SRC_REACH_REACH_EVALUATE_H_ */
