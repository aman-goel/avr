/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


/*
 * reach_cube.h
 *
 *  Created on: Nov 18, 2017
 *      Author: rock
 */

#ifndef SRC_REACH_REACH_CUBE_H_
#define SRC_REACH_REACH_CUBE_H_

#include "avr_util.h"
#include "avr_word_netlist.h"

namespace reach
{

class SOLUTION {
public:
  InstL predicates;
  map< pair< int, SORT>, map< mpz_class, InstL > > partitions;

  SOLUTION()
  {
    clear();
  }

  void clear()
  {
    predicates.clear();
    partitions.clear();
  };
};

class ABSTRACT_REACH_VIOL
{
public:
	InstL	t1Constraints;					/// Tier 1 constraints
	InstL	t2Constraints;					/// Tier 2 constraints
	InstL	t3Constraints;					/// Tier 3 constraints
	InstL	t4Constraints;					/// Tier 4 constraints

	InstL	mainConstraints;				/// All default constraints (i.e. from COI)
  InstL mainSubConstraints;        /// All default constraints (i.e. from COI)

	InstL	predConstraints;				/// Constraints from evaluating simulation predicates

	InstL	fprojAbConstraints;				/// Functional projection constraints for abstract cube (optional)
	InstL	fprojCcConstraints;				/// Functional projection constraints for concrete cube (optional)

	InstL	projAbConstraints;				/// Projection constraints for abstract cube (optional)
	InstL	projCcConstraints;				/// Projection constraints for concrete cube (optional)

	InstL	subsConstraints;				/// Constraints from substitution for abstract cube (optional)

	InstL	nextStateConstraints;
	InstL	nextStateSubConstraints;

	InstL	concreteConstraints;
	InstL	relevantWires;
	InstL	relevantWiresNext;

	/// For stats collection
	InstS	t1Set;					/// Tier 1 constraints
	InstS	t2Set;					/// Tier 2 constraints
	InstS	t3Set;					/// Tier 3 constraints
	InstS	t4Set;					/// Tier 4 constraints

	InstS coiAbSet;
	InstS coiCcSet;

	InstS predAbSet;
	InstS predCcSet;

	InstS fprojAbSet;
	InstS fprojCcSet;

	InstS projAbSet;
	InstS projCcSet;

	InstS subsAbSet;

	SOLUTION generalized_s;
	InstToInstM nextMap;

	void print_cubes()
	{
		return;

		AVR_LOG(15, 0, "\t(abstract)" << endl);
		for (auto& v: mainConstraints)
		{
			AVR_LOG(15, 0, "\t\t" << *v << endl);
		}
		AVR_LOG(15, 0, "\t(concrete)" << endl);
		for (auto& v: concreteConstraints)
		{
			AVR_LOG(15, 0, "\t\t" << *v << endl);
		}
	}

	void clear()
	{
		t1Constraints.clear();
		t2Constraints.clear();
		t3Constraints.clear();
		t4Constraints.clear();

		mainConstraints.clear();
    mainSubConstraints.clear();
		predConstraints.clear();

		fprojAbConstraints.clear();
		fprojCcConstraints.clear();

		projAbConstraints.clear();
		projCcConstraints.clear();

		subsConstraints.clear();

		nextStateConstraints.clear();
		nextStateSubConstraints.clear();

		concreteConstraints.clear();
		relevantWires.clear();
		relevantWiresNext.clear();

		t1Set.clear();
		t2Set.clear();
		t3Set.clear();
		t4Set.clear();

		coiAbSet.clear();
		coiCcSet.clear();

		predAbSet.clear();
		predCcSet.clear();

		fprojAbSet.clear();
		fprojCcSet.clear();

		projAbSet.clear();
		projCcSet.clear();

		subsAbSet.clear();

		generalized_s.clear();
		nextMap.clear();
	}
	ABSTRACT_REACH_VIOL()
	{
		clear();
	}
	~ABSTRACT_REACH_VIOL()
	{
		clear();
	}
};
inline std::ostream & operator<<(std::ostream & out, ABSTRACT_REACH_VIOL const & abViol)
{
	int maxSz = 20;
	out << endl;
	if (!abViol.mainConstraints.empty())
	{
		int sz = abViol.mainConstraints.size();
		if (sz < maxSz)
		{
			out << "\t(main cube)" << endl;
			for (auto& c: abViol.mainConstraints)
				out << "\t\t" << *c << endl;
		}
		else
			out << "\t(main cube sz: " << sz << ")" << endl;
	}

	if (!abViol.nextStateConstraints.empty())
	{
		int sz = abViol.nextStateConstraints.size();
		if (sz < maxSz)
		{
			out << "\t(next state)" << endl;
			for (auto& c: abViol.nextStateConstraints)
				out << "\t\t" << *c << endl;
		}
		else
			out << "\t(next state sz: " << sz << ")" << endl;
	}

	if (!abViol.concreteConstraints.empty())
	{
		int sz = abViol.concreteConstraints.size();
		if (sz < maxSz)
		{
			out << "\t(concrete version)" << endl;
			for (auto& c: abViol.concreteConstraints)
				out << "\t\t" << *c << endl;
		}
		else
			out << "\t(concrete version sz: " << sz << ")" << endl;
	}

//	if (!abViol.relevantWires.empty())
//	{
//		int sz = abViol.relevantWires.size();
//		if (sz < maxSz)
//		{
//			out << "\t(wires)" << endl;
//			for (auto& c: abViol.relevantWires)
//				out << "\t\t" << *c << endl;
//		}
//		else
//			out << "\t(# wires: " << sz << ")" << endl;
//	}
//	}
	return out;
}





}




#endif /* SRC_REACH_REACH_CUBE_H_ */
