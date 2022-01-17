/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


/*
 * btor2_parser.h
 *
 *  Created on: Sep 3, 2019
 *      Author: rock
 */

#ifndef SRC_VWN_BTOR2_PARSER_H_
#define SRC_VWN_BTOR2_PARSER_H_


#include "btor2_utils.h"

namespace bt2
{

#define btor2_logvv(expr)	//cout << expr;
#define btor2_logv(expr)	//cout << expr;
#define btor2_log(expr)	  cout << expr;
#define btor2_logw(expr)	cout << "\t(warning: " << expr << ')' << endl;
#define btor2_logwv(expr)	cout << "\t(warning: " << expr << ')' << endl;
#define btor2_loge(expr)	cout << "\t(error: " << expr << ')' << endl; \
													assert(0);


// equality predicates and hash functions for Btor2Line

inline bool operator==(Btor2Line a, Btor2Line b) {
    return a.id == b.id;
}

inline bool operator!=(Btor2Line a, Btor2Line b) {
    return !(a == b);
}

inline bool operator<(const Btor2Line a, const Btor2Line b) {
  return a.id < b.id;
}

/**
 * A simple class for representing a transition system.
 */
class Btor2_Parser {
public:
	Btor2_Parser(std::string filename);
	///< constructor using Btor2 environment for building terms

	~Btor2_Parser();
	///< destructor for Btor2 environment

	bool read_ts(const char* filename);
	///< reading of the TS

	std::string name(Btor2Line& t, bool skip=true);

protected:
  Btor2Parser* reader;

private:
};


}

#endif /* SRC_VWN_BTOR2_PARSER_H_ */
