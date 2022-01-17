/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


/*
 * btor2_parser.cpp
 *
 *  Created on: Sep 3, 2019
 *      Author: rock
 */


#include <algorithm>

#include "btor2_parser.h"

using namespace std;

namespace bt2
{

Btor2_Parser::Btor2_Parser(string filename) {
	reader = NULL;
	assert (!filename.empty());
	if (!read_ts(filename.c_str())) {
			btor2_loge("unable to read input file " << filename);
	}
}


Btor2_Parser::~Btor2_Parser() {
	if (reader != NULL)
		btor2parser_delete (reader);
}


/**
 * read a transition system from a file in BTOR2 format.
 */
bool Btor2_Parser::read_ts(const char* filename) {
    FILE *f;
		f = fopen(filename, "r");

    if (!f) {
        return false;
    }

    btor2_log("Using Btor2Parser" << endl);

		const char* err;
		btor2_log("\t(reading btor2 file " << filename << ")\n");
		reader = btor2parser_new ();
		if (!btor2parser_read_lines (reader, f)) {
			err = btor2parser_error (reader);
			assert (err);
			btor2_log("\t(parse error in " << filename << ", err: " << err << ")\n");
			btor2parser_delete (reader);
			fclose (f);
			exit (1);
		}
		fclose (f);
		btor2_log("\t(finished parsing btor2 file " << filename << ")\n");
    return true;
}


std::string Btor2_Parser::name(Btor2Line& t, bool skip)
{
	if (skip)
		return "id" + to_string(t.id);
	if (t.symbol)
		return string(t.symbol);
	return "id" + to_string(t.id);
}


}




