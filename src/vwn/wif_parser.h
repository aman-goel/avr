/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


/*
 * wif_parser.h
 *
 *  Created on: May 14, 2019
 *      Author: amangoel
 */

#ifndef SRC_VWN_WIF_PARSER_H_
#define SRC_VWN_WIF_PARSER_H_


#include "wif_utils.h"
#include "avr_config.h"

extern ofstream _resFile;
extern Config* config;

namespace _wif {


#define wif_logvv(expr)	//cout << expr;
#define wif_logv(expr)	//cout << expr;
#define wif_log(expr)	cout << expr;
#define wif_logw(expr)	cout << "\t(warning: " << expr << ')' << endl;
#define wif_logwv(expr)	//cout << "\t(warning: " << expr << ')' << endl;
#define wif_loge(expr)	cout << "\t(error: " << expr << ')' << endl; \
												assert(0);


class WifParser;

class WifConvert {
public:
	void help();
	void execute();

	WifConvert(string filename, string wifoptions, string ps);
	~WifConvert();

	list< WifNode > nodes;
	list< pair< string, WifNode* > > safetychecks;
	list< WifNode* > assumes;

private:
	void traverse_system();
	void print_system();

	WifParser* wp;
};

static bool endsWith(const std::string& str, const std::string& suffix)
{
    return str.size() >= suffix.size() && 0 == str.compare(str.size()-suffix.size(), suffix.size(), suffix);
}

}


#endif /* SRC_VWN_WIF_PARSER_H_ */
