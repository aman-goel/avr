/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


/*
 * ilang_utils.h
 *
 *  Created on: Jun 6, 2017
 *      Author: rock
 */

#ifndef SRC_VWN_ILANG_UTILS_H_
#define SRC_VWN_ILANG_UTILS_H_

#include <iostream>
#include <stdarg.h>
#include <string>
#include <vector>
#include <map>
#include <set>
#include <unordered_map>
#include <deque>

namespace yos
{


static std::string vstringf(const char *fmt, va_list ap)
{
	std::string string;
	char *str = NULL;

#ifdef _WIN32
	int sz = 64, rc;
	while (1) {
		va_list apc;
		va_copy(apc, ap);
		str = (char*)realloc(str, sz);
		rc = vsnprintf(str, sz, fmt, apc);
		va_end(apc);
		if (rc >= 0 && rc < sz)
			break;
		sz *= 2;
	}
#else
	if (vasprintf(&str, fmt, ap) < 0)
		str = NULL;
#endif

	if (str != NULL) {
		string = str;
		free(str);
	}

	return string;
}

static std::string stringf(const char *fmt, ...)
{
	std::string string;
	va_list ap;

	va_start(ap, fmt);
	string = vstringf(fmt, ap);
	va_end(ap);

	return string;
}


}


#endif /* SRC_VWN_ILANG_UTILS_H_ */
