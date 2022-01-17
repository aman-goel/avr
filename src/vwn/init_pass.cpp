/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


/*
 * init_pass.cpp
 *
 *  Created on: Nov 21, 2018
 *      Author: rock
 */

#include "init_pass.h"

namespace init
{


const char InitParser::specialChars[] = {'(', ')', ',', ';', '#', '*', '\"'};
std::unordered_map <char, bool> InitParser::specCharLibDir;

void InitParser::help()
{
	//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
	init_log("\n");
	init_log("    read_init [filename]\n");
	init_log("\n");
	init_log("Reads the init state in a '.init' file. (.init is a text representation\n");
	init_log("of init/reset state.)\n");
	init_log("\n");
	init_log("Note: Design should be already elaborated and flattened\n");
	init_log("\n");
}

void InitParser::execute()
{
	init_log("Executing INIT pass.\n");
	init_log("\t(file: " << filename << ")" << endl);
	bool status = read_init();

	if (!status)
	{
		init_loge("failure encountered in input file: " << filename);
	}
	else
	{
		process_init();
		print_init();
	}
}

void InitParser::print_init()
{
//	int tsbT = 0;
//	for (auto& v: states)
//		tsbT += v.second->get_size();
//	int tsbI = 0;
//	for (auto& v: map_init)
//		tsbI += v.first->get_size();
//
//	init_logcerr(tsbI << " / " << tsbT << " flops initialized from " << filename);
//
//	init_log("Initial conditions after parsing" << endl);
//	for (auto& m: map_init) {
//		init_log("\t" << *m.first << " = " << *m.second << endl);
//	}
//	init_log(endl);
}

void InitParser::process_init()
{

}

bool InitParser::read_init()
{
	_init();

	deque<string> tokens ;
	bool valid = read_line_as_tokens (is, tokens, false);
	while(valid)
	{
		if(tokens[0] != "")
		{
			Inst* lhs = read_sig(tokens);
			valid = read_line_as_tokens (is, tokens, false);
			Inst* rhs = read_num(tokens);
			if (lhs != NULL) {
				map_init[lhs] = rhs;
//				init_log("\tadding init condition: " << *lhs << " = " << *rhs << endl);
			}
		}
		else
		{
//			init_log("skipping line starting with unknown start keyword: " << tokens[0] << endl);
			// Do nothing
		}
		valid=read_line_as_tokens (is, tokens, false) ;
	}
	_close();
	return true;
}

Inst* InitParser::read_sig(deque < string >& tokens)
{
//	print_tokens(tokens);
	assert(tokens.size() == 1);
	string name = tokens[0];
	name.erase(remove_if(name.begin(), name.end(), ::isspace), name.end());

	Inst* tve;
	map<string, Inst* >::iterator mit = states.find(name);
	if (mit == states.end()) {
		string prefix1 = INIT_PREFIX1;
		string prefix2 = INIT_PREFIX2;
		string suffix = INIT_SUFFIX;
		string old_name = name;

		if (name.compare(0, prefix1.length(), prefix1) == 0) {
			name = name.substr(prefix1.length());
		}
		if (name.compare(0, prefix2.length(), prefix2) == 0) {
			name = name.substr(prefix2.length());
		}
		if (name.compare(name.length() - suffix.length(), suffix.length(), suffix) == 0) {
			name = name.substr(0, name.length() - suffix.length());
		}

		for (map<string, Inst*>::iterator mit2 = states.begin(); mit2 != states.end(); mit2++) {
			size_t found = (*mit2).first.find(name);
			if (found != std::string::npos) {
				mit = mit2;
				init_logw("using similar found match: " << (*mit2).first << " for " << tokens[0]);
				break;
			}
		}

		if (mit == states.end()) {
			init_logw("unable to find signal in init pass for " << tokens[0]);
			return NULL;
		}
	}
	tve = (*mit).second;
	return tve;
}

Inst* InitParser::read_num(deque < string >& tokens)
{
//	print_tokens(tokens);
	assert(tokens.size() == 1);

	std::string s = tokens[0];
	std::string delimiter = "'";

	size_t pos = 0;
	std::string token = "";
	while ((pos = s.find(delimiter)) != std::string::npos)
	{
	    token = s.substr(0, pos);
	    s.erase(0, pos + delimiter.length());
	}
	assert (token != "");

	int sz = stoi(token);
	assert(s.length() > 1);

	char type = s[0];
	s = s.substr(1);

	Inst* num;
	switch(type) {
	case 'b':
		num = NumInst::create(s, sz, 2);
		break;
	case 'd':
		num = NumInst::create(s, sz, 10);
		break;
	case 'h':
		num = NumInst::create(s, sz, 16);
		break;
	default:
		init_loge("unable to decode init number: " << tokens[0]);
	}

	constants.insert(num);
//	init_log ("   creating num: " << *num << " from " << tokens[0] << endl);
	return num;
}

void InitParser::print_tokens(deque < string >& tokens)
{
	for (auto i = 0; i < tokens.size(); i++)
	{
		init_log("[" << i << "] " << tokens[i] << endl);
	}
}

/**
 * Function for initialization of parser
 */
void InitParser::_init(void)
{
	for (int i=0; i < (int)sizeof(specialChars); ++i)
		specCharLibDir[specialChars[i]] = true;
	return;
}

/**
 * Function to close and free input file stream
 */
void InitParser::_close(void)
{
//	free(is);
	is.close();
	return;
}

/**
 * \param is Input .ilang file stream
 * \param tokens Set of words in a line (separated by specified delimiters)
 * \param includeSpecialChars Flag to indicate if special characters to be included
 * \result Returns true if tokens is not empty
 *
 * Reads from the input stream and splits a line into a set of words separated by delimiters
 */
bool InitParser::read_line_as_tokens (istream& is, deque<string>& tokens, bool includeSpecialChars )
{
	tokens.clear();
	string line;
	std::getline (is, line);

	while (is && tokens.empty())
	{
		string token = "" ;
		for (int i = 0; i < (int)line.size(); ++i)
		{
			char currChar = line[i];
			bool isSpecialChar = specCharLibDir[currChar];
//			if (std::isspace (currChar) || isSpecialChar)
			if (isSpecialChar)
			{
				if (!token.empty())
				{
					// Add the current token to the list of tokens
					tokens.push_back(token);
					token.clear();
				}
				if (includeSpecialChars && isSpecialChar)
				{
					tokens.push_back(string(1, currChar));
				}
			}
			else
			{
				// Add the char to the current token
				token.push_back(currChar);
			}
		}
		if (!token.empty())
			tokens.push_back(token);

		// Previous line read was empty. Read the next one.
		if (tokens.empty())
			std::getline (is, line);
	}
	return !tokens.empty();
}

}


