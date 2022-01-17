/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


#include "eufabs_parser.hpp"

extern "C" {
#include <fcntl.h>
}

#include <iostream>

using namespace std; 

namespace eufabs {

  eufabs_parser::eufabs_parser(const string& filename) : sexpparse(filename) {

	init();

    sexpr_parser::iterator sexpr_it = sexpparse.begin();

    while (sexpr_it != sexpparse.end())
    {
		sexpr expression = *sexpr_it++;

		switch (expression.getTy()) {
		  case elt_ty::LIST: {
			sexpr::iterator programListIterator = expression.begin();
			auto programKeyword = *programListIterator++;
			auto prg = programKeyword.copyVal();

			switch (getKey(prg)) {
			case $def_constant          : parseConstant(expression);	break;
			case $def_state_type        : parseVariables(expression);	break;
			case $def_states            : parseInitial(expression);		break;
			case $def_transition        : parseTransition(expression);	break;
			case $def_transition_system : parseSystem(expression);		break;
			case $def_query             : parseProperty(expression);	break;
			default                 : throw parse_error("unexpected keyword");
			}

			break;
		  }

		  default:
			throw parse_error("expected program list");

		}
    }
  }

  void eufabs_parser::print() const {
	cout << "constant:" << endl;
	for (auto& binding : constant) {
		cout << "  " << binding.asString() << endl;
	}

	cout << "state:" << endl;
    for (auto& binding : state) {
    	cout << "  " << binding.asString() << endl;
    }
    
    cout << "input:" << endl;
    for (auto& binding : input) {
    	cout << "  " << binding.asString() << endl;
    }
    
    cout << "gates:" << endl;
    for (auto& binding : gates) {
    	cout << "  " << binding.asString() << endl;
    }
    
    cout << "next:" << endl;
    for (auto& binding : next) {
    	cout << "  " << binding.asString() << endl;
    }
    
    cout << "initial:" << endl;
    for (auto& binding : initial) {
    	cout << "  " << binding.asString() << endl;
    }

    cout << "property:" << endl;
    for (auto& binding : property) {
    	cout << "  " << binding.asString() << endl;
    }

  }


  void eufabs_parser::init() {
	  keyHash["define-constant"]          = $def_constant;
	  keyHash["define-state-type"]        = $def_state_type;
	  keyHash["define-states"]            = $def_states;
	  keyHash["define-transition"]        = $def_transition;
	  keyHash["define-transition-system"] = $def_transition_system;
	  keyHash["query"]                    = $def_query;

	  keyHash["initial_states"]           = $initial_states;
	  keyHash["transition"]				  = $transition;

	  keyHash["and"]			          = $and;
	  keyHash["let"]			          = $let;
  }

  void eufabs_parser::parseConstant(sexpr psexpr) {
	if (!psexpr.isList()) {
	  throw parse_error("constant not a list");
	}

	constant.push_back(psexpr);
  }

  void eufabs_parser::parseVariables(sexpr psexpr) {
	if (!psexpr.isList()) {
	  throw parse_error("variables not a list");
	}

	auto iter = psexpr.begin();
	auto keyword = *iter++;
	auto name = *iter++;

	if (iter != psexpr.end())	parseState(*iter++);
	if (iter != psexpr.end())	parseInput(*iter++);

	assert (iter == psexpr.end());
  }

  void eufabs_parser::parseInitial(sexpr psexpr) {
    if (!psexpr.isList()) {
      throw parse_error("initial not a list");
    }

	auto iter = psexpr.begin();
	auto keyword = *iter++;
	auto name = *iter++;
	auto nameKey = name.copyVal();
	assert(getKey(nameKey) == $initial_states);
	auto type = *iter++;

	if (iter != psexpr.end())
	{
		auto s = *iter++;
		auto bindingiter = s.begin();
		auto name = *bindingiter++;
		auto nameKey = name.copyVal();
		if (getKey(nameKey) != $and)
			initial.push_back(s);
		else
		{
		    while (bindingiter != s.end())
				initial.push_back(*bindingiter++);
		}
	}

	assert (iter == psexpr.end());
  }

  void eufabs_parser::parseTransition(sexpr psexpr) {
    if (!psexpr.isList()) {
      throw parse_error("transition not a list");
    }

	auto iter = psexpr.begin();
	auto keyword = *iter++;
	auto name = *iter++;
	auto nameKey = name.copyVal();
	assert(getKey(nameKey) == $transition);
	auto type = *iter++;

	while (iter != psexpr.end())
	{
		auto s = *iter++;
		auto bindingiter = s.begin();
		auto name = *bindingiter++;
		auto nameKey = name.copyVal();

		Keyword key = getKey(nameKey);
		if (key == $let)
			parseGate(*bindingiter++);
		else if (key == $and)
		{
		    while (bindingiter != s.end())
				parseNext(*bindingiter++);
		}
		else
			parseNext(s);
	}

	assert (iter == psexpr.end());
  }

  void eufabs_parser::parseSystem(sexpr psexpr) {
    if (!psexpr.isList()) {
      throw parse_error("system not a list");
    }

	auto iter = psexpr.begin();
	auto keyword = *iter++;
	auto name = *iter++;
	auto type = *iter++;

	auto init = *iter++;
	auto initKey = init.copyVal();
	assert(getKey(initKey) == $initial_states);

	auto tr = *iter++;
	auto trKey = tr.copyVal();
	assert(getKey(trKey) == $transition);

	assert (iter == psexpr.end());
  }

  void eufabs_parser::parseProperty(sexpr psexpr) {
    if (!psexpr.isList()) {
      throw parse_error("property not a list");
    }

    auto iter = psexpr.begin();
	auto keyword = *iter++;
    iter++;

    property.push_back(*iter++);

	assert (iter == psexpr.end());
  }


  void eufabs_parser::parseState(sexpr psexpr) {
	if (!psexpr.isList()) {
	  throw parse_error("state not a list");
	}

	auto iter = psexpr.begin();

    while (iter != psexpr.end()) {
      auto s = *iter++;
  	  state.push_back(s);
    }
  }
  
  void eufabs_parser::parseInput(sexpr psexpr) {
	if (!psexpr.isList()) {
	  throw parse_error("input not a list");
	}

	auto iter = psexpr.begin();

    while (iter != psexpr.end()) {
      auto s = *iter++;
  	  input.push_back(s);
    }
  }

  void eufabs_parser::parseGate(sexpr psexpr) {
    if (!psexpr.isList()) {
      throw parse_error("gate not a list");
    }

    gates.push_back(psexpr);
  }

  void eufabs_parser::parseNext(sexpr psexpr) {
    if (!psexpr.isList()) {
      throw parse_error("next not a list");
    }

	next.push_back(psexpr);
  }


  Keyword eufabs_parser::getKey(std::string keyword) {
	  if (keyHash.find(keyword) == keyHash.end())
		  return $unknown;
	  return keyHash[keyword];
  }
}
