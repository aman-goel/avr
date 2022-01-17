/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


#include <string>
#include <unordered_map>
#include <list>
#include "sexpr_parser.hpp"

namespace eufabs {

  enum Keyword {
	$def_constant,
	$def_state_type,
	$def_states,
	$def_transition,
	$def_transition_system,
	$def_query,
	$unknown,

	$initial_states,
	$transition,
	$and,
	$let
  };


  class parse_error : public std::exception {
    std::string _what;
    public:
    parse_error(const std::string& what) : _what(what) {}
    const char *what() const noexcept { return _what.c_str(); }
  };

  class eufabs_parser {

    std::unordered_map<std::string, Keyword> keyHash; // maps string keyword to Keyword

    sexpr_parser sexpparse;

    
    std::list<sexpr> constant;

    std::list<sexpr> state;
    
    std::list<sexpr> input;
    
    std::list<sexpr> gates;

    std::list<sexpr> next;

    std::list<sexpr> initial;

    std::list<sexpr> property;
    
    void init();
    void parseConstant(sexpr);
    void parseVariables(sexpr);
    void parseInitial(sexpr);
    void parseTransition(sexpr);
    void parseSystem(sexpr);
    void parseProperty(sexpr);

    void parseState(sexpr);
    void parseInput(sexpr);
    void parseGate(sexpr);
    void parseNext(sexpr);


    Keyword getKey(std::string);

    public:
    eufabs_parser(const std::string& filename);

    void print() const;

    const std::list<sexpr>& getConstant() const { return constant; }
    const std::list<sexpr>& getState() const { return state; }
    const std::list<sexpr>& getInput() const { return input; }
    const std::list<sexpr>& getGates() const { return gates; }
    const std::list<sexpr>& getNext() const { return next; }
    const std::list<sexpr>& getInitial() const { return initial; }
    const std::list<sexpr>& getProperty() const { return property; }

  };


}
