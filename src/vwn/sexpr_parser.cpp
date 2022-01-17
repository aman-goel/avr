/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


#include <cassert>
#include <iostream>
#include "sexpr_parser.hpp"

extern "C" {
#include <fcntl.h>
#include "sexp.h"
#include "cstring.h"
}

using namespace std;

namespace eufabs {
  /*-----------------------------------------------------------------------------*/
  /*SEXPR*/
#define SEXPR ((sexp_t*)_sexpr)

  sexpr::sexpr() : _sexpr(nullptr) {}
  
  sexpr::sexpr(void *s) : _sexpr(s) {}

  void sexpr::destroy() {
    destroy_sexp(SEXPR);
    _sexpr = nullptr;
  }

  sexpr::operator bool() const { return SEXPR != nullptr; }

  bool sexpr::operator==(const sexpr& other) const { return _sexpr == other._sexpr; }

  elt_ty sexpr::getTy() const {
    switch (SEXPR->ty) {
      case SEXP_VALUE: return elt_ty::VALUE;
      case SEXP_LIST:  return elt_ty::LIST;
    }
  }
  
  atom_ty sexpr::getAtomTy() const {
    switch (SEXPR->aty) {
      case SEXP_BASIC:  return atom_ty::BASIC;
      case SEXP_SQUOTE: return atom_ty::SQUOTE;
      case SEXP_DQUOTE: return atom_ty::DQUOTE;
      case SEXP_BINARY: return atom_ty::BINARY;
    }
  }

  const char *const sexpr::getVal() const {
    return SEXPR->val;
  }

  string sexpr::copyVal() const {
    assert(getTy() == elt_ty::VALUE);
    assert(getAtomTy() != atom_ty::BINARY);
    assert(SEXPR->val[SEXPR->val_used-1] == '\0');
    string ret(SEXPR->val, SEXPR->val_used-1);
    return ret;
  }

  sexpr sexpr::getList() const {
    return sexpr(SEXPR->list);
  }
  
  sexpr sexpr::getNext() const {
    return sexpr(SEXPR->next);
  }

  string sexpr::asString() const {
    auto *str = snew(100);
    auto r = print_sexp_cstr(&str, SEXPR, 100);
    string ret(str->base, str->curlen);
    sdestroy(str);
    return ret;
  }
  
#undef SEXPR
  

  /*-----------------------------------------------------------------------------*/
  
  sexpr_parser::sexpr_parser(const string& filename) {
    int fd = open(filename.c_str(), O_RDONLY);
    iowrap = init_iowrap(fd);
    
    sexpr s = getNextSexpr();
    while (s) {
      exprs.emplace_back(s);
      s = getNextSexpr();
    }

    destroy_iowrap((sexp_iowrap_t*) iowrap);
  }

  sexpr_parser::~sexpr_parser() {
    for (auto& sex : exprs) {
      destroy_sexp((sexp_t*)sex._sexpr);
    }
  }

  sexpr sexpr_parser::getNextSexpr() {
    return sexpr(read_one_sexp((sexp_iowrap_t*) iowrap));
  }
  
  sexpr_parser::iterator sexpr_parser::begin() {
    return iterator(*this, std::begin(exprs));
  }
  
  sexpr_parser::iterator sexpr_parser::end() {
    return iterator(*this, std::end(exprs));
  }
}


