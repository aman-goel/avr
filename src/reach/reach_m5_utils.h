/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


/*
 * reach_m5_utils.h
 *
 *  Created on: Feb 13, 2019
 *      Author: rock
 */

#ifndef SRC_REACH_REACH_M5_UTILS_H_
#define SRC_REACH_REACH_M5_UTILS_H_

/// MathSAT 5 Backend Utils

#include "reach_m5.h"

#ifdef _M5

namespace _m5 {


#define vmt_logvv(expr)	//cout << expr;
#define vmt_logv(expr)	//cout << expr;
#define vmt_log(expr)	  cout << expr;
#define vmt_logw(expr)	cout << "\t(warning: " << expr << ')' << endl;
#define vmt_logwv(expr)	//cout << "\t(warning: " << expr << ')' << endl;
#define vmt_loge(expr)	cout << "\t(error: " << expr << ')' << endl; \
												assert(0);


struct NODE_INFO {
	msat_term term;
	msat_symbol_tag tag;
	Inst* node;

	NODE_INFO() {
		tag = MSAT_TAG_ERROR;
		node = NULL;
	}
};

inline std::ostream &operator<<(std::ostream &out, NODE_INFO &l) {
	if (l.node != NULL)
//		out << "inst: " << *l.node << '\t' << l.name << '\n';
		out << "inst: " << *l.node << '\n';
	else
		out << "inst: " << "??" << '\t' << "tag:" << l.tag << '\n';
	return out;
}

class VmtFrontend
{
public:
	VmtFrontend(m5_context_ptr ictx) : ctx(ictx) { };
	Inst* traverse_node(msat_term t);

private:
	Inst* process_node(msat_term t, InstL& args);
  void get_node(NODE_INFO& info, InstL& args);
  SORT get_node_type(msat_type& type);
  Inst* process_sig(NODE_INFO& info, int sz, SORT sort);

  m5_context& get_env() { return *ctx; }

  map< msat_term, Inst* > processed;
  m5_context_ptr ctx;
} ;

// Utils

/** generate a suitable configuration for MathSAT, given the input options */
enum ModelGeneration {
    NO_MODEL,
    BOOL_MODEL,
    FULL_MODEL
};

static m5_expr_ptr m5_make_implies(m5_context& ctx, m5_expr_ptr a, m5_expr_ptr b) {
	return msat_make_or(ctx, msat_make_not(ctx, a), b);
}

static m5_expr_ptr m5_make_and(m5_context& ctx, m5_expr_list& args) {
	m5_expr_list::iterator argIt = args.begin();
	m5_expr_ptr out = *argIt;
	argIt++;
	for (; argIt != args.end(); argIt++) {
			out = msat_make_and(ctx, out, *argIt);
	}
	return out;
}

static m5_expr_ptr m5_make_or(m5_context& ctx, m5_expr_list& args) {
	m5_expr_list::iterator argIt = args.begin();
	m5_expr_ptr out = *argIt;
	argIt++;
	for (; argIt != args.end(); argIt++) {
			out = msat_make_or(ctx, out, *argIt);
	}
	return out;
}

static m5_expr_ptr m5_make_neq(m5_context& ctx, m5_expr_ptr a, m5_expr_ptr b) {
	return msat_make_not(ctx, msat_make_eq(ctx, a, b));
}

static m5_expr_ptr m5_make_lt(m5_context& ctx, m5_expr_ptr a, m5_expr_ptr b) {
	return msat_make_and(ctx, msat_make_leq(ctx, a, b), m5_make_neq(ctx, a, b));
}

static m5_expr_ptr m5_make_gt(m5_context& ctx, m5_expr_ptr a, m5_expr_ptr b) {
	return msat_make_not(ctx, msat_make_leq(ctx, a, b));
}

static m5_expr_ptr m5_make_geq(m5_context& ctx, m5_expr_ptr a, m5_expr_ptr b) {
	return msat_make_not(ctx, m5_make_lt(ctx, a, b));
}

}

#endif

#endif /* SRC_REACH_REACH_M5_UTILS_H_ */
