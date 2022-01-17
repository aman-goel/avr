/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


/*
 * vmt_parser.h
 *
 *  Created on: Sep 29, 2018
 *      Author: rock
 */

#ifndef SRC_VWN_VMT_PARSER_H_
#define SRC_VWN_VMT_PARSER_H_

#include "vmt_utils.h"

// equality predicates and hash functions for msat_termS

inline bool operator==(msat_term a, msat_term b)
{
    return msat_term_id(a) == msat_term_id(b);
}

inline bool operator!=(msat_term a, msat_term b)
{
    return !(a == b);
}

inline bool operator<(msat_term a, msat_term b)
{
    return msat_term_id(a) < msat_term_id(b);
}

namespace std
{

template<>
struct hash<::msat_term> {
    size_t operator()(::msat_term t) const { return msat_term_id(t); }
};

}

namespace vmt
{

#define vmt_logvv(expr)	//cout << expr;
#define vmt_logv(expr)	//cout << expr;
#define vmt_log(expr)	  cout << expr;
#define vmt_logw(expr)	cout << "\t(warning: " << expr << ')' << endl;
#define vmt_logwv(expr)	//cout << "\t(warning: " << expr << ')' << endl;
#define vmt_loge(expr)	cout << "\t(error: " << expr << ')' << endl; \
												assert(0);


/**
 * Destructor class for msat_env
 */
class EnvDeleter {
public:
    EnvDeleter(msat_env env): env_(env) {}
    ~EnvDeleter()
    {
        if (!MSAT_ERROR_ENV(env_)) {
            msat_destroy_env(env_);
        }
    }

private:
    msat_env env_;
    msat_config cfg_;
};


// some convenience typedefs

typedef std::vector<msat_term> TermList;
typedef std::unordered_map<msat_term, msat_term> TermMap;
typedef std::set<msat_term> TermSet;
typedef std::unordered_set<msat_term> TermHashSet;


/**
 * Apply a substitution to an arbitrary term. cache is used for
 * memoization. func is a unary function invoked on every variable occurring
 * in the input term (that is not already in the cache), which must return the
 * substitution for the variable
 */
template <class Func>
msat_term apply_substitution(msat_env env, msat_term term, TermMap &cache,
                             Func subst)
{
    struct Data {
        Func subst;
        TermMap &cache;
        TermList args;

        Data(Func s, TermMap &c): subst(s), cache(c) {}
    };

    auto visit =
        [](msat_env e, msat_term t, int preorder,
           void *data) -> msat_visit_status
        {
            Data *d = static_cast<Data *>(data);

            if (d->cache.find(t) != d->cache.end()) {
                // cache hit
                return MSAT_VISIT_SKIP;
            }

            if (!preorder) {
                msat_term v;
                msat_decl s = msat_term_get_decl(t);
                if (msat_term_arity(t) == 0 &&
                    msat_decl_get_tag(e, s) == MSAT_TAG_UNKNOWN &&
                    !msat_term_is_number(e, t)) {
                    // t is a variable: get the substitution from the
                    // user-provided function
                    v = d->subst(t);
                } else {
                    // t is not a variable: build the result term from the
                    // results of its children
                    TermList &args = d->args;
                    args.clear();
                    args.reserve(msat_term_arity(t));
                    for (size_t i = 0; i < msat_term_arity(t); ++i) {
                        args.push_back(d->cache[msat_term_get_arg(t, i)]);
                    }
                    v = msat_make_term(e, s, &args[0]);
                }

                d->cache[t] = v;
            }

            return MSAT_VISIT_PROCESS;
        };
    Data data(subst, cache);
    msat_visit_term(env, term, visit, &data);

    return cache[term];
}


/**
 * A simple class for representing a transition system.
 *
 * We represent a transition system (TS) using 3 formulas: init for the
 * initial states, trans for the transition relation, and prop for the
 * invariant property. Init and prop are over a set of state variables X,
 * whereas trans is over state variables X, next-state variables X', and input
 * variables Y.
 */
class MsatParser {
public:
	MsatParser(std::string filename);
	///< constructor using MathSAT environment for building terms

	~MsatParser();
	///< destructor for MathSAT environment

	bool read_ts(std::string filename);
	///< reading of the TS

	void initialize(const TermMap &statevars,
									msat_term init, msat_term trans, TermList &props);
	///< initialization of the TS from the 3 formulas mentioned above and a
	///< map from state variables to their primed version

	msat_env get_env() const { return env_; }

	const TermList &statevars() const { return statevars_; }
	const TermList &inputvars() const { return inputvars_; }
	const TermList &nextstatevars() const { return nextstatevars_; }

	msat_term init() const { return init_; }
	msat_term trans() const { return trans_; }
	const TermList & props() const { return props_; }

	bool is_statevar(msat_term t) const
	{ return statevars_set_.find(t) != statevars_set_.end(); }

	bool is_nextstatevar(msat_term t) const
	{ return nextstatevars_set_.find(t) != nextstatevars_set_.end(); }

	bool is_inputvar(msat_term t) const
	{ return inputvars_set_.find(t) != inputvars_set_.end(); }

	msat_term cur(msat_term next_formula) const;
	///< given a formula f(X',Y) over next-state vars X' and input vars Y,
	///< returns f(X,Y)

	msat_term next(msat_term cur_formula) const;
	///< given a formula f(X,Y) over state vars X and input vars Y,
	///< returns f(X',Y)

	void add_statevar(msat_term c, msat_term n);
	void add_init(msat_term t);
	void add_trans(msat_term t);

	std::string name(msat_term t, bool skip=true);

private:
	void reset();
	void collect_inputs();

	msat_env env_;
	msat_config cfg_;
	TermList statevars_;
	TermList nextstatevars_;
	TermList inputvars_;

	TermSet statevars_set_;
	TermSet nextstatevars_set_;
	TermSet inputvars_set_;

	mutable TermMap cur2next_;
	mutable TermMap next2cur_;
	msat_term init_;
	msat_term trans_;
	TermList props_;
};


}




#endif /* SRC_VWN_VMT_PARSER_H_ */
