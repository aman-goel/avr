/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


/*
 * vmt_parser.cpp
 *
 *  Created on: Sep 29, 2018
 *      Author: rock
 */


#include <algorithm>

#include "vmt_parser.h"

using namespace std;

namespace vmt
{

MsatParser::MsatParser(string filename)
{
    reset();

    cfg_ = msat_create_config();
    env_ = msat_create_env(cfg_);

    if (!read_ts(filename)) {
        vmt_loge("unable to read input file " << filename);
    }
}


MsatParser::~MsatParser()
{
  EnvDeleter del_env(env_);
  msat_destroy_config(cfg_);
}


/**
 * read a transition system from a file in VMT format. VMT is an extension of
 * the SMT-LIBv2 format for specifying fair symbolic transition systems, and
 * for specifying properties over the transition system.
 *
 * VMT exploits the capability offered by the SMT2 language of attaching
 * annotations to terms and formulas in order to specify the components of the
 * transition system and the properties to verify.  More specifically, the
 * following annotations are used:
 *
 * - ":next name" is used to represent state variables. For each variable x in
 *   the model, the VMT file contains a pair of variables, x^c and x^n,
 *   representing respectively the current and next version of x.  The two
 *   variables are linked by annotating x^c with the attribute ":next x^n".
 *   All the variables that are not in relation with another by means of
 *   a ":next" attribute are considered inputs.
 *
 * - ":init true" is used to specify the formula for the initial states of the
 *   model.  This formula should contain neither next-state variables nor
 *   input variables. (The dummy value "true" in the annotation is needed
 *   because the current SMT2 standard requires annotations to always have an
 *   associated value.)
 *
 * - ":trans true" is used to specify the formula for the transition relation.
 *
 * - ":invar-property idx" is used to specify invariant properties.  The
 *   non-negative integer "idx" is a unique identifier for the property. Only
 *   single-property files are supported by this function.
 *
 * - ":predicate true" is used to annotate a predicate used for computing the
 *   initial abstraction.
 *
 * In a VMT file, only annotated terms and their sub-terms are
 * meaningful. Any other term is ignored.  Moreover, only the following
 * commands are allowed to occur in VMT files:
 *
 *   set-logic set-option declare-sort define-sort declare-fun define-fun
 *
 * (For convenience, an additional "(assert true)" command is
 * allowed to appear at the end of the file.)
 */
bool MsatParser::read_ts(string filename)
{
    msat_term *terms;
    char **annots;
    size_t n;

    struct File {
        File(): file(stdin) {}
        ~File()
        {
            if (file && file != stdin) {
                fclose(file);
            }
        }

        FILE *file;
    };
    File f;

    assert (!filename.empty());
		f.file = fopen(filename.c_str(), "r");

    if (!f.file) {
        return false;
    }

    char* version = msat_get_version();
    vmt_log("Using " << version << endl);
    msat_free(version);

    int err = msat_annotated_list_from_smtlib2_file(get_env(), f.file, &n,
                                                    &terms, &annots);

    if (err) {
    		vmt_loge("vmt parsing failed, MathSAT reported error- " << msat_last_error_message(get_env()));
        return false;
    }

    TermMap statevars;
    msat_term init, trans;
    TermList props;

    auto getidx = [](char *v) -> int
        {
            istringstream tmp(v);
            int ret;
            if (!(tmp >> ret)) {
                ret = -1;
            }
            return ret;
        };

    for (size_t i = 0; i < n; ++i) {
        string key(annots[2*i]);
        msat_term t = terms[i];
        if (key == "init") {
            init = t;
        } else if (key == "trans") {
            trans = t;
        } else if (key == "invar-property") {
            int idx = getidx(annots[2*i+1]);
            if (idx < 0) {
                vmt_loge("invalid property index " << annots[2*i+1] << endl);
                return false;
            } else {
                props.push_back(t);
            }
        } else if (key == "next") {
            string val(annots[2*i+1]);
            if (val.length() && val[0] == '|') {
                val = val.substr(1, val.length()-2);
            }
            msat_decl d = msat_find_decl(get_env(), val.c_str());
            if (MSAT_ERROR_DECL(d)) {
                d = msat_declare_function(get_env(), val.c_str(),
                                          msat_term_get_type(terms[i]));
            }
            msat_term n = msat_make_constant(get_env(), d);
            statevars[t] = n;
        }
    }

    initialize(statevars, init, trans, props);

    msat_free(terms);
    for (size_t i = 0; i < n; ++i) {
        msat_free(annots[2*i]);
        msat_free(annots[2*i+1]);
    }
    msat_free(annots);

    vmt_log("parsed system with " << statevars.size() << " state variables" << endl);

    return true;
}


void MsatParser::initialize(
    const TermMap &statevars,
    msat_term init, msat_term trans, TermList &props)
{
    reset();

    for (auto p : statevars) {
        statevars_.push_back(p.first);
    }
    sort(statevars_.begin(), statevars_.end());

    for (auto s : statevars_) {
        msat_term n = statevars.find(s)->second;
        nextstatevars_.push_back(n);
        cur2next_[s] = n;
        next2cur_[n] = s;
        statevars_set_.insert(s);
        nextstatevars_set_.insert(n);

        // Log
        vmt_logv("adding statevar: " << name(s) << endl);
        vmt_logv("\twith next: " << name(n) << endl);
    }

    init_ = init;
    trans_ = trans;
    for (auto p: props) {
    	props_.push_back(p);
    }

    collect_inputs();

//    // Log
//    vmt_logv("adding init : " << name(init) << endl);
//    vmt_logv("adding trans: " << name(trans) << endl);
//    for (auto p: props) {
//			vmt_logv("adding prop : " << name(p) << endl);
//    }
}


void MsatParser::reset()
{
    statevars_.clear();
    nextstatevars_.clear();
    inputvars_.clear();

    statevars_set_.clear();
    nextstatevars_set_.clear();
    inputvars_set_.clear();

    cur2next_.clear();
    next2cur_.clear();
}


void MsatParser::collect_inputs()
{
    auto visit = [](msat_env e, msat_term t, int preorder,
                    void *data) -> msat_visit_status
        {
            TermList *out = static_cast<TermList *>(data);
            // a variable is a term with no children and no built-in
            // interpretation
            if (preorder &&
                msat_term_arity(t) == 0 &&
                msat_decl_get_tag(
                    e, msat_term_get_decl(t)) == MSAT_TAG_UNKNOWN &&
                !msat_term_is_number(e, t)) {
                out->push_back(t);
            }
            return MSAT_VISIT_PROCESS;
        };

    TermList allvars;
    // mark all variables in T, P, I that are not state vars as inputs
    msat_visit_term(env_, trans_, visit, &allvars);
    for (auto& p: props_)
    	msat_visit_term(env_, p, visit, &allvars);
    msat_visit_term(env_, init_, visit, &allvars);

    for (msat_term v : allvars) {
        if (statevars_set_.find(v) == statevars_set_.end() &&
            nextstatevars_set_.find(v) == nextstatevars_set_.end()) {
            inputvars_.push_back(v);
            cur2next_[v] = v;
            next2cur_[v] = v;
            inputvars_set_.insert(v);

            // Log
            vmt_logv("adding input: " << name(v) << endl);
        }
    }
    sort(inputvars_.begin(), inputvars_.end());
}


msat_term MsatParser::cur(msat_term next_formula) const
{
    auto it = next2cur_.find(next_formula);
    if (it != next2cur_.end()) {
        return it->second;
    }
    auto identity = [](msat_term v) -> msat_term { return v; };
    // next2cur_ is already filled for state variables, so identity will only
    // be called for input vars (see apply_substitution in utils.h)
    return apply_substitution(env_, next_formula, next2cur_, identity);
}


msat_term MsatParser::next(msat_term cur_formula) const
{
    auto it = cur2next_.find(cur_formula);
    if (it != cur2next_.end()) {
        return it->second;
    }
    auto identity = [](msat_term v) -> msat_term { return v; };
    // cur2next_ is already filled for state variables, so identity will only
    // be called for input vars (see apply_substitution in utils.h)
    return apply_substitution(env_, cur_formula, cur2next_, identity);
}


void MsatParser::add_statevar(msat_term c, msat_term n)
{
    statevars_.push_back(c);
    nextstatevars_.push_back(n);
    cur2next_[c] = n;
    next2cur_[n] = c;
    statevars_set_.insert(c);
    nextstatevars_set_.insert(n);
}


void MsatParser::add_init(msat_term t)
{
    init_ = msat_make_and(env_, init_, t);
}


void MsatParser::add_trans(msat_term t)
{
    trans_ = msat_make_and(env_, trans_, t);
}


std::string MsatParser::name(msat_term t, bool skip)
{
	if (skip)
		return "id" + to_string(msat_term_id(t));

	char* sp = msat_term_repr(t);
  string s = string(sp);
  msat_free(sp);
  return s;
}


}


