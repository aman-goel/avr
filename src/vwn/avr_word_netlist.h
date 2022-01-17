/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


#ifndef AVERROES_FLOW_WN_H__
#define AVERROES_FLOW_WN_H__

/* 
 wn.h
 Word-level Netlist
 */

#include <iostream>
#include <list>
#include <vector>
#include <map>
#include <set>
#include <assert.h>
#include <sstream>
#include <gmpxx.h>
#include "avr_util.h"
#include "avr_config.h"
#include <cstring>
#include <stdlib.h>

// extern "C" {
// #include"yices_c.h"
// }

#define WN_VERSION 0.1

#define USE_INTERMEDIATE_NAMES

#define NEXT_SUFFIX "$next"
#define NEXT_SUFFIX_LENGTH 5

#define NUM    0	// 0: Contains Num as a child
#define SIG    1	// 1: Contains Sig as a child
#define NEXT   2	// 2: Contains (or is) a next sig


typedef enum {
	// Signal
	Sig,
	// Number
	Num,
	/// Aman
	// Internal Signal
	Wire,
	// Constant
	Const,
	/// END
	// Operation
	Op,
	// Extraction
	Ex,
	// Memory
	Mem,
	// UF
	UF,
	// now, things that were used in software verification!
	// Lambda
	Lambda,
	// Array. Can be equated to other arrays or to Lambdas!
	Array
} InstType;

class Inst;

struct compare {
	bool operator()(Inst* left, Inst* right) const;
};

struct compare_pair_unsigned {
	bool operator()(const pair< Inst*, unsigned >& left, const pair< Inst*, unsigned >& right) const;
};

typedef std::list<Inst*> InstL;
typedef std::list<InstL> InstLL;
typedef std::vector<Inst*> InstV;
typedef std::set<std::string> StringS;
typedef std::map<std::string,Inst*> SigToInstM;

typedef set<Inst*, compare> InstS;
typedef map<Inst*, Inst*, compare> InstToInstM;
typedef map<Inst*, InstS, compare> InstToSetM;
typedef map<Inst*, unsigned, compare> InstToUintM;
typedef map<Inst*, string, compare> InstToStringM;
typedef map<Inst*, list<pair<Inst*, Inst*> >, compare> InstToListPairM;
typedef map< pair < Inst*, unsigned >, Inst*, compare_pair_unsigned> PairUintToInstM;

#define INT_SZ 2

typedef enum {
	bvtype = 0,
	arraytype,
	inttype
}SortType;

struct SORT {
	SortType type;
	unsigned sz;						// size for bvtype
	vector<SORT> args;

	SORT(unsigned s = 0) {
		type = bvtype;
		sz = s;
	}
	SORT(SortType t, unsigned s = 0) {
		type = t;
		sz = s;
	}
	SORT(SortType t, unsigned w, unsigned s) {
		assert(t == arraytype);
		type = t;
		args.push_back(SORT(w));
		args.push_back(SORT(s));
		sz = s;
	}
	SORT(SortType t, SORT d, SORT r) {
		assert(t == arraytype);
		type = t;
		args.push_back(d);
		args.push_back(r);
		sz = r.sz;
	}
	bool operator<(const SORT &rhs)  const {
		if (this->type == rhs.type)
			if (this->type == bvtype)
				return (this->sz < rhs.sz);
			else
				return this->args < rhs.args;
		else
			return this->type < rhs.type;
	}
	bool operator==(const SORT &rhs)  const {
		return (this->type == rhs.type) &&
					 ((this->type == bvtype) ? (this->sz == rhs.sz) : (this->args == rhs.args));
	}
	bool operator!=(const SORT &rhs)  const {
		return (this->type != rhs.type) ||
				 ((this->type == bvtype) ? (this->sz != rhs.sz) : (this->args != rhs.args));
	}
	string sort2str() {
		switch(type) {
		case bvtype:
			return "bv" + to_string(sz);
		case arraytype:
			return "arr$" + args.front().sort2str() + "$" + args.back().sort2str();
		case inttype:
			return "int";
		default:
			return "unknown";
		}
		return "unknown";
	}
};
inline std::ostream &operator<<(std::ostream &out, SORT &s) {
	out << s.sort2str();
	return out;
}

// Instance
class Inst{
public:
	bool operator< (const Inst& obj) const {
		if(obj.m_id < this->m_id)
			return true;
	}
	bool operator< (const Inst* obj) const {
		if(obj && obj->m_id < this->m_id)
			return true;
		return false;
	}

	// API
	// print the instance recursively (textuall)
	virtual void print(std::ostream&) = 0;
	// print the instance locally (no recursion)
	virtual void print_summary(std::ostream&);
	// print the instance locally (no recursion), using Verilog syntax!
	virtual void print_verilog(std::ostream&);
	// auxialiary function for print_verilog!
	void print_verilog_name(std::ostream&);
	// get bit-width
	unsigned get_size() {
		return m_size;
	}
	SORT get_sort() {
		return m_sort;
	}
	SortType get_sort_type() {
		return m_sort.type;
	}
	unsigned get_sort_sz() {
		return m_sort.sz;
	}
	SORT* get_sort_domain() {
		if (m_sort.args.size() == 2)
			return &m_sort.args.front();
		else
			return NULL;
	}
	SORT* get_sort_range() {
		if (m_sort.args.size() == 2)
			return &m_sort.args.back();
		else {
			cout << m_sort.sort2str() << endl;
			assert(0);
		}
	}

	// get type (of the InstType's above)
	virtual InstType get_type() = 0;
	virtual void print_blif(std::ostream &out) = 0;
	virtual std::string get_blif_name();
	static std::string blif_suffix(unsigned);
	virtual Inst *bit_blast(InstToInstM& bb_map, bool init_visit = false) = 0;
	virtual Inst *split_signals(InstToInstM& bb_map, bool init_visit = false) = 0;
	// get a uniqifier.
	unsigned get_id() {
		return m_id;
	}
	// allocate a new id.
	static unsigned allocate_id() {
		return st_id++;
	}
	// call in order to free all instances
	static void uncreate_all();
	// print sizes of all instances
	static void dump_size_all(std::ostream&);
	// use as follows:
	// init_visit() ... before any new traversal
	// if(get_visit())
	//   skip...
	// else: set_visit .. and process instance
	std::set<int> m_pbb;	// how to split, {1, 8, 9} means {[31,9], [8:8], [7:1] ,[0]}
	unsigned get_count() {
		return m_tcnt;
	}
	void inc_count() {
		m_tcnt++;
	}
	bool dec_count() {
		m_tcnt--;
		if(m_tcnt == 0){
			return true;
		}
		return false;
	}
	void set_visit() {
		m_visit = st_visit;
	}
	void unset_visit() {
		m_visit--;
	}
	bool get_visit() {
		return m_visit == st_visit;
	}
	void set_visit2() {
		m_visit2 = st_visit2;
	}
	bool get_visit2() {
		return m_visit2 == st_visit2;
	}
	static void init_visit() {
		st_visit++;
	}
	static void init_visit2() {
		st_visit2++;
	}
	// returns null if there are no children!
	virtual const InstL* get_children() = 0;
	// see below simplification rules supported (and enabled)
	// this function marks the simplified nodes with 'visit', and avoids simplifying a node that has the 'visit' flag on!
	//    virtual Inst* simplify() = 0;
	// return a new instance with a new set of children!
	virtual Inst* apply_children(InstL&args, bool to_simplify = true);
	// searches for an instance that matches 'src' (based on the is_similar predicate), and
	// when encountered, replaces it with 'tgt'.
	Inst* replace_child(Inst*src, Inst*tgt);
	Inst* replace_child_by_stripping_header(std::string header);
	// stupid implementation: goes over the list of ALL nodes!
	static Inst* get_node(unsigned id);
	// checks consistency (mainly size compatibility).
	// if not consistent, prints the erratic instance to the stream.
	virtual bool check_consistency(std::ostream& out);
	// am I similar to e?
	// we don't use any advanced properties here.
	// for example, a=b and b=a are 2 similar instances.
	// this function can eb augmented if needed.
	virtual bool is_similar(Inst* e) {
		return (get_type() == e->get_type()) && (m_size == e->get_size()) && (m_hash1 = e->get_hash1()) && (m_hash1 < 10);
	}
	virtual int instcmp(Inst* e);
	unsigned get_hash1() {
		return m_hash1;
	}
	void set_hash1(unsigned h) {
		m_hash1 = h;
	}

	class RecService {
	public:
		RecService() :
			postorder(true) {
		}
		virtual void serve(Inst*) = 0;
		virtual ~RecService() {
		}
		// true for post-order traversal, false for pre-order
		bool postorder;
	};

	// a generic recursive service! (POSTORDER-type traversal!)
	// pass a child of RecService and use the function
	// to traverse (and do something!) on each node encountered.
	// (nodes that share pointers are visited just once!)
	void serve(RecService*);

	virtual ~Inst() {
	}

	typedef std::set<std::string> StringS;
	// (change the design.. it's a bit wacky!)
	// used by print_verilog
	static StringS st_printed_signals;

	///////// arguments that control simplification during creation.
	// sig[7:0] is replaced by sig for an 8-bits signal sig
	static bool wn_simplify_extract_adv;
	static bool wn_simplify_extract;
	// {one element} is replaced by the element
	static bool wn_simplify_concat;
	// 1 & 1 = 1, 1 & 0 = 0, etc.
	static bool wn_simplify_const_pred;
	// addition and subtraction of constants is replaced by the result!
	// also a+c1=a+c2 is replaced by the value c1==c2. example, a+5=a+6 is replaced by 0, and a+2=a+2 by 1, and a=a+4 by 0.
	static bool wn_simplify_const_num;
	// prune then or else branches for ITEs
	static bool wn_simplify_ite;
	// a & a = a, ite(p,x,x)=x, etc.
	static bool wn_simplify_repetition;
	// binary &, binary |, and ~ applied on 1-bit signals are turned into &&, ||, and !
	static bool wn_1bit_dp_to_control;
	// a=a is 1.
	static bool wn_simplify_eq;
	static void turn_off_wn_simplify() {
		wn_simplify_extract = false;
		wn_simplify_concat = false;
		wn_simplify_const_pred = false;
		wn_simplify_const_num = false;
		wn_simplify_ite = false;
		wn_simplify_repetition = false;
		wn_1bit_dp_to_control = false;
		wn_simplify_eq = false;
	}

	virtual Inst* get_port(void)
	{
		return this;
	}

	//std::vector<unsigned> m_solver_visit;
	// YICES variable
	// Can be more than one... allows different solver to work on the same
	// instance and save, each one, their own yvar!
	std::vector<void *> yvar;
	// what does the current instance equal to under the given ACEX.
	// eval_term assigns this!
	Inst* acex_coi;

	int	cex_val;	// set 0 or 1 if m_size is one (i.e. control signals)
	mpz_class cex_mpz;
	virtual void write_bin();

	bool find_next()
	{
		return childrenInfo[NEXT];
	}

	bool find_sig()
	{
		return childrenInfo[SIG];
	}

	// 0: Contains Num as a child
	// 1: Contains Sig as a child
	// 2: Has next sig
	bool childrenInfo[3];

	bool is_rhs; //TODO
	unsigned term_of_consts;	// 2: not yet computed, 1: true, 0: false
protected:

	unsigned m_size;
	SORT m_sort;
	unsigned m_id;
	// fast characterizations for a node
	// currently: hash1 is the # of nodes in the subtree, including itself!
	unsigned m_hash1;

	static unsigned st_id;
	friend class Trans;
	friend class ExInst;
	friend class OpInst;
	friend class MemInst;

	// called when this instance is simplified to a new instance e
	// 'masked' is described above (in "on_simplify").
	// returns e2
	//TODO remove this
	static Inst* finalize_simplify(Inst*e1, Inst* e2, InstL masked);

protected:

	// you can't call!
	Inst();
	static InstL m_exps_pool;

private:

	unsigned m_tcnt;	// temporary counter
	unsigned m_visit;
	unsigned m_visit2;
	static unsigned st_visit;
	static unsigned st_visit2;
	virtual void serve(RecService*, bool init);
};

// Signal
class SigInst: public Inst {
public:
	typedef std::map<std::string, Inst*> StrVM;
	static StrVM hm_SigInst;// hash map of NumInst

	static Inst* create(std::string name, unsigned size, SORT sort);
	static SigInst* as(Inst* e) {
		return dynamic_cast<SigInst*> (e);
	}
	virtual InstType get_type() {
		return Sig;
	}
	virtual void print(std::ostream&);
	virtual void print_summary(std::ostream&);
	virtual void print_verilog(std::ostream&);
	const InstL* get_children() {
		return 0;
	}
	//    virtual Inst* simplify();
	virtual bool check_consistency(std::ostream& out) {
		return Inst::check_consistency(out);
	}
	virtual bool is_similar(Inst* e);
	virtual int instcmp(Inst* e);

	std::string get_name() {
		return m_name;
	}
	virtual void print_blif(std::ostream &out);
	virtual std::string get_blif_name(); // auxialiary function for print_blif!
	virtual Inst *bit_blast(InstToInstM& bb_map, bool init_visit = false);
	virtual Inst *split_signals(InstToInstM& bb_map, bool init_visit = false);
	static std::string dollar_dot_to_underscore(std::string);
	static Inst *read_bin();
	virtual void write_bin();
protected:

	bool is_next(void)
	{
		unsigned sz = m_name.length();
		if (sz < NEXT_SUFFIX_LENGTH)
			return false;
		return (m_name.substr(sz - NEXT_SUFFIX_LENGTH) == NEXT_SUFFIX);
	}

	std::string m_name;
	// you can't call!
	SigInst(std::string name, unsigned size, SORT sort){
		m_sort = sort;
		m_size = size;
		m_name = name;

		childrenInfo[NUM]    = false;
		childrenInfo[SIG]    = true;
		childrenInfo[NEXT]   = is_next();
	}
private:
	static SigInst* create();
	friend class Trans;

};

/// Aman
// Internal signal
class WireInst: public Inst {
public:
	typedef map<string, Inst*> WireVM;
	static WireVM hm_WireInst;// hash map of WireInst

	static Inst* create(string name, unsigned sz, Inst* port = NULL);
	static WireInst* as(Inst*e) {
		return dynamic_cast<WireInst*> (e);
	}
	virtual ~WireInst() {
	}

	virtual InstType get_type() {
		return Wire;
	}
	virtual void print(ostream&);
	virtual void print_summary(ostream&);
	virtual void print_verilog(ostream&);

	virtual bool check_consistency(ostream& out) {
		return Inst::check_consistency(out);
	}
	virtual bool is_similar(Inst* e);
	virtual int instcmp(Inst* e);

	virtual void print_blif(ostream &out);
	virtual Inst *split_signals(InstToInstM& bb_map, bool init_visit = false);
	virtual Inst *bit_blast(InstToInstM& bb_map, bool init_visit = false);

	string get_name() {
		return m_name;
	}

	void set_name(string name)
	{
//		cout << "Renaming " << m_name << " to " << name << endl;
		m_name = name;
	}

	const InstL* get_children() {
		return &m_exps;
	}

	Inst* get_port() {
		if (m_exps.empty())
		{
			assert(0);
			return NULL;
		}
		return m_exps.front();
	}
	void set_port(Inst* port) {
//		cout << "(setting port of " << this << " to " << port << ")" << endl;

		assert (port->get_type() == Op || port->get_type() == Ex);
		m_exps.push_back(port);
		assert(m_exps.size() == 1);
	}
	void update_port(Inst* port) {
//		cout << "(updating port of " << this << " to " << port << ")" << endl;

		assert (port->get_type() == Op || port->get_type() == Ex);
		assert(m_exps.size() == 1);
		m_exps.pop_back();
		m_exps.push_back(port);
	}

	static Inst *read_bin();
	virtual void write_bin();

private:
	string m_name;
	InstL m_exps;

//	WireInst(string name, unsigned sz)
//	{
//		m_name = name;
//		m_size = sz;
//	}

	WireInst(Inst* port, string name)
	{
		assert(name != "");
		m_name = name;
		m_size = port->get_size();
		m_sort = port->get_sort();
		set_port(port);
		assert(m_exps.size() == 1);
		childrenInfo[NUM]    = port->childrenInfo[NUM];
		childrenInfo[SIG]    = port->childrenInfo[SIG];
		childrenInfo[NEXT]   = port->childrenInfo[NEXT];
	}
private:
	static WireInst* create();
	friend class Trans;
};
/// END

// Number
class NumInst: public Inst {
public:
	typedef std::pair<mpz_class, std::pair<unsigned, SORT>> NumType;
	struct NumType_comp {
		bool operator()(const NumType& lhs, const NumType& rhs) const {
			if (lhs.second == rhs.second) {
				return lhs.first < rhs.first;
			}
			return lhs.second < rhs.second;
		}
	};

	typedef std::map<NumType, Inst*, NumType_comp> NumHashM;	// <num, size>
	static NumHashM hm_NumInst;// hash map of NumInst
//	static SNumHashM hm_SNumInst;// hash map of NumInst whose width is bigger than 64

	static Inst* create(std::string snum, unsigned size, unsigned base, SORT sort = SORT());
	static Inst* create(unsigned long num, unsigned size);
	static Inst* create(mpz_class mnum, unsigned size);
	
	static NumInst* as(Inst*e) {
		return dynamic_cast<NumInst*> (e);
	}
	virtual ~NumInst() {
	}

	virtual InstType get_type() {
		return Num;
	}
	virtual void print(std::ostream&);
	virtual void print_summary(std::ostream&);
	virtual void print_verilog(std::ostream&);
	virtual void print_blif(std::ostream &out);
	//	virtual std::string get_blif_name(); // auxialiary function for print_blif!
	virtual Inst *bit_blast(InstToInstM& bb_map, bool init_visit = false);
	virtual Inst *split_signals(InstToInstM& bb_map, bool init_visit = false);
	const InstL* get_children() {
		return 0;
	}
	//    virtual Inst* simplify();
	virtual bool check_consistency(std::ostream& out) {
		return Inst::check_consistency(out);
	}
	virtual bool is_similar(Inst* e);
	virtual int instcmp(Inst* e);

	mpz_class *get_mpz(){
		return &m_mpz;
	}

	long long get_num() {
		return m_mpz.get_si();
	}

	static Inst *read_bin();
	virtual void write_bin();

private:
	mpz_class m_mpz;

	// you can't call!
	NumInst(unsigned long num, unsigned size, SORT sort) {
		m_sort = sort;
		m_size = size;
		m_mpz = mpz_class(num);

		childrenInfo[NUM]    = true;
		childrenInfo[SIG]    = false;
		childrenInfo[NEXT]   = false;
	}
// 	NumInst(std::string snum = "0", unsigned size = 0, unsigned base = 10) {
// 		m_size = size;
// 		m_mpz.set_str(snum, base);
// 	}
	NumInst(mpz_class mnum, unsigned size, SORT sort) {
		m_sort = sort;
		m_size = size;
		m_mpz = mnum;

		childrenInfo[NUM]    = true;
		childrenInfo[SIG]    = false;
		childrenInfo[NEXT]   = false;
	}
private:
	static NumInst* create();
	friend class Trans;

};

/// Aman
// Constant
class ConstInst: public Inst {
public:
	typedef map<string, Inst*> ConstVM;
	static ConstVM hm_ConstInst;// hash map of ConstInst

	static Inst* create(string name, unsigned size);
	static ConstInst* as(Inst*e) {
		return dynamic_cast<ConstInst*> (e);
	}
	virtual ~ConstInst() {
	}

	virtual InstType get_type() {
		return Const;
	}
	virtual void print(ostream&);
	virtual void print_summary(ostream&);
	virtual void print_verilog(ostream&);

	const InstL* get_children() {
		return 0;
	}
	virtual bool check_consistency(ostream& out) {
		return Inst::check_consistency(out);
	}
	virtual bool is_similar(Inst* e);
	virtual int instcmp(Inst* e);

	virtual void print_blif(ostream &out);
	virtual Inst *split_signals(InstToInstM& bb_map, bool init_visit = false);
	virtual Inst *bit_blast(InstToInstM& bb_map, bool init_visit = false);

	string get_name() {
		return m_name;
	}

	static Inst *read_bin();
	virtual void write_bin();

private:
	string m_name;
	ConstInst(string name, unsigned size, SORT sort) :
		m_name(name) {
		m_sort = sort;
		m_size = size;
		childrenInfo[NUM]    = false;
		childrenInfo[SIG]    = false;
		childrenInfo[NEXT]   = false;
	}
private:
	static ConstInst* create();
	friend class Trans;
};
/// END

// operator instance
class OpInst: public Inst {
public:
	typedef struct OpHash {
		unsigned a;
		unsigned b;
		unsigned c;
	} OpHash;

	struct OpHash_comp {
		bool operator()(const OpHash& lhs, const OpHash& rhs) const {
			if (lhs.a == rhs.a) {
				if (lhs.b == rhs.b) {
					return lhs.c < rhs.c;
				} else {
					return lhs.b < rhs.b;
				}
			}
			return lhs.a < rhs.a;
		}
	};
	typedef std::map<OpHash, Inst*, OpHash_comp> OpHashM;
	typedef std::multimap<OpHash, Inst*, OpHash_comp> OpHashMM;
	static OpHashM hm_OpInst;//(type, inst_1, inst_2)
	static OpHashM hm_ITEInst;//(inst_1, inst_2, inst_3)
	static OpHashMM hm_ETCInst;//(inst_1, inst_2, inst_3)

#if 0
	typedef enum {
		Unknown,
		Extract,
		// Operands are from left to right
		Concat,
		Minus,Add,Sub,Mult,Div,Mod,
		Eq,NotEq,Gr,Le,GrEq,LeEq,
		BitWiseAnd,BitWiseOr,BitWiseNot,BitWiseXor,
		BitWiseXNor,BitWiseNor,BitWiseNand,
		LogAnd,LogOr,LogNot,
		ReductionAnd,ReductionOr,ReductionXor,ReductionXNor,
		ReductionNand,ReductionNor,
		ShiftL,ShiftR,
		Ternary,
		Future
	}OpType;
#else
	typedef enum {
		Unknown, Extract,
		// Operands are from left to right
		Concat,
		Minus,
		Add,//add without a carry out : i.e. input width = n, output width = n
		AddC,//add with a carry out : i.e. input width = n, output width = (n+1)
		Sub,
		Mult,
		Div,
		SDiv,
		Rem,
		SRem,
		SMod,
		Eq,
		NotEq,
		Gr,
		SGr,
		Le,
		SLe,
		GrEq,
		SGrEq,
		LeEq,
		SLeEq,
		Sext,		// sign extend
		Zext,		// zero extend
		BitWiseAnd,
		BitWiseOr,
		BitWiseNot,
		BitWiseXor,
		BitWiseXNor,
		BitWiseNor,
		BitWiseNand,
		LogTrue,
		LogFalse,
		Identity,
		LogAnd,
		LogOr,
		LogNot,
		LogNand,
		LogNor,
		LogXor,
		LogXNor,
		ReductionAnd,
		ReductionOr,
		ReductionXor,
		ReductionXNor,
		ReductionNand,
		ReductionNor,
		ShiftL,		// Logical shift left
		ShiftR,		// Logical shift right
		AShiftR,	// Arithmetic shift right
		AShiftL,	// Arithmetic shift left : not used
		RotateL,
		RotateR,
		// V* operators are introduced to handle calypto benchmarks
		VShiftL,	// Logical shift left by non-constant amount
		VShiftR,	// Logical shift right by non-constant amount
		VAShiftL,	// Arithmetic shift left by non-constant amount	: NOT USED (use VShiftL instead)
		VAShiftR,	// Arithmetic shift right by non-constant amount
		VRotateL,// rotate left by non-constant amount
		VRotateR,// rotate right by non-constant amount
		VEx,			// one-bit extraction of non-constant index (ex. a[b])
		Ternary,
		ArrayConst,  // array = arrayconst (width, sz, value)
		ArraySelect, // value = arrayselect(array, addr)
		ArrayStore,  // array = arraystore (array, addr, value)
		IntAdd,	// integer addition
		IntSub,	// integer subtraction
		IntMult,	// integer multiplication
		IntDiv,	// integer division
		IntFloor,// integer floor
		IntLe,	// integer less than
		IntLeEq,	// integer less than equal to
		IntGr,	// integer greater than
		IntGrEq,	// integer greater than equal to
		IntMod,	// integer modular congruence
		IntMinus, // integer minus (i.e. unary negation)
		Future
	} OpType;
#endif
	virtual void print_blif(std::ostream &out);
	virtual Inst *bit_blast(InstToInstM& bb_map, bool init_visit = false);
	Inst *bit_blast_table(OpType op_type, InstL &chs_top);

	virtual Inst *split_signals(InstToInstM& bb_map, bool init_visit = false);
	Inst *split_signals_table(OpType op_type, InstL &chs_top);

	static Inst* create(OpType op, InstL exps, int o_size=0, bool to_simplify = true, Inst* wire=NULL, SORT sort = SORT());
	static Inst* create(OpType op, Inst* exp1, Inst* exp2 = 0, Inst* exp3 = 0, int o_size=0, bool to_simplify = true, Inst* wire=NULL, SORT sort = SORT());

	static OpInst* as(Inst*e) {
		return dynamic_cast<OpInst*> (e);
	}
	virtual void print(std::ostream&);
	virtual void print_summary(std::ostream&);
	virtual void print_verilog(std::ostream&);
	virtual InstType get_type() {
		return Op;
	}
	static std::string op2str(OpType t);
	const InstL* get_children() {
		return &m_exps;
	}
	//    virtual Inst* simplify();
	virtual bool check_consistency(std::ostream& out);
	virtual bool is_similar(Inst* e);
	virtual int instcmp(Inst* e);

	OpType get_op() {
		return m_op;
	}
	const InstL& get_exps() {
		return m_exps;
	}
	static void print_blif_table(std::ostream&out, OpType t, std::string i0, unsigned w_i0,
								 std::string i1, unsigned w_i1, std::string i2, unsigned w_i2,
								 std::string o, unsigned w_o, Inst *e = NULL);
	static Inst *read_bin();
	string get_euf_func_name();
	string get_euf_type_name();

	Inst* get_wire() {
		return m_wire;
	}
	void set_wire(Inst* wire) {
		m_wire = wire;
	}

protected:
	OpType m_op;
	InstL m_exps;
	string euf_func_name;

	Inst* m_wire;

	// you can't call!
	OpInst(OpType op, InstL exps, int o_size, Inst* wire, SORT sort) :
		m_op(op), m_exps(exps), m_wire(wire) {
		calc_size();
		if(o_size != 0){
			m_size = o_size;
		}
		m_sort.sz = m_size;

		if (op == Eq || op == NotEq) {
			assert(exps.front()->get_sort() == exps.back()->get_sort());
		}

		childrenInfo[NUM]    = false;
		childrenInfo[SIG]    = false;
		childrenInfo[NEXT]   = false;
		for (InstL::iterator it = exps.begin(), end_it = exps.end(); it != end_it; ++it)
		{
			childrenInfo[NUM]    	|= (*it)->childrenInfo[NUM];
			childrenInfo[SIG]    	|= (*it)->childrenInfo[SIG];
			childrenInfo[NEXT]   	|= (*it)->childrenInfo[NEXT];
		}
	}
	OpInst(OpType op, Inst* exp, int o_size, Inst* wire, SORT sort) :
		m_op(op), m_wire(wire) {
		m_exps.push_back(exp);
		if(o_size == 0){
			calc_size();
		}else{
			m_size = o_size;
			m_sort = sort;
		}
	}
	OpInst() {
	}
	virtual void write_bin();

protected:
	static OpInst* create();
	friend class Trans;
	virtual void calc_size();
};

// extraction (with constant indices)
class ExInst: public OpInst {
public:
	static OpHashM hm_ExInst;//(type, inst_1, inst_2)	

	static Inst* create(Inst* exp, unsigned hi, unsigned lo, Inst* wire=NULL);
	static ExInst* as(Inst*e) {
		return dynamic_cast<ExInst*> (e);
	}
	virtual InstType get_type() {
		return Ex;
	}
	virtual void print(std::ostream&);
	virtual void print_summary(std::ostream&);
	virtual void print_verilog(std::ostream&);
	virtual void print_blif(std::ostream &out);
	virtual Inst *bit_blast(InstToInstM& bb_map, bool init_visit = false);
	virtual Inst *split_signals(InstToInstM& bb_map, bool init_visit = false);
	//    virtual Inst* simplify();
	virtual bool check_consistency(std::ostream& out);
	virtual bool is_similar(Inst* e);
	virtual int instcmp(Inst* e);

	Inst* get_exp();
	unsigned get_hi() {
		return m_hi;
	}
	unsigned get_lo() {
		return m_lo;
	}
	static Inst *read_bin();
	virtual void write_bin();

	string get_euf_func_name();

private:
	unsigned m_hi, m_lo;
	string euf_func_name;

	// you can't call!
	// calc_size is called twice here. but that's ok!
	ExInst(Inst* exp, unsigned hi, unsigned lo, Inst* wire = NULL) :
		OpInst(OpInst::Extract, exp, 0, wire, SORT()), m_hi(hi), m_lo(lo) {
		calc_size();
		m_sort.sz = m_size;
		childrenInfo[NUM] 	= exp->childrenInfo[NUM];
		childrenInfo[SIG] 	= exp->childrenInfo[SIG];
		childrenInfo[NEXT] 	= exp->childrenInfo[NEXT];
	}
	ExInst() {
	}

private:
	static ExInst* create();
	virtual void calc_size();
	friend class Trans;
};

// memory instance
class MemInst: public Inst {
public:
	typedef enum {
		Init, Read, Write
	} MemType;

	// For write, the write-ports are a list of tripples {addr,enable,data}
	// For initialization, we have pairs of (addr,data) and a default (data) instances.
	// For read: it's a single instance of (addr)
	static Inst* create(std::string name, unsigned size, MemType t, InstL&ports);
	static MemInst* as(Inst*e) {
		return dynamic_cast<MemInst*> (e);
	}
	virtual ~MemInst() {
	}
	virtual void print(std::ostream&);
	virtual void print_summary(std::ostream&) {
		assert(0);
	}
	virtual void print_verilog(std::ostream&);
	virtual void print_blif(std::ostream &out);
	virtual Inst *bit_blast(InstToInstM& bb_map, bool init_visit = false);
	virtual Inst *split_signals(InstToInstM& bb_map, bool init_visit = false);
	virtual InstType get_type() {
		return Mem;
	}
	const InstL* get_children() {
		return &m_ports;
	}
	const std::string get_name() {
		return m_name;
	}
	//    virtual Inst* simplify();
	virtual bool check_consistency(std::ostream& out);
	virtual bool is_similar(Inst* e);
	virtual int instcmp(Inst* e) {
		assert(0);
		return false;
	}
	MemType get_mem_type() {
		return m_memtype;
	}
	static Inst *read_bin();
	virtual void write_bin();

private:
	std::string m_name;
	InstL m_ports;
	MemType m_memtype;

	// you can't call!
	MemInst(std::string name, unsigned size, MemType t, InstL&writes) :
		m_name(name), m_ports(writes), m_memtype(t) {
		m_size = size;
	}
	MemInst() {
	}
private:
	static MemInst* create();
	friend class Trans;
};

// UF instance
class UFInst: public Inst {
public:
	// create a UF instance
	static Inst* create(std::string name, unsigned size, InstL&children);
	static UFInst* as(Inst*e) {
		return dynamic_cast<UFInst*> (e);
	}
	virtual ~UFInst() {
	}
	virtual void print(std::ostream&);
	virtual void print_summary(std::ostream&) {
		assert(0);
	}
	virtual void print_verilog(std::ostream&);
	virtual void print_blif(std::ostream &out);
	virtual Inst *bit_blast(InstToInstM& bb_map, bool init_visit = false);
	virtual Inst *split_signals(InstToInstM& bb_map, bool init_visit = false);
	virtual InstType get_type() {
		return UF;
	}
	const InstL* get_children() {
		return &m_children;
	}
	const std::string get_name() {
		return m_name;
	}
	//    virtual Inst* simplify();
	virtual bool check_consistency(std::ostream& out) {
		return true;
	}
	virtual bool is_similar(Inst* e);
	virtual int instcmp(Inst* e);
	static Inst *read_bin();
	virtual void write_bin();

private:
	std::string m_name;
	InstL m_children;

	// you can't call!
	UFInst(std::string name, unsigned size, InstL&children) :
		m_name(name), m_children(children) {
		m_size = size;
	}
	UFInst() {
	}
private:
	static UFInst* create();
	friend class Trans;
};

// this is for software!

// Lambda instance
class LambdaInst: public Inst {
public:
	// create a UF instance
	static Inst* create(InstL lambdas, Inst* arg, unsigned size);
	static LambdaInst* as(Inst*e) {
		return dynamic_cast<LambdaInst*> (e);
	}
	virtual ~LambdaInst() {
	}
	virtual void print(std::ostream&);
	virtual void print_summary(std::ostream&) {
		assert(0);
	}
	virtual void print_verilog(std::ostream&) {
		assert(0);
	}
	virtual void print_blif(std::ostream &out) {
		assert(0);
	}
	virtual Inst *bit_blast(InstToInstM& bb_map, bool init_visit = false) {
		assert(0);
	}
	virtual Inst *split_signals(InstToInstM& bb_map, bool init_visit = false) {
		assert(0);
	}
	virtual InstType get_type() {
		return Lambda;
	}
	const InstL* get_children() {
		return &m_children;
	}
	//    virtual Inst* simplify();
	virtual bool check_consistency(std::ostream& out) {
		assert(0);
	}
	virtual bool is_similar(Inst* e) {
		assert(0);
	}
	virtual int instcmp(Inst* e) {
		assert(0);
	}

private:
	// first is arg, the rest are the lambdas!
	InstL m_children;

	// you can't call!
	LambdaInst(InstL&children, unsigned size) :
		m_children(children) {
		m_size = size;
	}
	LambdaInst() {
	}
};

// Lambda instance
class ArrayInst: public Inst {
public:
	// create a UF instance
	static Inst* create(std::string name, unsigned size);
	static ArrayInst* as(Inst*e) {
		return dynamic_cast<ArrayInst*> (e);
	}
	virtual ~ArrayInst() {
	}
	virtual void print(std::ostream&);
	virtual void print_summary(std::ostream&) {
		assert(0);
	}
	virtual void print_verilog(std::ostream&) {
		assert(0);
	}
	virtual void print_blif(std::ostream &out) {
		assert(0);
	}
	virtual Inst *bit_blast(InstToInstM& bb_map, bool init_visit = false) {
		assert(0);
	}
	virtual Inst *split_signals(InstToInstM& bb_map, bool init_visit = false) {
		assert(0);
	}
	virtual InstType get_type() {
		return Array;
	}
	const InstL* get_children() {
		return 0;
	}
	//    virtual Inst* simplify();
	virtual bool check_consistency(std::ostream& out) {
		assert(0);
	}
	virtual bool is_similar(Inst* e) {
		assert(0);
	}
	virtual int instcmp(Inst* e) {
		assert(0);
	}

	std::string get_name() {
		return m_name;
	}

private:
	std::string m_name;

	// you can't call!
	ArrayInst(std::string name, unsigned size) :
		m_name(name) {
		m_size = size;
	}
	ArrayInst() {
	}
};

class TransElem {
public:
	Inst* lhs;
	Inst* rhs;
	// 0 for init, 1 for CSF, and 2 for NSF
	unsigned type;
	void print(std::ostream&);
	static void print_blif_latch(std::ostream&, std::string edge,
			std::string q, unsigned q_width, std::string s, unsigned s_width,
			std::string clk, std::string init);
};

typedef std::list<TransElem> TransElemL;

class Trans: public TransElemL {
public:
	Trans() {
	}
	void read_bin(std::istream&);
	void write_bin(std::ostream &out);
	// overrides default push_back
	void push_back(const TransElem&);
	void simplify();
	bool check_consistency();
	bool is_wire(std::string s) {
		// I am assuming at least one wire.
		assert(!m_wires.empty());
		return m_wires.find(s) != m_wires.end();
	}

	typedef struct Port {
		std::string port_name;
		int msb;
		int lsb;
	} Port;
	std::vector<Port> m_input_ports;
	std::vector<Port> m_output_ports;

	static std::string m_module_name;

	static std::istream* st_in;
	static std::ostream* st_out;

	static SORT read_sort();
	static void write_sort(SORT sort);

	static int read_int();
	static void write_int(int i);
	
	static long long read_long();
	static void write_long(long long value);
	
	static std::string read_str();
	static void write_str(std::string s);
	static char read_char();
	static void write_char(char value);


	static InstV st_id_to_ptr;
	static InstToUintM st_ptr_to_id;

	static Inst* id_to_ptr(unsigned id);
	static unsigned ptr_to_id(Inst*e);
	static InstL reachable;
	static void collect_reachable(Inst*);

	typedef std::set<std::string> StringS;
	StringS m_wires;
	bool wires_updated;
private:

	friend class Inst;
	friend class SigInst;
	friend class NumInst;
	friend class OpInst;
	friend class ExInst;
	friend class MemInst;
	friend class UFInst;
};

inline bool compare::operator()(Inst* left, Inst* right) const {
	if (Config::g_random)
		return left < right;

	if (left && right)
			return (left->get_id() < right->get_id());
		else
			return false;
}

inline bool compare_pair_unsigned::operator()(const pair< Inst*, unsigned >& left, const pair< Inst*, unsigned >& right) const {
	if (Config::g_random)
		return left < right;

	if (left.second == right.second) {
		if (left.first && right.first)
				return (left.first->get_id() < right.first->get_id());
			else
				return false;
	}
	else
		return (left.second < right.second);
}

Inst* create_sig(std::string name, unsigned sz);
Inst* create_num(unsigned val, unsigned sz);
Inst* create_eq(Inst*e1, Inst*e2);
Inst* create_and(Inst*e1, Inst*e2);
Inst* create_or(Inst*e1, Inst*e2);
Inst* create_not(Inst*e);
Inst* create_future(Inst*e);
Inst* create_ite(Inst*conde, Inst*thene, Inst*elsee);
Inst* create_uf(std::string name, unsigned sz, Inst* child1, Inst* child2 = 0, Inst* child3 = 0);

std::ostream& operator<<(std::ostream& out, InstType& t);
std::ostream& operator<<(std::ostream& out, Inst& e);
std::ostream& operator<<(std::ostream& out, InstL& l);
std::ostream& operator<<(std::ostream& out, TransElem& t);
std::ostream& operator<<(std::ostream& out, TransElemL& l);
std::ostream& operator<<(std::ostream&, StringS&);
std::ostream& operator<<(std::ostream&, SigToInstM&);

#endif
