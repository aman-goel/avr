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
#include <unordered_map>

#include "avr_config.h"
#include "avr_backend.h"

/// Aman
#include <deque>
/// END

using namespace std;

#define AVR_WIRE_NAME_PREFIX "l$"

#define DEFAULT_VAL -1    // (-1: not set, 1: true, 0: false)

#define NUM    0	// 0: Contains Num as a child
#define SIG    1	// 1: Contains Sig as a child
#define CONST  2	// 2: Contains Const as a child
#define FC     3	// 3: Contains function composition
#define NEXT   4	// 4: Contains (or is) a next sig
#define WIRE   5	// 5: Contains (or is) a wire
#define CTRL   6	// 6: Contains (or is) a control operation (excluding mux)
#define MUX    7	// 7: Contains (or is) a mux operation
#define EQ  	 8	// 8: Contains (or is) a =/!= operation

#define NEXT_SUFFIX "$next"
#define NEXT_SUFFIX_LENGTH 5

//#define ABSTRACT 0
//#define CONCRETE 1
//#define ABSTRACT_WO_EX_CC 2

#define UF_V	0
#define BV_V	1
#define UFBV_V	2
#define CONNECT_V  3

#define UF_C			0
#define BV_C			1
#define UFBV_C			2
#define UF_C_WO_EX_CC	3

#define INVALID_SVAL  -1
#define INVALID_SMPZ  NULL
#define DONTCARE_SVAL  2

#define TIER_1 3
#define TIER_2 2
#define TIER_3 1
#define TIER_4 0

#define IS_PRED      0
#define IS_LOCAL_PRED     1

#define IS_PRESENT   0
#define HAS_REG      1
#define HAS_INP      2
#define HAS_NEXT_REG 3
#define HAS_NEXT_INP 4

#ifdef SINGLE_TIER
	#define DEFAULT_TIER 3
#else
	#ifdef DOUBLE_TIER
		#define DEFAULT_TIER 2
	#else
		#define DEFAULT_TIER 0
	#endif
#endif

#ifdef INTERPRET_EX_UF
  #define UF_SUFFIX_ANY    2
  #define UF_SUFFIX_ZER0   1
  #define UF_NEVER        -1
#endif

#ifdef _Z3
	class Z3_INFO
	{
	public:

		Z3_INFO()
		{
			clear();
		}
		~Z3_INFO()
		{
		}

		static int st_z3_key;
		static void inc_z3_key()
		{
			st_z3_key++;
		}
		int get_z3_key()
		{
			return key;
		}

		inline z3_expr_ptr solv_var(int idx) {
			return z3_var[idx];
		}
		inline bool solv_vset(int idx) {
			return z3_vset[idx];
		}
		inline z3_expr_list& solv_constraints(int idx) {
			return z3_constraints[idx];
		}
		inline bool solv_cset(int idx) {
			return z3_cset[idx];
		}

		// Z3 variable
		z3_expr_ptr z3_var [4];					// one for UF_VAR (UF/Bool), other for BV_VAR (BV), third for UFBV_VAR (BV/Bool)

		// Whether solv_var is set
		bool z3_vset [4];

		// Z3 constraints
		z3_expr_list z3_constraints [4];		// one for UF_C, second for BV_C, third for UFBV_C, fourth for UF_C_WO_EX_CC

		// Whether solv_constraints set
		bool z3_cset [4];

		void set_key(void)
		{
			if (key != st_z3_key)
			{
				clear();
			}
		}

	private:
		int key;

		void clear()
		{
			z3_var[UF_V] = Z3_INVALID_EXPR;
			z3_var[BV_V] = Z3_INVALID_EXPR;
			z3_var[UFBV_V] = Z3_INVALID_EXPR;
			z3_var[CONNECT_V] = Z3_INVALID_EXPR;

			z3_vset[UF_V] = false;
			z3_vset[BV_V] = false;
			z3_vset[UFBV_V] = false;
			z3_vset[CONNECT_V] = false;

			z3_constraints[UF_C].clear();
			z3_constraints[BV_C].clear();
			z3_constraints[UFBV_C].clear();
			z3_constraints[UF_C_WO_EX_CC].clear();

			z3_cset[UF_C] = false;
			z3_cset[BV_C] = false;
			z3_cset[UFBV_C] = false;
			z3_cset[UF_C_WO_EX_CC] = false;

			key = st_z3_key;
//			key = -1;
		}
	};
#endif

#ifdef _Y2
	class Y2_INFO
	{
	public:

		Y2_INFO()
		{
			clear();
		}
		~Y2_INFO()
		{
		}

		static int st_y2_key;
		static void inc_y2_key()
		{
			st_y2_key++;
		}
		int get_y2_key()
		{
			return key;
		}

		inline y2_expr_ptr solv_var(int idx) {
			return y2_var[idx];
		}
		inline bool solv_vset(int idx) {
			return y2_vset[idx];
		}
		inline y2_expr_list& solv_constraints(int idx) {
			return y2_constraints[idx];
		}
		inline bool solv_cset(int idx) {
			return y2_cset[idx];
		}

		// Whether solv_var is set
		bool y2_vset [4];

		// Whether solv_constraints set
		bool y2_cset [4];

		// Y2 variable
		y2_expr_ptr y2_var [4];					// one for UF_VAR (UF/Bool), other for BV_VAR (BV), third for UFBV_VAR (UF/BV/Bool), fourth for CONNECT_VAR

		// Y2 constraints
		y2_expr_list y2_constraints [4];					// one for UF_VAR (UF/Bool), other for BV_VAR (BV)

		void set_key(void)
		{
			if (key != st_y2_key)
			{
				clear();
			}
		}

		void print()
		{
			cout << y2_var[UF_V] << "_";
			cout << y2_var[BV_V] << "_";
			cout << y2_var[UFBV_V] << "_";
			cout << y2_var[CONNECT_V] << "_";

			cout << y2_vset[UF_V] << "_";
			cout << y2_vset[BV_V] << "_";
			cout << y2_vset[UFBV_V] << "_";
			cout << y2_vset[CONNECT_V] << "_";

			cout << y2_cset[UF_C] << "_";
			cout << y2_cset[BV_C] << "_";
			cout << y2_cset[UFBV_C] << "_";
			cout << y2_cset[UF_C_WO_EX_CC] << "_";

			cout << key << "_";
			cout << st_y2_key << endl;
		}

	private:
		int key;

		void clear()
		{
			y2_var[UF_V] = Y2_INVALID_EXPR;
			y2_var[BV_V] = Y2_INVALID_EXPR;
			y2_var[UFBV_V] = Y2_INVALID_EXPR;
			y2_var[CONNECT_V] = Y2_INVALID_EXPR;

			y2_vset[UF_V] = false;
			y2_vset[BV_V] = false;
			y2_vset[UFBV_V] = false;
			y2_vset[CONNECT_V] = false;

			y2_constraints[UF_C].clear();
			y2_constraints[BV_C].clear();
			y2_constraints[UFBV_C].clear();
			y2_constraints[UF_C_WO_EX_CC].clear();

			y2_cset[UF_C] = false;
			y2_cset[BV_C] = false;
			y2_cset[UFBV_C] = false;
			y2_cset[UF_C_WO_EX_CC] = false;

			key = st_y2_key;
//			key = -1;
		}
	};
#endif

#ifdef _M5
	class M5_INFO
	{
	public:

		M5_INFO()
		{
			clear();
		}
		~M5_INFO()
		{
		}

		static int st_m5_key;
		static void inc_m5_key()
		{
			st_m5_key++;
		}
		int get_m5_key()
		{
			return key;
		}

		inline m5_expr_ptr solv_var(int idx) {
			return m5_var[idx];
		}
		inline bool solv_vset(int idx) {
			return m5_vset[idx];
		}
		inline m5_expr_list& solv_constraints(int idx) {
			return m5_constraints[idx];
		}
		inline bool solv_cset(int idx) {
			return m5_cset[idx];
		}

		// Whether solv_var is set
		bool m5_vset [4];

		// Whether solv_constraints set
		bool m5_cset [4];

		// M5 variable
		m5_expr_ptr m5_var [4];					// one for UF_VAR (UF/Bool), other for BV_VAR (BV), third for UFBV_VAR (UF/BV/Bool), fourth for CONNECT_VAR

		// M5 constraints
		m5_expr_list m5_constraints [4];					// one for UF_VAR (UF/Bool), other for BV_VAR (BV)

		void set_key(void)
		{
			if (key != st_m5_key)
			{
				clear();
			}
		}

		void print()
		{
//			cout << m5_var[UF_V] << "_";
//			cout << m5_var[BV_V] << "_";
//			cout << m5_var[UFBV_V] << "_";
//			cout << m5_var[CONNECT_V] << "_";

			cout << m5_vset[UF_V] << "_";
			cout << m5_vset[BV_V] << "_";
			cout << m5_vset[UFBV_V] << "_";
			cout << m5_vset[CONNECT_V] << "_";

			cout << m5_cset[UF_C] << "_";
			cout << m5_cset[BV_C] << "_";
			cout << m5_cset[UFBV_C] << "_";
			cout << m5_cset[UF_C_WO_EX_CC] << "_";

			cout << key << "_";
			cout << st_m5_key << endl;
		}

	private:
		int key;

		void clear()
		{
			MSAT_MAKE_ERROR_TERM(m5_var[UF_V]);
			MSAT_MAKE_ERROR_TERM(m5_var[BV_V]);
			MSAT_MAKE_ERROR_TERM(m5_var[UFBV_V]);
			MSAT_MAKE_ERROR_TERM(m5_var[CONNECT_V]);

			m5_vset[UF_V] = false;
			m5_vset[BV_V] = false;
			m5_vset[UFBV_V] = false;
			m5_vset[CONNECT_V] = false;

			m5_constraints[UF_C].clear();
			m5_constraints[BV_C].clear();
			m5_constraints[UFBV_C].clear();
			m5_constraints[UF_C_WO_EX_CC].clear();

			m5_cset[UF_C] = false;
			m5_cset[BV_C] = false;
			m5_cset[UFBV_C] = false;
			m5_cset[UF_C_WO_EX_CC] = false;

			key = st_m5_key;
//			key = -1;
		}
	};
#endif

#ifdef _BT
	class BT_INFO
	{
	public:

		BT_INFO()
		{
			clear();
		}
		~BT_INFO()
		{
		}

		static int st_bt_key;
		static void inc_bt_key()
		{
			st_bt_key++;
		}
		int get_bt_key(int idx)
		{
			return key[idx];
		}

		inline bt_expr_ptr solv_var(int idx) {
			return bt_var[idx];
		}
		inline bool solv_vset(int idx) {
			return bt_vset[idx];
		}
		inline bt_expr_list& solv_constraints(int idx) {
			return bt_constraints[idx];
		}
		inline bool solv_cset(int idx) {
			return bt_cset[idx];
		}

		// Whether solv_var is set
		bool bt_vset [4];

		// Whether solv_constraints set
		bool bt_cset [4];

		// BT variable
		bt_expr_ptr bt_var [4];					// one for UF_VAR (UF/Bool), other for BV_VAR (BV), third for UFBV_VAR (UF/BV/Bool), fourth for CONNECT_VAR

		// BT constraints
		bt_expr_list bt_constraints [4];					// one for UF_VAR (UF/Bool), other for BV_VAR (BV)

		void set_key(int idx)
		{
			key[idx] = st_bt_key;
		}

		void print()
		{
//			cout << m5_var[UF_V] << "_";
//			cout << m5_var[BV_V] << "_";
//			cout << m5_var[UFBV_V] << "_";
//			cout << m5_var[CONNECT_V] << "_";

			cout << bt_vset[UF_V] << "_";
			cout << bt_vset[BV_V] << "_";
			cout << bt_vset[UFBV_V] << "_";
			cout << bt_vset[CONNECT_V] << "_";

			cout << bt_cset[UF_C] << "_";
			cout << bt_cset[BV_C] << "_";
			cout << bt_cset[UFBV_C] << "_";
			cout << bt_cset[UF_C_WO_EX_CC] << "_";

			cout << key << "_";
			cout << st_bt_key << endl;
		}

	private:
		int key[4];

		void clear()
		{
			bt_var[UF_V] = BT_INVALID_EXPR;
			bt_var[BV_V] = BT_INVALID_EXPR;
			bt_var[UFBV_V] = BT_INVALID_EXPR;
			bt_var[CONNECT_V] = BT_INVALID_EXPR;

			bt_vset[UF_V] = false;
			bt_vset[BV_V] = false;
			bt_vset[UFBV_V] = false;
			bt_vset[CONNECT_V] = false;

			bt_constraints[UF_C].clear();
			bt_constraints[BV_C].clear();
			bt_constraints[UFBV_C].clear();
			bt_constraints[UF_C_WO_EX_CC].clear();

			bt_cset[UF_C] = false;
			bt_cset[BV_C] = false;
			bt_cset[UFBV_C] = false;
			bt_cset[UF_C_WO_EX_CC] = false;

			key[UF_C] = -1;
			key[BV_C] = -1;
			key[UFBV_C] = -1;
			key[UF_C_WO_EX_CC] = -1;
		}
	};
#endif

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

/// Stores int value
class KEY_INT_VALUE
{
public:
  int key;
  int val;

  void clear()
  {
    key = -1;
    val = -1;
  }

  KEY_INT_VALUE()
  {
    clear();
  }
};

class KEY_COI_VALUE
{
public:
	static int st_coi_key;

	static void inc_coi_key() {
		st_coi_key++;
	}

	inline void set_coi_key() {
		if (!valid_coi_key()) {
			clear_coi();
			coi_key = st_coi_key;
		}
	}
	inline bool valid_coi_key() {
		return (coi_key == st_coi_key);
	}

	inline bool pred() {
  	return valid_coi_key() ? coi[IS_PRED] : false;
  }
	inline void set_pred() {
  	set_coi_key();
  	coi[IS_PRED] = true;
  }

	inline bool local_pred() {
  	return valid_coi_key() ? coi[IS_LOCAL_PRED] : false;
  }
	inline void set_local_pred() {
  	set_coi_key();
  	coi[IS_LOCAL_PRED] = true;
  }

	static int st_project_key;

	static void inc_project_key() {
		st_project_key++;
	}

	inline void set_project_key() {
		if (!valid_project_key()) {
			clear_project();
			project_key = st_project_key;
		}
	}
	inline bool valid_project_key() {
		return (project_key == st_project_key);
	}

	inline bool present() {
  	return project[IS_PRESENT];
  }
	inline bool has_reg() {
  	return project[HAS_REG];
  }
	inline bool has_inp() {
  	return project[HAS_INP];
  }
	inline bool has_next_reg() {
  	return project[HAS_NEXT_REG];
  }
	inline bool has_next_inp() {
  	return project[HAS_NEXT_INP];
  }

	inline void set_present() {
  	project[IS_PRESENT] = true;
  }
	inline void set_absent() {
  	project[IS_PRESENT] = false;
  }
	inline void set_reg() {
  	project[HAS_REG] = true;
  }
	inline void set_inp() {
  	project[HAS_INP] = true;
  }
	inline void set_next_reg() {
  	project[HAS_NEXT_REG] = true;
  }
	inline void set_next_inp() {
  	project[HAS_NEXT_INP] = true;
  }

  string str() {
  	return to_string(present()) +
  			   to_string(has_reg()) +
  			   to_string(has_inp()) +
  			   to_string(has_next_reg()) +
  			   to_string(has_next_inp());
  }

  inline void update(KEY_COI_VALUE& in) {
  	project[IS_PRESENT]   &= in.present();
  	project[HAS_REG]      |= in.has_reg();
  	project[HAS_INP]      |= in.has_inp();
  	project[HAS_NEXT_REG] |= in.has_next_reg();
  	project[HAS_NEXT_INP] |= in.has_next_inp();
  }

  inline void clear_coi()
  {
    coi_key = -1;
    coi[IS_PRED]          = false;
    coi[IS_LOCAL_PRED]    = false;
  }
  inline void clear_project()
  {
    project_key = -1;
    project[IS_PRESENT]   = false;
    project[HAS_REG]      = false;
    project[HAS_INP]      = false;
    project[HAS_NEXT_REG] = false;
    project[HAS_NEXT_INP] = false;
  }

	inline bool req_pred() {
  	return required;
  }
	inline void set_req_pred() {
  	required = true;
  }

  KEY_COI_VALUE()
  {
    clear_coi();
    clear_project();
    required = false;
  }

private:
	int project_key;
	int coi_key;

	bool coi[2];
  bool project[5];
	bool required;							// required predicate to avoid repeated refinements

};

/// Stores solver value
class SOLVER_VALUE
{
public:
	int key;

	int	cex_val;	// set 0 or 1 if m_size is one (i.e. control signals)
	mpz_class* cex_mpz;

	SOLVER_VALUE()
	{
	  clear();
	}

	void clear()
	{
		key = -1;
		cex_val = INVALID_SVAL;
		cex_mpz = INVALID_SMPZ;
	}
};

/// Stores dont care value
class KEY_VALUE
{
public:
	int key;
	bool val;

	KEY_VALUE()
	{
		key = -1;
		val = false;
	}

	void clear()
	{
		key = -1;
		val = false;
	}
};

/// Stores eval value
class KEY_LONG_VALUE
{
public:
	int key;
	long long val;

	void clear()
	{
		key = -1;
		val = -1;
	}

	KEY_LONG_VALUE()
	{
		clear();
	}
};

class Inst;
class CLAUSE;

struct compare {
	bool operator()(Inst* left, Inst* right) const;
};

struct compare_pair {
	bool operator()(const pair< Inst*, Inst* >& left, const pair< Inst*, Inst* >& right) const;
};

struct compare_pair_int {
	bool operator()(const pair< Inst*, int >& left, const pair< Inst*, int >& right) const;
};

struct compare_pair_string {
	bool operator()(const pair< Inst*, string >& left, const pair< Inst*, string >& right) const;
};

/// Stores instance with key
class KEY_INST
{
public:
	int key;
	Inst* val;

	void clear()
	{
		key = -1;
		val = NULL;
	}
	KEY_INST()
	{
		clear();
	}
};

typedef list<Inst*> InstL;
typedef list<InstL> InstLL;
typedef vector<Inst*> InstV;
typedef set<string> StringS;
typedef map<string,Inst*> SigToInstM;

typedef set<Inst*, compare> InstS;
typedef set< pair< Inst*, Inst* >, compare_pair> InstPairS;
typedef map<Inst*, Inst*, compare> InstToInstM;
typedef map<Inst*, InstL, compare> InstToListM;
typedef map<Inst*, InstS, compare> InstToSetM;
typedef map<Inst*, bool, compare> InstToBoolM;
typedef map<Inst*, int, compare> InstToIntM;
typedef map<Inst*, unsigned, compare> InstToUintM;
typedef map<Inst*, string> InstToStringM;
typedef map<Inst*, mpz_class, compare> InstToMpzM;
typedef map<Inst*, mpz_class*, compare> InstToMpzRefM;
typedef map<Inst*, pair< Inst*, bool >, compare> InstToPairBoolM;
typedef map<Inst*, pair< Inst*, Inst* >, compare> InstToPairInstM;
typedef map<Inst*, pair< InstL, InstL >, compare> InstToPairListM;
typedef map< pair< Inst*, Inst* >, bool, compare_pair> InstPairToBoolM;

#define INVALID_INST NULL

/// Macros for invalid state term and term types
#define NOT_YET_COMPUTED 16

#define VALID			 0
#define INVALID			 1

/// Note - Below term type macros cannot be changed arbitrarily
#define CONSTANT_ONLY		0	// term of constants (i.e. no states and no inputs)
#define NO_INPUTS			1	// includes only states and constants (no inputs)
#define NO_STATES			2	// includes only inputs and constants (no states)
#define STATES_AND_INPUTS	3	// includes both states and inputs
#define ALLOWED_INPUTS		2	// includes only inputs and constants (no states)

/// Prefix for new intermediate names
#define NAME_PREFIX "w#"
#define NAME_PREFIX_LENGTH 2

class InterpretationInfo
{
public:
	InterpretationInfo()
	{
		concrete_in  = false;
		concrete_out = false;
	}

	bool is_concrete(void)
	{
		return (concrete_in && concrete_out);
	}

	bool input_concrete(void)
	{
		return concrete_in;
	}

	bool output_concrete(void)
	{
		return concrete_out;
	}

	void set_concrete(void)
	{
//		/ Stopped for time being
		concrete_in  = true;
		concrete_out = true;
	}

	void set_input_concrete(void)
	{
		concrete_in = true;
	}

	void set_output_concrete(void)
	{
		concrete_out = true;
	}

private:
	bool concrete_in;
	bool concrete_out;
};


extern vector<Inst*> _idxHash; // Converting index to pre (or next) register, or inputs in the design

extern vector<Inst*> _wIdxHash; // Converting index to wire in the design

typedef enum {
		h, v, f_err, f_mo, f_to, f_to_query, f_poor_ab, h_triv
} ResultType;


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
	string sort2smt2str() {
		switch(type) {
		case bvtype:
			if (sz == 1)
				return "Bool";
			else
				return "(_ BitVec " + to_string(sz) + ")";
		case arraytype:
			return "unknown";
		case inttype:
			return "Int";
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

// Expression
// TODO Find the better name
// netlist consists of "instances" and "nets", so
// we may have to rename SigInst to Net.
class Inst{
public:
	static Config* config;
	static ResultType g_result;

	static int avr_wid;

	inline bool operator< (const Inst& obj) const {
		return (obj.m_id < this->m_id);
	}

	static bool CompareInstByChildInfo (Inst *first, Inst *second);
	static bool CompareInstByChildInfoTier (Inst *first, Inst *second);
	static bool CompareCoreByChildInfoTier (const pair<Inst*, string>& first, const pair<Inst*, string>& second);

  static void print_cc() {
    print_concrete = true;
  }
  static void print_ab() {
    print_concrete = false;
  }

  // API
	// print the instance recursively (textuall)
	virtual void print(ostream&) = 0;
	// print the instance locally (no recursion)
	virtual void print_summary(ostream&);
	// print the instance locally (no recursion), using Verilog syntax!
	virtual void print_verilog(ostream&);
	// auxialiary function for print_verilog!
	void print_verilog_name(ostream&);
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
		else
			return NULL;
	}

	// get type (of the InstType's above)
	virtual InstType get_type() = 0;
	virtual void print_blif(ostream &out) = 0;
	virtual string get_blif_name();
	static string blif_suffix(unsigned);
	virtual Inst *bit_blast(InstToInstM& bb_map, bool init_visit = false) = 0;
	virtual Inst* bit_blast_version() = 0;

	virtual InstV& word2bool() = 0;

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
	static void dump_size_all(ostream&);
	// print total number of instances
	static unsigned total_nodes();

	// use as follows:
	// init_visit() ... before any new traversal
	// if(get_visit())
	//   skip...
	// else: set_visit .. and process instance
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
	void set_visit3() {
		m_visit3 = st_visit3;
	}
	bool get_visit2() {
		return m_visit2 == st_visit2;
	}
	bool get_visit3() {
		return m_visit3 == st_visit3;
	}
	static void init_visit() {
		st_visit++;
	}
	static void init_visit2() {
		st_visit2++;
	}
	static void init_visit3() {
		st_visit3++;
	}
	// returns null if there are no children!
	virtual const InstL* get_children() = 0;
	// see below simplification rules supported (and enabled)
	// this function marks the simplified nodes with 'visit', and avoids simplifying a node that has the 'visit' flag on!
	//    virtual Inst* simplify() = 0;
	// return a new instance with a new set of children!
	virtual Inst* apply_children(InstL& args);
	// searches for an instance that matches 'src' (based on the is_similar predicate), and
	// when encountered, replaces it with 'tgt'.
	Inst* replace_child(Inst*src, Inst*tgt);
	Inst* replace_child_by_stripping_header(string header);
	// stupid implementation: goes over the list of ALL nodes!
	static Inst* get_node(unsigned id);
	// checks consistency (mainly size compatibility).
	// if not consistent, prints the erratic instance to the stream.
	virtual bool check_consistency(ostream& out);
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

	static int check_term_type(Inst *e);
	static int is_matched(Inst *inst_a, Inst *inst_b);

	static void collect_next_reg(Inst *top, InstS& s_next, bool init_visit = false);

#ifdef ABSTRACTION_COURSE
	static int check_v_important(Inst *top);
	static int contains_black_uf(Inst *top);
	static bool check_if_uf_black(Inst *top);
#endif


//	int check_term_type(void);
//	int is_matched(Inst *inst_b);
//	int check_v_important(void);
//	void init_v_important(bool init_visit=false);

	string get_euf_func_name();

	Inst* add_missing_wires();

	Inst* get_signal();

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

	static Inst *all_next2pre(Inst *e);
	static Inst *all_pre2next(Inst *e);

	virtual ~Inst() {
	}

	typedef set<string> StringS;

	static int maxContextCalls;
	static int numContextCalls;

	static unsigned num_warnings;

	// (change the design.. it's a bit wacky!)
	// used by print_verilog
	static StringS st_printed_signals;

	///////// arguments that control simplification during creation.
	// sig[7:0] is replaced by sig for an 8-bits signal sig
//	static bool wn_simplify_extract_adv;
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

	static InstS _s_reg; // set of registers in the design, used to filter out inputs later
	static InstS _s_inp; // set of inputs in the design

	// a kind of a map of (state_var, simplified nsf of it)
	static InstToPairBoolM _m_sn; // simplified next,
	static InstToSetM _m_inp; // relation for inputs,
	static InstToSetM _m_inp_next; // relation for next inputs,

	static map< string, Inst*> _m_state_to_ptr; // Map of name to pointer for registers in the design

	static InstToInstM _m_next_to_pre; // Map of next state registers to present state registers in the design
	static InstToInstM _m_pre_to_next; // Map of present state registers to next state registers in the design
	static InstToInstM _m_next_input_pre; // Map of next input to present input in the design
	static InstToInstM _m_pre_input_next; // Map of present input to next input in the design

	static InstToInstM _m_next_wire_pre; // Map of next wire to present wire in the design
	static InstToInstM _m_pre_wire_next; // Map of present wire to next wire in the design

	static InstToSetM _m_forward_coi;  // Map of present state register/input to next state registers that are affected by it's value in the design
	static InstToSetM _m_backward_coi; // Map of present next state register to present state registers/inputs that it is affected by in the design

	// a kind of a map of (state_var (pre) and number of new cones it introduces)
	static InstToIntM _m_numRegs;

	static vector<InstS> _relevantCones;

	static map<string, InstL> _whiteFlist;
	static map<string, InstL> _blackFlist;

	static InstPairToBoolM _setContains;	// caching result of set_contains function

	static mpz_class _mpz_zero;
	static mpz_class _mpz_one;

	/// Information on interpretation of object (during abstract reachability)
	InterpretationInfo ab_interpret;

	static bool has_trelation(Inst* sigNext);
	static Inst* fetch_trelation_eq(Inst* sigNext);
	static Inst* fetch_trelation(Inst* sigNext);
	static Inst* fetch_trelation(InstToPairBoolM::iterator mit);

	virtual Inst* get_port(void) = 0;
	virtual Inst* get_simple(void) = 0;

	//vector<unsigned> m_solver_visit;

#ifdef _Z3
	Z3_INFO z3_node;
#endif

#ifdef _Y2
	Y2_INFO y2_node;
#endif

#ifdef _M5
	M5_INFO m5_node;
#endif

#ifdef _BT
	BT_INFO bt_node;
#endif

	// YICES solver value
	// Array of value based on solver BA index
	vector < SOLVER_VALUE > sval;

	KEY_COI_VALUE coi;

	// Global counter for key used in retrieving solver value
	static int st_retrieve_key;
	static void inc_rkey()
	{
		st_retrieve_key++;
	}

	inline static int get_rkey()
	{
		return st_retrieve_key;
	}

	static unsigned st_ba_idx;
	static void set_ba_idx(unsigned baIdx)
	{
		st_ba_idx = baIdx;
	}

	inline static unsigned get_bIdx()
	{
		return st_ba_idx;
	}

	void set_bval(int val)
	{
		while (st_ba_idx >= sval.size())
		{
			SOLVER_VALUE dummy;
			sval.push_back(dummy);
		}
		SOLVER_VALUE& sVal = sval[st_ba_idx];
		sVal.cex_val = val;
		sVal.key = st_retrieve_key;
	}
	void set_ival(mpz_class* val)
	{
		while (st_ba_idx >= sval.size())
		{
			SOLVER_VALUE dummy;
			sval.push_back(dummy);
		}
		SOLVER_VALUE& sVal = sval[st_ba_idx];
		sVal.cex_mpz = val;
		sVal.key = st_retrieve_key;
	}

	virtual long long get_num() {
		assert(0);
	}

	inline int get_bval(void)
	{
		if (st_ba_idx >= sval.size())
		{
			if ((m_size == 1) && (get_type() == Num))
				return get_num();

			return INVALID_SVAL;
		}
		SOLVER_VALUE& sVal = sval[st_ba_idx];
		if (sVal.key != st_retrieve_key)
		{
			if ((m_size == 1) && (get_type() == Num))
				return get_num();

			return INVALID_SVAL;
		}
		else
			return sVal.cex_val;
	}
	inline mpz_class* get_ival(void)
	{
		if (st_ba_idx >= sval.size())
			return INVALID_SMPZ;
		SOLVER_VALUE& sVal = sval[st_ba_idx];
		if (sVal.key != st_retrieve_key)
			return INVALID_SMPZ;
		else
			return sVal.cex_mpz;
	}

	KEY_VALUE dcVal;
	void set_dcVal(bool val)
	{
		dcVal.key = st_dont_care_key;
		dcVal.val = val;
	}
	bool get_dcVal(int key)
	{
		if (dcVal.key != key)
			return false;
		return dcVal.val;
	}

	KEY_VALUE hlVal;
	void set_hlVal(bool val)
	{
		hlVal.key = st_dont_care_key;
		hlVal.val = val;
	}
	bool get_hlVal(int key)
	{
		if (hlVal.key != key)
			return false;
		return hlVal.val;
	}

  KEY_INT_VALUE drVal;
  void set_drVal(int val)
  {
    drVal.key = st_draw_key;
    drVal.val = val;
  }
  int get_drVal(int key)
  {
    if (drVal.key != key)
      return -1;
    return drVal.val;
  }

  static int st_draw_key;
  static void inc_drkey() {
    if (st_draw_key > 100)
      st_draw_key = 1;
    else
      st_draw_key++;
  }
  inline static int get_drkey() {
    return st_draw_key;
  }


	static int st_dont_care_key;
	static void inc_dckey()
	{
		st_dont_care_key++;
	}

	inline static int get_dckey()
	{
		return st_dont_care_key;
	}


	bool find_next()
	{
		return childrenInfo[NEXT];
	}

	bool find_sig()
	{
		return childrenInfo[SIG];
	}

//	// Associated solver_id with corresponding constraints
//	// (solver_id changes whenever YicesAPISolver constructor is called)
//	vector<unsigned> y_solver_id;

	/// Aman
	//	Below constructs added to enable reusing of constraints among different solver calls
	//
	// Added for reusing constraints in solver calls
	//
//	// Flag to check if corresponding yvar is already set (True) or not (False)
//	vector<char> yvar_set;
//	//
//	// Stored constraints
//	vector< std::list<yices_expr> > y_constraints;
	//
	//
	/// END

	// Structural hashing string
	set< string > saPrefix;

	// next2pre or pre2next
	Inst* next2pre;
  Inst* pre2next;

	InstV w2b;

	// what does the current instance equal to under the given ACEX.
	// eval_term assigns this!
	Inst* acex_coi;

	// what does the current instance equal to under the given minterm (substituted).
#ifdef	FIND_SUB_EXPRESSION
	Inst* subs_coi;
#endif

  // what does the current instance equal to under the given minterm (w/o substitution).
  Inst* nsub_coi;

	// true if acex_coi has function composition
	bool acex_fc;

  // for generic bool storing in functions: find_from_minset
  bool genBval;

  // for generic bool storing in functions: find_from_minset
  bool genBval2;

  // for find_input
  int hasInput;

  // for find_reg
  int hasReg;

  // for cube_contains_init
  int hasNegInit;

	// 0: Contains Num as a child
	// 1: Contains Sig as a child
	// 2: Contains Const as a child
	// 3: Has function composition
	// 4: Has next sig
	// 5: Contains Wire as a child
	// 6: Contains control as a child (excluding mux)
	// 7: Contains Mux as a child
	// 8: Contains =/!= as a child
	bool childrenInfo[9];
	unsigned fcLevel;
	unsigned trueFcLevel;
	unsigned maxSize;
	unsigned level;

	unsigned fcCombDist;

	bool is_t1()
	{
		return tier == TIER_1;
	}
	bool is_t2()
	{
		return tier == TIER_2;
	}
	bool is_t3()
	{
		return tier == TIER_3;
	}
	bool is_t4()
	{
		return tier == TIER_4;
	}

	void upgrade_tier()
	{
		if (tier < TIER_1)
			tier += 1;
	}

	void set_t1()
	{
		tier = TIER_1;
	}
	void set_t2()
	{
		tier = TIER_2;
	}
	void set_t3()
	{
		tier = TIER_3;
	}
	void set_t4()
	{
		tier = TIER_4;
	}

	int& get_tier()
	{
		return tier;
	}

	virtual void write_bin();
	bool is_rhs; //TODO

	int v_counter;			// Counter to keep track whether new function/input got modified or not
	static int v_gcounter;	// Global counter to keep track whether new function/input got modified or not

	int v_important;		/// Flag to indicate whether constraint important or not
							/// It can be VALID, INVALID, NOT_YET_COMPUTED

	int is_invalid_state_term;	// 4: not yet computed
								// 0: valid
								// 1: invalid (newly introduced term or term containing inputs)
	int term_type;			// 0: term of constants (i.e. no states and no inputs), 1: includes states but not inputs
							// 2: includes inputs and constants, 3: includes both states and inputs
							// 4: not yet computed
	Inst *ve_orig;	//TODO getter and setter

	Inst *ve_sim_orig;	//TODO getter and setter

	static int not_yet_computed;

#ifdef ABSTRACTION_COURSE
	static int _allowed_abLevel;
#endif


	KEY_INST reduce_coi;
	KEY_LONG_VALUE reduce_val;
	void set_reduceEval(Inst* val)
	{
		reduce_coi.key = st_reduce_key;
		reduce_coi.val = val;
	}
	Inst* get_reduceEval(int key = get_reduceKey())
	{
		if (reduce_coi.key != key)
			return NULL;
		return reduce_coi.val;
	}

	void set_reduceVal(long long val)
	{
		reduce_val.key = st_reduce_key;
		reduce_val.val = val;
	}
	int get_reduceVal(int key = get_reduceKey())
	{
		if (reduce_val.key != key)
			return -1;
		return reduce_val.val;
	}

	inline static void inc_reduceKey()
	{
		st_reduce_key++;
	}
	inline static int get_reduceKey()
	{
		return st_reduce_key;
	}


	KEY_INT_VALUE tsim_val;
  void set_tsim_val(int val)
  {
    tsim_val.key = st_tsim_key;
    tsim_val.val = val;
  }
  int get_tsim_val(int key)
  {
    if (tsim_val.key != key)
      return -1;
    return tsim_val.val;
  }
  int get_tsim_key(void)
  {
    return tsim_val.key;
  }

  inline static void inc_tsim_key()
  {
    st_tsim_key++;
  }
  inline static int tsim_key()
  {
    return st_tsim_key;
  }


	void add_parent(Inst* parent, int idx) {
		all_parents[idx] = parent;
	}
	pair< int, Inst* > pop_parent(int idx) {
		if (all_parents.empty())
			return make_pair(-1, this);
		else {
			map< int, Inst* >::iterator mit = all_parents.find(idx);
			if (mit == all_parents.end())
				mit = all_parents.begin();
//				return make_pair(idx, this);

			pair< int, Inst* > p = make_pair((*mit).first, (*mit).second);
			all_parents.erase((*mit).first);
			return p;
		}
	}

	Inst* t_simple;

	static bool en_array;
	static bool en_integer;

	int activity;

	void bump_activity() {
		activity++;
	}

protected:
	map< int, Inst* > all_parents;

	static int st_reduce_key;
  static int st_tsim_key;

  SORT m_sort;
	unsigned m_size;
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

  static bool print_concrete;

private:

	int tier;
	
	unsigned m_tcnt;	// temporary counter
	unsigned m_visit;
	unsigned m_visit2;
	unsigned m_visit3;
	static unsigned st_visit;
	static unsigned st_visit2;
	static unsigned st_visit3;
	virtual void serve(RecService*, bool init);
};

// Signal
class SigInst: public Inst {
public:
	typedef map<string, Inst*> StrVM;
	static StrVM hm_SigInst;// hash map of NumInst

	static Inst* create(string name, unsigned size, SORT sort);
	static SigInst* as(Inst* e) {
		return dynamic_cast<SigInst*> (e);
	}
	virtual InstType get_type() {
		return Sig;
	}
	virtual void print(ostream&);
	virtual void print_summary(ostream&);
	virtual void print_verilog(ostream&);
	const InstL* get_children() {
		return 0;
	}
	//    virtual Inst* simplify();
	virtual bool check_consistency(ostream& out) {
		return Inst::check_consistency(out);
	}
	virtual bool is_similar(Inst* e);
	virtual int instcmp(Inst* e);

	virtual Inst* get_port(void) {
		return this;
	}
	virtual Inst* get_simple(void) {
		return this;
	}

	string get_name() {
		return m_name;
	}

	virtual void print_blif(ostream &out);
	virtual string get_blif_name(); // auxialiary function for print_blif!
	virtual Inst *bit_blast(InstToInstM& bb_map, bool init_visit = false);
	virtual Inst* bit_blast_version();

	virtual InstV& word2bool();

	static string dollar_dot_to_underscore(string);
	static Inst *read_bin();
	virtual void write_bin();

	bool interpret();

	int get_idx()
	{
		return idx;
	}
	void set_idx()
	{
		idx = _idxHash.size();
		_idxHash.push_back(this);
	}

	bool is_pre_reg()
	{
		assert(get_idx() >= 0);
		return (get_idx() < Inst::_s_reg.size());
	}

protected:

	bool is_next(void)
	{
		string prefix = NEXT_SUFFIX;
		unsigned sz = m_name.length();
		unsigned psz = prefix.length();
		if (sz < psz)
			return false;
		return (m_name.substr(sz - psz) == NEXT_SUFFIX);
	}

	string m_name;
	// you can't call!
	SigInst(std::string name, unsigned size, SORT sort){
		m_sort = sort;
		m_size = size;
		m_name = name;

		childrenInfo[NUM]    = false;
		childrenInfo[SIG]    = true;
		childrenInfo[CONST]  = false;
		childrenInfo[FC]     = false;
		childrenInfo[NEXT]   = is_next();
		childrenInfo[WIRE]   = false;
		childrenInfo[CTRL]   = false;
		childrenInfo[MUX]    = false;
		childrenInfo[EQ]     = false;

		m_size = size;
		idx = -1;
		maxSize = m_size;

		if (m_sort.type == bvtype && m_size <= Config::g_ab_interpret_limit)
			ab_interpret.set_concrete();
		else if (m_sort.type == arraytype) {
			if (m_sort.args.front().type == bvtype && m_sort.args.front().sz <= Config::g_ab_interpret_limit) {
				ab_interpret.set_input_concrete();
			}
			if (m_sort.args.back().type == bvtype && m_sort.args.back().sz <= Config::g_ab_interpret_limit) {
				ab_interpret.set_output_concrete();
			}
		}
	}
private:
	int idx;

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
	virtual Inst *bit_blast(InstToInstM& bb_map, bool init_visit = false);
	virtual Inst* bit_blast_version();

	virtual InstV& word2bool();

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
	virtual Inst* get_simple(void) {
		return this;
//		return get_port();
	}

	static Inst *read_bin();
	virtual void write_bin();

//	void set_connect(Inst* rhs)
//	{
//		connection.first.key = st_connect_key;
//		connection.first.val = true;
//		connection.second = rhs;
//	}
//	bool is_connected(int key)
//	{
//		if (connection.first.key != key)
//			return false;
//		return connection.first.val;
//	}
//	Inst* get_connection(void)
//	{
//		assert(connection.second);
//		return connection.second;
//	}

	void set_connect(void)
	{
		connection.key = st_connect_key;
		connection.val = true;
	}
	bool is_connected(int key)
	{
		if (connection.key != key)
			return false;
		return connection.val;
	}

	static void inc_connect_key()
	{
		st_connect_key++;
	}

	inline static int get_connect_key()
	{
		return st_connect_key;
	}

	KEY_VALUE sliceVal;
	void reset_sliceVal()
	{
		sliceVal.clear();
	}
	void set_sliceVal(bool val = true)
	{
		sliceVal.key = st_slice_key;
		sliceVal.val = val;
	}
	bool get_sliceVal(int key)
	{
		if (sliceVal.key != key)
			return false;
		return sliceVal.val;
	}

	inline static void inc_slicekey()
	{
		st_slice_key++;
	}
	inline static int get_slicekey()
	{
		return st_slice_key;
	}

	int get_idx()
	{
		return idx;
	}
	void set_idx()
	{
		idx = _wIdxHash.size();
		_wIdxHash.push_back(this);
	}

	bool is_added(void)
	{
		string prefix = AVR_WIRE_NAME_PREFIX;
		unsigned sz = m_name.length();
		unsigned psz = prefix.length();
		if (sz < psz)
			return false;
		return (m_name.substr(0, psz) == prefix);
	}

private:
	static int st_connect_key;
	static int st_slice_key;

	string m_name;
	InstL m_exps;
//	pair< KEY_VALUE, Inst* > connection;
	KEY_VALUE connection;

	int idx;

	WireInst(Inst* port, string name)
	{
		assert(name != "");
		m_name = name;
		m_size = port->get_size();
		m_sort = port->get_sort();
		set_port(port);
//		m_exps.push_back(port);
		assert(m_exps.size() == 1);
//		idx = -1;

		set_idx();

		childrenInfo[NUM]    = port->childrenInfo[NUM];
		childrenInfo[SIG]    = port->childrenInfo[SIG];
		childrenInfo[CONST]  = port->childrenInfo[CONST];
		childrenInfo[FC]     = port->childrenInfo[FC];
		childrenInfo[NEXT]   = port->childrenInfo[NEXT];
		childrenInfo[WIRE]   = true;
		childrenInfo[CTRL]   = port->childrenInfo[CTRL];
		childrenInfo[MUX]    = port->childrenInfo[MUX];
		childrenInfo[EQ]     = port->childrenInfo[EQ];
		fcLevel 			 = port->fcLevel;
		trueFcLevel 			 = port->trueFcLevel;
		maxSize = port->maxSize;
		level 			 = port->level;

		ab_interpret = port->ab_interpret;
	}
private:
	static WireInst* create();
	friend class Trans;
};
/// END

// Number
class NumInst: public Inst {
public:
	typedef pair<mpz_class, pair<unsigned, SORT>> NumType;
	struct NumType_comp {
		bool operator()(const NumType& lhs, const NumType& rhs) const {
			if (lhs.second == rhs.second) {
				return lhs.first < rhs.first;
			}
			return lhs.second < rhs.second;
		}
	};

	typedef map<NumType, Inst*, NumType_comp> NumHashM;	// <num, size>
	static NumHashM hm_NumInst;// hash map of NumInst

#ifdef ASSERT_DISTINCT_NUMBERS
	static map< pair<unsigned, SORT>, InstS > m_sz_to_constants;
#endif

//	static SNumHashM hm_SNumInst;// hash map of NumInst whose width is bigger than 64

	static Inst* create(std::string snum, unsigned size, unsigned base, SORT sort, bool fromSystem = false);
	static Inst* create(unsigned long num, unsigned size, SORT sort, bool fromSystem = false);
	static Inst* create(mpz_class mnum, unsigned size, SORT sort, bool fromSystem = false);
	
	static NumInst* as(Inst*e) {
		return dynamic_cast<NumInst*> (e);
	}
	virtual ~NumInst() {
	}

	virtual InstType get_type() {
		return Num;
	}
	virtual void print(ostream&);
	virtual void print_summary(ostream&);
	virtual void print_verilog(ostream&);

	virtual void print_blif(ostream &out);
	//	virtual string get_blif_name(); // auxialiary function for print_blif!
	virtual Inst *bit_blast(InstToInstM& bb_map, bool init_visit = false);
	virtual Inst* bit_blast_version();

	virtual InstV& word2bool();

	const InstL* get_children() {
		return 0;
	}
	//    virtual Inst* simplify();
	virtual bool check_consistency(ostream& out) {
		return Inst::check_consistency(out);
	}
	virtual bool is_similar(Inst* e);
	virtual int instcmp(Inst* e);

	virtual Inst* get_port(void) {
		return this;
	}
	virtual Inst* get_simple(void) {
		return this;
	}

	mpz_class *get_mpz(){
		return &m_mpz;
	}

	long long get_num() {
		return m_mpz.get_si();
	}

	static Inst *read_bin();
	virtual void write_bin();

	bool interpret();

	bool get_distinct() {
		return m_distinct;
	}
	void set_distinct() {
		m_distinct = true;
	}

	bool fromSystem() {
		return m_fromSystem;
	}

private:
	mpz_class m_mpz;
	bool m_distinct;

	bool m_fromSystem;

	// you can't call!
	NumInst(unsigned long num, unsigned size, bool fromSystem, SORT sort) {
		m_sort = sort;
		m_size = size;
		m_mpz = mpz_class(num);
		m_distinct = false;
		m_fromSystem = fromSystem;

		childrenInfo[NUM]    = true;
		childrenInfo[SIG]    = false;
		childrenInfo[CONST]  = false;
		childrenInfo[FC]     = false;
		childrenInfo[NEXT]   = false;
		childrenInfo[WIRE]   = false;
		childrenInfo[CTRL]   = false;
		childrenInfo[MUX]    = false;
		childrenInfo[EQ]     = false;
		maxSize = m_size;

		if (m_sort.type == bvtype && m_size <= Config::g_ab_interpret_limit)
			ab_interpret.set_concrete();
		else if (m_sort.type == arraytype) {
			if (m_sort.args.front().type == bvtype && m_sort.args.front().sz <= Config::g_ab_interpret_limit) {
				ab_interpret.set_input_concrete();
			}
			if (m_sort.args.back().type == bvtype && m_sort.args.back().sz <= Config::g_ab_interpret_limit) {
				ab_interpret.set_output_concrete();
			}
		}
	}
// 	NumInst(string snum = "0", unsigned size = 0, unsigned base = 10) {
// 		m_size = size;
// 		m_mpz.set_str(snum, base);
// 	}
	NumInst(mpz_class mnum, unsigned size, bool fromSystem, SORT sort) {
		m_sort = sort;
		m_size = size;
		m_mpz = mnum;
		m_distinct = false;
		m_fromSystem = fromSystem;

		childrenInfo[NUM]    = true;
		childrenInfo[SIG]    = false;
		childrenInfo[CONST]  = false;
		childrenInfo[FC]     = false;
		childrenInfo[NEXT]   = false;
		childrenInfo[WIRE]   = false;
		childrenInfo[CTRL]   = false;
		childrenInfo[MUX]    = false;
		childrenInfo[EQ]     = false;
		maxSize = m_size;

		if (m_sort.type == bvtype && m_size <= Config::g_ab_interpret_limit)
			ab_interpret.set_concrete();
		else if (m_sort.type == arraytype) {
			if (m_sort.args.front().type == bvtype && m_sort.args.front().sz <= Config::g_ab_interpret_limit) {
				ab_interpret.set_input_concrete();
			}
			if (m_sort.args.back().type == bvtype && m_sort.args.back().sz <= Config::g_ab_interpret_limit) {
				ab_interpret.set_output_concrete();
			}
		}
	}
	NumInst()
	{
		/// Aman TODO: Check need for m_distinct (remove it in case not needed)
		m_distinct = false;
		m_fromSystem = false;

		childrenInfo[NUM]    = true;
		childrenInfo[SIG]    = false;
		childrenInfo[CONST]  = false;
		childrenInfo[FC]     = false;
		childrenInfo[NEXT]   = false;
		childrenInfo[WIRE]   = false;
		childrenInfo[CTRL]   = false;
		childrenInfo[MUX]    = false;
		childrenInfo[EQ]     = false;
		maxSize = m_size;

		if (m_sort.type == bvtype && m_size <= Config::g_ab_interpret_limit)
			ab_interpret.set_concrete();
		else if (m_sort.type == arraytype) {
			if (m_sort.args.front().type == bvtype && m_sort.args.front().sz <= Config::g_ab_interpret_limit) {
				ab_interpret.set_input_concrete();
			}
			if (m_sort.args.back().type == bvtype && m_sort.args.back().sz <= Config::g_ab_interpret_limit) {
				ab_interpret.set_output_concrete();
			}
		}
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

//	static Inst* create(string name, unsigned size);
	static Inst* create(string name, unsigned size, Inst* parent, int pIdx, SORT sort);
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
	virtual Inst *bit_blast(InstToInstM& bb_map, bool init_visit = false);
	virtual Inst* bit_blast_version();

	virtual InstV& word2bool();

	string get_name() {
		return m_name;
	}

	static Inst *read_bin();
	virtual void write_bin();

	Inst* get_parent() {
	  return m_parent.first;
	}
	int get_parent_index() {
	  return m_parent.second;
	}

	virtual Inst* get_port(void) {
		return this;
	}
	virtual Inst* get_simple(void) {
		return this;
	}

private:
	string m_name;
	pair< Inst*, int > m_parent;

	ConstInst(string name, unsigned size, SORT sort, Inst* parent = NULL, int pIdx = -1) :
		m_name(name) {
	  m_parent = make_pair(parent, pIdx);
	  m_size = size;
	  m_sort = sort;
		childrenInfo[NUM]    = false;
		childrenInfo[SIG]    = false;
		childrenInfo[CONST]  = true;
		childrenInfo[FC]     = false;
		childrenInfo[NEXT]   = false;
		childrenInfo[WIRE]   = false;
		childrenInfo[CTRL]   = false;
		childrenInfo[MUX]    = false;
		childrenInfo[EQ]     = false;
		maxSize = m_size;

		if (m_sort.type == bvtype && m_size <= Config::g_ab_interpret_limit)
			ab_interpret.set_concrete();
		else if (m_sort.type == arraytype) {
			if (m_sort.args.front().type == bvtype && m_sort.args.front().sz <= Config::g_ab_interpret_limit) {
				ab_interpret.set_input_concrete();
			}
			if (m_sort.args.back().type == bvtype && m_sort.args.back().sz <= Config::g_ab_interpret_limit) {
				ab_interpret.set_output_concrete();
			}
		}
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
		unsigned d;
	} OpHash;

	struct OpHash_comp {
		bool operator()(const OpHash& lhs, const OpHash& rhs) const {
			if (lhs.a == rhs.a)
				if (lhs.b == rhs.b)
					if (lhs.c == rhs.c)
						return lhs.d < rhs.d;
					else
						return lhs.c < rhs.c;
				else
					return lhs.b < rhs.b;
			else
				return lhs.a < rhs.a;
		}
	};
	typedef map<OpHash, Inst*, OpHash_comp> OpHashM;
	typedef multimap<OpHash, Inst*, OpHash_comp> OpHashMM;
	static OpHashM hm_OpInst;//(type, inst_1, inst_2)
	static OpHashM hm_ITEInst;//(inst_1, inst_2, inst_3)
	static OpHashMM hm_ETCInst;//(inst_1, inst_2, inst_3)

	static int _wid;
	static int _numConcat;
	static int _numEx;
	static int _numUF;

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
		ArrayConst,  // array = arrayconst (width, value)
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
		IntMinus,	// integer minus (i.e. unary negation)
		Future
	} OpType;
#endif
	virtual void print_blif(ostream &out);
	virtual Inst *bit_blast(InstToInstM& bb_map, bool init_visit = false);
	virtual Inst* bit_blast_version();
	Inst *bit_blast_table(OpType op_type, InstL &chs_top);

	virtual InstV& word2bool();

	static Inst* create(OpType op, InstL exps, int o_size=0, bool to_simplify = true, Inst* wire=NULL, SORT sort = SORT());
	static Inst* create(OpType op, Inst* exp1, Inst* exp2 = 0, Inst* exp3 = 0, int o_size=0, bool to_simplify = true, Inst* wire=NULL, SORT sort = SORT());

	static OpInst* as(Inst*e) {
		return dynamic_cast<OpInst*> (e);
	}
	virtual void print(ostream&);
	virtual void print_summary(ostream&);
	virtual void print_verilog(ostream&);
	virtual InstType get_type() {
		return Op;
	}
	static string op2str(OpType t);
	const InstL* get_children() {
		return &m_exps;
	}
	//    virtual Inst* simplify();
	virtual bool check_consistency(ostream& out);
	virtual bool is_similar(Inst* e);
	virtual int instcmp(Inst* e);

	OpType get_op() {
		return m_op;
	}
	const InstL& get_exps() {
		return m_exps;
	}
	static void print_blif_table(ostream&out, OpType t, string i0, unsigned w_i0,
								 string i1, unsigned w_i1, string i2, unsigned w_i2,
								 string o, unsigned w_o, Inst *e = NULL);
	static Inst *read_bin();
	string get_euf_func_name();
	string get_euf_type_name();

	bool interpret();

	Inst* get_wire() {
		return m_wire;
	}
	void set_wire(Inst* wire) {
		assert(wire->get_type() == Wire);
		m_wire = wire;
	}

	Inst* concat_conditionals (InstL& vel, InstToIntM condMap);

  bool m_simple;


	int uf_counter;			// Counter to keep track whether a function got modified or not
	static int uf_gcounter;	// Global counter to keep track whether a function got modified or not

	int uf_white;		/// Flag to indicate whether a UF is white or not
						/// It can be VALID (white), INVALID (black), NOT_YET_COMPUTED

	virtual Inst* get_port(void) {
		return this;
	}
	virtual Inst* get_simple(void) {
//		return this;
	  if (m_simple)
	    return t_simple;
	  else
	    return this;
	}

#ifdef INTERPRET_EX_UF
  int get_simple_version();
  bool is_unordered_uf();
#endif

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
			if (op == Concat)
			{
				if (m_size != o_size)
				{
					cout << "Size mismatch: " << endl;
					cout << "msz: " << m_size << endl;
					cout << "osz: " << o_size << endl;
					for (auto ch : exps)
					{
						ch->print(cout);
						cout << " sz: " << ch->get_size() << endl;
					}
				}
				assert(m_size == o_size);
			}
			m_size = o_size;
		}
		m_sort.sz = m_size;

		childrenInfo[NUM]    = false;
		childrenInfo[SIG]    = false;
		childrenInfo[CONST]  = false;
		childrenInfo[FC]     = false;
		childrenInfo[NEXT]   = false;
		childrenInfo[WIRE]   = false;
		childrenInfo[CTRL]   = false;
		childrenInfo[MUX]    = false;
		childrenInfo[EQ]     = false;

		bool inputConcrete = true;

		bool isUF = (this->get_euf_func_name() != "0");
		fcLevel = 0;
		maxSize = m_size;
		trueFcLevel = 0;
		level = 0;
		for (InstL::iterator it = exps.begin(), end_it = exps.end(); it != end_it; ++it)
		{
			childrenInfo[NUM]    	|= (*it)->childrenInfo[NUM];
			childrenInfo[SIG]    	|= (*it)->childrenInfo[SIG];
			childrenInfo[CONST]   |= (*it)->childrenInfo[CONST];
			childrenInfo[FC	]   	|= (*it)->childrenInfo[FC];
			childrenInfo[NEXT]   	|= (*it)->childrenInfo[NEXT];
			childrenInfo[WIRE]   	|= (*it)->childrenInfo[WIRE];
			childrenInfo[CTRL]   	|= (*it)->childrenInfo[CTRL];
			childrenInfo[MUX]   	|= (*it)->childrenInfo[MUX];
			childrenInfo[EQ]    	|= (*it)->childrenInfo[EQ];

//			isConcrete &= (*it)->ab_interpret.is_concrete();
			inputConcrete &= (*it)->ab_interpret.output_concrete();

			if (fcLevel < (*it)->fcLevel)
				fcLevel = (*it)->fcLevel;

			if (trueFcLevel < (*it)->trueFcLevel)
				trueFcLevel = (*it)->trueFcLevel;

			if (maxSize < (*it)->maxSize)
				maxSize = (*it)->maxSize;

			if (level < (*it)->level)
				level = (*it)->level;

			if (isUF && !childrenInfo[FC])
			{
				OpInst* op = OpInst::as(*it);
				if (op && op->get_euf_func_name() != "0")
					childrenInfo[FC] = true;
				else
				{
					if ((*it)->get_type() == Ex)
						childrenInfo[FC] = true;
				}
			}
		}
		level += 1;
		if (isUF)
		{
			fcLevel += 1;
			if (m_op != Concat)
				trueFcLevel += 1;
		}
		else {
			if (m_op == Ternary)
				childrenInfo[MUX] = true;
			else
				childrenInfo[CTRL] = true;
			if (m_op == Eq || m_op == NotEq)
				childrenInfo[EQ] = true;
		}

		uf_white = not_yet_computed;
		uf_counter = 0;

//		if (isConcrete)
//			ab_interpret.set_concrete();
//		else if (m_size < st_concrete_limit)
//			ab_interpret.set_output_concrete();
		if (m_size <= Config::g_ab_interpret_limit)
		{
			if (inputConcrete)
				ab_interpret.set_concrete();
			else
				ab_interpret.set_output_concrete();
		}
	}
	OpInst(OpType op, Inst* exp, int o_size, Inst* wire, SORT sort) :
		m_op(op), m_wire(wire) {
		m_exps.push_back(exp);
		calc_size();
		if(o_size != 0){
			m_size = o_size;
		}
		uf_white = not_yet_computed;
		uf_counter = 0;
	}
	OpInst() {
	}
	virtual void write_bin();

	void print_complete(ostream&out);

	static OpInst* create();
	friend class Trans;
	virtual void calc_size();

private:
	static Inst* compare_and_simplify(Inst* lhs, Inst* rhs, bool eq);
};

unsigned find_size(OpInst::OpType op, InstL& exps);

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
	virtual void print(ostream&);
	virtual void print_summary(ostream&);
	virtual void print_verilog(ostream&);
	virtual void print_blif(ostream &out);
	virtual Inst *bit_blast(InstToInstM& bb_map, bool init_visit = false);
	virtual Inst* bit_blast_version();
	//    virtual Inst* simplify();

	virtual InstV& word2bool();

	virtual bool check_consistency(ostream& out);
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

	bool interpret();

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
		childrenInfo[CONST] = exp->childrenInfo[CONST];
		childrenInfo[FC] 	= exp->childrenInfo[FC];
		childrenInfo[NEXT] 	= exp->childrenInfo[NEXT];
		childrenInfo[WIRE]   = exp->childrenInfo[WIRE];
		childrenInfo[CTRL]   = exp->childrenInfo[CTRL];
		childrenInfo[MUX]    = exp->childrenInfo[MUX];
		childrenInfo[EQ]     = exp->childrenInfo[EQ];

		fcLevel = exp->fcLevel + 1;
		trueFcLevel = exp->trueFcLevel;
		maxSize = exp->maxSize;
		level = exp->level + 1;

		if (!childrenInfo[FC])
		{
			OpInst* op = OpInst::as(exp);
			if (op && op->get_euf_func_name() != "0")
			{
				childrenInfo[FC] = true;
			}
		}

//		if (exp->ab_interpret.is_concrete())
//			ab_interpret.set_concrete();
//		else if (m_size < st_concrete_limit)
//			ab_interpret.set_output_concrete();

		if (m_size <= Config::g_ab_interpret_limit)
		{
			if (exp->ab_interpret.output_concrete())
				ab_interpret.set_concrete();
			else
				ab_interpret.set_output_concrete();
		}
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
	static Inst* create(string name, unsigned size, MemType t, InstL&ports);
	static MemInst* as(Inst*e) {
		return dynamic_cast<MemInst*> (e);
	}
	virtual ~MemInst() {
	}
	virtual void print(ostream&);
	virtual void print_summary(ostream&) {
		assert(0);
	}
	virtual void print_verilog(ostream&);

	virtual void print_blif(ostream &out);
	virtual Inst *bit_blast(InstToInstM& bb_map, bool init_visit = false);
	virtual Inst* bit_blast_version();

	virtual InstV& word2bool();

	virtual InstType get_type() {
		return Mem;
	}
	const InstL* get_children() {
		return &m_ports;
	}
	const string get_name() {
		return m_name;
	}
	//    virtual Inst* simplify();
	virtual bool check_consistency(ostream& out);
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

	virtual Inst* get_port(void) {
		return this;
	}
	virtual Inst* get_simple(void) {
		return this;
	}
private:
	string m_name;
	InstL m_ports;
	MemType m_memtype;

	// you can't call!
	MemInst(string name, unsigned size, MemType t, InstL&writes) :
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
	static Inst* create(string name, unsigned size, InstL&children);
	static UFInst* as(Inst*e) {
		return dynamic_cast<UFInst*> (e);
	}
	virtual ~UFInst() {
	}
	virtual void print(ostream&);
	virtual void print_summary(ostream&) {
		assert(0);
	}
	virtual void print_verilog(ostream&);
	virtual void print_blif(ostream &out);
	virtual Inst *bit_blast(InstToInstM& bb_map, bool init_visit = false);
	virtual Inst* bit_blast_version();

	virtual InstV& word2bool();

	virtual InstType get_type() {
		return UF;
	}
	const InstL* get_children() {
		return &m_children;
	}
	const string get_name() {
		return m_name;
	}
	//    virtual Inst* simplify();
	virtual bool check_consistency(ostream& out) {
		return true;
	}
	virtual bool is_similar(Inst* e);
	virtual int instcmp(Inst* e);
	static Inst *read_bin();
	virtual void write_bin();

	virtual Inst* get_port(void) {
		return this;
	}
	virtual Inst* get_simple(void) {
		return this;
	}
private:
	string m_name;
	InstL m_children;

	// you can't call!
	UFInst(string name, unsigned size, InstL&children) :
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
	virtual void print(ostream&);
	virtual void print_summary(ostream&) {
		assert(0);
	}
	virtual void print_verilog(ostream&) {
		assert(0);
	}
	virtual void print_blif(ostream &out) {
		assert(0);
	}
	virtual Inst *bit_blast(InstToInstM& bb_map, bool init_visit = false) {
		assert(0);
	}
	virtual Inst* bit_blast_version();

	virtual InstV& word2bool();

	virtual InstType get_type() {
		return Lambda;
	}
	const InstL* get_children() {
		return &m_children;
	}
	//    virtual Inst* simplify();
	virtual bool check_consistency(ostream& out) {
		assert(0);
	}
	virtual bool is_similar(Inst* e) {
		assert(0);
	}
	virtual int instcmp(Inst* e) {
		assert(0);
	}

	virtual Inst* get_port(void) {
		return this;
	}
	virtual Inst* get_simple(void) {
		return this;
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
	static Inst* create(string name, unsigned size);
	static ArrayInst* as(Inst*e) {
		return dynamic_cast<ArrayInst*> (e);
	}
	virtual ~ArrayInst() {
	}
	virtual void print(ostream&);
	virtual void print_summary(ostream&) {
		assert(0);
	}
	virtual void print_verilog(ostream&) {
		assert(0);
	}
	virtual void print_blif(ostream &out) {
		assert(0);
	}
	virtual Inst *bit_blast(InstToInstM& bb_map, bool init_visit = false) {
		assert(0);
	}
	virtual Inst* bit_blast_version();

	virtual InstV& word2bool();

	virtual InstType get_type() {
		return Array;
	}
	const InstL* get_children() {
		return 0;
	}
	//    virtual Inst* simplify();
	virtual bool check_consistency(ostream& out) {
		assert(0);
	}
	virtual bool is_similar(Inst* e) {
		assert(0);
	}
	virtual int instcmp(Inst* e) {
		assert(0);
	}

	string get_name() {
		return m_name;
	}

	virtual Inst* get_port(void) {
		return this;
	}
	virtual Inst* get_simple(void) {
		return this;
	}
private:
	string m_name;

	// you can't call!
	ArrayInst(string name, unsigned size) :
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
	void print(ostream&);
	static void print_blif_latch(ostream&, string edge,
			string q, unsigned q_width, string s, unsigned s_width,
			string clk, string init);
};

typedef list<TransElem> TransElemL;

class Trans: public TransElemL {
public:
	Trans() {
	}
	void read_bin(istream&);
	void write_bin(ostream &out);
	// overrides default push_back
	void push_back(const TransElem&);
	void simplify();
	bool check_consistency();
	bool is_wire(string s) {
		// I am assuming at least one wire.
		assert(!m_wires.empty());
		return m_wires.find(s) != m_wires.end();
	}

	typedef struct Port {
		string port_name;
		int msb;
		int lsb;
	} Port;
	vector<Port> m_input_ports;
	vector<Port> m_output_ports;

	static string m_module_name;

	static istream* st_in;
	static ostream* st_out;

	static SORT read_sort();
	static void write_sort(SORT sort);

	static int read_int();
	static void write_int(int i);
	
	static long long read_long();
	static void write_long(long long value);
	
	static string read_str();
	static void write_str(string s);
	static char read_char();
	static void write_char(char value);


	static InstV st_id_to_ptr;
	static InstToUintM st_ptr_to_id;

	static Inst* id_to_ptr(unsigned id);
	static unsigned ptr_to_id(Inst*e);
	static InstL reachable;
	static void collect_reachable(Inst*);

	typedef set<string> StringS;
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

inline bool compare_pair::operator()(const pair< Inst*, Inst* >& left, const pair< Inst*, Inst* >& right) const {
	if (Config::g_random)
		return left < right;
	if (left.second == right.second) {
		if (left.first && right.first)
				return (left.first->get_id() < right.first->get_id());
			else
				return false;
	}
	else {
		if (left.second && right.second)
				return (left.second->get_id() < right.second->get_id());
			else
				return false;
	}
}

inline bool compare_pair_int::operator()(const pair< Inst*, int >& left, const pair< Inst*, int >& right) const {
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

inline bool compare_pair_string::operator()(const pair< Inst*, string >& left, const pair< Inst*, string >& right) const {
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

class CLAUSE {
public:
	static int _numSubsumedCube;

	Inst* cube;
	Inst* clause;
	InstV literals;

	CLAUSE () {
		cube = NULL;
		clause = NULL;
	}
	CLAUSE (const InstL& inp) {
		if (inp.empty()) {
			literals.push_back(NumInst::create(1, 1, SORT()));
			cube = literals.front();
		}
		else {
			for (InstL::const_iterator cit = inp.begin(); cit != inp.end(); cit++)
				literals.push_back(*cit);
			std::sort(literals.begin(), literals.end(), compare());
			if (literals.size() == 1)
				cube = inp.front();
			else
				cube = OpInst::create(OpInst::LogAnd, inp);
		}
		clause = OpInst::create(OpInst::LogNot, cube);
	}

	inline bool subsumes(const CLAUSE &b) {
	    return (literals.size() <= b.literals.size() &&
	            std::includes(b.literals.begin(), b.literals.end(), literals.begin(), literals.end(), compare()));
	}
};


ostream& operator<<(ostream& out, InstType& t);
ostream& operator<<(ostream& out, Inst& e);
ostream& operator<<(ostream& out, InstL& l);
ostream& operator<<(ostream& out, InstS& s);
ostream& operator<<(ostream& out, TransElem& t);
ostream& operator<<(ostream& out, TransElemL& l);
ostream& operator<<(ostream&, StringS&);
ostream& operator<<(ostream&, SigToInstM&);

#endif
