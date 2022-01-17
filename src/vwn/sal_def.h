/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


/*
 * sal_def.h
 *
 *  Created on: Feb 3, 2018
 *      Author: rock
 */

#ifndef SRC_VWN_SAL_DEF_H_
#define SRC_VWN_SAL_DEF_H_

#include <iostream>
#include <unordered_map>
#include <string>

// For Averroes
#include "avr_config.h"
#include "avr_word_netlist.h"

using namespace std;


namespace sal
{

#define sal_log(expr)	//cout << expr;
#define sal_logh(expr)	cout << expr;
#define sal_loge(expr)	cout << expr;
#define sal_logp(expr)	cout << expr;

#define ANY_NUM	-1

// Restriction on input sizes
typedef enum {
	$anysz,			// No restriction
	$samesz,		// All inputs of same size
	$tersz,			// All inputs (except first) of same size as output
	$outsz,			// All inputs of same size as output
	$boolsz			// All inputs boolean
} SizeType;

class CellType
{
public:
	CellType(const OpInst::OpType &typeIn, const int &numInp, const SizeType &inpSz, const bool &constantOp2)
		: type(typeIn), num_inp(numInp), inp_sz(inpSz), op2_const(constantOp2)
	{}

	CellType()
	{}

	OpInst::OpType get_op(void)			{	return  type;		}
	int get_num_input(void)				{	return  num_inp;	}
	SizeType get_input_restrcition(void){	return  inp_sz;		}
	bool is_constant_op2(void)			{	return  op2_const;	}

private:
	OpInst::OpType type;
	int num_inp;
	SizeType inp_sz;
	bool op2_const;
};

class CellTypes
{
public:
	CellTypes()
	{
		setup();
	}

	void clear()
	{
		cell_types.clear();
	}

	CellType get_sal_op(string type, bool force_exist = true)
	{
		map<string, OpInst::OpType>::iterator it = type_hash.find(type);
		if (it != type_hash.end())
			return cell_types[(*it).second];

		if (force_exist)
		{
			sal_loge("Error: cell type " << type << " not found" << endl);
			assert(0);
		}
		return cell_types[OpInst::Unknown];
	}

private:
	map<string, OpInst::OpType> type_hash;
	map<OpInst::OpType, CellType> cell_types;


	void setup()
	{
		setup_hash();
		setup_internals();
	}

	void setup_hash(void)
	{
		type_hash["+"]			= OpInst::Add;
		type_hash["-"]			= OpInst::Sub;
		type_hash["*"]			= OpInst::Mult;
		type_hash["/"]			= OpInst::Div;
		type_hash["%"]			= OpInst::Rem;
		type_hash["="]			= OpInst::Eq;
		type_hash["!="]			= OpInst::NotEq;
		type_hash["/="]			= OpInst::NotEq;
		type_hash[">"]			= OpInst::Gr;
		type_hash["<"]			= OpInst::Le;
		type_hash[">="]			= OpInst::GrEq;
		type_hash["<="]			= OpInst::LeEq;

		type_hash["and"]		= OpInst::LogAnd;
		type_hash["or"]			= OpInst::LogOr;
		type_hash["not"]		= OpInst::LogNot;
		type_hash["nand"]		= OpInst::LogNand;
		type_hash["nor"]		= OpInst::LogNor;
		type_hash["xor"]		= OpInst::LogXor;
		type_hash["xnor"]		= OpInst::LogXNor;

		type_hash["ite"]		= OpInst::Ternary;

		type_hash["extract"]	= OpInst::Extract;
		type_hash["concat"]		= OpInst::Concat;

		type_hash["minus"]		= OpInst::Minus;

		type_hash["bvand"]		= OpInst::BitWiseAnd;
		type_hash["bvor"]		= OpInst::BitWiseOr;
		type_hash["bvnot"]		= OpInst::BitWiseNot;
		type_hash["bvxor"]		= OpInst::BitWiseXor;
		type_hash["bvxnor"]		= OpInst::BitWiseXNor;
		type_hash["bvnor"]		= OpInst::BitWiseNor;
		type_hash["bvnand"]		= OpInst::BitWiseNand;

		type_hash["redand"]		= OpInst::ReductionAnd;
		type_hash["redor"]		= OpInst::ReductionOr;
		type_hash["redxor"]		= OpInst::ReductionXor;
		type_hash["redxnor"]	= OpInst::ReductionXNor;
		type_hash["rednand"]	= OpInst::ReductionNand;
		type_hash["rednor"]		= OpInst::ReductionNor;

		type_hash["shl"]		= OpInst::ShiftL;
		type_hash["shr"]		= OpInst::ShiftR;
		type_hash["ashl"]		= OpInst::AShiftL;
		type_hash["ashr"]		= OpInst::AShiftR;

		type_hash["true"]		= OpInst::LogTrue;
		type_hash["false"]		= OpInst::LogFalse;
		type_hash["uf"]			= OpInst::Unknown;


		/// Unavailable
//		AddC,//add with a carry out : i.e. input width = n, output width = (n+1)
//		Identity,
//		RotateL,
//		RotateR,
//		// V* operators are introduced to handle calypto benchmarks
//		VShiftL,	// Logical shift left by non-constant amount
//		VShiftR,	// Logical shift right by non-constant amount
//		VAShiftL,	// Arithmetic shift left by non-constant amount	: NOT USED (use VShiftL instead)
//		VAShiftR,	// Arithmetic shift right by non-constant amount
//		VRotateL,// rotate left by non-constant amount
//		VRotateR,// rotate right by non-constant amount
//		VEx,			// one-bit extraction of non-constant index (ex. a[b])
//		Future
	}

	void setup_type(OpInst::OpType type, int num_inp, SizeType inp_sz = $anysz, bool op2_const = false)
	{
		CellType ct(type, num_inp, inp_sz, op2_const);
		cell_types[type] = ct;
	}

	void setup_internals()
	{
		setup_type(OpInst::Add,		2, $outsz);
		setup_type(OpInst::Sub,		2, $outsz);
		setup_type(OpInst::Mult,	2, $outsz);
		setup_type(OpInst::Div,		2, $outsz);
		setup_type(OpInst::Rem,		2, $outsz);

		setup_type(OpInst::Eq,		2, $samesz);
		setup_type(OpInst::NotEq,	2, $samesz);
		setup_type(OpInst::Gr,		2, $samesz);
		setup_type(OpInst::Le,		2, $samesz);
		setup_type(OpInst::GrEq,	2, $samesz);
		setup_type(OpInst::LeEq,	2, $samesz);

		setup_type(OpInst::LogAnd,	ANY_NUM, $boolsz);
		setup_type(OpInst::LogOr,	ANY_NUM, $boolsz);
		setup_type(OpInst::LogNot,	1, $boolsz);
		setup_type(OpInst::LogNand,	ANY_NUM, $boolsz);
		setup_type(OpInst::LogNor,	ANY_NUM, $boolsz);
		setup_type(OpInst::LogXor,	2, $boolsz);
		setup_type(OpInst::LogXNor,	2, $boolsz);

		setup_type(OpInst::Ternary,	3, $tersz);

		setup_type(OpInst::Extract,	ANY_NUM);
		setup_type(OpInst::Concat,	ANY_NUM);

		setup_type(OpInst::Minus,	1, $outsz);

		setup_type(OpInst::BitWiseAnd,	2, $outsz);
		setup_type(OpInst::BitWiseOr,	2, $outsz);
		setup_type(OpInst::BitWiseNot,	1, $outsz);
		setup_type(OpInst::BitWiseXor,	2, $outsz);
		setup_type(OpInst::BitWiseXNor,	2, $outsz);
		setup_type(OpInst::BitWiseNor,	2, $outsz);
		setup_type(OpInst::BitWiseNand,	2, $outsz);

		setup_type(OpInst::ReductionAnd,	2, $samesz);
		setup_type(OpInst::ReductionOr,		2, $samesz);
		setup_type(OpInst::ReductionXor,	2, $samesz);
		setup_type(OpInst::ReductionXNor,	2, $samesz);
		setup_type(OpInst::ReductionNand,	2, $samesz);
		setup_type(OpInst::ReductionNor,	2, $samesz);

		setup_type(OpInst::ShiftL,	2, $samesz, true);
		setup_type(OpInst::ShiftR,	2, $samesz, true);
		setup_type(OpInst::AShiftL,	2, $samesz);
		setup_type(OpInst::AShiftL,	2, $samesz);

		setup_type(OpInst::LogTrue,		1, $boolsz);
		setup_type(OpInst::LogFalse,	1, $boolsz);
		setup_type(OpInst::Unknown,		ANY_NUM);
	}

};


}


#endif /* SRC_VWN_SAL_DEF_H_ */
