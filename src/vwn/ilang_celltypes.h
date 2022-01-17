/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


/*
 * ilang_celltypes.h
 *
 *  Created on: Jun 6, 2017
 *      Author: rock
 */

#ifndef SRC_VWN_ILANG_CELLTYPES_H_
#define SRC_VWN_ILANG_CELLTYPES_H_

#include "ilang_utils.h"


using namespace std;

namespace yos
{


enum TypeHash
{
	/// Internal memory cells
	// Unary
	$not,
	$pos,
	$neg,
	$reduce_and,
	$reduce_or,
	$reduce_xor,
	$reduce_xnor,
	$reduce_bool,
	$logic_not,
	$slice,
	$lut,
	$sop,

	// Binary
	$and,
	$or,
	$xor,
	$xnor,
	$shl,
	$shr,
	$sshl,
	$sshr,
	$shift,
	$shiftx,
	$lt,
	$le,
	$eq,
	$ne,
	$eqx,
	$nex,
	$ge,
	$gt,
	$add,
	$sub,
	$mul,
	$div,
	$mod,
	$pow,
	$logic_and,
	$logic_or,
	$concat,
	$macc,

	$mux,
	$pmux,
	$lcu,
	$alu,
	$fa,
	$tribuf,

	/// Internal memory cells
	$sr,
	$ff,
	$dff,
	$dffe,
	$dffsr,
	$adff,
	$dlatch,
	$dlatchsr,
	$memrd,
	$memwr,
	$meminit,
	$mem,
	$fsm,

	/// Standard cells
	$_BUF_,
	$_NOT_,
	$_AND_,
	$_NAND_,
	$_OR_,
	$_NOR_,
	$_XOR_,
	$_XNOR_,
	$_ANDNOT_,
	$_ORNOT_,
	$_MUX_,
	$_MUX4_,
	$_MUX8_,
	$_MUX16_,
	$_AOI3_,
	$_OAI3_,
	$_AOI4_,
	$_OAI4_,
	$_TBUF_,

	/// More cells
	$assert,
	$assume,

	/// Standard memory cells skipped for time being
	$_DFF_P_,
	$_DFF_N_
};

static map < string, TypeHash > m_hash;

class CellType
{
public:
	string type;
	set<string> inputs, outputs, params;
	bool is_evaluable;
};

class CellTypes
{
public:
	static map<string, CellType> cell_types;

	CellTypes()
	{
		setup();
	}

	void clear()
	{
		cell_types.clear();
	}

	bool cell_known(string type)
	{
		return cell_types.find(type) != cell_types.end();
	}

	bool cell_output(string type, string port)
	{
		auto it = cell_types.find(type);
		return it != cell_types.end() && it->second.outputs.count(port) != 0;
	}

	bool cell_input(string type, string port)
	{
		auto it = cell_types.find(type);
		return it != cell_types.end() && it->second.inputs.count(port) != 0;
	}

	bool cell_evaluable(string type)
	{
		auto it = cell_types.find(type);
		return it != cell_types.end() && it->second.is_evaluable;
	}

	static bool cell_is_memory(TypeHash type)
	{
		switch(type) {
		case $memrd:
		case $memwr:
		case $meminit:
			return true;
		}
		return false;
	}

private:
	void setup()
	{
		setup_internals();
		setup_internals_mem();
		setup_stdcells();
		setup_stdcells_mem();
		setup_hash();
	}

	void setup_hash(void)
	{
		/// Internal memory cells

		// Unary
		m_hash["$not"] 			= $not;
		m_hash["$pos"] 			= $pos;
		m_hash["$neg"] 			= $neg;
		m_hash["$reduce_and"] 	= $reduce_and;
		m_hash["$reduce_or"] 	= $reduce_or;
		m_hash["$reduce_xor"] 	= $reduce_xor;
		m_hash["$reduce_xnor"] 	= $reduce_xnor;
		m_hash["$reduce_bool"] 	= $reduce_bool;
		m_hash["$logic_not"] 	= $logic_not;
		m_hash["$slice"] 		= $slice;
		m_hash["$lut"] 			= $lut;
		m_hash["$sop"] 			= $sop;

		// Binary
		m_hash["$and"] 			= $and;
		m_hash["$or"] 			= $or;
		m_hash["$xor"] 			= $xor;
		m_hash["$xnor"] 		= $xnor;
		m_hash["$shl"] 			= $shl;
		m_hash["$shr"] 			= $shr;
		m_hash["$sshl"] 		= $sshl;
		m_hash["$sshr"] 		= $sshr;
		m_hash["$shift"] 		= $shift;
		m_hash["$shiftx"] 		= $shiftx;
		m_hash["$lt"] 			= $lt;
		m_hash["$le"] 			= $le;
		m_hash["$eq"] 			= $eq;
		m_hash["$ne"] 			= $ne;
		m_hash["$eqx"] 			= $eqx;
		m_hash["$nex"] 			= $nex;
		m_hash["$ge"] 			= $ge;
		m_hash["$gt"] 			= $gt;
		m_hash["$add"] 			= $add;
		m_hash["$sub"] 			= $sub;
		m_hash["$mul"] 			= $mul;
		m_hash["$div"] 			= $div;
		m_hash["$mod"] 			= $mod;
		m_hash["$pow"] 			= $pow;
		m_hash["$logic_and"] 	= $logic_and;
		m_hash["$logic_or"] 	= $logic_or;
		m_hash["$concat"] 		= $concat;
		m_hash["$macc"] 		= $macc;

		m_hash["$mux"] 			= $mux;
		m_hash["$pmux"] 		= $pmux;
		m_hash["$lcu"] 			= $lcu;
		m_hash["$alu"] 			= $alu;
		m_hash["$fa"] 			= $fa;
		m_hash["$tribuf"]		= $tribuf;

		/// Internal memory cells
		m_hash["$sr"] 			= $sr;
		m_hash["$ff"] 			= $ff;
		m_hash["$dff"] 			= $dff;
		m_hash["$dffe"] 		= $dffe;
		m_hash["$dffsr"] 		= $dffsr;
		m_hash["$adff"] 		= $adff;
		m_hash["$dlatch"] 		= $dlatch;
		m_hash["$dlatchsr"] 	= $dlatchsr;
		m_hash["$memrd"] 		= $memrd;
		m_hash["$memwr"] 		= $memwr;
		m_hash["$meminit"] 		= $meminit;
		m_hash["$mem"] 			= $mem;
		m_hash["$fsm"] 			= $fsm;

		/// Standard cells
		m_hash["$_BUF_"] 		= $_BUF_;
		m_hash["$_NOT_"] 		= $_NOT_;
		m_hash["$_AND_"] 		= $_AND_;
		m_hash["$_NAND_"] 		= $_NAND_;
		m_hash["$_OR_"] 		= $_OR_;
		m_hash["$_NOR_"] 		= $_NOR_;
		m_hash["$_XOR_"] 		= $_XOR_;
		m_hash["$_XNOR_"] 		= $_XNOR_;
		m_hash["$_ANDNOT_"] 	= $_ANDNOT_;
		m_hash["$_ORNOT_"] 		= $_ORNOT_;
		m_hash["$_MUX_"] 		= $_MUX_;
		m_hash["$_MUX4_"] 		= $_MUX4_;
		m_hash["$_MUX8_"] 		= $_MUX8_;
		m_hash["$_MUX16_"] 		= $_MUX16_;
		m_hash["$_AOI3_"] 		= $_AOI3_;
		m_hash["$_OAI3_"] 		= $_OAI3_;
		m_hash["$_AOI4_"] 		= $_AOI4_;
		m_hash["$_OAI4_"] 		= $_OAI4_;
		m_hash["$_TBUF_"] 		= $_TBUF_;

		/// Property cells
		m_hash["$assert"] 		= $assert;
		m_hash["$assume"] 		= $assume;

		/// Standard memory cells
		m_hash["$_DFF_P_"] 		= $_DFF_P_;
		m_hash["$_DFF_N_"] 		= $_DFF_N_;
		m_hash["$_FF_"] 		  = $ff;

	}

	void setup_type(string type, const set<string> &inputs, const set<string> &outputs, const set<string> &params, bool is_evaluable = false)
	{
		CellType ct = {type, inputs, outputs, params, is_evaluable};
		cell_types[ct.type] = ct;
	}

	void setup_internals()
	{
		std::vector<string> unary_ops = {
			"$not", "$pos", "$neg",
			"$reduce_and", "$reduce_or", "$reduce_xor", "$reduce_xnor", "$reduce_bool",
			"$logic_not", "$slice", "$lut", "$sop"
		};

		std::vector<string> binary_ops = {
			"$and", "$or", "$xor", "$xnor",
			"$shl", "$shr", "$sshl", "$sshr", "$shift", "$shiftx",
			"$lt", "$le", "$eq", "$ne", "$eqx", "$nex", "$ge", "$gt",
			"$add", "$sub", "$mul", "$div", "$mod", "$pow",
			"$logic_and", "$logic_or", "$concat", "$macc"
		};
		string A = "\\A", B = "\\B", S = "\\S", Y = "\\Y";
		string P = "\\P", G = "\\G", C = "\\C", X = "\\X";
		string BI = "\\BI", CI = "\\CI", CO = "\\CO", EN = "\\EN";

		set<string> params = {};

		set<string> inputs_unary = {A};
		set<string> outputs_unary = {Y};
		for (auto type : unary_ops)
			setup_type(type, inputs_unary, outputs_unary, params, true);

		set<string> inputs_binary = {A, B};
		set<string> outputs_binary = {Y};
		for (auto type : binary_ops)
			setup_type(type, inputs_binary, outputs_binary, params, true);

		set<string> inputs_mux = {A, B, S};
		set<string> outputs_mux = {Y};
		for (auto type : std::vector<string>({"$mux", "$pmux"}))
			setup_type(type, inputs_mux, outputs_mux, params, true);

		set<string> inputs_lcu = {P, G, CI};
		set<string> outputs_lcu = {CO};
		setup_type("$lcu", inputs_lcu, outputs_lcu, params, true);

		set<string> inputs_alu = {A, B, CI, BI};
		set<string> outputs_alu = {X, Y, CO};
		setup_type("$alu", inputs_alu, outputs_alu, params, true);

		set<string> inputs_fa = {A, B, C};
		set<string> outputs_fa = {X, Y};
		setup_type("$fa", inputs_fa, outputs_fa, params, true);

		set<string> inputs_tbuf = {A, EN};
		set<string> outputs_tbuf = {Y};
		setup_type("$tribuf", inputs_tbuf, outputs_tbuf, params, true);

		set<string> inputs_assert = {A, EN};
		setup_type("$assert", inputs_assert, set<string>(), params, true);

		set<string> inputs_assume = {A, EN};
		setup_type("$assume", inputs_assume, set<string>(), params, true);

//		setup_type("$live", {A, EN}, pool<RTLIL::IdString>(), true);
//		setup_type("$fair", {A, EN}, pool<RTLIL::IdString>(), true);
//		setup_type("$cover", {A, EN}, pool<RTLIL::IdString>(), true);
//		setup_type("$initstate", pool<RTLIL::IdString>(), {Y}, true);
//		setup_type("$anyconst", pool<RTLIL::IdString>(), {Y}, true);
//		setup_type("$anyseq", pool<RTLIL::IdString>(), {Y}, true);
//		setup_type("$equiv", {A, B}, {Y}, true);
	}

	void setup_internals_mem()
	{
		string SET = "\\SET", CLR = "\\CLR", CLK = "\\CLK", ARST = "\\ARST", EN = "\\EN";
		string Q = "\\Q", D = "\\D", ADDR = "\\ADDR", DATA = "\\DATA", RD_EN = "\\RD_EN";
		string RD_CLK = "\\RD_CLK", RD_ADDR = "\\RD_ADDR", WR_CLK = "\\WR_CLK", WR_EN = "\\WR_EN";
		string WR_ADDR = "\\WR_ADDR", WR_DATA = "\\WR_DATA", RD_DATA = "\\RD_DATA";
		string CTRL_IN = "\\CTRL_IN", CTRL_OUT = "\\CTRL_OUT";
		string ARST_POLARITY = "\\ARST_POLARITY", ARST_VALUE = "\\ARST_VALUE";
		string ABITS = "\\ABITS", MEMID = "\\MEMID", WORDS = "\\WORDS";
//		string CLK_ENABLE = "\\CLK_ENABLE", CLK_POLARITY = "\\CLK_POLARITY";

		set<string> params = {};

		set<string> inputs_sr = {SET, CLR};
		set<string> outputs_sr = {Q};
		setup_type("$sr", inputs_sr, outputs_sr, params);

		set<string> inputs_ff = {D};
		set<string> outputs_ff = {Q};
		setup_type("$ff", inputs_ff, outputs_ff, params);

		set<string> inputs_dff = {CLK, D};
		set<string> outputs_dff = {Q};
		setup_type("$dff", inputs_dff, outputs_dff, params);

		set<string> inputs_dffe = {CLK, EN, D};
		set<string> outputs_dffe = {Q};
		setup_type("$dffe", inputs_dffe, outputs_dffe, params);

		set<string> inputs_dffsr = {CLK, SET, CLR, D};
		set<string> outputs_dffsr = {Q};
		setup_type("$dffsr", inputs_dffsr, outputs_dffsr, params);

		set<string> params_adff = {ARST_POLARITY, ARST_VALUE};
		set<string> inputs_adff = {CLK, ARST, D};
		set<string> outputs_adff = {Q};
		setup_type("$adff", inputs_adff, outputs_adff, params_adff);

		set<string> inputs_dlatch = {EN, D};
		set<string> outputs_dlatch = {Q};
		setup_type("$dlatch", inputs_dlatch, outputs_dlatch, params);

		set<string> inputs_dlatchsr = {EN, SET, CLR, D};
		set<string> outputs_dlatchsr = {Q};
		setup_type("$dlatchsr", inputs_dlatchsr, outputs_dlatchsr, params);

		set<string> inputs_memrd = {CLK, EN, ADDR};
		set<string> outputs_memrd = {DATA};
		setup_type("$memrd", inputs_memrd, outputs_memrd, params);

		set<string> inputs_memwr = {CLK, EN, ADDR, DATA};
		set<string> outputs_memwr;
		setup_type("$memwr", inputs_memwr, outputs_memwr, params);

		set<string> inputs_meminit = {ADDR, DATA};
		set<string> outputs_meminit;
		setup_type("$meminit", inputs_meminit, outputs_meminit, params);

		set<string> inputs_mem = {RD_CLK, RD_EN, RD_ADDR, WR_CLK, WR_EN, WR_ADDR, WR_DATA};
		set<string> outputs_mem = {RD_DATA};
		setup_type("$mem", inputs_mem, outputs_mem, params);

		set<string> inputs_fsm = {CLK, ARST, CTRL_IN};
		set<string> outputs_fsm = {CTRL_OUT};
		setup_type("$fsm", inputs_fsm, outputs_fsm, params);
	}

	void setup_stdcells()
	{
		string A = "\\A", B = "\\B", C = "\\C", D = "\\D";
		string E = "\\E", F = "\\F", G = "\\G", H = "\\H";
		string I = "\\I", J = "\\J", K = "\\K", L = "\\L";
		string M = "\\I", N = "\\N", O = "\\O", P = "\\P";
		string S = "\\S", T = "\\T", U = "\\U", V = "\\V";
		string Y = "\\Y";

		set<string> params = {};

		set<string> inputs_buf = {A};
		set<string> outputs_buf = {Y};
		setup_type("$_BUF_", inputs_buf, outputs_buf, params, true);

		set<string> inputs_not = {A};
		set<string> outputs_not = {Y};
		setup_type("$_NOT_", inputs_not, outputs_not, params, true);

		set<string> inputs_and = {A, B};
		set<string> outputs_and = {Y};
		setup_type("$_AND_", inputs_and, outputs_and, params, true);

		set<string> inputs_nand = {A, B};
		set<string> outputs_nand = {Y};
		setup_type("$_NAND_", inputs_nand, outputs_nand, params, true);

		set<string> inputs_or = {A, B};
		set<string> outputs_or = {Y};
		setup_type("$_OR_",  inputs_or, outputs_or, params, true);

		set<string> inputs_nor = {A, B};
		set<string> outputs_nor = {Y};
		setup_type("$_NOR_", inputs_nor, outputs_nor, params, true);

		set<string> inputs_xor = {A, B};
		set<string> outputs_xor = {Y};
		setup_type("$_XOR_", inputs_xor, outputs_xor, params, true);

		set<string> inputs_xnor = {A, B};
		set<string> outputs_xnor = {Y};
		setup_type("$_XNOR_", inputs_xnor, outputs_xnor, params, true);

		set<string> inputs_andnot = {A, B};
		set<string> outputs_andnot = {Y};
		setup_type("$_ANDNOT_", inputs_andnot, outputs_andnot, params, true);

		set<string> inputs_ornot = {A, B};
		set<string> outputs_ornot = {Y};
		setup_type("$_ORNOT_", inputs_ornot, outputs_ornot, params, true);

		set<string> inputs_mux = {A, B, S};
		set<string> outputs_mux = {Y};
		setup_type("$_MUX_", inputs_mux, outputs_mux, params, true);

		set<string> inputs_mux4 = {A, B, C, D, S, T};
		set<string> outputs_mux4 = {Y};
		setup_type("$_MUX4_", inputs_mux4, outputs_mux4, params, true);

		set<string> inputs_mux8 = {A, B, C, D, E, F, G, H, S, T, U};
		set<string> outputs_mux8 = {Y};
		setup_type("$_MUX8_", inputs_mux8, outputs_mux8, params, true);

		set<string> inputs_mux16 = {A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, S, T, U, V};
		set<string> outputs_mux16 = {Y};
		setup_type("$_MUX16_", inputs_mux16, outputs_mux16, params, true);

		set<string> inputs_aoi3 = {A, B, C};
		set<string> outputs_aoi3 = {Y};
		setup_type("$_AOI3_", inputs_aoi3, outputs_aoi3, params, true);

		set<string> inputs_oai3 = {A, B, C};
		set<string> outputs_oai3 = {Y};
		setup_type("$_OAI3_", inputs_oai3, outputs_oai3, params, true);

		set<string> inputs_aoi4 = {A, B, C, D};
		set<string> outputs_aoi4 = {Y};
		setup_type("$_AOI4_", inputs_aoi4, outputs_aoi4, params, true);

		set<string> inputs_oai4 = {A, B, C, D};
		set<string> outputs_oai4 = {Y};
		setup_type("$_OAI4_", inputs_oai4, outputs_oai4, params, true);

		set<string> inputs_tbuf = {A, E};
		set<string> outputs_tbuf = {Y};
		setup_type("$_TBUF_", inputs_tbuf, outputs_tbuf, params, true);
	}

	void setup_stdcells_mem()
	{
		string S = "\\S", R = "\\R", C = "\\C";
		string D = "\\D", Q = "\\Q", E = "\\E";

		std::vector<char> list_np = {'N', 'P'}, list_01 = {'0', '1'};

		set<string> params = {};

		set<string> inputs_sr = {S, R};
		set<string> outputs_sr = {Q};
		for (auto c1 : list_np)
		for (auto c2 : list_np)
			setup_type(stringf("$_SR_%c%c_", c1, c2), inputs_sr, outputs_sr, params);

		set<string> inputs_ff = {D};
		set<string> outputs_ff = {Q};
		setup_type("$_FF_", inputs_ff, outputs_ff, params);

		set<string> inputs_dff = {C, D};
		set<string> outputs_dff = {Q};
		for (auto c1 : list_np)
			setup_type(stringf("$_DFF_%c_", c1), inputs_dff, outputs_dff, params);

		set<string> inputs_dffe = {C, D, E};
		set<string> outputs_dffe = {Q};
		for (auto c1 : list_np)
		for (auto c2 : list_np)
			setup_type(stringf("$_DFFE_%c%c_", c1, c2), inputs_dffe, outputs_dffe, params);

		set<string> inputs_dff_01 = {C, R, D};
		set<string> outputs_dff_01 = {Q};
		for (auto c1 : list_np)
		for (auto c2 : list_np)
		for (auto c3 : list_01)
			setup_type(stringf("$_DFF_%c%c%c_", c1, c2, c3), inputs_dff_01, outputs_dff_01, params);

		set<string> inputs_dffsr = {C, S, R, D};
		set<string> outputs_dffsr = {Q};
		for (auto c1 : list_np)
		for (auto c2 : list_np)
		for (auto c3 : list_np)
			setup_type(stringf("$_DFFSR_%c%c%c_", c1, c2, c3), inputs_dffsr, outputs_dffsr, params);

		set<string> inputs_dlatch = {E, D};
		set<string> outputs_dlatch = {Q};
		for (auto c1 : list_np)
			setup_type(stringf("$_DLATCH_%c_", c1), inputs_dlatch, outputs_dlatch, params);

		set<string> inputs_dlatchsr = {E, S, R, D};
		set<string> outputs_dlatchsr = {Q};
		for (auto c1 : list_np)
		for (auto c2 : list_np)
		for (auto c3 : list_np)
			setup_type(stringf("$_DLATCHSR_%c%c%c_", c1, c2, c3), inputs_dlatchsr, outputs_dlatchsr, params);
	}

};


}


#endif /* SRC_VWN_ILANG_CELLTYPES_H_ */
