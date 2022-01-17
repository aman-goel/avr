/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


/*
 * wif_utils.h
 *
 *  Created on: May 14, 2019
 *      Author: amangoel
 */

#ifndef SRC_VWN_WIF_UTILS_H_
#define SRC_VWN_WIF_UTILS_H_

#include <string>
#include <iostream>
#include <list>
#include <unordered_map>
#include <set>
#include <assert.h>

using namespace std;


namespace _wif {

/* Enum representing kinds of nets */
//add new ops before Dummy
enum WifOp {
	wConst, wVar, wDelay, wIte, wNot, wAnd, wAdd, wSub,
	wMul, wDiv, wSdiv, wMod, wSmod, wSh, wSsh, wExt,
	wSext, wBfe, wCat, wSelect, wUpdate, wEq,
	wLe, wSle, wLt, wSlt, wShl, wShr, wSshr, wVec, wPin, wLut, wRange,
	wSigned, wUnsigned, wDummy, wOpMax
};

static char const *wifop_str[] = {
	"Const", "Var", "Delay", "Ite", "Not", "And", "Add", "Sub",
	"Mul", "Div", "Sdiv", "Mod", "Smod", "Sh", "Ssh", "Ext",
	"Sext", "Bfe", "Cat", "Select", "Update", "Eq",
	"Le", "Sle", "Lt", "Slt", "Shl", "Shr", "Sshr", "Vec", "Pin", "Lut",
	"Range", "Signed", "Unsigned", "Dummy", "OpMax"
};

static unordered_map < string, WifOp > m_wifop;

class WifNode {
public:
	unsigned id;
	string name;
	int size;
	WifOp type;
	string attr;
	list < WifNode* > args;

	WifNode() {
		id = 0;
		name = "";
		size = 1;
		type = wConst;
		attr  = "";
		args.clear();
	}
	string print() {
		return	name +
				"\ts:" + to_string(size) +
				"\ttype: " + wifop_str[type] +
				"\targs:" + to_string(args.size()) +
				"\t" + attr;
	}

	bool operator<(const WifNode& other) const {
	    if(id == other.id) {
	    	assert(name == other.name);
	    }
		return id < other.id;
	}

	static unsigned _id;
	static void setup_op() {
//		for (int i = 0; i <= 36; i++) {
//			cout << "m_wifop[\"" << wifop_str[i] << "\"] = w" << wifop_str[i] << ";\n";
//		}
		m_wifop["Const"] = wConst;
		m_wifop["Var"] = wVar;
		m_wifop["Delay"] = wDelay;
		m_wifop["Ite"] = wIte;
		m_wifop["Not"] = wNot;
		m_wifop["And"] = wAnd;
		m_wifop["Add"] = wAdd;
		m_wifop["Sub"] = wSub;
		m_wifop["Mul"] = wMul;
		m_wifop["Div"] = wDiv;
		m_wifop["Sdiv"] = wSdiv;
		m_wifop["Mod"] = wMod;
		m_wifop["Smod"] = wSmod;
		m_wifop["Sh"] = wSh;
		m_wifop["Ssh"] = wSsh;
		m_wifop["Ext"] = wExt;
		m_wifop["Sext"] = wSext;
		m_wifop["Bfe"] = wBfe;
		m_wifop["Cat"] = wCat;
		m_wifop["Select"] = wSelect;
		m_wifop["Update"] = wUpdate;
		m_wifop["Eq"] = wEq;
		m_wifop["Le"] = wLe;
		m_wifop["Sle"] = wSle;
		m_wifop["Lt"] = wLt;
		m_wifop["Slt"] = wSlt;
		m_wifop["Shl"] = wShl;
		m_wifop["Shr"] = wShr;
		m_wifop["Sshr"] = wSshr;
		m_wifop["Vec"] = wVec;
		m_wifop["Pin"] = wPin;
		m_wifop["Lut"] = wLut;
		m_wifop["Range"] = wRange;
		m_wifop["Signed"] = wSigned;
		m_wifop["Unsigned"] = wUnsigned;
		m_wifop["Dummy"] = wDummy;
		m_wifop["OpMax"] = wOpMax;
	}
};


}

#endif /* SRC_VWN_WIF_UTILS_H_ */
