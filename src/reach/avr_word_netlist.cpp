/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


#include "avr_word_netlist.h"
#include <cstring>
#include <stdlib.h>
#include <iomanip>

//#define USE_INTERPRETED_ADD_SUB // this one is not used, see solver.cpp
#define PRINT_SHORTHAND_CONCAT

Config* Inst::config = NULL;

ResultType Inst::g_result = f_err;
int Inst::avr_wid = 0;

InstL Inst::m_exps_pool;
NumInst::NumHashM NumInst::hm_NumInst;

#ifdef ASSERT_DISTINCT_NUMBERS
map< pair<unsigned, SORT>, InstS > NumInst::m_sz_to_constants;
#endif

vector<Inst*> _idxHash; // Converting index to pre (or next) register, or inputs in the design

vector<Inst*> _wIdxHash; // Converting index to wire in the design

int Inst::maxContextCalls = REFRESH_CONTEXT_THRESHOLD;
int Inst::numContextCalls = 0;

unsigned Inst::num_warnings = 0;

InstS Inst::_s_reg = InstS(); // set of registers in the design, used to filter out inputs later
InstS Inst::_s_inp = InstS(); // set of inputs in the design

InstToPairBoolM Inst::_m_sn = InstToPairBoolM(); // simplified next,
InstToSetM Inst::_m_inp = InstToSetM(); // relation for inputs,
InstToSetM Inst::_m_inp_next = InstToSetM(); // relation for next inputs,

map< string, Inst*> Inst::_m_state_to_ptr = map< string, Inst*>(); // Map of name to pointer for registers in the design

InstToInstM Inst::_m_next_to_pre = InstToInstM(); // Map of next state registers to present state registers in the design
InstToInstM Inst::_m_pre_to_next = InstToInstM(); // Map of present state registers to next state registers in the design
InstToInstM Inst::_m_next_input_pre = InstToInstM(); // Map of next input to present input in the design
InstToInstM Inst::_m_pre_input_next = InstToInstM(); // Map of present input to next input in the design

InstToInstM Inst::_m_next_wire_pre = InstToInstM(); // Map of next wire to present wire in the design
InstToInstM Inst::_m_pre_wire_next = InstToInstM(); // Map of present wire to next wire in the design

InstToSetM Inst::_m_forward_coi = InstToSetM();  // Map of present state register/input to next state registers that are affected by it's value in the design
InstToSetM Inst::_m_backward_coi = InstToSetM(); // Map of present next state register to present state registers/inputs that it is affected by in the design



InstToIntM Inst::_m_numRegs;

vector<InstS> Inst::_relevantCones;

map<string, InstL> Inst::_whiteFlist = map<string, InstL>();
map<string, InstL> Inst::_blackFlist = map<string, InstL>();

InstPairToBoolM Inst::_setContains = InstPairToBoolM();

SigInst::StrVM SigInst::hm_SigInst;
WireInst::WireVM WireInst::hm_WireInst;
ConstInst::ConstVM ConstInst::hm_ConstInst;

OpInst::OpHashM OpInst::hm_OpInst;//(type, inst_1, inst_2)
OpInst::OpHashM OpInst::hm_ITEInst;//(inst_1, inst_2, inst_3)
OpInst::OpHashMM OpInst::hm_ETCInst;//(inst_1, inst_2, inst_3)
OpInst::OpHashM ExInst::hm_ExInst;//(inst_1, inst_2, inst_3)

int OpInst::_numUF = 0;
int OpInst::_numConcat = 0;
int OpInst::_numEx = 0;
int OpInst::_wid = 0;

unsigned Inst::st_visit = 1;
unsigned Inst::st_visit2 = 1;
unsigned Inst::st_visit3 = 1;
int Inst::not_yet_computed = NOT_YET_COMPUTED;
int Inst::v_gcounter = 0;
int OpInst::uf_gcounter = 0;

#ifdef ABSTRACTION_COURSE
int Inst::_allowed_abLevel = 1;
#endif

mpz_class Inst::_mpz_zero(0);
mpz_class Inst::_mpz_one(1);

string Trans::m_module_name = "";
istream* Trans::st_in = 0;
ostream* Trans::st_out = 0;
InstL Trans::reachable;
InstV Trans::st_id_to_ptr;
InstToUintM Trans::st_ptr_to_id;
unsigned Inst::st_id = 0;
Inst::StringS Inst::st_printed_signals;

int KEY_COI_VALUE::st_coi_key = 0;
int KEY_COI_VALUE::st_project_key = 0;

int Inst::st_retrieve_key = 0;
unsigned Inst::st_ba_idx = 0;

int Inst::st_dont_care_key = 0;
int Inst::st_reduce_key = 0;
int Inst::st_draw_key = 0;

int Inst::st_tsim_key = 0;

int WireInst::st_connect_key = 0;
int WireInst::st_slice_key = 0;

#if 1
//bool Inst::wn_simplify_extract_adv = false;
bool Inst::wn_simplify_extract = false;
bool Inst::wn_simplify_concat = false;
bool Inst::wn_simplify_const_pred = true;
bool Inst::wn_simplify_const_num = true;
bool Inst::wn_simplify_ite = true;
bool Inst::wn_simplify_repetition = true;
bool Inst::wn_1bit_dp_to_control = true;
bool Inst::wn_simplify_eq = true;
#else
bool Inst::wn_simplify_extract_adv = false;
bool Inst::wn_simplify_extract = false;
bool Inst::wn_simplify_concat = false;
bool Inst::wn_simplify_const_pred = false;
bool Inst::wn_simplify_const_num = false;
bool Inst::wn_simplify_ite = false;
bool Inst::wn_simplify_repetition = false;
bool Inst::wn_1bit_dp_to_control = true;
bool Inst::wn_simplify_eq = false;
#endif

bool Inst::print_concrete = false;

bool Inst::en_array = false;
bool Inst::en_integer = false;

int CLAUSE::_numSubsumedCube = 0;

Inst::Inst() {
	ve_orig = NULL;
	m_tcnt = 0;
	m_visit = 0;
	m_visit2 = 0;
	m_visit3 = 0;
	m_id = st_id++;
	term_type = not_yet_computed;
	is_invalid_state_term = not_yet_computed;
	v_important = not_yet_computed;
	v_counter = 0;
	acex_coi = 0;
	acex_fc = false;
	fcLevel = 0;
	trueFcLevel = 0;
	fcCombDist = 0;
	maxSize = 0;
	level = 0;

	tier = DEFAULT_TIER;

  hasInput = DEFAULT_VAL;
  hasReg   = DEFAULT_VAL;
  hasNegInit = DEFAULT_VAL;

  next2pre = INVALID_INST;
  pre2next = INVALID_INST;

	sval.clear();

	t_simple = this;
	activity = 0;
}

bool Inst::CompareInstByChildInfo (Inst *first, Inst *second) {
	if (first->activity != second->activity)
		return (first->activity > second->activity);

	if (first->fcLevel != second->fcLevel)
		return (first->fcLevel < second->fcLevel);

	if (first->childrenInfo[EQ] != second->childrenInfo[EQ])
		return (first->childrenInfo[EQ] > second->childrenInfo[EQ]);

	if (first->childrenInfo[NUM] != second->childrenInfo[NUM])
		return (first->childrenInfo[NUM] < second->childrenInfo[NUM]);

	if (first->maxSize != second->maxSize)
		return (first->maxSize > second->maxSize);

	return (first->get_id() < second->get_id());
}

bool Inst::CompareInstByChildInfoTier (Inst *first, Inst *second) {
	if (first->get_tier() != second->get_tier())
		return (first->get_tier() > second->get_tier());

	return CompareInstByChildInfo(first, second);
}



bool Inst::has_trelation(Inst* sigNext) {
	return _m_sn.find(sigNext) != _m_sn.end();
}

Inst* Inst::fetch_trelation_eq(Inst* sigNext) {
	InstToPairBoolM::iterator mit = _m_sn.find(sigNext);
	if (mit != _m_sn.end()) {
		if ((*mit).second.second)
			return (*mit).second.first;
	}
	return NULL;
}

Inst* Inst::fetch_trelation(Inst* sigNext) {
	InstToPairBoolM::iterator mit = _m_sn.find(sigNext);
	if (mit != _m_sn.end()) {
		return fetch_trelation(mit);
	}
	assert(0);
}

Inst* Inst::fetch_trelation(InstToPairBoolM::iterator mit) {
	assert (mit != _m_sn.end());
//	if ((*mit).second.second)
		return OpInst::create(OpInst::Eq, (*mit).first, (*mit).second.first);
	assert(0);
}


bool Inst::check_consistency(ostream& out) {
	if (m_size == 0) {
		//out << "zero size for instance: " << *this << endl;
		return false;
	}
	return true;
}

void Inst::collect_next_reg(Inst *top, InstS& s_next, bool init_visit)
{
	if (init_visit) {
		Inst::init_visit();
	}
	if (top->get_visit()) {
		return;
	}
	top->set_visit();

//	cout << "top: " << *top << endl;

	if (!(top->childrenInfo[NEXT]))
		return;

	const InstL* ch = top->get_children();
	if (ch)
	{
		for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it)
		{
			Inst * tve = *it;
			collect_next_reg(tve, s_next, false);
		}
	}
	else
	{
		SigInst* sig = SigInst::as(top);
		if (sig)
		{
			InstToPairBoolM::iterator mit = _m_sn.find(sig);
			if (mit != _m_sn.end())
			{
//				cout << "Inserting sig " << *sig << endl;
				s_next.insert(sig);
				if (!(*mit).second.second) {
					collect_next_reg((*mit).second.first, s_next, false);
				}
			}

//			string sigName = sig->get_name();
////			cout << sigName << endl;
//			if (sigName.find_last_of('$') != string::npos)
//			{
//				string next = sigName.substr(sigName.find_last_of('$'), 5);
//	//			cout << next << endl;
//				if (next.compare("$next") == 0)
//				{
//	//				cout << "Inserting sig " << *sig << endl;
//					s_next.insert(sig);
//				}
//			}

		}
	}
}

// Returns 1 if inst_a can be derived from inst_b
// with a certain combination of mux controls
// We assume that 1) a boolean net can be substituted with
// a boolean constant and 2) inst_a does not contain
// any muxes (but inst_b may contain muxes)
int Inst::is_matched(Inst *inst_a, Inst *inst_b){
	if(inst_a->get_size() != inst_b->get_size()){
		return 0;
	}

	if((inst_a->get_type() == Num) && (inst_a->get_size() == 1)){
		return 1;
	}

	if((inst_b->get_type() == Sig) || (inst_b->get_type() == Num)){
		return (inst_a == inst_b) ? 1 : 0;
	}

	OpInst *op_inst_b = OpInst::as(inst_b);
	if(op_inst_b){
		if(op_inst_b->get_op() == OpInst::Ternary){
			// if op_inst_b contains a mux, check every term it can be
			const InstL* ch_b = inst_b->get_children();
			assert(ch_b);
			InstL::const_iterator it_chb = ch_b->begin();
			for (; it_chb != ch_b->end(); ++it_chb){
				int ret = is_matched(inst_a, *it_chb);
				if(ret == 1){
					return 1;
				}
			}
		}else{
			OpInst *op_inst_a = OpInst::as(inst_a);
			if(op_inst_a){
				if(op_inst_a->get_op() == op_inst_b->get_op()){
					const InstL* ch_a = inst_a->get_children();
					const InstL* ch_b = inst_b->get_children();
					if (ch_a && ch_b && (ch_a->size() == ch_b->size())){
						InstL::const_iterator it_cha = ch_a->begin();
						InstL::const_iterator it_chb = ch_b->begin();
						for (; it_cha != ch_a->end(); ++it_cha, ++it_chb){
							int ret = is_matched(*it_cha, *it_chb);
							if(ret != 1){
								return ret;
							}
						}
						return 1;
					}
				}
			}
		}
	}

	return 0;
}

Inst* Inst::get_signal()
{

	OpInst* op = OpInst::as(this);
	if (op)
	{
		Inst* sig = op->get_wire();
		assert(sig);
		return sig;
	}
	else
		return this;
}

// returns term_type;
// 		CONSTANT_ONLY 	  (0): term of constants (i.e. no states and no inputs)
// 		NO_INPUTS 	  	  (1): includes only states and constants (no inputs)
// 		NO_STATES		  (2): includes only inputs and constants (no states)
//		STATES_AND_INPUTS (3): includes both states and inputs
// Note that top->term_type is Inst::not_yet_computed if the term_type of top has not been computed
int Inst::check_term_type(Inst *top) {
	if(top->term_type != Inst::not_yet_computed){
		return top->term_type;
	}

	int top_term_type = 0;
	if (top->get_type() == Sig) {
		if((!Inst::has_trelation(top)) && (_s_reg.find(top) == _s_reg.end())){	// inputs
			top_term_type = NO_STATES;
		}else{	// registers
			top_term_type = NO_INPUTS;
		}
	} else {
		const InstL* ch = top->get_children();
		if (ch) {
			for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it) {
				int ch_term_type = check_term_type(*it);
				top_term_type = top_term_type | ch_term_type;
			}
		}else{ // constants
			top_term_type = CONSTANT_ONLY;
		}
	}
	top->term_type = top_term_type;
	return top->term_type;
}

Inst* OpInst::compare_and_simplify(Inst* lhs, Inst* rhs, bool eq) {
  //{a1, b1, c1} == {a2, b2, c2} -> (a1 == a2) && (b1 == b2) && (c1 == c2)
  const InstL* chL = lhs->get_children();
  const InstL* chR = rhs->get_children();
  assert(chL);
  assert(chR);
  InstL vel;
  bool isFalse = false;
  InstL::const_iterator citL = chL->begin();
  InstL::const_iterator citR = chR->begin();
  for (; citL != chL->end(); ++citL, ++citR)
  {
    Inst *tveL = *citL;
    Inst *tveR = *citR;
    tveL = tveL->get_port();
    tveR = tveR->get_port();
#ifdef EX_CC_LEVEL1
    tveL = tveL->get_simple();
    tveR = tveR->get_simple();
#endif
    if (tveL != tveR) {
      if ((tveL->get_type() == Num) && (tveR->get_type() == Num)) {
        isFalse = true;
        break;
      }
      else {
        Inst* eqInst = OpInst::create(Eq, tveL, tveR);
#ifdef EX_CC_LEVEL2
//            eqInst = eqInst->get_port();
        eqInst = eqInst->get_simple();
#endif
        vel.push_back(eqInst);
      }
    }
  }
  Inst* v_and;

  if (isFalse)
    v_and = NumInst::create(0, 1, SORT());
  else if (vel.size() == 0)
    v_and = NumInst::create(1, 1, SORT());
  else if (vel.size() == 1)
    v_and = vel.front();
  else
    v_and = OpInst::create(OpInst::LogAnd, vel);

  if (!eq)
    v_and = OpInst::create(LogNot, v_and);

  return v_and;
}


#ifdef ABSTRACTION_COURSE
// check_v_important() returns
// INVALID (1) : if top is invalid
// VALID   (0) : if top is valid
int Inst::check_v_important(Inst *top)
{
	if(top->v_important != Inst::not_yet_computed)
	{
		return top->v_important;
	}
	else
	{
		if (top->fcLevel > Inst::_allowed_abLevel)
		{
			top->v_important = INVALID;
			return INVALID;
		}
		else
		{
			top->v_important = VALID;
			return VALID;
		}
	}
}
#endif

// check_if_uf_black() returns
// INVALID (1) : if top is UF and in _blackFlist
// INVALID (0) : otherwise
#ifdef ABSTRACTION_COURSE
bool Inst::check_if_uf_black(Inst *top)
{
	OpInst *op_inst = OpInst::as(top);
	if(op_inst)
	{
		if (op_inst->uf_counter != OpInst::uf_gcounter)
		{
			op_inst->uf_white = Inst::not_yet_computed;
			op_inst->uf_counter = OpInst::uf_gcounter;
		}

		if(op_inst->uf_white != Inst::not_yet_computed)
		{
			return op_inst->uf_white;
		}

		string top_euf_func_name;
		ExInst *ex_inst = ExInst::as(top);
		if(ex_inst)
		{
			top_euf_func_name = ex_inst->get_euf_func_name();
		}
		else
		{
			top_euf_func_name = op_inst->get_euf_func_name();
		}

		if (ex_inst || op_inst->get_op() == OpInst::Concat)
		{
			top_euf_func_name = "0";
		}

		if(top_euf_func_name != "0")
		{
			InstL& apps = _blackFlist[top_euf_func_name];
			for(InstL::iterator it_apps = apps.begin(); it_apps != apps.end(); ++it_apps)
			{
				Inst *t_inst = *it_apps;
				if((top == t_inst))
				{
					op_inst->uf_white = INVALID;
					return INVALID;
				}
			}
		}
		op_inst->uf_white = VALID;
	}
	return VALID;
}

// contains_black_uf() returns
// INVALID aka True (1) : if top contains a UF in _blackFlist
// VALID aka False  (0) : if top is valid
int Inst::contains_black_uf(Inst *top)
{
	if (top->v_counter != Inst::v_gcounter)
	{
		top->v_important = Inst::not_yet_computed;
		top->v_counter = Inst::v_gcounter;
	}

	if(top->v_important != Inst::not_yet_computed)
	{
		return top->v_important;
	}

	const InstL* ch_top = top->get_children();
	if(ch_top)
	{
		InstL::const_iterator it_top = ch_top->begin();
		for (; it_top != ch_top->end(); ++it_top)
		{
			Inst *t_inst = *it_top;
			contains_black_uf(t_inst);
			int t_ist = t_inst->v_important;
			if(t_ist == INVALID)
			{
				top->v_important = INVALID;
				return 1;
			}
		}

		string top_euf_func_name;
		OpInst *op_inst = OpInst::as(top);
		if(op_inst)
		{
			ExInst *ex_inst = ExInst::as(top);
			if(ex_inst)
			{
				top_euf_func_name = ex_inst->get_euf_func_name();
			}
			else
			{
				top_euf_func_name = op_inst->get_euf_func_name();
			}

			if (ex_inst || op_inst->get_op() == OpInst::Concat)
			{
				top_euf_func_name = "0";
			}
		}
		if(top_euf_func_name != "0")
		{
			InstL& apps = _blackFlist[top_euf_func_name];
			for(InstL::iterator it_apps = apps.begin(); it_apps != apps.end(); ++it_apps)
			{
				Inst *t_inst = *it_apps;
				if((top == t_inst))
				{
					top->v_important = INVALID;
					return 1;
				}
			}
		}
	}
	top->v_important = VALID;
	return 0;
}
#endif

Inst* SigInst::create(string name, unsigned size, SORT sort) {
	assert(name != "");
	assert(size != 0 || sort.type != bvtype);

	StrVM::iterator it = hm_SigInst.find(name);
	if (it != hm_SigInst.end()) {
		return it->second;
	}

	sort.sz = size;
	if (sort.type == arraytype)
		assert(sort.sz == sort.args[1].sz);

	SigInst* e = new SigInst(name, size, sort);
	m_exps_pool.push_back(e);
	e->set_hash1(1);
	hm_SigInst.insert(make_pair(name, e));
	e->interpret();
	return e;
}

//SigInst* SigInst::create() {
//	SigInst* e = new SigInst;
//	m_exps_pool.push_back(e);
//	e->set_hash1(1);
//	return e;
//}

Inst* NumInst::create(string snum, unsigned size, unsigned base, SORT sort, bool fromSystem) {	// Note 4'd0 : "0000"
	assert(size != 0 || sort.type == inttype);
	if (sort.type == arraytype) {
		cout << "trying creating number of array sort " << sort << endl;
		assert(0);
	}

// 	string *str = new string(snum);
// 	mpz_class t_mpzc(str->c_str(), 2);

// 	mpz_class t_mpzc = 2000;
//	(string("10000").c_str());
//	mpz_class t_mpzc(snum.c_str(), 2);
// 	string tstr(snum);
// 	mpz_class t_mpzc(tstr, 2);
//	mpz_class t_mpzc(tstr, 2);
//	mpz_class t_mpzc(snum.c_str(), 2);
	
//	cout << "snum: " << snum << ", size: " << size << ", base: " << base << endl;

	mpz_t mpz_mask;	// after shift right
	mpz_init(mpz_mask);
	mpz_set_str(mpz_mask, snum.c_str(), base);

	// NOTE!! This is tricky, but you should not initialize an mpz_class instance
	// directly from string. This often does not set the value of the instance.
	// Therefore, you should use mpz_t initialized by the string to initialize
	// the instance.
	mpz_class t_mpzc(mpz_mask);
//	cout << "t_mpzc: " << t_mpzc << endl;
//	t_mpzc = "11111111";
	mpz_clear(mpz_mask);
//	cout << "1" << endl;

	sort.sz = size;
	NumType t_idx(t_mpzc, make_pair(size, sort));
//	cout << "2" << endl;
	NumHashM::iterator it = hm_NumInst.find(t_idx);
//	cout << "3" << endl;
	if (it != hm_NumInst.end()) {
		return it->second;
	}
//	cout << "4" << endl;
 	NumInst* e = new NumInst(t_mpzc, size, fromSystem, sort);
	m_exps_pool.push_back(e);
	e->set_hash1(1);
//	cout << "5" << endl;
	hm_NumInst.insert(make_pair(t_idx, e));

#ifdef ASSERT_DISTINCT_NUMBERS
	if (!(Config::g_ab_interpret && Config::g_ab_interpret_limit == 0)) {
		pair<unsigned, SORT> sz = make_pair(size, sort);
		if ((sz.first != 1) && (sz.first > Config::g_ab_interpret_limit || sz.second.type != bvtype))
		{
			map< pair<unsigned, SORT>, InstS >::iterator tit = m_sz_to_constants.find(sz);
			if (tit == m_sz_to_constants.end())
			{
				InstS consts;
				consts.insert(e);
				m_sz_to_constants[sz] = consts;
			}
			else
			{
				InstS& consts = (*tit).second;
				if (consts.find(e) == consts.end())
					consts.insert(e);
			}
		}
	}
#endif
	e->interpret();
	return e;
}
Inst* NumInst::create(unsigned long num, unsigned size, SORT sort, bool fromSystem) {
	assert(size != 0 || sort.type == inttype);
	if (size == 1)
		assert(num == 0 || num == 1);
	if (sort.type == arraytype) {
		cout << "trying creating number of array sort " << sort << endl;
		assert(0);
	}

	sort.sz = size;
	NumType t_idx(mpz_class(num), make_pair(size, sort));
	NumHashM::iterator it = hm_NumInst.find(t_idx);
	if (it != hm_NumInst.end()) {
		return it->second;
	}
	NumInst* e = new NumInst(num, size, fromSystem, sort);
	m_exps_pool.push_back(e);
	e->set_hash1(1);
	hm_NumInst.insert(make_pair(t_idx, e));

#ifdef ASSERT_DISTINCT_NUMBERS
	if (!(Config::g_ab_interpret && Config::g_ab_interpret_limit == 0)) {
		pair<unsigned, SORT> sz = make_pair(size, sort);
		if ((sz.first != 1) && (sz.first > Config::g_ab_interpret_limit || sz.second.type != bvtype))
		{
			map< pair<unsigned, SORT>, InstS >::iterator tit = m_sz_to_constants.find(sz);
			if (tit == m_sz_to_constants.end())
			{
				InstS consts;
				consts.insert(e);
				m_sz_to_constants[sz] = consts;
			}
			else
			{
				InstS& consts = (*tit).second;
				if (consts.find(e) == consts.end())
					consts.insert(e);
			}
		}
	}
#endif
	e->interpret();
	return e;
}
Inst* NumInst::create(mpz_class mnum, unsigned size, SORT sort, bool fromSystem) {
	assert(size != 0 || sort.type != bvtype);
	if (sort.type == arraytype) {
		cout << "trying creating number of array sort " << sort << endl;
		assert(0);
	}
	sort.sz = size;
	NumType t_idx(mnum, make_pair(size, sort));
	NumHashM::iterator it = hm_NumInst.find(t_idx);
	if (it != hm_NumInst.end()) {
		return it->second;
	}
	NumInst* e = new NumInst(mnum, size, fromSystem, sort);
	m_exps_pool.push_back(e);
	e->set_hash1(1);
	hm_NumInst.insert(make_pair(t_idx, e));

#ifdef ASSERT_DISTINCT_NUMBERS
	if (!(Config::g_ab_interpret && Config::g_ab_interpret_limit == 0)) {
		pair<unsigned, SORT> sz = make_pair(size, sort);
		if ((sz.first != 1) && (sz.first > Config::g_ab_interpret_limit || sz.second.type != bvtype))
		{
			map< pair<unsigned, SORT>, InstS >::iterator tit = m_sz_to_constants.find(sz);
			if (tit == m_sz_to_constants.end())
			{
				InstS consts;
				consts.insert(e);
				m_sz_to_constants[sz] = consts;
			}
			else
			{
				InstS& consts = (*tit).second;
				if (consts.find(e) == consts.end())
					consts.insert(e);
			}
		}
	}
#endif
	e->interpret();
	return e;
}

/// Aman
Inst* WireInst::create(string name, unsigned sz, Inst* port) {
	WireVM::iterator it = hm_WireInst.find(name);
	if (it != hm_WireInst.end()) {
		return it->second;
	}

	WireInst* e;
	if (port)
	{
		if (port->get_size() != sz)
		{
			cout << name << "  " << sz << "  " << *port << "  " << port->get_size() << endl;
		}
		assert(port->get_size() == sz);

		if (!(port->get_type() == Op || port->get_type() == Ex))
		{
			switch(port->get_type())
			{
			case Sig:
			case Num:
			case Wire:
				return port;
				break;
			default:
				assert(0);
			}
		}

		e = new WireInst(port, name);
		if (e->get_size() != sz)
		{
			cout << *e << "  " << e->get_size() << endl;
			cout << *port << "  " << sz << endl;
		}
		assert(e->get_size() == sz);

		OpInst* op = OpInst::as(port);
		assert(op);
		op->set_wire(e);
	}
	else
		assert(0);

	m_exps_pool.push_back(e);
	e->set_hash1(1);
	hm_WireInst.insert(make_pair(name, e));

//	cout << "Creating " << *e << " from " << *port << endl;
	return e;
}
/// END

/// Aman
//Inst* ConstInst::create(string name, unsigned size) {
//  return ConstInst::create(name, size, NULL);
//}

Inst* ConstInst::create(string name, unsigned size, Inst* parent, int pIdx, SORT sort) {
	assert(name != "");
	assert(size != 0 || sort.type != bvtype);

	ConstVM::iterator it = hm_ConstInst.find(name);
	if (it != hm_ConstInst.end()) {
		return it->second;
	}

	sort.sz = size;
	ConstInst* e = new ConstInst(name, size, sort, parent, pIdx);
	m_exps_pool.push_back(e);
	e->set_hash1(1);
	hm_ConstInst.insert(make_pair(name, e));
	return e;
}
/// END

Inst* ExInst::create(Inst* exp_orig, unsigned hi_orig, unsigned lo_orig, Inst* wire) {
	//	assert(hi < 1073741824);//1073741824 = 2^30
	OpHash t_idx;
	//	t_idx.a = (unsigned)exp;
	t_idx.a = exp_orig->get_id();
	t_idx.b = hi_orig;
	t_idx.c = lo_orig;
	t_idx.d = hi_orig - lo_orig + 1;
	OpHashM::iterator it = hm_ExInst.find(t_idx);
	if (it != hm_ExInst.end()) {
		if (wn_simplify_extract)
		{
			ExInst* tmp = ExInst::as(it->second);
//			cout << "Simp: " << *tmp << " -> " << *tmp->t_simple << endl;
			return tmp->get_simple();
		}
		else
			return it->second;
	}

	assert(exp_orig);
	assert(hi_orig >= lo_orig);
	assert((hi_orig - lo_orig + 1) <= exp_orig->get_size());

	ExInst* e = new ExInst(exp_orig, hi_orig, lo_orig, wire);
	m_exps_pool.push_back(e);

	e->set_hash1(exp_orig->get_hash1());

	_numEx++;

	Inst* t_simplified_ve = e;
	bool need_new = false;

#ifdef INTERPRET_EX_CC
	Inst* exp = e->get_exp();
	unsigned hi = e->get_hi();
	unsigned lo = e->get_lo();

  e->m_simple = true;

  if (e->interpret()) {
  	// do nothing, done
  }
	/// If Ex limits are whole range, done
  else if (exp->get_size() == (hi - lo + 1))
	{
		need_new = true;
    exp = exp->get_port();
#ifdef EX_CC_LEVEL1
		exp = exp->get_simple();
#endif
		t_simplified_ve = exp;
		assert(lo == 0);
	}
	else
	{
		exp = exp->get_port();
#ifdef EX_CC_LEVEL1
		exp = exp->get_simple();
#endif

		/// Deal with Cc expression
		if (exp->get_type() == Op && (OpInst::as(exp)->get_op() == OpInst::Concat))
		{
			need_new = true;
			//{c[1:0], a[2:1], b[2:0]}[5:3] -> {c[1:0][0:0], a[2:1][2:1]}
			const InstL* ch = exp->get_children();
			assert(ch);
			{
				InstL vel;
				unsigned s_loc = 0, e_loc = 0;
				for (InstL::const_iterator cit = ch->begin(); cit != ch->end(); ++cit)
				{
					Inst *tve = *cit;
          tve = tve->get_port();
#ifdef EX_CC_LEVEL1
					tve = tve->get_simple();
#endif
					unsigned size = tve->get_size();
					unsigned ns = 0;
					unsigned ne = size - 1;
					s_loc = e_loc;
					e_loc += size;
					if (s_loc < lo) {
						ns = lo - s_loc;
					}
					if (ns > ne) {
						continue;
					}
					if (e_loc > hi) {
						// (hi > s_loc) is always true
						ne = hi - s_loc;
					}
					if ((ne - ns + 1) != size) {

						tve = ExInst::create(tve, ne, ns);
					}

#ifdef EX_CC_LEVEL2
//					tve = tve->get_port();
					tve = tve->get_simple();
#endif
					vel.push_back(tve);

					if (hi < e_loc) {
						break;
					}
				}
				Inst* v_concat;

				if (vel.size() == 1)
					v_concat = vel.front();
				else
					v_concat = OpInst::create(OpInst::Concat, vel);

#ifdef EX_CC_LEVEL2
				v_concat = v_concat->get_simple();
#endif
				t_simplified_ve = v_concat;
//					cout << "## simplification: " << *e << " -> " << *v_concat << endl;
			}
		}
		/// Deal with Ex expression
		else if (exp->get_type() == Ex)
		{
			need_new = true;
			//c[1:0][0:0] -> c[0:0]
			//unsigned exp_hi = ExInst::as(exp)->get_hi();
			unsigned exp_lo = ExInst::as(exp)->get_lo();
			unsigned ns = exp_lo + lo;
			unsigned ne = exp_lo + hi;

			Inst *tve = exp->get_children()->front();
			tve = tve->get_port();
#ifdef EX_CC_LEVEL1
			tve = tve->get_simple();
#endif

			Inst* v_ex = ExInst::create(tve, ne, ns);
#ifdef EX_CC_LEVEL2
			v_ex = v_ex->get_simple();
#endif
			t_simplified_ve = v_ex;
			//			cout << "## simplification2: " << *e << " -> " << *v_ex << endl;
		}
		/// Deal with Num expression
		else if (exp->get_type() == Num)
		{
			need_new = true;
			//255'd0[0:0] -> 1'd0
			mpz_t mpz_shift_right;	// after shift right
			mpz_t mpz_mask;	// after shift right
			mpz_t mpz_extracted;
			unsigned width = hi - lo + 1;

			mpz_init(mpz_shift_right);
			mpz_init(mpz_mask);
			mpz_init(mpz_extracted);

			mpz_fdiv_q_2exp(mpz_shift_right, NumInst::as(exp)->get_mpz()->get_mpz_t(), lo);

			string str_mask(NumInst::as(exp)->get_size() - width, '0');
			str_mask.append(width, '1');
			mpz_set_str(mpz_mask, str_mask.c_str(), 2);
			mpz_and(mpz_extracted, mpz_shift_right, mpz_mask);

			mpz_class mpzc_extracted = mpz_class(mpz_extracted);
			Inst* v_num = NumInst::create(mpzc_extracted, width, SORT());
			mpz_clear(mpz_shift_right);
			mpz_clear(mpz_mask);
			mpz_clear(mpz_extracted);
			t_simplified_ve = v_num;
		}
		/// Deal with Ternary expression
		else if (exp->get_type() == Op && (OpInst::as(exp)->get_op() == OpInst::Ternary))
		{
			need_new = true;
			//(ite(cond, ife, the))[5:3] -> (ite(cond, ife[5:3], the[5:3]))
			InstL::const_iterator it = exp->get_children()->begin();
			Inst* cond = *it;
			it++;
			Inst* ife = *it;
			it++;
			Inst* the = *it;
			assert(cond && ife && the);
      cond = cond->get_port();
      ife = ife->get_port();
      the = the->get_port();
#ifdef EX_CC_LEVEL1
			cond = cond->get_simple();
			ife = ife->get_simple();
			the = the->get_simple();
#endif

#ifdef EX_CC_LEVEL3
      if (ife->get_type() == Sig) {
        if (the->get_type() == Sig) {
          need_new = false;
        }
      }
      else
#endif
			{
        /// Push in Ex to children and go to simplified children
        Inst* ife_new = ExInst::create(ife, hi, lo);
        Inst* the_new = ExInst::create(the, hi, lo);
#ifdef EX_CC_LEVEL2
        ife_new = ife_new->get_simple();
        the_new = the_new->get_simple();
#endif

        Inst* tve = OpInst::create(OpInst::Ternary, cond, ife_new, the_new);

#ifdef EX_CC_LEVEL2
        tve = tve->get_simple();
#endif

        t_simplified_ve = tve;
  //			cout << "## simplification: " << *e << " -> " << *t_simplified_ve << endl;
			}
		}
#ifdef INTERPRET_EX_UF
    else if (exp->get_type() == Op)
    {
      OpInst* opExp = OpInst::as(exp);
      int version = opExp->get_simple_version();
      if (version != UF_NEVER) {
        bool allowed = false;
        int lo_new = lo;
        if (version == UF_SUFFIX_ANY)
          allowed = true;
        else if (version == UF_SUFFIX_ZER0) {
        	if (lo == 0)
        		allowed = true;
        	else if (hi != (opExp->get_size() - 1)) {
        		lo_new = 0;
        		allowed = true;
        	}
        }

        if (allowed) {
          e->m_simple = false;
          need_new = true;
//					cout << "## simplifying: " << *e << endl;

          // ({Pa (u-bit), A (v-bit), Sa (w-bit)} op {Pb (u-bit), B (v-bit), Sb (w-bit)})[v+w-1:w-1] = (A op B)
          const InstL* ch = exp->get_children();
          assert(ch);
          {
            InstL vel;
            for (InstL::const_iterator cit = ch->begin(); cit != ch->end(); ++cit)
            {
              Inst *tve = *cit;
              tve = tve->get_port();
#ifdef EX_CC_LEVEL1
              tve = tve->get_simple();
#endif
              int hi_new = hi;
              if (hi_new >= tve->get_size())
              	hi_new = tve->get_size() - 1;
              tve = ExInst::create(tve, hi_new, lo_new);

#ifdef EX_CC_LEVEL2
//              tve = tve->get_port();
              tve = tve->get_simple();
#endif
              vel.push_back(tve);
            }
            Inst* v_op;

            if (vel.size() != ch->size()) {
              cout << "e: " << *e << endl;
              cout << "vel: " << vel << endl;
            }
            assert (vel.size() == ch->size());
            v_op = OpInst::create(opExp->get_op(), vel, hi - lo_new + 1);

#ifdef EX_CC_LEVEL2
            v_op = v_op->get_simple();
#endif
            if ((version == UF_SUFFIX_ZER0) && (lo_new != lo)) {
              v_op = ExInst::create(v_op, hi, lo);

#ifdef EX_CC_LEVEL2
              v_op = v_op->get_simple();
#endif
            }

            if (v_op->get_size() != e->get_size()) {
              assert(v_op->get_size() > e->get_size());
              cout << "## simplification: " << *e << " -> " << *v_op << endl;
              assert(0);
//              v_op = ExInst::create(v_op, (e->get_size() - 1), 0);
            }

            t_simplified_ve = v_op;
//            cout << "## simplification: " << *e << " -> " << *v_op << endl;
//            assert(0);
          }
        }
      }
    }
#endif
	}
#endif

	if (e->get_size() != t_simplified_ve->get_size())
	{
		cout << "## simplification: " << *e << " -> " << *t_simplified_ve << endl;
		assert(0);
	}

	if (need_new)
		e->t_simple = t_simplified_ve;
	else
		e->t_simple = e;

	hm_ExInst.insert(make_pair(t_idx, e));

//	if (e != e->t_simple) {
//		cout << "excc: " << *e << " -> " << *(e->t_simple) << endl;
//	}

	if (wn_simplify_extract)
	{
//		cout << "Simp: " << *e_orig << " -> " << *t_simplified_ve << endl;
		return e->get_simple();
	}
	else
		return e;

}
ExInst* ExInst::create() {
	ExInst* e = new ExInst;
	m_exps_pool.push_back(e);
	e->set_hash1(2); // arbitrary (check that!)
	return e;
}

bool ExInst::check_consistency(ostream& out) {
	if (!Inst::check_consistency(out)) {
		return false;
	}
	Inst* son = *(m_exps.begin());
	assert(son != 0);
	if (!(son->check_consistency(out)))
		return false;

	if (get_lo() >= son->get_size() || get_hi() >= son->get_size()) {
		out << "out of bound extraction [" << get_hi() << ":" << get_lo() << "] for " << *son << endl;
		out << "of size: " << son->get_size() << endl;
		return false;
	}
	return true;
}

string ExInst::get_euf_func_name(){
	if(euf_func_name.empty()){
		ostringstream oss;
		oss << "Ex";
		oss << "_" << m_hi;
		oss << "_" << m_lo;
		oss << "_" << (m_exps.front())->get_size();
		euf_func_name = oss.str();
	}
	return euf_func_name;
}

// return "0" if it is not going to be abstracted (control operator)
string OpInst::get_euf_type_name(){
	string opstr;
	switch (m_op) {
		case Gr:
			opstr = "GT";
			break;
		case SGr:
			opstr = "SGT";
			break;
		case Le:
			opstr = "LT";
			break;
		case SLe:
			opstr = "SLT";
			break;
		case GrEq:
			opstr = "GE";
			break;
		case SGrEq:
			opstr = "SGE";
			break;
		case LeEq:
			opstr = "LE";
			break;
		case SLeEq:
			opstr = "SLE";
			break;
		case Concat:
			opstr = "Concat";
			break;
		case VShiftL:
			opstr = "VShiftL";
			break;
		case VShiftR:
			opstr = "VShiftR";
			break;
		case VAShiftL:
			opstr = "VAShiftL";
			break;
		case VAShiftR:
			opstr = "VAShiftR";
			break;
		case VRotateL:
			opstr = "VRotateL";
			break;
		case VRotateR:
			opstr = "VRotateR";
			break;
		case VEx:
			opstr = "VEx";
			break;
		case Minus:
			opstr = "Minus";
			break;
		case AddC:
			opstr = "AddC";
			break;
		case Add:
			opstr = "Add";
			break;
		case Sub:
			opstr = "Sub";
			break;
		case Mult:
			opstr = "Mult";
			break;
		case Div:
			opstr = "Div";
			break;
		case SDiv:
			opstr = "SDiv";
			break;
		case Rem:
			opstr = "Rem";
			break;
		case SRem:
			opstr = "SRem";
			break;
		case SMod:
			opstr = "SMod";
			break;
		case Sext:
			opstr = "Sext";
			break;
		case Zext:
			opstr = "Zext";
			break;
		case BitWiseAnd:
			opstr = "BitWiseAnd";
			break;
		case BitWiseOr:
			opstr = "BitWiseOr";
			break;
		case BitWiseNot:
			opstr = "BitWiseNot";
			break;
		case BitWiseXor:
			opstr = "BitWiseXor";
			break;
		case BitWiseXNor:
			opstr = "BitWiseXNor";
			break;
		case BitWiseNor:
			opstr = "BitWiseNor";
			break;
		case BitWiseNand:
			opstr = "BitWiseNand";
			break;
		case ReductionAnd:
			opstr = "ReductionAnd";
			break;
		case ReductionOr:
			opstr = "ReductionOr";
			break;
		case ReductionXor:
			opstr = "ReductionXor";
			break;
		case ReductionXNor:
			opstr = "ReductionXNor";
			break;
		case ReductionNand:
			opstr = "ReductionNand";
			break;
		case ReductionNor:
			opstr = "ReductionNor";
			break;
		case RotateL:
			opstr = "RotateL";
			break;
		case RotateR:
			opstr = "RotateR";
			break;
		case ShiftL:
			opstr = "ShiftL";
			break;
		case ShiftR:
			opstr = "ShiftR";
			break;
		case AShiftR:
			opstr = "AShiftR";
			break;
		case AShiftL:
			opstr = "AShiftL";
			break;
		case Extract:
			opstr = "Extract";
			break;
		case ArrayConst:
			opstr = "ArrayConst";
			break;
		case ArraySelect:
			opstr = "ArraySelect";
			break;
		case ArrayStore:
			opstr = "ArrayStore";
			break;
		case IntAdd:
			opstr = "IntAdd";
			break;
		case IntSub:
			opstr = "IntSub";
			break;
		case IntMult:
			opstr = "IntMult";
			break;
		case IntDiv:
			opstr = "IntDiv";
			break;
		case IntFloor:
			opstr = "IntFloor";
			break;
		case IntLe:
			opstr = "IntLT";
			break;
		case IntLeEq:
			opstr = "IntLeEq";
			break;
		case IntGr:
			opstr = "IntGT";
			break;
		case IntGrEq:
			opstr = "IntGrEq";
			break;
		case IntMod:
			opstr = "IntMod";
			break;
		case IntMinus:
			opstr = "IntMinus";
			break;
		case LogNot:
		case LogNand:
		case LogNor:
		case LogAnd:
		case LogXor:
		case LogXNor:
		case LogOr:
		case Eq:
		case NotEq:
		case Ternary:
		default:
			opstr = "0";
	}
	return opstr;
}

// return "0" if it is not going to be abstracted (control operator)
string OpInst::get_euf_func_name(){
	if(euf_func_name.empty()){
		string opstr;
		switch (m_op) {
			case Gr:
				opstr = "GT";
				break;
			case SGr:
				opstr = "SGT";
				break;
			case Le:
				opstr = "LT";
				break;
			case SLe:
				opstr = "SLT";
				break;
			case GrEq:
				opstr = "GE";
				break;
			case SGrEq:
				opstr = "SGE";
				break;
			case LeEq:
				opstr = "LE";
				break;
			case SLeEq:
				opstr = "SLE";
				break;
			case Concat:
				opstr = "Concat";
				break;
			case VShiftL:
				opstr = "VShiftL";
				break;
			case VShiftR:
				opstr = "VShiftR";
				break;
			case VAShiftL:
				opstr = "VAShiftL";
				break;
			case VAShiftR:
				opstr = "VAShiftR";
				break;
			case VRotateL:
				opstr = "VRotateL";
				break;
			case VRotateR:
				opstr = "VRotateR";
				break;
			case VEx:
				opstr = "VEx";
				break;
			case Minus:
				opstr = "Minus";
				break;
			case AddC:
				opstr = "AddC";
				break;
			case Add:
				opstr = "Add";
				break;
			case Sub:
				opstr = "Sub";
				break;
			case Mult:
				opstr = "Mult";
				break;
			case Div:
				opstr = "Div";
				break;
			case SDiv:
				opstr = "SDiv";
				break;
			case Rem:
				opstr = "Rem";
				break;
			case SRem:
				opstr = "SRem";
				break;
			case SMod:
				opstr = "SMod";
				break;
			case Sext:
				opstr = "Sext";
				break;
			case Zext:
				opstr = "Zext";
				break;
			case BitWiseAnd:
				opstr = "BitWiseAnd";
				break;
			case BitWiseOr:
				opstr = "BitWiseOr";
				break;
			case BitWiseNot:
				opstr = "BitWiseNot";
				break;
			case BitWiseXor:
				opstr = "BitWiseXor";
				break;
			case BitWiseXNor:
				opstr = "BitWiseXNor";
				break;
			case BitWiseNor:
				opstr = "BitWiseNor";
				break;
			case BitWiseNand:
				opstr = "BitWiseNand";
				break;
			case ReductionAnd:
				opstr = "ReductionAnd";
				break;
			case ReductionOr:
				opstr = "ReductionOr";
				break;
			case ReductionXor:
				opstr = "ReductionXor";
				break;
			case ReductionXNor:
				opstr = "ReductionXNor";
				break;
			case ReductionNand:
				opstr = "ReductionNand";
				break;
			case ReductionNor:
				opstr = "ReductionNor";
				break;
			case RotateL:
				opstr = "RotateL";
				break;
			case RotateR:
				opstr = "RotateR";
				break;
			case ShiftL:
				opstr = "ShiftL";
				break;
			case ShiftR:
				opstr = "ShiftR";
				break;
			case AShiftR:
				opstr = "AShiftR";
				break;
			case AShiftL:
				opstr = "AShiftL";
				break;
			case Extract:
			{
				return ExInst::as(this)->get_euf_func_name();
//				opstr = "Extract";
			}
				break;
			case ArrayConst:
				opstr = "ArrayConst";
				break;
			case ArraySelect:
				opstr = "ArraySelect";
				break;
			case ArrayStore:
				opstr = "ArrayStore";
				break;
			case IntAdd:
				opstr = "IntAdd";
				break;
			case IntSub:
				opstr = "IntSub";
				break;
			case IntMult:
				opstr = "IntMult";
				break;
			case IntDiv:
				opstr = "IntDiv";
				break;
			case IntFloor:
				opstr = "IntFloor";
				break;
			case IntLe:
				opstr = "IntLT";
				break;
			case IntLeEq:
				opstr = "IntLeEq";
				break;
			case IntGr:
				opstr = "IntGT";
				break;
			case IntGrEq:
				opstr = "IntGrEq";
				break;
			case IntMod:
				opstr = "IntMod";
				break;
			case IntMinus:
				opstr = "IntMinus";
				break;
			case Unknown:
				opstr = "Unknown";
				break;
			case Future:
				opstr = "Future";
				break;
			case LogNot:
			case LogNand:
			case LogNor:
			case LogAnd:
			case LogXor:
			case LogXNor:
			case LogOr:
			case Eq:
			case NotEq:
			case Ternary:
			{
				euf_func_name = "0";
				return euf_func_name;
			}
			default:
				assert(0);
		}

		ostringstream oss;
		oss << opstr;
		oss << "_";
		if (get_sort_type() == bvtype)
			oss << get_size();
		else
			oss << get_sort().sort2str();
		if (m_op == Concat)
		{
			Inst* oldCh = NULL;
			int count = 1;
			for (InstL::const_reverse_iterator it = m_exps.rbegin(); it != m_exps.rend(); ++it) {
				if (oldCh == (*it))
				{
					count++;
					continue;
				}
				if (count > 1)
				{
					oss << "_x" << count;
				}
				count = 1;
				oss << "_";
				if ((*it)->get_sort_type() == bvtype)
					oss << (*it)->get_size();
				else
					oss << (*it)->get_sort().sort2str();
				oldCh = (*it);
			}
			if (count > 1)
			{
				oss << "_x" << count;
			}
		}
		else
		{
			for (InstL::const_iterator it = m_exps.begin(); it != m_exps.end(); ++it) {
				oss << "_";
				if ((*it)->get_sort_type() == bvtype)
					oss << (*it)->get_size();
				else
					oss << (*it)->get_sort().sort2str();
			}
		}
		euf_func_name = oss.str();
	}
	return euf_func_name;
}

#ifdef INTERPRET_EX_UF
int OpInst::get_simple_version() {
  int version = UF_NEVER;
  switch (m_op) {
    case BitWiseAnd:
    case BitWiseOr:
    case BitWiseNot:
    case BitWiseXor:
    case BitWiseXNor:
    case BitWiseNor:
    case BitWiseNand:
      version = UF_SUFFIX_ANY;
      break;
    case Add:
    case Sub:
      version = UF_SUFFIX_ZER0;
      break;
    case Mult:
      if (m_size > 2)
        version = UF_SUFFIX_ZER0;
      else
      	version = UF_NEVER;
      break;
    case Zext:
    case Sext:
      version = UF_SUFFIX_ZER0;
      break;
    case AddC:
    case Div:
    case SDiv:
    case Rem:
    case SRem:
    case SMod:
    case Minus:
    case VShiftL:
    case VShiftR:
    case VAShiftL:
    case VAShiftR:
    case VRotateL:
    case VRotateR:
    case VEx:
    case RotateL:
    case RotateR:
    case Unknown:
    case Future:
      AVR_LOG(15, 0, "\t(warning: found unexpected UF interacting with Ex/Cc for " << *this << endl);
      break;
    case ShiftL:
    case ShiftR:
    case AShiftR:
    case AShiftL:
      version = UF_NEVER;
      break;
    case Extract:
    case Concat:
    case Eq:
    case NotEq:
    case Ternary:
      version = UF_NEVER;
      break;
    case Gr:
    case SGr:
    case Le:
    case SLe:
    case GrEq:
    case SGrEq:
    case LeEq:
    case SLeEq:
    case ReductionAnd:
    case ReductionOr:
    case ReductionXor:
    case ReductionXNor:
    case ReductionNand:
    case ReductionNor:
    case LogNot:
    case LogNand:
    case LogNor:
    case LogAnd:
    case LogXor:
    case LogXNor:
		case ArrayConst:
		case ArraySelect:
		case ArrayStore:
		case IntAdd:
		case IntSub:
		case IntMult:
		case IntDiv:
		case IntFloor:
		case IntLe:
		case IntLeEq:
		case IntGr:
		case IntGrEq:
		case IntMod:
		case IntMinus:
    case LogOr:
      version = UF_NEVER;
      break;
    default:
      assert(0);
  }
	return version;
}

bool OpInst::is_unordered_uf() {
  bool result = false;
  switch (m_op) {
    case BitWiseAnd:
    case BitWiseOr:
    case BitWiseXor:
    case BitWiseXNor:
    case BitWiseNor:
    case BitWiseNand:
    case Add:
    case Mult:
    	result = true;
      break;
//    case Sub:
//    case AddC:
//    case Div:
//    case Mod:
//    case Minus:
//    case VShiftL:
//    case VShiftR:
//    case VAShiftL:
//    case VAShiftR:
//    case VRotateL:
//    case VRotateR:
//    case VEx:
//    case RotateL:
//    case RotateR:
//    case Unknown:
//    case Future:
//    case ShiftL:
//    case AShiftL:
//    case ShiftR:
//    case AShiftR:
//    case Extract:
//    case Concat:
//    case Eq:
//    case NotEq:
//    case Ternary:
//    case Gr:
//    case Le:
//    case GrEq:
//    case LeEq:
//    case ReductionAnd:
//    case ReductionOr:
//    case ReductionXor:
//    case ReductionXNor:
//    case ReductionNand:
//    case ReductionNor:
//    case LogNot:
//    case LogNand:
//    case LogNor:
//    case LogAnd:
//    case LogXor:
//    case LogXNor:
//    case LogOr:
//      break;
    default:
      ;
  }
	return result;
}
#endif

Inst* OpInst::create(OpType op, Inst* exp1, Inst* exp2, Inst* exp3, int o_size, bool to_simplify, Inst* wire, SORT sort) {
	if (op == OpInst::LogNot) {
		OpInst* opt = OpInst::as(exp1);
		if ((opt && opt->get_op() == OpInst::LogNot)) {
			return (opt->get_children())->front();
		}
	}

	InstL l;
	l.push_back(exp1);
	if (exp2)
		l.push_back(exp2);
	if (exp3)
		l.push_back(exp3);
	return create(op, l, o_size, to_simplify, wire, sort);

}
Inst* OpInst::create(OpInst::OpType op, InstL exps, int o_size, bool to_simplify, Inst* wire, SORT sort) {

	OpHash t_idx;
	Inst* t_simplified_ve;

	o_size = (o_size == 0) ? find_size(op, exps) : o_size;

//	if((op == ShiftL) || (op == ShiftR) || (op == AShiftL) || (op == AShiftR))
	if((op == AShiftL))
	{
		InstL::iterator it = exps.begin();
		++it;
		if((*it)->get_type() != Num)
		{
			cout << "we DONOT support the operator, shift by variable!!!" << endl;
			cout << *(exps.front()) << "  shift " << *(*it) << endl;
			assert(0);
		}
	}

	if (op == BitWiseNand || op == BitWiseNor) {
		string temp = op == BitWiseNand ? "BitWiseNand" : "BitWiseNor";
		cout << temp << endl << exps << endl;
		assert(0);
	}
	
	if (Config::g_uf_no_bitwise)
	if (op == BitWiseNot || op == BitWiseAnd || op == BitWiseOr) {
		InstL new_ch;

		if (op == BitWiseNot) {
			assert(exps.size() == 1);
			Inst* arg = exps.front()->get_port();
#ifdef EX_CC_LEVEL1
			arg = arg->get_simple();
#endif
			for (int i = 0; i < arg->get_size(); i++) {
				Inst* tve = ExInst::create(arg, i, i);
				tve = tve->get_port();
#ifdef EX_CC_LEVEL2
				tve = tve->get_simple();
#endif
				Inst* tveNew = OpInst::create(LogNot, tve);
				new_ch.push_back(tveNew);
			}
		}
		else if (op == BitWiseAnd || op == BitWiseOr) {
			assert(exps.size() == 2);
			Inst* arg1 = exps.front()->get_port();
			Inst* arg2 = exps.back()->get_port();
#ifdef EX_CC_LEVEL1
			arg1 = arg1->get_simple();
			arg2 = arg2->get_simple();
#endif
			for (int i = 0; i < arg1->get_size(); i++) {
				Inst* tve1 = ExInst::create(arg1, i, i);
				Inst* tve2 = ExInst::create(arg2, i, i);
				tve1 = tve1->get_port();
				tve2 = tve2->get_port();
#ifdef EX_CC_LEVEL2
				tve1 = tve1->get_simple();
				tve2 = tve2->get_simple();
#endif
				Inst* tveNew = OpInst::create((op == BitWiseAnd) ? LogAnd : LogOr, tve1, tve2);
				new_ch.push_back(tveNew);
			}
		}
		exps.swap(new_ch);
		op = Concat;
	}

	if (Config::g_uf_no_sext)
	if (op == Sext) {
		assert(exps.size() == 2);
		Inst* arg1 = exps.front()->get_port();
#ifdef EX_CC_LEVEL1
		arg1 = arg1->get_simple();
#endif

		Inst* arg2 = exps.back();
		int sz = arg2->get_size();
		InstL new_ch;
		new_ch.push_back(arg1);
		int arg1sz = arg1->get_size();
		Inst* signArg = ExInst::create(arg1, (arg1sz - 1), (arg1sz - 1));
		signArg = signArg->get_port();
#ifdef EX_CC_LEVEL2
		signArg = signArg->get_simple();
#endif
		for (int i = 0; i < (sz - arg1sz); i++) {
			new_ch.push_back(signArg);
		}
		exps.swap(new_ch);
		op = Concat;
	}

	if (Config::g_uf_no_shift)
	if (op == ShiftL || op == ShiftR || op == AShiftL || op == AShiftR) {
		assert(exps.size() == 2);

		Inst* arg1 = exps.front()->get_port();
#ifdef EX_CC_LEVEL2
		arg1 = arg1->get_simple();
#endif
		int arg1sz = arg1->get_size();

		Inst* arg2 = exps.back()->get_port();
#ifdef EX_CC_LEVEL2
		arg2 = arg2->get_simple();
#endif
		NumInst* numArg = NumInst::as(arg2);
		int amount = -1;
		if (numArg) {
			amount = numArg->get_num();
			if (amount > arg1sz)
				amount  = arg1sz;
		}

		if (amount != -1) {
			assert(amount <= arg1sz);

			InstL new_ch;

//			cout << "op: " << op << endl;
//			cout << "exps: " << exps << endl;

			if (amount < arg1sz) {
				Inst* shiftArg = ExInst::create(arg1, (arg1sz - 1), amount);
				shiftArg = shiftArg->get_port();
#ifdef EX_CC_LEVEL2
				shiftArg = shiftArg->get_simple();
#endif
				new_ch.push_back(shiftArg);
			}

			if (op == ShiftL || op == AShiftL)
				new_ch.push_front(NumInst::create(0, amount, SORT(amount)));
			else if (op == ShiftR)
				new_ch.push_back(NumInst::create(0, amount, SORT(amount)));
			else {
				assert (op == AShiftR);

				Inst* signArg = ExInst::create(arg1, (arg1sz - 1), (arg1sz - 1));
				signArg = signArg->get_port();
#ifdef EX_CC_LEVEL2
				signArg = signArg->get_simple();
#endif
				for (int i = 0; i < amount; i++) {
					new_ch.push_back(signArg);
				}
			}

//			cout << "op: " << op << endl;
//			cout << "exps: " << exps << endl;
//			cout << "new_ch: " << new_ch << endl;

			exps.swap(new_ch);
			op = Concat;
		}
	}

	// 	if(op == BitWiseXor || op == LogXor){
	// 		string temp = op == BitWiseXor ? "BitWiseXor" : "LogXor";
	// 		cout << temp << endl << exps << endl;
	// 		assert(0);
	// 	}

	if ((op == LogAnd || op == LogOr) && (exps.size() == 1)) {
		return exps.front();
	}

	if (op == Eq || op == NotEq) {
		assert(exps.front()->get_size() == exps.back()->get_size());
		assert(exps.front()->get_sort() == exps.back()->get_sort());
	}

	if (op == LogNot) {
		OpInst* oparg = OpInst::as(exps.front()->get_port());
		if (oparg) {
			if (oparg->get_op() == LogNot) {
				return oparg->get_children()->front();
			}
		}
	}

	if (op == Zext || op == Sext) {
		assert(exps.size() == 2);
		Inst* arg1 = exps.front();
		Inst* arg2 = exps.back();
		int sz = arg2->get_size();

		if (arg1->get_size() >= sz)
			return ExInst::create(arg1, (sz - 1), 0);
	}

	// TODO	there are two issues, "clk && future(clk)", "a$next = b" <- In thses cases, the order of children is important
	// 	if(exps.size() > 1){
	// 		if(op != Unknown && op != Extract && op != Concat && op != Sub && op != Div && op != Mod && op != Gr
	// 			&& op != Le && op != GrEq && op != LeEq && op != ShiftL && op != ShiftR
	// 			&& op != Future && op != Ternary && op != Eq && op != NotEq && op != LogAnd){
	// 			exps.sort();
	// 		}
	// 	}
	// TODO		a == b is equal to b == a, a && b is equal to b && a, and so on.
	// TODO		a ? b : c is equal to ~a ? c : b
	if (op == Ternary) {
		InstL::iterator it = exps.begin();
		Inst* cond = (*it++);
    Inst* the  = (*it++);
    Inst* els  = (*it++);

		t_idx.a = cond->get_id();
		t_idx.b = the->get_id();
		t_idx.c = els->get_id();
		t_idx.d = o_size;

		OpHashM::iterator it2 = hm_ITEInst.find(t_idx);
		if (it2 != hm_ITEInst.end()) {
      return it2->second;
		}
		else if (t_idx.b == t_idx.c) {
		  assert(the == els);
		  return the;
		}
	} else if (exps.size() < 3) {
		InstL::iterator it = exps.begin();
		t_idx.d = o_size;
		t_idx.b = (unsigned) op;
		if (it != exps.end()) {
			t_idx.a = (*it++)->get_id();
		} else {
			t_idx.a = 0;
		}
		if (it != exps.end()) {
			t_idx.c = (*it)->get_id();
		} else {
			t_idx.c = 0;
		}

		OpHashM::iterator it2 = hm_OpInst.find(t_idx);
		if (it2 != hm_OpInst.end())
		{
			if (op == Concat && wn_simplify_concat)
			{
				OpInst* tmp = OpInst::as(it2->second);
//				cout << "Simp: " << *tmp << " -> " << *tmp->t_simple << endl;
				return tmp->t_simple;
			}
			else
				return it2->second;
		}

		if((op == Eq) || (op == NotEq)){
			OpHash t_idx_rev;
			t_idx_rev.d = o_size;
			t_idx_rev.b = (unsigned) op;
			t_idx_rev.a = t_idx.c;
			t_idx_rev.c = t_idx.a;

			OpHashM::iterator it_rev = hm_OpInst.find(t_idx_rev);
			if (it_rev != hm_OpInst.end()) {
				return it_rev->second;
			}
		}
	} else {
		t_idx.d = o_size;
		t_idx.c = (exps.size() << 8) + ((unsigned) op);
		InstL::iterator it = exps.begin();
		t_idx.b = (*it)->get_id();
		t_idx.a = (*it++)->get_id();
		for (; it != exps.end(); it++) {
			unsigned tid = (*it)->get_id();
			t_idx.b += tid;
			t_idx.a = ((unsigned) ((t_idx.a + 1) * tid));
			t_idx.a <<= 1;
		}

		pair < OpHashMM::iterator, OpHashMM::iterator > ret;
		ret = hm_ETCInst.equal_range(t_idx);
		if (ret.first != ret.second) {
			OpHashMM::iterator it2 = ret.first;
			for (; it2 != ret.second; it2++) {
				bool actually_equal = true;
				Inst *tve = it2->second;
				const InstL* ch = tve->get_children();
				if(!ch || (exps.size() != ch->size())){
					//!ch means that a simplification lead to a constant
					// However, this is no harm (unique node for the same instance) to compute the simplification routine again
					// because, it then calls NumInst::create() at the end, and the hash map in NumInst will return
					// the same node
					actually_equal = false;
				} else {
					it = exps.begin();
					if (ch) {
						for (InstL::const_iterator cit = ch->begin(); cit != ch->end(); ++cit) {
							if ((*it++)->get_id() != (*cit)->get_id()) {
								// 								cout << "a: " << *(*it) << endl;
								// 								cout << "b: " << *(*cit) << endl << endl;
								actually_equal = false;
							}
						}
					}
				}
				if (actually_equal == true)
				{
					if (op == Concat && wn_simplify_concat)
					{
						OpInst* tmp = OpInst::as(it2->second);
//						cout << "Simp: " << *tmp << " -> " << *tmp->t_simple << endl;
						return tmp->t_simple;
					}
					else
						return it2->second;
				}
				else {
					// 				cout << op2str(op) << endl;
					// 				for (InstL::iterator it = exps.begin(); it != exps.end(); it++){
					// 					cout << *(*it) << endl;
					// 				}
					// 					cout << "##############################" << endl;
					// 					cout << "###		This is the case, OphashMM" << endl;
					// 					cout << "##############################" << endl;
				}
			}
		}
	}

	assert(op != Unknown);
	assert(!exps.empty());
	for (InstL::iterator it = exps.begin(), end_it = exps.end(); it != end_it; ++it)
		if (!(*it)) {
			assert(0);
		}
	OpInst* e = new OpInst(op, exps, o_size, wire, sort);
	m_exps_pool.push_back(e);

	unsigned hash = 0;
	for (InstL::iterator it = exps.begin(), end_it = exps.end(); it != end_it; ++it)
		hash += (*it)->get_hash1();
	e->set_hash1(hash);

	e->t_simple = e;
  e->m_simple = true;

	if (wn_1bit_dp_to_control) {
		if ((exps.front())->get_size() == 1) {
			switch (op) {
				
#if 1
				case BitWiseAnd:
					op = LogAnd;
					break;
				case BitWiseOr:
					op = LogOr;
					break;
				case BitWiseNot:
					op = LogNot;
					break;
// 				case BitWiseXor:
// 					op = LogXor;
// 					break;
// 				case BitWiseXNor:
// 					op = LogXNor;
// 					break;
				case BitWiseXor:
					op = NotEq;
					break;
				case BitWiseXNor:
					op = Eq;
					break;
				case LogXor:
					op = NotEq;
					break;
				case LogXNor:
					op = Eq;
					break;
				default: {
				} // nothing
#else
				case BitWiseAnd:
					op = LogAnd;
					break;
				case BitWiseOr:
					op = LogOr;
					break;
				case BitWiseNot:
					op = LogNot;
					break;
// 				case BitWiseXor:
// 					op = LogXor;
// 					break;
// 				case BitWiseXNor:
// 					op = LogXNor;
// 					break;
				case BitWiseXor:
					op = LogXor;
					break;
				case BitWiseXNor:
					op = LogXNor;
					break;
				case LogXor:
					op = LogXor;
					break;
				case LogXNor:
					op = LogXNor;
					break;
				case NotEq:
					op = LogXor;
					break;
				case Eq:
					op = LogXNor;
					break;
				default: {
				} // nothing
#endif
			}
		}
	}

	// !(a == b) => (a != b)
	if (op == LogNot) {
		InstL::const_iterator it = exps.begin();
		Inst *ve_ch = *it;
		if((ve_ch->get_type() == Op) && ((OpInst::as(ve_ch))->get_op() == OpInst::Eq)){
			op = NotEq;
			exps.clear();
			exps.push_back(ve_ch->get_children()->front());
			exps.push_back(ve_ch->get_children()->back());
		}else if((ve_ch->get_type() == Op) && ((OpInst::as(ve_ch))->get_op() == OpInst::NotEq)){
			op = Eq;
			exps.clear();
			exps.push_back(ve_ch->get_children()->front());
			exps.push_back(ve_ch->get_children()->back());
		}
	}
	
	if((op == Eq) || (op == NotEq)){
		exps.sort(CompareInstByChildInfo);

		InstL::const_iterator it = exps.begin();
		Inst *ve_lhs = *it++;
		Inst *ve_rhs = *it;
		if(
			   ((ve_lhs->get_type() != Sig) && (ve_rhs->get_type() == Sig))
			|| ((ve_lhs->get_type() == Num) && (ve_rhs->get_type() != Num))
		)
		{
			exps.clear();
			exps.push_back(ve_rhs);
			exps.push_back(ve_lhs);
		}
	}
	
	if (op != e->get_op()) {
		t_simplified_ve = finalize_simplify(e, create(op, exps), InstL());
		if (exps.size() < 3) {
			hm_OpInst.insert(make_pair(t_idx, t_simplified_ve));
		} else {
			hm_ETCInst.insert(make_pair(t_idx, t_simplified_ve));
		}
		return t_simplified_ve;
	}

	if (op == Unknown)
		assert(0);
	if (op == Extract)
		assert(0);

#ifdef USE_INTERPRETED_ADD_SUB
	if ((op == Add || op == Sub || op == Mult) && wn_simplify_const_num) {
		assert(exps.size()==2);
		InstL::const_iterator it = exps.begin(), it2 = exps.begin();
		it2++;
		if ((*it)->get_type() == Num && (*it2)->get_type() == Num) {
			NumInst* num1 = NumInst::as(*it);
			NumInst* num2 = NumInst::as(*it2);
			mpz_class r = (op == OpInst::Add) ? *(num1->get_mpz()) + *(num2->get_mpz()) : 
						(op == OpInst::Sub) ? *(num1->get_mpz()) - *(num2->get_mpz()) : 
						*(num1->get_mpz()) * *(num2->get_mpz());

			t_simplified_ve = finalize_simplify(e, NumInst::create(r, num1->get_size()), InstL());
			hm_OpInst.insert(make_pair(t_idx, t_simplified_ve));
			return t_simplified_ve;
		}
	}
#endif
/*
	if (op == Concat && exps.size() == 1) {
		t_simplified_ve = finalize_simplify(e, *(exps.begin()), InstL());
		hm_OpInst.insert(make_pair(t_idx, t_simplified_ve));
		return t_simplified_ve;
	}
*/
	if (op == Ternary) {
		InstL::iterator it = exps.begin();
		Inst* ife = *(it++);
		Inst* thene = *(it++);
		Inst* elsee = *(it++);

		if (wn_simplify_ite) {
			NumInst* ifnum = NumInst::as(ife);
			if (ifnum) {
				InstL masked;
				masked.push_back(ifnum);
				if (*(ifnum->get_mpz()) == 0) {
					t_simplified_ve = finalize_simplify(e, elsee, masked);
					hm_ITEInst.insert(make_pair(t_idx, t_simplified_ve));
					return t_simplified_ve;
				} else if (*(ifnum->get_mpz()) == 1) {
					t_simplified_ve = finalize_simplify(e, thene, masked);
					hm_ITEInst.insert(make_pair(t_idx, t_simplified_ve));
					return t_simplified_ve;
				} else
					assert(0);
			}
		}
		if (wn_simplify_repetition) {
			if (thene->is_similar(elsee)) {
				InstL masked;
				masked.push_back(elsee);
				t_simplified_ve = finalize_simplify(e, thene, masked);
				hm_ITEInst.insert(make_pair(t_idx, t_simplified_ve));
				return t_simplified_ve;
			}
		}
	}

	if (op == LogAnd || op == LogOr || op == LogNot) {

		InstL new_ch;
		if (wn_simplify_const_pred) {

			// try the easy thing first!
			// check if the node can now be replaced by a constant!
			int dominating_const = -1;
			for (InstL::iterator it = exps.begin(), end_it = exps.end(); it != end_it; ++it) {
				NumInst* num = NumInst::as(*it);
				if (num != 0) {
					bool is_true = (*(num->get_mpz()) == 1);
					if ((op == LogNot) || ((op == LogAnd) && !is_true) || ((op == LogOr) && is_true)) {
						dominating_const = (op == LogNot) ? (1 - is_true) : is_true;
						break;
					}
				}
			}
			if (dominating_const >= 0) {
				t_simplified_ve = finalize_simplify(e, NumInst::create(dominating_const, 1, SORT()), exps);
				if (exps.size() < 3) {
					hm_OpInst.insert(make_pair(t_idx, t_simplified_ve));
				} else {
					hm_ETCInst.insert(make_pair(t_idx, t_simplified_ve));
				}
				return t_simplified_ve;
			}

			// if not... remove all unnecessary nodes... i.e. 1 & 1 & x becomes x !!
			if (op != LogNot) {
				for (InstL::iterator it = exps.begin(), end_it = exps.end(); it != end_it; ++it) {
					NumInst* num = NumInst::as(*it);
					if (num != 0) {
						bool is_true = (*(num->get_mpz()) == 1);
						if ((op == LogAnd) && is_true)
							continue;
						if ((op == LogOr) && !is_true)
							continue;
					}
					new_ch.push_back(*it);
				}
				if (new_ch.empty()) {
					t_simplified_ve = finalize_simplify(e, *(exps.begin()), InstL());
					if (exps.size() < 3) {
						hm_OpInst.insert(make_pair(t_idx, t_simplified_ve));
					} else {
						hm_ETCInst.insert(make_pair(t_idx, t_simplified_ve));
					}
					return t_simplified_ve;
				}
			}
		}

		if (wn_simplify_repetition) {
			if (op != LogNot) {
				assert(!new_ch.empty());
				// check if the node has something like: x & x ...
				// this is implemented in a dumb way!
				// whatever!
				bool similar = true;
				for (InstL::iterator it = new_ch.begin(), end_it = new_ch.end(); it != end_it; ++it) {
					bool s = (*it) == *(new_ch.begin());
					if (!s) {
						similar = false;
						break;
					}
				}
				if (similar) {
					InstL masked = exps;
					masked.pop_front();
					t_simplified_ve = finalize_simplify(e, *(new_ch.begin()), masked);
					if (exps.size() < 3) {
						hm_OpInst.insert(make_pair(t_idx, t_simplified_ve));
					} else {
						hm_ETCInst.insert(make_pair(t_idx, t_simplified_ve));
					}
					return t_simplified_ve;
				}
			}
		}
	}

	//TODO generalize these routines
	if ((op == LogAnd) && wn_simplify_const_pred && (exps.size() == 2)) {
		InstL::const_iterator it = exps.begin();
		Inst *ve_lhs = *it++;
		Inst *ve_rhs = *it;
		NumInst *nve = NumInst::as(ve_rhs);
		if(nve){
			if((*(nve->get_mpz()) == 1)){
				t_simplified_ve = finalize_simplify(e, ve_lhs, InstL());
			}else{
				t_simplified_ve = finalize_simplify(e, NumInst::create(0, 1, SORT()), InstL());
			}
			if (exps.size() < 3) {
				hm_OpInst.insert(make_pair(t_idx, t_simplified_ve));
			} else {
				hm_ETCInst.insert(make_pair(t_idx, t_simplified_ve));
			}
			//cout << exps << ", simplified: " << *t_simplified_ve << endl;
			return t_simplified_ve;
		}else{
			nve = NumInst::as(ve_lhs);
			if(nve){
				if((*(nve->get_mpz()) == 1)){
					t_simplified_ve = finalize_simplify(e, ve_rhs, InstL());
				}else{
					t_simplified_ve = finalize_simplify(e, NumInst::create(0, 1, SORT()), InstL());
				}
				if (exps.size() < 3) {
					hm_OpInst.insert(make_pair(t_idx, t_simplified_ve));
				} else {
					hm_ETCInst.insert(make_pair(t_idx, t_simplified_ve));
				}
				//cout << exps << ", simplified: " << *t_simplified_ve << endl;
				return t_simplified_ve;
			}
		}
	}
	if ((op == LogOr) && wn_simplify_const_pred && (exps.size() == 2)) {
		InstL::const_iterator it = exps.begin();
		Inst *ve_lhs = *it++;
		Inst *ve_rhs = *it;
		NumInst *nve = NumInst::as(ve_rhs);
		if(nve){
			if((*(nve->get_mpz()) == 0)){
				t_simplified_ve = finalize_simplify(e, ve_lhs, InstL());
			}else{
				t_simplified_ve = finalize_simplify(e, NumInst::create(1, 1, SORT()), InstL());
			}
			if (exps.size() < 3) {
				hm_OpInst.insert(make_pair(t_idx, t_simplified_ve));
			} else {
				hm_ETCInst.insert(make_pair(t_idx, t_simplified_ve));
			}
			//cout << exps << ", simplified: " << *t_simplified_ve << endl;
			return t_simplified_ve;
		}else{
			nve = NumInst::as(ve_lhs);
			if(nve){
				if((*(nve->get_mpz()) == 0)){
					t_simplified_ve = finalize_simplify(e, ve_rhs, InstL());
				}else{
					t_simplified_ve = finalize_simplify(e, NumInst::create(1, 1, SORT()), InstL());
				}
				if (exps.size() < 3) {
					hm_OpInst.insert(make_pair(t_idx, t_simplified_ve));
				} else {
					hm_ETCInst.insert(make_pair(t_idx, t_simplified_ve));
				}
				//cout << exps << ", simplified: " << *t_simplified_ve << endl;
				return t_simplified_ve;
			}
		}
	}
	if ((op == LogNot) && wn_simplify_const_pred) {
		InstL::const_iterator it = exps.begin();
		Inst *ve_ch = *it;
		NumInst *nve = NumInst::as(ve_ch);
		if(nve){
			if((*(nve->get_mpz()) == 0)){
				t_simplified_ve = finalize_simplify(e, NumInst::create(1, 1, SORT()), InstL());
			}else{
				t_simplified_ve = finalize_simplify(e, NumInst::create(0, 1, SORT()), InstL());
			}
			if (exps.size() < 3) {
				hm_OpInst.insert(make_pair(t_idx, t_simplified_ve));
			} else {
				hm_ETCInst.insert(make_pair(t_idx, t_simplified_ve));
			}
			//cout << exps << ", simplified: " << *t_simplified_ve << endl;
			return t_simplified_ve;
		}
	}
	
	if ((op == Eq) && wn_simplify_const_pred && ((exps.front())->get_size() == 1)) {
		InstL::const_iterator it = exps.begin();
		Inst *ve_lhs = *it++;
		Inst *ve_rhs = *it;
		NumInst *nve = NumInst::as(ve_rhs);
		if(nve){
			if((*(nve->get_mpz()) == 1)){
				t_simplified_ve = finalize_simplify(e, ve_lhs, InstL());
			}else{
				t_simplified_ve = finalize_simplify(e, create(LogNot, ve_lhs), InstL());
			}
			if (exps.size() < 3) {
				hm_OpInst.insert(make_pair(t_idx, t_simplified_ve));
			} else {
				hm_ETCInst.insert(make_pair(t_idx, t_simplified_ve));
			}
			//cout << exps << ", simplified: " << *t_simplified_ve << endl;
			return t_simplified_ve;
		}else{
			nve = NumInst::as(ve_lhs);
			if(nve){
				if((*(nve->get_mpz()) == 1)){
					t_simplified_ve = finalize_simplify(e, ve_rhs, InstL());
				}else{
					t_simplified_ve = finalize_simplify(e, create(LogNot, ve_rhs), InstL());
				}
				if (exps.size() < 3) {
					hm_OpInst.insert(make_pair(t_idx, t_simplified_ve));
				} else {
					hm_ETCInst.insert(make_pair(t_idx, t_simplified_ve));
				}
				//cout << exps << ", simplified: " << *t_simplified_ve << endl;
				return t_simplified_ve;
			}
		}
	}
	
	if ((op == NotEq) && wn_simplify_const_pred && ((exps.front())->get_size() == 1)) {
		InstL::const_iterator it = exps.begin();
		Inst *ve_lhs = *it++;
		Inst *ve_rhs = *it;
		NumInst *nve = NumInst::as(ve_rhs);
		if(nve){
			if((*(nve->get_mpz()) == 0)){
				t_simplified_ve = finalize_simplify(e, ve_lhs, InstL());
			}else{
				t_simplified_ve = finalize_simplify(e, create(LogNot, ve_lhs), InstL());
			}
			if (exps.size() < 3) {
				hm_OpInst.insert(make_pair(t_idx, t_simplified_ve));
			} else {
				hm_ETCInst.insert(make_pair(t_idx, t_simplified_ve));
			}
			//cout << exps << ", simplified: " << *t_simplified_ve << endl;
			return t_simplified_ve;
		}else{
			nve = NumInst::as(ve_lhs);
			if(nve){
				if((*(nve->get_mpz()) == 0)){
					t_simplified_ve = finalize_simplify(e, ve_rhs, InstL());
				}else{
					t_simplified_ve = finalize_simplify(e, create(LogNot, ve_rhs), InstL());
				}
				if (exps.size() < 3) {
					hm_OpInst.insert(make_pair(t_idx, t_simplified_ve));
				} else {
					hm_ETCInst.insert(make_pair(t_idx, t_simplified_ve));
				}
				//cout << exps << ", simplified: " << *t_simplified_ve << endl;
				return t_simplified_ve;
			}
		}
	}
	
	if (op == Eq && wn_simplify_eq) {
		assert(exps.size() == 2);
		InstL::const_iterator it = exps.begin(), it2 = exps.begin();
		it2++;
		if ((*it)->is_similar(*it2)) {
			t_simplified_ve = finalize_simplify(e, NumInst::create(1, 1, SORT()), InstL());
			hm_OpInst.insert(make_pair(t_idx, t_simplified_ve));
			return t_simplified_ve;
		}
		if ((*it)->get_type() == Num && (*it2)->get_type() == Num) {
			NumInst* num1 = NumInst::as(*it);
			NumInst* num2 = NumInst::as(*it2);
			t_simplified_ve = finalize_simplify(e, NumInst::create(*(num1->get_mpz()) == *(num2->get_mpz()), 1, SORT()), InstL());
			hm_OpInst.insert(make_pair(t_idx, t_simplified_ve));
			return t_simplified_ve;
		}
		if (wn_simplify_const_num) {
			Inst* sig1 = 0;
			Inst* sig2 = 0;
			mpz_class c1 = 0;
			mpz_class c2 = 0;
			if ((*it)->get_type() == Op) {
				OpInst *op = OpInst::as(*it);
				assert(op);
#ifdef USE_INTERPRETED_ADD_SUB
				if (op->get_op() == OpInst::Add || op->get_op() == OpInst::Sub) {
					const InstL* ll = op->get_children();
					InstL::const_iterator cit = ll->begin(), cit2 = ll->begin();
					cit2++;
					if ((*cit2)->get_type() == Num) {
						sig1 = *cit;
						mpz_class c = *(NumInst::as(*cit2)->get_mpz());
						c1 = (op->get_op() == OpInst::Add) ? c : -c;
					}
				}
#endif
			}
			if (!sig1) {
				sig1 = *it;
			}
			if ((*it2)->get_type() == Op) {
				OpInst *op = OpInst::as(*it2);
				assert(op);
#ifdef USE_INTERPRETED_ADD_SUB
				if (op->get_op() == OpInst::Add || op->get_op() == OpInst::Sub) {
					const InstL* ll = op->get_children();
					InstL::const_iterator cit = ll->begin(), cit2 = ll->begin();
					cit2++;
					if ((*cit2)->get_type() == Num) {
						sig2 = *cit;
						mpz_class c = *(NumInst::as(*cit2)->get_mpz());
						c2 = (op->get_op() == OpInst::Add) ? c : -c;
					}
				}
#endif
			}
			if (!sig2) {
				sig2 = *it2;
			}
			assert(sig1);
			assert(sig2);
			if (sig1->is_similar(sig2)) {
				//	cout<<*sig1<<" is similar to "<<*sig2<<endl;
				//	cout<<"in node: "<<*r<<endl;
				t_simplified_ve = finalize_simplify(e, NumInst::create(c1 == c2, 1, SORT()), InstL());
				hm_OpInst.insert(make_pair(t_idx, t_simplified_ve));
				return t_simplified_ve;
			}
		}
	}

	if (op == Eq || op == NotEq) {
    t_simplified_ve = e;
    bool need_new = false;

#ifdef INTERPRET_EX_CC
	  bool eq = (op == Eq);

    /// Iterate over children
    InstL::iterator it = exps.begin();
    Inst* lhs = *it;
    it++;
    Inst* rhs = *it;
    assert(lhs && rhs);

    lhs = lhs->get_port();
    rhs = rhs->get_port();

    OpInst* opL = OpInst::as(lhs);
    OpInst* opR = OpInst::as(rhs);
    if (opL && opR) {
      string opNameL = opL->get_euf_func_name();
      string opNameR = opR->get_euf_func_name();
      if (opL->get_op() == Concat && opR->get_op() == Concat && opNameL == opNameR) {
        t_simplified_ve = compare_and_simplify(opL, opR, eq);
//        cout << "## simplification: " << *e << " -> " << *t_simplified_ve << endl;
        need_new = true;
      }
    }

    if (!need_new) {
//#ifdef EX_CC_LEVEL1
//      lhs = lhs->get_simple();
//      rhs = rhs->get_simple();
//#endif

      if (lhs->get_type() != Op)
      	swap(lhs, rhs);

      if (lhs->get_type() == Op) {
      	OpInst* opL = OpInst::as(lhs);
      	if (opL->get_op() == OpInst::Concat) {

      		if (rhs->get_type() == Op) {
          	OpInst* opR = OpInst::as(rhs);
          	if (opR->get_op() == OpInst::Concat) {
          		if (opR->get_children()->size() > opL->get_children()->size()) {
          			swap(lhs, rhs);
          			swap(opL, opR);
          		}
          	}
          }

          need_new = true;
          //{a, b} == A -> (a == A[part1]) && (b == A[part2])
          const InstL* ch = lhs->get_children();
          assert(ch);
          InstL vel;
          unsigned s_loc = 0, e_loc = 0;
          bool isFalse = false;
          for (InstL::const_iterator cit = ch->begin(); cit != ch->end(); ++cit)
          {
            Inst *tve = *cit;
            tve = tve->get_port();
#ifdef EX_CC_LEVEL1
            tve = tve->get_simple();
#endif
            unsigned size = tve->get_size();
            s_loc = e_loc;
            e_loc += size;
            unsigned ns = s_loc;
            unsigned ne = size - 1 + s_loc;

            Inst* Ai = ExInst::create(rhs, ne, ns);
#ifdef EX_CC_LEVEL2
            Ai = Ai->get_simple();
#endif
            if (tve != Ai) {
              if (tve->get_type() == Num && Ai->get_type() == Num) {
                isFalse = true;
                break;
              }

              Inst* eqInst = OpInst::create(Eq, tve, Ai);
#ifdef EX_CC_LEVEL2
              eqInst = eqInst->get_simple();
#endif
              vel.push_back(eqInst);
            }
          }
          Inst* v_and;

          if (isFalse)
            v_and = NumInst::create(0, 1, SORT());
          else if (vel.size() == 0)
            v_and = NumInst::create(1, 1, SORT());
          else if (vel.size() == 1)
            v_and = vel.front();
          else
            v_and = OpInst::create(OpInst::LogAnd, vel);

          if (!eq)
            v_and = OpInst::create(LogNot, v_and);

          t_simplified_ve = v_and;
//          cout << "## simplification: " << *e << " -> " << *v_and << endl;
      	}
      }
    }

    if (!need_new) {
      InstType lhst = lhs->get_type();
      InstType rhst = rhs->get_type();

      Inst* num = NULL;
      Inst* cc = NULL;
      Inst* cc2 = NULL;
      switch(lhst) {
      case Num:
        num = lhs;
        break;
      case Op:
      {
        OpInst* opInst = OpInst::as(lhs);
        if (opInst->get_op() == Concat) {
          cc = lhs;
          cc2 = lhs;
        }
      }
      break;
      }
      switch(rhst) {
      case Num:
        num = rhs;
        break;
      case Op:
      {
        OpInst* opInst = OpInst::as(rhs);
        if (opInst->get_op() == Concat)
          cc = rhs;
      }
      break;
      }

      if (num != NULL && cc != NULL) {
        need_new = true;

        //{a, b} == Kc -> (a == Ka) && (b == Kb)
        const InstL* ch = cc->get_children();
        assert(ch);
        InstL vel;
        unsigned s_loc = 0, e_loc = 0;
        bool isFalse = false;
        for (InstL::const_iterator cit = ch->begin(); cit != ch->end(); ++cit)
        {
          Inst *tve = *cit;
          tve = tve->get_port();
#ifdef EX_CC_LEVEL1
          tve = tve->get_simple();
#endif
          unsigned size = tve->get_size();
          s_loc = e_loc;
          e_loc += size;
          unsigned ns = s_loc;
          unsigned ne = size - 1 + s_loc;

  //        if (tve->get_type() == Num)
  //          continue;

          Inst* Ki = ExInst::create(num, ne, ns);

  //#ifdef EX_CC_LEVEL2
  //        Ki = Ki->get_port();
          Ki = Ki->get_simple();
          assert (Ki->get_type() == Num);
  //#endif
          if (tve != Ki) {
            if (tve->get_type() == Num) {
              isFalse = true;
              break;
            }

            Inst* eqInst = OpInst::create(Eq, tve, Ki);
#ifdef EX_CC_LEVEL2
  //          eqInst = eqInst->get_port();
            eqInst = eqInst->get_simple();
#endif
            vel.push_back(eqInst);
          }
        }
        Inst* v_and;

        if (isFalse)
          v_and = NumInst::create(0, 1, SORT());
        else if (vel.size() == 0)
          v_and = NumInst::create(1, 1, SORT());
        else if (vel.size() == 1)
          v_and = vel.front();
        else
          v_and = OpInst::create(OpInst::LogAnd, vel);

        if (!eq)
          v_and = OpInst::create(LogNot, v_and);

        t_simplified_ve = v_and;
  //      cout << "## simplification: " << *e << " -> " << *v_and << endl;
      }
      else if (false && cc != NULL && cc2 != NULL) {
        OpInst* opL = OpInst::as(cc);
        OpInst* opR = OpInst::as(cc2);
        assert(opL);
        assert(opR);

        if (opL->get_euf_func_name() == opR->get_euf_func_name()) {
          need_new = true;
          t_simplified_ve = compare_and_simplify(opL, opR, eq);
//          cout << "## simplification: " << *e << " -> " << *t_simplified_ve << endl;
        }
      }
    }
#endif

    if (need_new)
      e->t_simple = t_simplified_ve;
    else
      e->t_simple = e;

    if (e != e->t_simple)
    {
      if (e->get_size() != t_simplified_ve->get_size())
      {
        cout << "## simplification: " << endl;
        cout << "## sz: " << e->get_size() << " -> " << t_simplified_ve->get_size() << endl;

        assert(0);
      }
//      cout << "==/!= simplification: " << *e << " -> " << *(e->t_simple) << endl;
    }
    else
    {
//      AVR_LOG(15, 0, "==/!=: " << *e << " -> same" << endl);
    }
	}
//	else if (op == Ternary)
//	{
//		t_simplified_ve = e;
//
//		/// Iterate over children
//		InstL::iterator it = exps.begin();
//		Inst* cond = *it;
//
//		it++;
//		Inst* ife = *it;
//
//		it++;
//		Inst* the = *it;
//
//		assert(cond && ife && the);
//
//		cond = cond->get_port();
//		ife = ife->get_port();
//		the = the->get_port();
//#ifdef EX_CC_LEVEL1
//		cond = cond->get_simple();
//		ife = ife->get_simple();
//		the = the->get_simple();
//#endif
//
//		bool need_new = false;
//
//#ifdef INTERPRET_EX_CC
//		// ite(cond, Concat{a, b}, Concat{c, d}) -> Concat{ite(cond, a, c), ite(cond, b, d)}
//		OpInst* op_ife = OpInst::as(ife);
//		OpInst* op_the = OpInst::as(the);
//		if (op_ife && op_the)
//		{
//			if ((op_ife->get_op() == OpInst::Concat) && (op_the->get_op() == OpInst::Concat))
//			{
//				const InstL* ch_ife = ife->get_children();
//				const InstL* ch_the = the->get_children();
//				size_t sz = ch_ife->size();
//				if (sz == ch_the->size())
//				{
//					bool szMatch = true;
//					InstL::const_iterator it_ife = ch_ife->begin();
//					InstL::const_iterator it_the = ch_the->begin();
//					for (int i = 0; i < sz; i++)
//					{
//						if ((*it_ife)->get_size() != (*it_the)->get_size())
//						{
//							szMatch = false;
//							break;
//						}
//						it_ife++;
//						it_the++;
//					}
//
//					if (szMatch)
//					{
//						need_new = true;
//						InstL::const_iterator it_ife = ch_ife->begin();
//						InstL::const_iterator it_the = ch_the->begin();
//
//						InstL newExps;
//						for (int i = 0; i < sz; i++)
//						{
//							InstL tmp;
//							tmp.push_back(cond);
//
//							Inst* ife_ch = (*it_ife);
//							Inst* the_ch = (*it_the);
//#ifdef EX_CC_LEVEL1
//							ife_ch = ife_ch->get_port();
//							the_ch = the_ch->get_port();
//
//							ife_ch = ife_ch->get_simple();
//							the_ch = the_ch->get_simple();
//#endif
//							tmp.push_back(ife_ch);
//							tmp.push_back(the_ch);
//
//							Inst* newExp = OpInst::create(OpInst::Ternary, tmp);
//							OpInst* op_new = OpInst::as(newExp);
//							assert(op_new);
//
//#ifdef EX_CC_LEVEL2
//							newExp = newExp->get_simple();
//#endif
//							newExps.push_back(newExp);
//
//							it_ife++;
//							it_the++;
//						}
//
//						Inst* tmp = OpInst::create(OpInst::Concat, newExps);
//#ifdef EX_CC_LEVEL2
//						tmp = tmp->get_simple();
//#endif
//						t_simplified_ve = tmp;
//					}
//				}
//			}
//		}
//#endif
//
//		if (need_new)
//			e->t_simple = t_simplified_ve;
//		else
//			e->t_simple = e;
//
//		if (e != e->t_simple)
//		{
//			if (e->get_size() != t_simplified_ve->get_size())
//			{
//				cout << "## simplification: " << endl;
//				cout << "## sz: " << e->get_size() << " -> " << t_simplified_ve->get_size() << endl;
//
//				const InstL* ch = e->get_children();
//				for (InstL::const_iterator cit = ch->begin(); cit != ch->end(); ++cit)
//				{
//					Inst* tve = *cit;
//					cout << "  " << *(*cit) << "  (sz: " << (*cit)->get_size() << endl;
//					const InstL* ch2 = tve->get_children();
//					for (InstL::const_iterator cit2 = ch2->begin(); cit2 != ch2->end(); ++cit2)
//					{
//						cout << "  \t" << *(*cit2) << "  (sz: " << (*cit2)->get_size() << ")" << endl;
//					}
//				}
//
//				cout << endl << "simple: " << *t_simplified_ve << endl;
//				ch = t_simplified_ve->get_children();
//				for (InstL::const_iterator cit = ch->begin(); cit != ch->end(); ++cit)
//				{
//					cout << "  " << *(*cit) << "  (sz: " << (*cit)->get_size() << endl;
//				}
//				assert(0);
//			}
////			cout << "Ter simplification: " << *e << " -> " << *(e->t_simple) << endl;
//		}
//		else
//		{
////			AVR_LOG(15, 0, "Cc: " << *e << " -> same" << endl);
//		}
//	}
	else if (op == Concat)
	{
		_numConcat++;

		t_simplified_ve = e;

		bool need_new = false;

#ifdef INTERPRET_EX_CC
		if (to_simplify && e->interpret()) {
			// do nothing, done
		}
		/// If only one child, easy. But simplify it first.
		else if (exps.size() == 1)
		{
			need_new = true;
			Inst* exp = exps.front();
      exp = exp->get_port();
#ifdef EX_CC_LEVEL1
			exp = exp->get_simple();
#endif
			t_simplified_ve = exp;
		}
		else
		{
			InstL vel;
      InstS conditions;
			/// Iterate over children
			for (InstL::iterator cot = exps.begin(); cot != exps.end(); cot++)
			{
				Inst* exp = *cot;

				exp = exp->get_port();
#ifdef EX_CC_LEVEL1
				exp = exp->get_simple();
#endif

				OpInst* op_exp = OpInst::as(exp);
				ExInst* ex_exp = ExInst::as(exp);
				NumInst* num_exp = NumInst::as(exp);

				/// Deal with Cc, i.e. flatten Cc(Cc .. )
				if (op_exp && (op_exp->get_op() == OpInst::Concat))
				{
					need_new = true;
					const InstL* ch = op_exp->get_children();
					assert(ch);
					/// Push to outer Cc
					for (InstL::const_iterator cit = ch->begin(); cit != ch->end(); ++cit)
					{
						Inst *tve = *cit;
            tve = tve->get_port();
#ifdef EX_CC_LEVEL1
						tve = tve->get_simple();
#endif
						vel.push_back(tve);
					}
				}
				/// Deal with Ex
				else if (ex_exp)
				{
					Inst* tve = exp;
					/// Below code merges multiple ExInsts
					if (!vel.empty())
					{
						Inst* prev = vel.back();
						prev = prev->get_port();
#ifdef EX_CC_LEVEL1
						prev = prev->get_simple();
#endif

						ExInst* ex_prev = ExInst::as(prev);
						if (ex_prev)
						{
							Inst* exp = ex_exp->get_exp();
							if (exp == ex_prev->get_exp())
							{
								if (ex_prev->get_hi() == (ex_exp->get_lo() - 1))
								{
									need_new = true;
									tve = ExInst::create(exp, ex_exp->get_hi(), ex_prev->get_lo());
//									cout << "merging " << *ex_prev << ", " << *ex_exp << " to " << *tve << endl;
#ifdef EX_CC_LEVEL2
									tve = tve->get_simple();
#endif
									vel.pop_back();
								}
							}
						}
					}
					vel.push_back(tve);
				}
				/// Deal with Num
				else if (num_exp)
				{
					Inst* tve = exp;
					/// Below code merges multiple NumInsts
					if (!vel.empty())
					{
						Inst* prev = vel.back();
						NumInst* num_prev = NumInst::as(prev);
						if (num_prev)
						{
							need_new = true;
							unsigned pSz = num_prev->get_size();
							unsigned eSz = num_exp->get_size();
							string s = num_prev->get_mpz()->get_str(2);
							while (s.length() != pSz)
								s = "0" + s;

							s = num_exp->get_mpz()->get_str(2) + s;
							while (s.length() != (eSz + pSz))
								s = "0" + s;

							tve = NumInst::create(s, (eSz + pSz), 2, SORT());
//							cout << "merging " << *num_prev << ", " << *num_exp << " to " << *tve << endl;
							vel.pop_back();
						}
					}
					vel.push_back(tve);
				}
				else if (op_exp && (op_exp->get_op() == OpInst::Ternary)) {
          /// Deal with Ternary, i.e. { ite(c, A, B), ite(c, C, D) } = ite(c, {A, C}, {B, D})
				  Inst* cond = op_exp->get_children()->front();
          cond = cond->get_port();
#ifdef EX_CC_LEVEL1
          cond = cond->get_simple();
#endif
				  conditions.insert(cond);
          vel.push_back(exp);
				}
				else
				{
					vel.push_back(exp);
				}
			}

      if (need_new)
      {
        if (vel.size() == 1)
          t_simplified_ve = vel.front();
        else
        {
          Inst* tmp = OpInst::create(OpInst::Concat, vel);
          t_simplified_ve = tmp;
        }
#ifdef EX_CC_LEVEL2
        t_simplified_ve = t_simplified_ve->get_simple();
#endif
      }
      else {

        /// Now we have all children in simplest form in vel
        /// vel does not have Cc
        /// Now only thing left is to deal with Ternary children in vel

        if (conditions.size() == 1) {
//          e->m_simple = false;
          need_new = true;

          InstL velT, velF;
          Inst* condNew = (*conditions.begin());
          for (auto& v: exps) {
            if (v->get_type() == Op && OpInst::as(v)->get_op() == Ternary) {
              /// Iterate over children
              InstL::const_iterator cit = v->get_children()->begin();
              Inst* cond = *cit;

              cit++;
              Inst* ife = *cit;

              cit++;
              Inst* the = *cit;

              assert(cond && ife && the);

              cond = cond->get_port();
              ife = ife->get_port();
              the = the->get_port();
#ifdef EX_CC_LEVEL1
              cond = cond->get_simple();
              ife = ife->get_simple();
              the = the->get_simple();
#endif
              assert(cond == condNew);
              velT.push_back(ife);
              velF.push_back(the);
            }
            else {
              Inst* tve = v;
              tve = tve->get_port();
#ifdef EX_CC_LEVEL1
              tve = tve->get_simple();
#endif
              velT.push_back(tve);
              velF.push_back(tve);
            }
          }
          Inst* ifnew = OpInst::create(OpInst::Concat, velT);
          Inst* thnew = OpInst::create(OpInst::Concat, velF);
#ifdef EX_CC_LEVEL2
          ifnew = ifnew->get_simple();
          thnew = thnew->get_simple();
#endif
          InstL velNew;
          velNew.push_back(condNew);
          velNew.push_back(ifnew);
          velNew.push_back(thnew);
          Inst* v_ite = OpInst::create(OpInst::Ternary, velNew);
#ifdef EX_CC_LEVEL2
          v_ite = v_ite->get_simple();
#endif
          t_simplified_ve = v_ite;
        }
      }
		}
#endif

		if (need_new)
			e->t_simple = t_simplified_ve;
		else
			e->t_simple = e;

		if (e != e->t_simple)
		{
			if (e->get_size() != t_simplified_ve->get_size())
			{
				cout << "## simplification: " << endl;
				cout << "## sz: " << e->get_size() << " -> " << t_simplified_ve->get_size() << endl;

				const InstL* ch = e->get_children();
				for (InstL::const_iterator cit = ch->begin(); cit != ch->end(); ++cit)
				{
					Inst* tve = *cit;
					cout << "  " << *(*cit) << "  (sz: " << (*cit)->get_size() << endl;
					const InstL* ch2 = tve->get_children();
					for (InstL::const_iterator cit2 = ch2->begin(); cit2 != ch2->end(); ++cit2)
					{
						cout << "  \t" << *(*cit2) << "  (sz: " << (*cit2)->get_size() << ")" << endl;
					}
				}

				cout << endl << "simple: " << *t_simplified_ve << endl;
				ch = t_simplified_ve->get_children();
				for (InstL::const_iterator cit = ch->begin(); cit != ch->end(); ++cit)
				{
					cout << "  " << *(*cit) << "  (sz: " << (*cit)->get_size() << endl;
				}
				assert(0);
			}
//			cout << "(concat): " << *e << " -> " << *(e->t_simple) << endl;
//			AVR_LOG(15, 0, "Cc: " << *e << " -> " << *(e->t_simple) << endl);
		}
		else
		{
//			AVR_LOG(15, 0, "Cc: " << *e << " -> same" << endl);
		}
	}
	else
	{
		if (e->get_euf_func_name() != "0") {
			_numUF++;

			if (to_simplify) {

				if (e->interpret()) {
//					return e->t_simple;
					// do nothing, done
				}
				else if (Config::g_uf_unordered) {
					if (e->is_unordered_uf()) {
						const InstL* ch = e->get_children();
						assert(ch);

						InstL newCh;
						for (InstL::const_iterator cit = ch->begin(); cit != ch->end(); cit++)
							newCh.push_front(*cit);
						e->t_simple = OpInst::create(op, newCh, e->get_size(), false);
					}
				}
			}
		}
	}

//	if (e != e->t_simple) {
//		cout << "excc: " << *e << " -> " << *(e->t_simple) << endl;
//	}

	if (o_size != 0 && o_size != e->get_size()) {
		cout << *e << "  " << e->get_size() << " instead of " << o_size << endl;
		assert(0);
	}

	if (op == Ternary) {
		hm_ITEInst.insert(make_pair(t_idx, e));
	} else if (exps.size() < 3) {
		hm_OpInst.insert(make_pair(t_idx, e));
	} else {
		hm_ETCInst.insert(make_pair(t_idx, e));
	}

	if (op == Concat && wn_simplify_concat)
	{
//		cout << "Simp: " << *e << " -> " << *e->t_simple << endl;
		return e->t_simple;
	}
	else
	{
		return e;
	}
}
OpInst* OpInst::create() {
	OpInst* e = new OpInst;
	m_exps_pool.push_back(e);
	return e;
}
bool OpInst::check_consistency(ostream& out) {
	if (!Inst::check_consistency(out)) {
		return false;
	}
	InstL::iterator it1 = m_exps.begin(), it2 = m_exps.begin(), end_it = m_exps.end();
	it2++;
	for (InstL::iterator it = m_exps.begin(), end_it = m_exps.end(); it != end_it; ++it)
		if (!((*it)->check_consistency(out)))
			return false;
	switch (get_op()) {
	case Unknown:
	case Extract:
		assert(0);
	case Concat: {
		unsigned sum = 0;
		for (InstL::iterator it = it1; it != end_it; ++it)
			sum += (*it)->get_size();
		if (sum != get_size()) {
			out << "in concat instance: " << *this << endl;
			out << "size is " << get_size() << " while sum of children is: " << sum << endl;
			return false;
		}
	}
		break;
	case Minus:
	case BitWiseNot:
	case ShiftL:
	case ShiftR:
	case AShiftR:
	{
		if((*it2)->get_type() != Num){
			cout << "we DONOT support the operator, shift by variable!!!" << endl;
			assert(0);
		}
		if (get_size() != (*it1)->get_size()) {
			out << "instance: " << *this << endl;
			out << "of size: " << get_size() << " should be equal to its child's size: " << (*it1)->get_size() << endl;
			return false;
		}
	}
		break;
	case Sext:
	case Zext:
	{
//		if((*it2)->get_type() != Num){
//			cout << "we DONOT support the operator, sign/zero extend by variable!!!" << endl;
//			assert(0);
//		}
		if (get_size() != (*it2)->get_size()) {
			out << "instance: " << *this << endl;
			out << "of size: " << get_size() << " should be equal to its 2nd arg size: " << (*it2)->get_size() << endl;
			return false;
		}
	}
		break;
//	case Add:
	case Sub:
	case Mult:
	case Div:
	case SDiv:
	case Eq:
	case NotEq:
	case Gr:
	case SGr:
	case Le:
	case SLe:
	case GrEq:
	case SGrEq:
	case LeEq:
	case SLeEq:
	case BitWiseAnd:
	case BitWiseOr:
	case BitWiseXor:
	case BitWiseXNor:
	case BitWiseNor:
	case BitWiseNand: {
		for (InstL::iterator it = it1; it != end_it; ++it)
			if ((*it)->get_size() != (*it1)->get_size()) {
				out << "in instance: " << *this << endl;
				out << "all argument sizes should be equal" << endl;
				out << "first argument size is: " << (*it1)->get_size() << " while this argument: " << *(*it) << " has size of: " << (*it)->get_size() << endl;
				return false;
			}
		switch (get_op()) {
//		case Add:
		case Sub:
		case Mult:
		case Div:
		case SDiv:
		case BitWiseAnd:
		case BitWiseOr:
		case BitWiseXor:
		case BitWiseXNor:
		case BitWiseNor:
		case BitWiseNand: {
			if ((*it1)->get_size() != get_size()) {
				out << "instance: " << *this << " of size: " << get_size() << endl;
				out << "should be equal to its argument size.. in this case: " << (*it1)->get_size() << endl;
				return false;
			}
		}
			break;
		case Eq:
		case NotEq:
		case Gr:
		case SGr:
		case Le:
		case SLe:
		case GrEq:
		case SGrEq:
		case LeEq:
		case SLeEq:
		{
			if (get_size() != 1) {
				out << "instance: " << *this << endl;
				out << "should be of size 1, but its size is: " << get_size() << endl;
				return false;
			}
		}
			break;
		default:
			AVR_COUT << get_op() << endl;
			assert(0);
		}
	}
		break;
	case LogXor:
	case LogXNor:
	case LogNand:
	case LogNor:
	case LogAnd:
	case LogOr:
	case LogNot: {
		if (get_size() != 1) {
			out << "instance: " << *this << endl;
			out << "should be of size 1, but its size is: " << get_size() << endl;
			return false;
		}
		for (InstL::iterator it = it1; it != end_it; ++it)
			if ((*it)->get_size() != 1) {
				out << "in instance: " << *this << endl;
				out << "all argument sizes should be 1" << endl;
				out << "this argument " << *(*it) << " is of size: " << (*it)->get_size() << endl;
				return false;
			}
	}
		break;
	case ReductionAnd:
	case ReductionOr:
	case ReductionXor:
	case ReductionXNor:
	case ReductionNand:
	case ReductionNor: {
		if (get_size() != 1) {
			out << "instance: " << *this << endl;
			out << "should be of size 1, but its size is: " << get_size() << endl;
			return false;
		}
	}
		break;
	case Ternary: {
		if ((*it1)->get_size() != 1) {
			out << "in instance: " << *this << endl;
			out << "the condition " << *(*it1) << " is of size: " << (*it1)->get_size() << endl;
			return false;
		}
		InstL::iterator it3 = it2;
		it3++;
		if ((*it2)->get_size() != (*it3)->get_size()) {
			out << "in instance: " << *this << endl;
			out << "the then and else sizes are not equal: " << (*it2)->get_size() << " " << (*it3)->get_size() << endl;
			return false;
		}
	}
		break;
	case Future: {
		if ((*it1)->get_size() != get_size()) {
			out << "instance: " << *this << endl;
			out << "size is " << get_size() << " while child's size is: " << (*it1)->get_size() << endl;
		}
	}
		break;
	default:
		assert(0);
	}
	return true;
}

Inst* MemInst::create(string name, unsigned size, MemType t, InstL&ports) {
	assert(name != "");
	for (InstL::iterator it = ports.begin(), end_it = ports.end(); it != end_it; ++it)
		assert(*it);
	MemInst* e = new MemInst(name, size, t, ports);
	m_exps_pool.push_back(e);
	unsigned hash = 0;
	for (InstL::iterator it = ports.begin(), end_it = ports.end(); it != end_it; ++it)
		hash += (*it)->get_hash1();
	e->set_hash1(hash);
	return e;
}
MemInst* MemInst::create() {
	MemInst* e = new MemInst;
	m_exps_pool.push_back(e);
	return e;
}
bool MemInst::check_consistency(ostream& out) {
	if (!Inst::check_consistency(out)) {
		return false;
	}
	for (InstL::iterator it = m_ports.begin(), end_it = m_ports.end(); it != end_it; ++it)
		if (!((*it)->check_consistency(out)))
			return false;
	switch (m_memtype) {
	case Write: {
		if ((m_ports.size() % 3) != 0) {
			out << "Need a 3x inputs for memory write!" << endl;
			out << "You have: " << m_ports.size() << " of them!" << endl;
			return false;
		}
		for (InstL::iterator it = m_ports.begin(), end_it = m_ports.end(); it != end_it;) {
			it++;
			if ((*it)->get_size() != 1) {
				out << "memory instance: " << this << " has enable instance of size: " << (*it)->get_size() << endl;
				return false;
			}
			it++;
			if ((*it)->get_size() != get_size()) {
				out << "memory instance: " << this << " has data instance of size: " << (*it)->get_size() << endl;
				out << "which is different that its own size: " << get_size() << endl;
				return false;
			}
			it++;
		}
	}
		break;
	case Read:
		if (m_ports.size() != 1) {
			out << "Need only one (addr) input for memory read!" << endl;
			out << "You have: " << m_ports.size() << " of them!" << endl;
			return false;
		}
		break;
	case Init: {
		if ((m_ports.size() % 2) != 1) {
			out << "Need a 2x+1 inputs for memory write!" << endl;
			out << "You have: " << m_ports.size() << " of them!" << endl;
			return false;
		}
		InstL::iterator it = m_ports.begin();
		for (InstL::iterator end_it = m_ports.end(); it != end_it;) {
			++it;
			if (it != m_ports.end()) {
				if ((*it)->get_size() != get_size()) {
					out << "memory instance: " << this << " has data instance of size: " << (*it)->get_size() << endl;
					out << "which is different that its own size: " << get_size() << endl;
				}
			}
			++it;
		}
		it--;
		if ((*it)->get_size() != get_size()) {
			out << "memory instance: " << this << " has data instance of size: " << (*it)->get_size() << endl;
			out << "which is different that its own size: " << get_size() << endl;
		}
	}
		break;
	}
	return true;
}
Inst* UFInst::create(string name, unsigned size, InstL&children) {
	assert(0);
	assert(name != "");
	for (InstL::iterator it = children.begin(), end_it = children.end(); it != end_it; ++it)
		assert(*it);
	UFInst* e = new UFInst(name, size, children);
	m_exps_pool.push_back(e);
	unsigned hash = 0;
	for (InstL::iterator it = children.begin(), end_it = children.end(); it != end_it; ++it)
		hash += (*it)->get_hash1();
	e->set_hash1(hash);
	return e;
}
UFInst* UFInst::create() {
	assert(0);
	UFInst* e = new UFInst;
	m_exps_pool.push_back(e);
	return e;
}
void Inst::uncreate_all() {
	for(InstL::iterator it = m_exps_pool.begin() , end_it = m_exps_pool.end() ; it != end_it ; ++it){
		delete *it;
	}
	 m_exps_pool.clear();
}

Inst* OpInst::concat_conditionals (InstL& vel, InstToIntM condMap)
{
//	cout << "\t" << condMap.size() << endl;
	Inst* cond = NULL;
	for (auto& mit : condMap)
	{
		if (mit.second == -1)
		{
			cond = mit.first;
			break;
		}
	}

	if (cond == NULL)
	{
		InstL exps;
		for (auto& tve : vel)
		{
			OpInst* op_tve = OpInst::as(tve);
			if (op_tve && op_tve->get_op() == OpInst::Ternary)
			{
				InstL::const_iterator it = tve->get_children()->begin();
				Inst* cond_tve = *it;
				it++;
				Inst* ife = *it;
				it++;
				Inst* the = *it;
				assert(cond_tve && ife && the);

//				/// Simplify children first
//				OpInst* op_tmp;
////				op_tmp = OpInst::as(cond);
////				if (op_tmp && op_tmp->get_op() == OpInst::Concat)
////				{
////					cond = op_tmp->t_simple;
////				}
////				else
////				{
////					ExInst* ex_tmp = ExInst::as(cond);
////					if (ex_tmp)
////						cond = ex_tmp->t_simple;
////				}
//				op_tmp = OpInst::as(ife);
//				if (op_tmp && op_tmp->get_op() == OpInst::Concat)
//				{
//					ife = op_tmp->t_simple;
//				}
//				else
//				{
//					ExInst* ex_tmp = ExInst::as(ife);
//					if (ex_tmp)
//						ife = ex_tmp->t_simple;
//				}
//				op_tmp = OpInst::as(the);
//				if (op_tmp && op_tmp->get_op() == OpInst::Concat)
//				{
//					the = op_tmp->t_simple;
//				}
//				else
//				{
//					ExInst* ex_tmp = ExInst::as(the);
//					if (ex_tmp)
//						the = ex_tmp->t_simple;
//				}

				InstToIntM::iterator mit = condMap.find(cond_tve);
				assert(mit != condMap.end());
				if ((*mit).second == 1)
					exps.push_back(ife);
				else
				{
					assert((*mit).second == 0);
					exps.push_back(the);
				}
			}
			else
				exps.push_back(tve);
		}
		Inst* tmp = OpInst::create(OpInst::Concat, exps);
		ExInst* ex = ExInst::as(tmp);
		assert(tmp);
		if (ex)
		{
			tmp = ex->t_simple;
		}
		else
		{
			OpInst* op = OpInst::as(tmp);
			if (op && op->get_op() == OpInst::Concat)
			{
				tmp = op->t_simple;
			}
		}
//		cout << "\treturning: " << *tmp << " for e: " << *this << endl;
		return tmp;
	}
	else
	{
		condMap[cond] = 1;
		Inst* ife = concat_conditionals(vel, condMap);
		condMap[cond] = 0;
		Inst* the = concat_conditionals(vel, condMap);

		InstL exps;
		exps.push_back(cond);
		exps.push_back(ife);
		exps.push_back(the);

		Inst* tmp = OpInst::create(OpInst::Ternary, exps);
//		cout << "\treturning: " << *tmp << " for e: " << *this << endl;
		return tmp;
	}
}

void Inst::dump_size_all(ostream& out) {
	for (InstL::iterator it = m_exps_pool.begin(), end_it = m_exps_pool.end(); it != end_it; ++it)
		out << *(*it) << " " << (*it)->get_size() << endl;
}

unsigned Inst::total_nodes() {
	return m_exps_pool.size();
}

Inst* Inst::all_next2pre(Inst *e) {
	Inst *res = e;
	if (e->next2pre != INVALID_INST) {
	  return e->next2pre;
	}

	if (!e->childrenInfo[SIG]){
		e->next2pre = e;
		return e;
	}
//	else if (find_pre(e))
//	{
//		cout << "(error: found pre signal in " << *e << " )" << endl;
//		assert(0);
//	}

	if (!e->find_next() && e->childrenInfo[SIG]) {
		cout << "expecting expression in next domain, got " << *e << endl;
		assert(0);
	}

	const InstL* ch = e->get_children();
	if (ch) {
		bool changed = false;
		InstL newl;
		for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it) {
			if ((*it)->get_type() == Num || (*it)->get_type() == Const) {
				newl.push_back(*it);
				continue;
			}
			Inst *tve;
			if ((*it)->get_type() == Sig)
			{
				SigInst* sig = SigInst::as(*it);
				InstToInstM::iterator pit = Inst::_m_next_to_pre.find(sig);
				if (pit != Inst::_m_next_to_pre.end())
				{
					tve = (*pit).second;
				}
				else
				{
					InstToInstM::iterator iit = Inst::_m_next_input_pre.find(sig);
					if (iit != Inst::_m_next_input_pre.end())
					{
						tve = (*iit).second;
					}
					else
					{
//						cout << "expecting next state/input variable, got " << *sig << endl;
//						assert(0);

						string sigName = sig->get_name();
						string sigName_wo_next = sigName.substr(0, sigName.find_last_of('$'));
						Inst* sigTmp = SigInst::create(sigName_wo_next, sig->get_size(), sig->get_sort());
						tve = sigTmp;
					}
				}
			}
			else {
				tve = all_next2pre(*it);
			}
			newl.push_back(tve);

			/// Aman
//			if(tve != *it)
//			{
				changed = true;
//			}
			/// END
		}
		if (changed) {

			WireInst* w_e = WireInst::as(e);
			if (w_e)
			{
				assert(newl.size() == 1);
				InstToInstM::iterator pit = Inst::_m_next_wire_pre.find(w_e);
				if (pit != Inst::_m_next_wire_pre.end())
				{
					res = (*pit).second;
				}
				else
				{
					string name = w_e->get_name() + "$pre";
					res = WireInst::create(name, w_e->get_size(), newl.front());

					Inst::_m_next_wire_pre[w_e] = res;
					Inst::_m_pre_wire_next[res] = w_e;
//					cout << "(wire: " << *res << " -- " << *w_e << ")" << endl;
				}
			}
			else
				res = e->apply_children(newl);

			if(res->ve_orig == NULL){
				if(e->ve_orig == NULL){
					res->ve_orig = e;
				}else{
					res->ve_orig = e->ve_orig;
				}
			}
		}
	} else {
		SigInst* sig = SigInst::as(e);
		if (sig) {
			 assert(sig->get_type() == Sig);
//			string t_str = sig->get_name();
// 			if (_m_sn.find(t_str) == _m_sn.end()) {
// 				string pre_name = t_str.substr(0, t_str.length() - 5) + "$pre";
// 				//				cout << "all_next2pre: " << t_str << " -> " << pre_name << endl;
// 				res = SigInst::create(pre_name, sig->get_size());
// 			} else
			{
				 InstToInstM::iterator pit = Inst::_m_next_to_pre.find(sig);
				if (pit != Inst::_m_next_to_pre.end())
				{
					res = (*pit).second;
				}
				else
				{
					InstToInstM::iterator iit = Inst::_m_next_input_pre.find(sig);
					if (iit != Inst::_m_next_input_pre.end())
					{
						res = (*iit).second;
					}
					else
					{
//						cout << "expecting next state/input variable, got " << *sig << endl;
//						assert(0);

						string sigName = sig->get_name();
						string sigName_wo_next = sigName.substr(0, sigName.find_last_of('$'));
						Inst* sigTmp = SigInst::create(sigName_wo_next, sig->get_size(), sig->get_sort());
						res = sigTmp;
					}
				}
			}
		}
	}
	e->next2pre = res;

// 	cout << "*e: " << *e << endl;
// 	cout << "*(e->next_pre): " << *(e->next_pre) << endl;

	return res;
}

// add $next to every signal
Inst* Inst::all_pre2next(Inst *e) {
	Inst *res = e;
	if (e->pre2next != INVALID_INST) {
		return e->pre2next;
	}

	if (!e->childrenInfo[SIG]){
		e->pre2next = e;
		return e;
	}

	if (e->find_next()) {
		cout << "expecting expression in present domain, got " << *e << endl;
		assert(0);
	}

	const InstL* ch = e->get_children();
	if (ch) {
		bool changed = false;
		InstL newl;
		for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it) {
			if ((*it)->get_type() == Num || (*it)->get_type() == Const) {
				//cout << *(*it) << endl;
				newl.push_back(*it);
				continue;
			}
			Inst *tve;
			/// Aman
			if ((*it)->get_type() == Sig)
			{
				SigInst* sig = SigInst::as(*it);
//				if (_msv_all_pre2next_vars.find(sig->get_name()) != _msv_all_pre2next_vars.end()) {
//					tve = _msv_all_pre2next_vars[sig->get_name()];
////										cout << SigInst::as(tve)->get_name() << endl;
//					//					e->replace_child(*it, _msv_all_pre2next_vars[sig->get_name()]);
//
//				} else {
//					string orig_name = sig->get_name();
//					int num_of_next = get_depth(orig_name);
//					if (_max_depth < num_of_next) {
//						_max_depth = num_of_next;
//					}
//					string next_name = orig_name + "$next";
//					tve = SigInst::create(next_name, sig->get_size());
//
//					_msv_all_next2pre_vars[next_name] = sig;
//					_msv_all_pre2next_vars[orig_name] = tve;
//				}
				InstToInstM::iterator pit = Inst::_m_pre_to_next.find(sig);
				if (pit != Inst::_m_pre_to_next.end())
				{
					tve = (*pit).second;
				}
				else
				{
					InstToInstM::iterator iit = Inst::_m_pre_input_next.find(sig);
					if (iit != Inst::_m_pre_input_next.end())
					{
						tve = (*iit).second;
					}
					else
					{
//						cout << "expecting present state/input variable, got " << *e << endl;
//						assert(0);

						string sigName = sig->get_name();
						string sigName_w_next = sigName + "$next";
						Inst* sigTmp = SigInst::create(sigName_w_next, sig->get_size(), sig->get_sort());
						tve = sigTmp;
					}
				}
				changed = true;
			}
			else {
				tve = all_pre2next(*it);
				if (tve != (*it))
					changed = true;
			}
			newl.push_back(tve);
			/// END
		}
		if (changed){
			WireInst* w_e = WireInst::as(e);
			if (w_e)
			{
				assert(newl.size() == 1);

				InstToInstM::iterator pit = Inst::_m_pre_wire_next.find(w_e);
				if (pit != Inst::_m_pre_wire_next.end())
				{
					res = (*pit).second;
				}
				else
				{
					string name = w_e->get_name() + "$next";
					res = WireInst::create(name, w_e->get_size(), newl.front());

					Inst::_m_pre_wire_next[w_e] = res;
					Inst::_m_next_wire_pre[res] = w_e;
//					cout << "(wire: " << *res << " -- " << *w_e << ")" << endl;
				}
			}
			else
				res = e->apply_children(newl);

			if(res->ve_orig == NULL)
			{
				if(e->ve_orig == NULL)
				{
					res->ve_orig = e;
				}
				else
				{
					res->ve_orig = e->ve_orig;
				}
			}
		}
	}
	else
	{
		SigInst* sig = SigInst::as(e);
		if (sig)
		{
			assert(sig->get_type() == Sig);
			InstToInstM::iterator pit = Inst::_m_pre_to_next.find(sig);
			if (pit != Inst::_m_pre_to_next.end())
			{
				res = (*pit).second;
			}
			else
			{
				InstToInstM::iterator iit = Inst::_m_pre_input_next.find(sig);
				if (iit != Inst::_m_pre_input_next.end())
				{
					res = (*iit).second;
				}
				else
				{
//					cout << "expecting present state/input variable, got " << *e << endl;
//					assert(0);

					string sigName = sig->get_name();
					string sigName_w_next = sigName + "$next";
					Inst* sigTmp = SigInst::create(sigName_w_next, sig->get_size(), sig->get_sort());
					res = sigTmp;
				}
			}
		}
	}
	e->pre2next = res;

	return res;
}




ostream& operator<<(ostream&out, StringS&s) {
	for (StringS::iterator it = s.begin(), end_it = s.end(); it != end_it; ++it)
		out << (*it) << " ";
	return out;
}

ostream& operator<<(ostream&out, SigToInstM&m) {
	for (SigToInstM::const_iterator it = m.begin(), end_it = m.end(); it != end_it; ++it)
		out << (*it).first << " ";
	return out;
}

ostream& operator<<(ostream& out, InstType& t) {
	switch (t) {
	case Sig:
		return out << "Sig";
	case Num:
		return out << "Num";
	case Wire:
		return out << "Wire";
	case Const:
		return out << "Const";
	case Op:
		return out << "Op";
	case Ex:
		return out << "Ex";
	case Mem:
		return out << "Mem";
	case UF:
		return out << "UF";
	default:
		assert(0);
	}
	assert(0);
	return out;
}

ostream& operator<<(ostream& out, Inst& e) {
	e.print(out);
	return out;
}

ostream& operator<<(ostream& out, InstL& l) {
	out << endl;
	for (InstL::iterator it = l.begin(), end_it = l.end(); it != end_it; ++it)
		out << "\t" << *(*it) << endl;
//		out << "\t\t\t\t" << *(*it) << endl;
	return out;
}

ostream& operator<<(ostream& out, InstS& s) {
	out << endl;
	for (InstS::iterator it = s.begin(), end_it = s.end(); it != end_it; ++it)
		out << "\t" << *(*it) << endl;
//		out << "\t\t\t\t" << *(*it) << endl;
	return out;
}

ostream& operator<<(ostream& out, TransElem& t) {
	t.print(out);
	return out;
}
ostream& operator<<(ostream& out, TransElemL& l) {
	out << endl;
	for (TransElemL::iterator it = l.begin(), end_it = l.end(); it != end_it; ++it)
		out << *it << endl;
	return out;
}

void TransElem::print(ostream& out) {
	switch (type) {
	case 0:
		out << "INIT";
		break;
	case 1:
		out << "CSF";
		break;
	case 2:
		out << "NSF";
		break;
	default:
		AVR_COUT << type << endl;
		assert(0);
	}
	out << "[" << *lhs << "] := " << *rhs;
}

void Inst::print_summary(ostream&out) {
#ifdef OPTIMIZE
	assert(0);
#endif
	out << "Id: " << get_id() << " Type: " << get_type() << " Children: ";
	const InstL* ch = get_children();
	if (ch) {
		for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it)
			out << (*it)->get_id() << " ";
	}
	out << " ";
}

void Inst::print_verilog_name(ostream&out) {
	out << "sig" << get_id();
}

void Inst::print_verilog(ostream&out) {
#ifdef OPTIMIZE
	assert(0);
#endif
	out << "wire";
	if (get_size() > 1)
		out << " [" << get_size() - 1 << ":0]";
	out << " ";
	print_verilog_name(out);
	out << " = ";
}

void SigInst::print(ostream&out) {
#ifdef OPTIMIZE
	//  assert(0);
#endif
	out << m_name;
}

void SigInst::print_summary(ostream&out) {
	Inst::print_summary(out);
	print(out);
	out << endl;
}

string SigInst::dollar_dot_to_underscore(string s) {
	string res;
	for (string::iterator it = s.begin(), end_it = s.end(); it != end_it; ++it)
		if (*it == '$' || *it == '.')
			res += "_";
		else
			res += *it;
	return res;
}

void SigInst::print_verilog(ostream&out) {
	string name = dollar_dot_to_underscore(m_name);
	if (st_printed_signals.find(name) == st_printed_signals.end()) {
		st_printed_signals.insert(name);
		out << "wire";
		if (get_size() > 1)
			out << " [" << get_size() - 1 << ":0]";
		out << " " << name << " = ND_";
		if (get_size() > 1)
			out << "T";
		else
			out << "B";
		out << ";" << endl;
	}
	Inst::print_verilog(out);
	out << name << ";" << endl;
	/*  Inst::print_verilog(out);
	 out<<" ND_";
	 if(get_size()>1)
	 out<<"T";
	 else
	 out<<"B";
	 out<<"; // "<<name<<endl;*/

}

void NumInst::print(ostream&out) {
	if (get_sort_type() == bvtype)
		out << m_size << "'d" << m_mpz;
	else
		out << get_sort().sort2str() << "'d" << m_mpz;
}

void NumInst::print_summary(ostream&out) {
	Inst::print_summary(out);
	print(out);
	out << endl;
}

void NumInst::print_verilog(ostream&out) {
	Inst::print_verilog(out);
	print(out);
	out << ";" << endl;
}

/// Aman
void WireInst::print(ostream&out) {
//	out << *get_port();
//	return;

  if (Inst::print_concrete) {

#ifdef I4
  	ostringstream tmp;
  	tmp << *get_port();
  	string stmp = tmp.str();
  	if (stmp.length() < 300) {
			out << stmp;
			return;
  	}
#endif

//  	if (true)
  	if (is_added())
  		out << *get_port();
  	else {
			Inst* port = get_port();
			OpInst* op = OpInst::as(port);
			if ((port->get_type() == Ex) || (op && (op->get_op() == OpInst::Concat)))
				out << *get_port();
			else
				out << m_name;
  	}
  }
  else
	  out << m_name;
}

void WireInst::print_summary(ostream&out) {
	Inst::print_summary(out);
	print(out);
	out << endl;
}

void WireInst::print_verilog(ostream&out) {
	Inst::print_verilog(out);
	print(out);
	out << ";" << endl;
	assert(0);
}

void ConstInst::print(ostream&out) {
	out << m_name;
}

void ConstInst::print_summary(ostream&out) {
	Inst::print_summary(out);
	print(out);
	out << endl;
}

void ConstInst::print_verilog(ostream&out) {
	Inst::print_verilog(out);
	print(out);
	out << ";" << endl;
	assert(0);
}
/// END


void ExInst::print(ostream&out) {
	assert(m_exps.size() == 1);
	bool complex = ((*(m_exps.begin()))->get_type() != Sig && (*(m_exps.begin()))->get_type() != Num);
	if (complex)
		out << "(";
	out << *(*(m_exps.begin()));
	if (complex)
		out << ")";
	out << "[" << m_hi << ":" << m_lo << "]";
}

void ExInst::print_summary(ostream&out) {
	Inst::print_summary(out);
	out << "[" << m_hi << ":" << m_lo << "]" << endl;
}

void ExInst::print_verilog(ostream&out) {
	Inst::print_verilog(out);
	assert(m_exps.size() == 1);
	(*(m_exps.begin()))->print_verilog_name(out);
	out << "[" << m_hi << ":" << m_lo << "]" << ";" << endl;
}

string OpInst::op2str(OpType t) {
	switch (t) {
	case Unknown:
		return "unknown";
	case Extract:
		return "[]";
	case Add:
		return "+";
	case AddC:
		return "+_";
	case Sub:
		return "-";
	case Mult:
		return "*";
	case Div:
		return "/";
	case SDiv:
		return "s/";
	case Rem:
		return "rem";
	case SRem:
		return "srem";
	case SMod:
		return "s%";
	case Eq:
		return "==";
	case NotEq:
		return "!=";
	case Gr:
		return ">";
	case SGr:
		return "s>";
	case Le:
		return "<";
	case SLe:
		return "s<";
	case GrEq:
		return ">=";
	case SGrEq:
		return "s>=";
	case LeEq:
		return "<=";
	case SLeEq:
		return "s<=";
	case Sext:
		return "sext";
	case Zext:
		return "zext";
	case BitWiseAnd:
		return "&";
	case BitWiseOr:
		return "|";
	case BitWiseNot:
		return "~";
	case BitWiseXor:
		return "^";
	case BitWiseXNor:
		return "~^";
	case BitWiseNor:
		return "~|";
	case BitWiseNand:
		return "~&";
	case LogXor:
		return "^";
	case LogXNor:
		return "~^";
	case LogAnd:
		return "&&";
	case LogOr:
		return "||";
	case LogNor:
		return "~|";
	case LogNand:
		return "~&";
	case LogNot:
		return "!";
	case Minus:
		return "-";
	case ReductionAnd:
		return "&";
	case ReductionOr:
		return "|";
	case ReductionXor:
		return "^";
	case ReductionXNor:
		return "~^";
	case ReductionNand:
		return "~&";
	case ReductionNor:
		return "~|";
	case ShiftL:
		return "<<";
	case ShiftR:
		return ">>";
	case AShiftR:
		return ">>>";
	case AShiftL:
		return "<<<";
	case RotateL:
		return "RotL";
	case RotateR:
		return "RotR";
	case VShiftL:
		return "<<_v";
	case VShiftR:
		return ">>_v";
	case VAShiftL:
		return "<<<_v";
	case VAShiftR:
		return ">>>_v";
	case VRotateL:
		return "RotL_v";
	case VRotateR:
		return "RotR_v";
	case VEx:
		return "Ex_v";
	case Concat:
		return "{}";
	case Ternary:
		return "?:";
	case ArrayConst:
		return "array";
	case ArraySelect:
		return "select";
	case ArrayStore:
		return "store";
	case IntAdd:
		return "i+";
	case IntSub:
		return "i-";
	case IntMult:
		return "i*";
	case IntDiv:
		return "i/";
	case IntFloor:
		return "floor";
	case IntLe:
		return "i<";
	case IntLeEq:
		return "i<=";
	case IntGr:
		return "i>";
	case IntGrEq:
		return "i>=";
	case IntMod:
		return "i%";
	case IntMinus:
		return "i-";
	case Future:
		return "future";
	default:
		AVR_COUT << t << endl;
		assert(0);
	}
	assert(0);
	return "";
}

void OpInst::print(ostream&out) {
	if (m_op == Future) {
		out << op2str(m_op) << "(";
		assert(m_exps.size() == 1);
		out << *(*(m_exps.begin()));
		out << ")";
	} else if (m_op == Concat) {
	  if (Inst::print_concrete) {
      out << "{";
      InstL::reverse_iterator it = m_exps.rbegin();
      out << *(*it);
      it++;
      for (InstL::reverse_iterator end_it = m_exps.rend(); it != end_it; ++it)
        out << " , " << *(*it);
      out << "}";
	  }
	  else {
      out << get_euf_func_name() << "(";
      InstL::reverse_iterator it = m_exps.rbegin();
      InstL::reverse_iterator it_old = it;
      out << *(*it);
      it++;
      for (InstL::reverse_iterator end_it = m_exps.rend(); it != end_it; )
      {
        if ((*it) != (*it_old))
          out << " , " << *(*it);
        it_old = it;
        it++;
      }
      out << ")";
	  }
	} else if (m_op == Ternary) {
		assert(m_exps.size() == 3);
		InstL::iterator it = m_exps.begin();
		out << "(";
		out << *(*it);
		out << "?";
		it++;
		out << *(*it);
		out << ":";
		it++;
		out << *(*it);
		out << ")";
	} else if (m_op == LogAnd || m_op == LogOr) {
		InstL::iterator it = m_exps.begin();
//		out << "(" << endl << "	" << *(*it);
		out << "(" << *(*it);
		it++;
		for (InstL::iterator end_it = m_exps.end(); it != end_it; ++it) {
//			out << " " << op2str(m_op) << " " << endl << "	" << *(*it);
			out << " " << op2str(m_op) << " " << *(*it);
		}
		out << ")";
	} else if (m_op == Eq || m_op == NotEq) {
		assert(m_exps.size() == 2);
		InstL::iterator it = m_exps.begin();
//		out << "(" << endl << "	" << *(*it);
		out << "(" << *(*it);
		it++;
		out << " " << op2str(m_op) << " " << *(*it);
		out << ")";
	} else {
	  string name = Inst::print_concrete ? "0" : get_euf_func_name();
		if (name != "0")
		{
			InstL::iterator it = m_exps.begin();
			out << name << "(" << *(*it);
			it++;

			for (InstL::iterator end_it = m_exps.end(); it != end_it; ++it) {
				out << ", " << *(*it);
			}
			out << ")";
		}
		else
		{
			unsigned sz = m_exps.size();
			if (m_op == ArraySelect) {
				InstL::iterator it = m_exps.begin();
				out << *(*it);
				it++;
				out << "[ ";
				for (InstL::iterator end_it = m_exps.end(); it != end_it; ++it) {
					out << *(*it) << " ";
				}
				out << "]";
			}
			else if (m_op == ArrayConst || m_op == ArrayStore) {
				InstL::iterator it = m_exps.begin();
				out << op2str(m_op) << "(" << *(*it);
				it++;

				for (InstL::iterator end_it = m_exps.end(); it != end_it; ++it) {
					out << ", " << *(*it);
				}
				out << ")";
			}
			else {
				assert(sz != 0);
				InstL::iterator it = m_exps.begin();
				out << op2str(m_op) << "(" << *(*it);
				it++;

				for (InstL::iterator end_it = m_exps.end(); it != end_it; ++it) {
					out << ", " << *(*it);
				}
				out << ")";
			}
		}
	}
}

void OpInst::print_summary(ostream&out) {
	Inst::print_summary(out);
	out << op2str(get_op()) << endl;
}

void OpInst::print_verilog(ostream&out) {
	Inst::print_verilog(out);
	if (m_op == Future) {
		assert(0);
	} else if (m_op == Concat) {
		out << "{";
		InstL::reverse_iterator it = m_exps.rbegin();
		(*it)->print_verilog_name(out);
		it++;
		for (InstL::reverse_iterator end_it = m_exps.rend(); it != end_it; ++it) {
			out << " , ";
			(*it)->print_verilog_name(out);
		}
		out << "}";
	} else if (m_op == Ternary) {
		assert(m_exps.size() == 3);
		InstL::iterator it = m_exps.begin();
		(*it)->print_verilog_name(out);
		out << "?";
		it++;
		(*it)->print_verilog_name(out);
		out << ":";
		it++;
		(*it)->print_verilog_name(out);
	} else {
		unsigned sz = m_exps.size();
		if (sz == 1) {
			out << op2str(m_op);
			ostringstream ss;
			(*(m_exps.begin()))->print_verilog_name(ss);
			if ((*(m_exps.begin()))->get_type() == Op || (*(m_exps.begin()))->get_type() == Ex) {
				out << "(" << ss.str() << ")";
			} else
				out << ss.str();
		} else {
			assert(sz != 0);
			// for add and subtract, substitute the constant.
			// allows Vapor to use succ/pred for UCLID
			if ((m_op == OpInst::Add || m_op == OpInst::Sub) && sz == 2) {
				InstL::iterator it = m_exps.begin(), it2 = m_exps.begin();
				it2++;
				if ((*it2)->get_type() == Num) {
					(*it)->print_verilog_name(out);
					out << " " << op2str(m_op) << " " << *(*it2) << ";" << endl;
					return;
				}
			}
			InstL::iterator it = m_exps.begin();
			out << "(";
			(*it)->print_verilog_name(out);
			it++;
			for (InstL::iterator end_it = m_exps.end(); it != end_it; ++it) {
				out << " " << op2str(m_op) << " ";
				(*it)->print_verilog_name(out);
			}
			out << ")";
		}
	}
	out << ";" << endl;
}

void MemInst::print(ostream&out) {
	switch (m_memtype) {
	case Init: {
		out << "MEM_INIT(";
		for (InstL::iterator it = m_ports.begin(), end_it = m_ports.end(); it != end_it;) {
			InstL::iterator it2 = it;
			it2++;
			if (it2 != m_ports.end()) {
				out << "<" << *(*it) << ",";
				it++;
				out << *(*it) << ">,";
				it++;
			} else {
				out << *(*it);
			}
		}
		out << ")";
	}
		break;
	case Read:
		out << m_name << "[" << *(*(m_ports.begin())) << "]";
		break;
	case Write: {
		out << "MEM_WRITE(";
		for (InstL::iterator it = m_ports.begin(), end_it = m_ports.end(); it != end_it;) {
			if (it != m_ports.begin())
				out << ",";
			out << "<" << *(*(it++));
			out << "," << *(*(it++));
			out << "," << *(*(it++)) << ">";
		}
		out << ")";
	}
		break;
	default:
		assert(0);
	}
}

void MemInst::print_verilog(ostream&out) {
	assert(0);
}

void UFInst::print(ostream&out) {
	out << m_name << "(";
	InstL::iterator it = m_children.begin();
	out << *(*it++);
	for (InstL::iterator end_it = m_children.end(); it != end_it; ++it)
		out << "," << *(*it);
	out << ")";
}

void UFInst::print_verilog(ostream&out) {
// 	Inst::print_verilog(out);
// 	string op = "";
// 	if (m_children.size() == 1) {
// 		op = "~";
// 		out << op;
// 		(*(m_children.begin()))->print_verilog_name(out);
// 		ostringstream str;
// 		str << "Using " << op << " to replace a 1-arity UF";
// 		AVR_COUT << str.str() << endl;
// 	} else if (m_children.size() == 2) {
// 		op = "+";
// 		InstL::iterator it = m_children.begin(), it2 = m_children.begin();
// 		it2++;
// 		(*it)->print_verilog_name(out);
// 		out << op;
// 		(*it2)->print_verilog_name(out);
// 		ostringstream str;
// 		str << "Using " << op << " to replace a 1-arity UF";
// 		AVR_COUT << str.str() << endl;
// 	} else
// 		assert(0);
// 	// otherwise, use other operators that return 1-bit so that
// 	// they'll be modeled as UPs
// 	assert(get_size() > 1);
// 	assert(op != "");
// 	out << ";" << endl;
}

Inst* Inst::apply_children(InstL&args) {
	assert(!args.empty());
	switch (get_type()) {
	case Sig:
	case Num:
		return this;
		break;
	case Wire: {
//		cout << *this << " -> " << args << endl;
		assert(args.size() == 1);
		return args.front();
		assert(0);
	}
		break;
	case Op: {
		OpInst* op = OpInst::as(this);
		assert(op != 0);
		unsigned sz = op->get_size();

		Inst* newTve = OpInst::create(op->get_op(), args, m_size);
//		if (newTve->get_size() != sz)
//		{
//			cout << "Op: " << op->get_op() << endl;
//			cout << "Ch: " << args << endl;
//			cout << m_size << endl;
//			cout << "Op: " << *op << endl;
//			cout << "Ne: " << *newTve << endl;
//		}
		assert(newTve->get_size() == sz);

		if (newTve->childrenInfo[CONST])
			newTve->ve_sim_orig = this;
		return newTve;
	}
		break;
	case Ex: {
		ExInst* ex = ExInst::as(this);
		assert(ex != 0);
		Inst* newTve = ExInst::create(*(args.begin()), ex->get_hi(), ex->get_lo());

		if (newTve->childrenInfo[CONST])
			newTve->ve_sim_orig = this;
		return newTve;
	}
		break;
	case Mem: {
		MemInst* mem = MemInst::as(this);
		assert(mem != 0);
		Inst* newTve = MemInst::create(mem->get_name(), mem->get_size(), mem->get_mem_type(), args);

		if (newTve->childrenInfo[CONST])
			newTve->ve_sim_orig = this;
		return newTve;
	}
		break;
	case UF: {
		UFInst* uf = UFInst::as(this);
		assert(uf != 0);
		Inst* newTve = UFInst::create(uf->get_name(), uf->get_size(), args);

		if (newTve->childrenInfo[CONST])
			newTve->ve_sim_orig = this;
		return newTve;
	}
	default:
		assert(0);
	}
	assert(0);
	return 0;
}

void Trans::read_bin(std::istream&in) {
	st_in = &in;

	int ver = read_int();

	if (ver != static_cast<int> (WN_VERSION * 10)) {
		AVR_COUT << "WRN: incompatible wn version, file: " << ver / 10.0 << ", reach: ";
		AVR_COUT << static_cast<int> (WN_VERSION * 10) / 10.0 << endl;
	}

	m_module_name = read_str();
	m_input_ports.clear();
	int num_input_ports = read_int();
	for (int i = 0; i < num_input_ports; i++) {
		Port t_p;
		t_p.port_name = read_str();
		t_p.msb = read_int();
		t_p.lsb = read_int();
		m_input_ports.push_back(t_p);
	}
	m_output_ports.clear();
	int num_output_ports = read_int();
	for (int i = 0; i < num_output_ports; i++) {
		Port t_p;
		t_p.port_name = read_str();
		t_p.msb = read_int();
		t_p.lsb = read_int();
		m_output_ports.push_back(t_p);
	}

	st_id_to_ptr.clear();
	clear();

	int nodes_num = read_int();

	// read types & construct nodes
	for (int i = 0; i < nodes_num; i++) {
		Inst* e = 0;
		switch (static_cast<InstType> (read_int())) {
		case Sig:
			e = SigInst::read_bin();
			break;
		case Num:
			e = NumInst::read_bin();
			break;
		case Op:
			e = OpInst::read_bin();
			break;
		case Ex:
			e = ExInst::read_bin();
			break;
		case Mem:
			e = MemInst::read_bin();
			break;
		case UF:
			e = UFInst::read_bin();
			break;
		default:
			assert(0);
		}
		assert(e != 0);
		st_id_to_ptr.push_back(e);
	}

	// now read NSF
	int sz = read_int();
	for (int i = 0; i < sz; i++) {
		TransElem e;
		e.lhs = Trans::id_to_ptr(read_int());
		e.rhs = Trans::id_to_ptr(read_int());
		e.type = read_int();
		push_back(e);
	}
}

void Trans::write_bin(std::ostream &out) {
	st_out = &out;

	write_int(static_cast<int> (WN_VERSION * 10));

	write_str( m_module_name);
	write_int(m_input_ports.size());
	for (size_t i = 0; i < m_input_ports.size(); i++) {
		write_str(m_input_ports[i].port_name);
		write_int(m_input_ports[i].msb);
		write_int(m_input_ports[i].lsb);
	}
	write_int(m_output_ports.size());
	for (size_t i = 0; i < m_output_ports.size(); i++) {
		write_str(m_output_ports[i].port_name);
		write_int(m_output_ports[i].msb);
		write_int(m_output_ports[i].lsb);
	}

	st_ptr_to_id.clear();

	reachable.clear();
	Inst::init_visit();

	// collect nodes in the NSF
	for (iterator it = begin(), end_it = end(); it != end_it; ++it) {
		collect_reachable((*it).lhs);
		collect_reachable((*it).rhs);
	}

	write_int(reachable.size());

	// writes types
	unsigned i = 0;
	for (InstL::iterator it = reachable.begin(), end_it = reachable.end(); it != end_it; ++it, i++) {
		Trans::write_int(static_cast<int> ((*it)->get_type()));
		(*it)->write_bin();
		st_ptr_to_id.insert(make_pair(*it, i));
	}

	// now write NSF
	write_int( size());
	for (iterator it = begin(), end_it = end(); it != end_it; ++it) {
		write_int(Trans::ptr_to_id((*it).lhs));
		write_int(Trans::ptr_to_id((*it).rhs));
		write_int((*it).type);
	}
}

void Inst::write_bin() {
	Trans::write_int( m_size);
}

void SigInst::write_bin() {
	Trans::write_sort( m_sort);
	Trans::write_int( m_size);
	Trans::write_str( m_name);
}
void NumInst::write_bin() {
	Trans::write_sort( m_sort);
	Trans::write_int( m_size);
	Trans::write_str( m_mpz.get_str(2));
}
/// Aman
void WireInst::write_bin() {
	Trans::write_int( m_size);
	Trans::write_str( m_name);
	Trans::write_int(m_exps.size());
	for (InstL::iterator it = m_exps.begin(); it != m_exps.end(); ++it) {
		Trans::write_int(Trans::ptr_to_id(*it));
	}
//	assert(0);
}
void ConstInst::write_bin() {
	Trans::write_int( m_size);
	Trans::write_str( m_name);
	assert(0);
}
/// END
void OpInst::write_bin() {
	Trans::write_sort( m_sort);
	Trans::write_int(static_cast<unsigned> (m_op));
	Trans::write_int( m_size);
	Trans::write_int(m_exps.size());
	for (InstL::iterator it = m_exps.begin(); it != m_exps.end(); ++it) {
		Trans::write_int(Trans::ptr_to_id(*it));
	}
}
void ExInst::write_bin() {
	Trans::write_int(Trans::ptr_to_id(get_exp()));
	Trans::write_int( m_hi);
	Trans::write_int( m_lo);
}
void MemInst::write_bin() {
	Trans::write_int( m_size);
	Trans::write_str( m_name);
	Trans::write_int( m_memtype);
	Trans::write_int(m_ports.size());
	for (InstL::iterator it = m_ports.begin(); it != m_ports.end(); ++it) {
		Trans::write_int(Trans::ptr_to_id(*it));
	}
}
void UFInst::write_bin() {
	Trans::write_int( m_size);
	Trans::write_str( m_name);
	Trans::write_int(m_children.size());
	for (InstL::iterator it = m_children.begin(); it != m_children.end(); ++it) {
		Trans::write_int(Trans::ptr_to_id(*it));
	}
}


Inst *SigInst::read_bin() {
	SORT sort = Trans::read_sort();
	unsigned size = Trans::read_int();
	return SigInst::create(Trans::read_str(), size, sort);
}
Inst *NumInst::read_bin() {
	SORT sort = Trans::read_sort();
	unsigned size = Trans::read_int();
	return NumInst::create(Trans::read_str(), size, 2, sort, true);
}
/// Aman
Inst *WireInst::read_bin() {
	unsigned size = Trans::read_int();
	string name = Trans::read_str();
	unsigned args = Trans::read_int();
	InstL exps;
	for (unsigned i = 0; i < args; ++i) {
		exps.push_back(Trans::id_to_ptr(Trans::read_int()));
	}
	assert(exps.size() == 1);
	return WireInst::create(name, size, exps.front());
}
Inst *ConstInst::read_bin() {
	unsigned size = Trans::read_int();
	assert(0);
	return ConstInst::create(Trans::read_str(), size, NULL, -1, SORT());
}
/// END
Inst *OpInst::read_bin() {
	SORT sort = Trans::read_sort();
	OpType op = static_cast<OpType> (Trans::read_int());
	unsigned size = Trans::read_int();
	unsigned args = Trans::read_int();
	InstL exps;
	for (unsigned i = 0; i < args; ++i) {
		exps.push_back(Trans::id_to_ptr(Trans::read_int()));
	}
	return OpInst::create(op, exps, size, true, NULL, sort);
}
Inst *ExInst::read_bin() {
	Inst *exp = Trans::id_to_ptr(Trans::read_int());
	unsigned hi = Trans::read_int();
	unsigned lo = Trans::read_int();
	return ExInst::create(exp, hi, lo);
}
Inst *MemInst::read_bin() {
	unsigned size = Trans::read_int();
	string name = Trans::read_str();
	MemType memtype = (MemType)(Trans::read_int());
	unsigned sz = Trans::read_int();
	InstL ports;
	for (unsigned i = 0; i < sz; ++i){
		ports.push_back(Trans::id_to_ptr(Trans::read_int()));
	}
	return MemInst::create(name, size, memtype, ports);
}
Inst *UFInst::read_bin() {
	unsigned size = Trans::read_int();
	string name = Trans::read_str();
	unsigned sz = Trans::read_int();
	InstL children;
	for (unsigned i = 0; i < sz; i++){
		children.push_back(Trans::id_to_ptr(Trans::read_int()));
	}
	return UFInst::create(name, size, children);
}

SORT Trans::read_sort() {
	SORT s;
	s.type = static_cast<SortType> (Trans::read_int());
	s.sz = Trans::read_int();
	int nargs = Trans::read_int();
	for (int i = 0; i < nargs; i++)
		s.args.push_back(read_sort());
	return s;
}
void Trans::write_sort(SORT sort) {
	Trans::write_int(static_cast<unsigned> (sort.type));
	Trans::write_int(sort.sz);
	Trans::write_int(sort.args.size());
	for (auto& s: sort.args)
		write_sort(s);
}

int Trans::read_int() {
	int int_value;
	(st_in->read((char *)&int_value, 4));
//	void* res = (st_in->read((char *)&int_value, 4));
//	assert(res != 0);
	return int_value;
}

void Trans::write_int(int value) {
	st_out->write((char *)&value, 4);
}

long long Trans::read_long() {
	long long long_value;
	(st_in->read((char *)&long_value, 8));
//	void* res = (st_in->read((char *)&long_value, 8));
//	assert(res != 0);
	return long_value;
}

void Trans::write_long(long long value) {
	st_out->write((char *)&value, 8);
}

void Trans::write_str(string st) {
	int length = st.size();
	write_int(length);
	for (int i = 0; i < length; i++)
		write_char(st[i]);
}

string Trans::read_str() {
	int length = read_int();
	string st;
	for (int i = 0; i < length; i++)
		st += read_char();
	return st;
}

void Trans::write_char(char value) {
	st_out->write(&value, 1);
}

char Trans::read_char() {
	char value;
	(st_in->read(&value, 1));
//	void* res = (st_in->read(&value, 1));
//	assert(res != 0);
	return value;
}

Inst* Trans::id_to_ptr(unsigned id) {
	assert(id < Trans::st_id_to_ptr.size());
	Inst* res = Trans::st_id_to_ptr[id];
	assert(res != 0);
	return res;
}

unsigned Trans::ptr_to_id(Inst*e) {
	if(e){
		assert(Trans::st_ptr_to_id.find(e) != Trans::st_ptr_to_id.end());
		return st_ptr_to_id[e];
	}
	return -1;
}

void Trans::collect_reachable(Inst*e) {
	assert(e != 0);
	if (e->get_visit())
		return;
	e->set_visit();
	const InstL* children = e->get_children();
	if (!children){
		reachable.push_back(e);
		return;
	}
	for (InstL::const_iterator it = children->begin(); it != children->end(); ++it){
		collect_reachable(*it);
	}
	reachable.push_back(e);
}

void ExInst::calc_size() {
	m_size = m_hi - m_lo + 1;
}

void OpInst::calc_size() {
	switch (m_op) {
	case Unknown:
		m_size = 0;
		break;
	case Extract:
		// do nothing since the inheriting child will compute that
		break;
	case Concat: {
		m_size = 0;
		for (InstL::iterator it = m_exps.begin(), end_it = m_exps.end(); it != end_it; ++it)
			m_size += (*it)->get_size();
	}
		break;
	case Eq:
	case NotEq:
	case Gr:
	case SGr:
	case Le:
	case SLe:
	case GrEq:
	case SGrEq:
	case LeEq:
	case SLeEq:
	case LogNand:
	case LogNor:
	case LogAnd:
	case LogOr:
	case LogNot:
	case LogXor:
	case LogXNor:
	case ReductionAnd:
	case ReductionOr:
	case ReductionXor:
	case ReductionXNor:
	case ReductionNand:
	case ReductionNor:
		m_size = 1;
		break;
	case BitWiseNot:
	case Future:
	case Minus: {
		assert(m_exps.size() == 1);
		InstL::iterator first = m_exps.begin();
		m_size = (*first)->get_size();
	}
		break;
	case Mult:{
#if 1
		m_size = 0;
		for (InstL::iterator it = m_exps.begin(), end_it = m_exps.end(); it != end_it; ++it){
			m_size += (*it)->get_size();
		}
#else
		m_size = 0;
		for (InstL::iterator it = m_exps.begin(), end_it = m_exps.end(); it != end_it; ++it){
			m_size = max(m_size, (*it)->get_size());
		}
		m_size = 2 * m_size;
#endif
		//m_size = 2 * (m_exps.front())->get_size();
	}
		break;
	case Add:
	case Sub:
	case Div:
	case SDiv:
	case Rem:
	case SRem:
	case SMod:
	case BitWiseAnd:
	case BitWiseOr:
	case BitWiseXor:
	case BitWiseXNor:
	case BitWiseNor:
	case BitWiseNand: {
		assert(m_exps.size() >= 2);
		m_size = 0;
		for (InstL::iterator it = m_exps.begin(), end_it = m_exps.end(); it != end_it; ++it)
			m_size = max(m_size, (*it)->get_size());
	}
		break;
	case AddC: {
		assert(m_exps.size() >= 2);
		m_size = 0;
		for (InstL::iterator it = m_exps.begin(), end_it = m_exps.end(); it != end_it; ++it){
			m_size = max(m_size, (*it)->get_size());
		}
		m_size+=1;
	}
		break;
	case RotateL:
	case RotateR:
	case ShiftL:
	case ShiftR:
	case AShiftR:
	case AShiftL:
	{
		assert(m_exps.size() == 2);
		InstL::iterator first = m_exps.begin();
		m_size = (*first)->get_size();
	}
		break;
	case Sext:
	case Zext:
	{
		assert(m_exps.size() == 2);
		InstL::iterator cit = m_exps.begin();
		cit++;
//		assert((*cit)->get_type() == Num);
		m_size = (*cit)->get_size();
		assert(m_size > 0);
		assert(m_size >= m_exps.front()->get_size());
	}
		break;
	case VShiftL:
	case VShiftR:
	case VAShiftL:
	case VAShiftR:
	case VRotateL:
	case VRotateR:{
		InstL::iterator first = m_exps.begin();
		m_size = (*first)->get_size();
	}
		break;
	case VEx:
		m_size = 1;
		break;
	case Ternary: {
		assert(m_exps.size() == 3);
		InstL::iterator second = m_exps.begin(), first = m_exps.begin();
		second++;
		m_size = (*second)->get_size();
		m_sort = (*second)->get_sort();
	}
		break;
	case ArrayConst: {
		assert(m_exps.size() == 2);
		InstL::iterator cit = m_exps.begin();
		assert((*cit)->get_type() == Num);
		unsigned width = NumInst::as(*cit)->get_num();
		cit++;
		assert((*cit)->get_type() == Num);
		m_size = (*cit)->get_size();
		m_sort.sz = m_size;
		unsigned range = m_size;
		assert(range > 0);

		m_sort.type = arraytype;
		m_sort.args.clear();
		m_sort.args.push_back(SORT(width));
		m_sort.args.push_back(SORT(range));
		assert(m_size > 0);
		assert(m_sort.sz > 0);
	}
		break;
	case ArraySelect: {
		assert(m_exps.size() == 2);
		InstL::iterator first = m_exps.begin();
		assert((*first)->get_sort_type() == arraytype);
		m_sort = *(*first)->get_sort_range();
		m_size = (*first)->get_sort_range()->sz;
	}
		break;
	case ArrayStore: {
		assert(m_exps.size() == 3);
		InstL::iterator first = m_exps.begin();
		assert((*first)->get_sort_type() == arraytype);
		m_sort = (*first)->get_sort();
		m_size = (*first)->get_size();
	}
		break;
	case IntAdd:
	case IntSub:
	case IntMult:
	case IntDiv:
	case IntMod:
	{
		assert(m_exps.size() == 2);
		InstL::iterator first = m_exps.begin();
		m_sort = (*first)->get_sort();
		m_size = (*first)->get_size();
		assert(m_size == INT_SZ);
		assert(m_sort.type == inttype);
	}
		break;
	case IntFloor:
	case IntMinus:
	{
		assert(m_exps.size() == 1);
		InstL::iterator first = m_exps.begin();
		m_sort = (*first)->get_sort();
		m_size = (*first)->get_size();
		assert(m_size == INT_SZ);
		assert(m_sort.type == inttype);
	}
		break;
	case IntLe:
	case IntLeEq:
	case IntGr:
	case IntGrEq:
	{
		assert(m_exps.size() == 2);
		InstL::iterator first = m_exps.begin();
		m_sort = SORT();
		m_size = 1;
	}
		break;
	default:
		AVR_COUT << op2str(m_op) << endl;
		assert(0);
	}
}

unsigned find_size(OpInst::OpType op, InstL& exps)
{
	unsigned size;
	switch (op) {
	case OpInst::Unknown:
		size = 0;
		break;
	case OpInst::Extract:
		// do nothing since the inheriting child will compute that
		break;
	case OpInst::Concat: {
		size = 0;
		for (InstL::iterator it = exps.begin(), end_it = exps.end(); it != end_it; ++it)
			size += (*it)->get_size();
	}
		break;
	case OpInst::Eq:
	case OpInst::NotEq:
	case OpInst::Gr:
	case OpInst::SGr:
	case OpInst::Le:
	case OpInst::SLe:
	case OpInst::GrEq:
	case OpInst::SGrEq:
	case OpInst::LeEq:
	case OpInst::SLeEq:
	case OpInst::LogNand:
	case OpInst::LogNor:
	case OpInst::LogAnd:
	case OpInst::LogOr:
	case OpInst::LogNot:
	case OpInst::LogXor:
	case OpInst::LogXNor:
	case OpInst::ReductionAnd:
	case OpInst::ReductionOr:
	case OpInst::ReductionXor:
	case OpInst::ReductionXNor:
	case OpInst::ReductionNand:
	case OpInst::ReductionNor:
		size = 1;
		break;
	case OpInst::BitWiseNot:
	case OpInst::Future:
	case OpInst::Minus: {
		assert(exps.size() == 1);
		InstL::iterator first = exps.begin();
		size = (*first)->get_size();
	}
		break;
	case OpInst::Mult:{
#if 1
		size = 0;
		for (InstL::iterator it = exps.begin(), end_it = exps.end(); it != end_it; ++it){
			size += (*it)->get_size();
		}
#else
		m_size = 0;
		for (InstL::iterator it = m_exps.begin(), end_it = m_exps.end(); it != end_it; ++it){
			m_size = max(m_size, (*it)->get_size());
		}
		m_size = 2 * m_size;
#endif
		//m_size = 2 * (m_exps.front())->get_size();
	}
		break;
	case OpInst::Add:
	case OpInst::Sub:
	case OpInst::Div:
	case OpInst::SDiv:
	case OpInst::Rem:
	case OpInst::SRem:
	case OpInst::SMod:
	case OpInst::BitWiseAnd:
	case OpInst::BitWiseOr:
	case OpInst::BitWiseXor:
	case OpInst::BitWiseXNor:
	case OpInst::BitWiseNor:
	case OpInst::BitWiseNand: {
		assert(exps.size() >= 2);
		size = 0;
		for (InstL::iterator it = exps.begin(), end_it = exps.end(); it != end_it; ++it)
			size = max(size, (*it)->get_size());
	}
		break;
	case OpInst::AddC: {
		assert(exps.size() >= 2);
		size = 0;
		for (InstL::iterator it = exps.begin(), end_it = exps.end(); it != end_it; ++it){
			size = max(size, (*it)->get_size());
		}
		size+=1;
	}
		break;
	case OpInst::RotateL:
	case OpInst::RotateR:
	case OpInst::ShiftL:
	case OpInst::ShiftR:
	case OpInst::AShiftR:
	case OpInst::AShiftL:
	{
		assert(exps.size() == 2);
		InstL::iterator first = exps.begin();
		size = (*first)->get_size();
	}
		break;
	case OpInst::Sext:
	case OpInst::Zext:
	{
		assert(exps.size() == 2);
		InstL::iterator cit = exps.begin();
		cit++;
//		assert((*cit)->get_type() == Num);
		size = (*cit)->get_size();
		assert(size > 0);
		assert(size >= exps.front()->get_size());
	}
		break;
	case OpInst::VShiftL:
	case OpInst::VShiftR:
	case OpInst::VAShiftL:
	case OpInst::VAShiftR:
	case OpInst::VRotateL:
	case OpInst::VRotateR:{
		InstL::iterator first = exps.begin();
		size = (*first)->get_size();
	}
		break;
	case OpInst::VEx:
		size = 1;
		break;
	case OpInst::Ternary: {
		assert(exps.size() == 3);
		InstL::iterator second = exps.begin(), first = exps.begin();
		second++;
		size = (*second)->get_size();
	}
		break;
	case OpInst::ArrayConst: {
		assert(exps.size() == 2);
		InstL::iterator first = exps.begin();
		InstL::iterator second = exps.begin();
		second++;
		assert((*first)->get_type() == Num);
		assert((*second)->get_type() == Num);
		size = (*second)->get_size();
		assert (size > 0);
	}
		break;
	case OpInst::ArraySelect: {
		assert(exps.size() == 2);
		InstL::iterator first = exps.begin();
		assert((*first)->get_sort_type() == arraytype);
		size = (*first)->get_sort_range()->sz;
	}
		break;
	case OpInst::ArrayStore: {
		assert(exps.size() == 3);
		InstL::iterator first = exps.begin();
		assert((*first)->get_sort_type() == arraytype);
		size = (*first)->get_size();
	}
		break;
	case OpInst::IntAdd:
	case OpInst::IntSub:
	case OpInst::IntMult:
	case OpInst::IntDiv:
	case OpInst::IntMod:
	{
		assert(exps.size() == 2);
		InstL::iterator first = exps.begin();
		size = (*first)->get_size();
		assert(size == INT_SZ);
	}
		break;
	case OpInst::IntFloor:
	case OpInst::IntMinus:
	{
		assert(exps.size() == 1);
		InstL::iterator first = exps.begin();
		size = (*first)->get_size();
		assert(size == INT_SZ);
	}
		break;
	case OpInst::IntLe:
	case OpInst::IntLeEq:
	case OpInst::IntGr:
	case OpInst::IntGrEq:
	{
		assert(exps.size() == 2);
		InstL::iterator first = exps.begin();
		size = 1;
	}
		break;
	default:
		AVR_COUT << OpInst::op2str(op) << endl;
		assert(0);
	}
	return size;
}

Inst* ExInst::get_exp() {
	assert(m_exps.size() == 1);
	return *(m_exps.begin());
}

void Trans::push_back(const TransElem&e) {
	if (e.lhs->get_size() != e.rhs->get_size()) {
		assert(0);
// 		AVR_COUT << "Incompatible LHS/RHS sizes: \n";
// 		AVR_COUT << *(e.lhs) << " is of size " << e.lhs->get_size() << "\n";
// 		AVR_COUT << *(e.rhs) << " is of size " << e.rhs->get_size() << "\n";
	}
	if (e.type == 1) {
		string name = "";
		if (e.lhs->get_type() == Sig)
			name = SigInst::as(e.lhs)->get_name();
		if (e.lhs->get_type() == Ex) {
			Inst* son = ExInst::as(e.lhs)->get_exp();
			if (son->get_type() == Sig)
				name = SigInst::as(son)->get_name();
		}
		if (name == "") {
			AVR_COUT << *(e.lhs) << endl;
			assert(0);
		}
		m_wires.insert(name);
	}
	TransElemL::push_back(e);
}

void Trans::simplify() {
	return;
	/*  for(iterator it = begin() , end_it = end();
	 it != end_it ; ++it){
	 (*it).lhs = (*it).lhs->simplify();
	 (*it).rhs = (*it).rhs->simplify();
	 }*/
}

Inst* Inst::finalize_simplify(Inst*e1, Inst*e2, InstL masked) {
	return e2;
}

Inst* Inst::get_node(unsigned id) {
	for (InstL::iterator it = m_exps_pool.begin(), end_it = m_exps_pool.end(); it != end_it; ++it)
		if ((*it)->get_id() == id)
			return *it;
	assert(0);
	return 0;
}

string Inst::get_euf_func_name(){
	string euf_func_name;
	ExInst *ex_inst = ExInst::as(this);
	OpInst *op_inst = OpInst::as(this);
	if(ex_inst){
		euf_func_name = ex_inst->get_euf_func_name();
	}else if(op_inst){
		euf_func_name = op_inst->get_euf_func_name();
	}else{
		euf_func_name = "0";
	}
	return euf_func_name;
}

bool Trans::check_consistency() {
	for (iterator it = begin(), end_it = end(); it != end_it; ++it) {
		if (!((*it).lhs->check_consistency(AVR_COUT))) {
			AVR_COUT << "In assignment: " << *((*it).lhs) << " = " << *((*it).rhs) << endl;
			return false;
		}
		if (!((*it).rhs->check_consistency(AVR_COUT))) {
			AVR_COUT << "In assignment: " << *((*it).lhs) << " = " << *((*it).rhs) << endl;
			return false;
		}
	}
	return true;
}

bool SigInst::is_similar(Inst* e) {
	if (!(Inst::is_similar(e)))
		return false;
	SigInst* sig = SigInst::as(e);
	assert(sig != 0);
	return (sig->get_name() == m_name);
}

bool NumInst::is_similar(Inst* e) {
	if (!(Inst::is_similar(e)))
		return false;
	NumInst* n = NumInst::as(e);
	assert(n != 0);
	return (*(n->get_mpz()) == m_mpz);
}

/// Aman
bool WireInst::is_similar(Inst* e) {
	if (!(Inst::is_similar(e)))
		return false;
	WireInst* c = WireInst::as(e);
	assert(c != 0);
	return (c->get_name() == m_name);
}

bool ConstInst::is_similar(Inst* e) {
	if (!(Inst::is_similar(e)))
		return false;
	ConstInst* c = ConstInst::as(e);
	assert(c != 0);
	return (c->get_name() == m_name);
}
/// END

bool OpInst::is_similar(Inst* e) {
	if (!(Inst::is_similar(e)))
		return false;
	OpInst* op = OpInst::as(e);
	assert(op != 0);
	if (m_op != op->get_op())
		return false;
	const InstL& exps = op->get_exps();
	if (exps.size() != m_exps.size())
		return false;
	for (InstL::const_iterator it = m_exps.begin(), end_it = m_exps.end(), o_it = exps.begin(); it != end_it; ++it, ++o_it)
		if (!(*it)->is_similar(*o_it))
			return false;
	return true;
}

bool ExInst::is_similar(Inst* e) {
	if (!(Inst::is_similar(e)))
		return false;
	ExInst* ex = ExInst::as(e);
	assert(ex != 0);
	unsigned hi = ex->get_hi();
	if (m_hi != hi)
		return false;
	unsigned lo = ex->get_lo();
	if (m_lo != lo)
		return false;
	Inst* exp = ex->get_exp();
	if (!(get_exp()->is_similar(exp)))
		return false;
	return true;
}

bool UFInst::is_similar(Inst* e) {
	if (!(Inst::is_similar(e)))
		return false;
	UFInst* uf = UFInst::as(e);
	assert(uf != 0);
	if (m_name != uf->get_name())
		return false;
	const InstL* exps = uf->get_children();
	assert(exps != 0);
	if (exps->size() != m_children.size())
		return false;
	for (InstL::const_iterator it = m_children.begin(), end_it = m_children.end(), o_it = exps->begin(); it != end_it; ++it, ++o_it)
		if (!(*it)->is_similar(*o_it))
			return false;
	return true;
}

bool MemInst::is_similar(Inst* e) {
	if (!(Inst::is_similar(e)))
		return false;
	MemInst* mem = MemInst::as(e);
	assert(mem != 0);
	if (m_name != mem->get_name())
		return false;
	if (m_memtype != mem->get_mem_type())
		return false;
	const InstL* exps = mem->get_children();
	assert(exps != 0);
	if (exps->size() != m_ports.size())
		return false;
	for (InstL::const_iterator it = m_ports.begin(), end_it = m_ports.end(), o_it = exps->begin(); it != end_it; ++it, ++o_it)
		if (!(*it)->is_similar(*o_it))
			return false;
	return true;
}

Inst* Inst::replace_child(Inst*src, Inst*tgt) {
	assert(src != 0);
	assert(tgt != 0);
	if (is_similar(src))
		return tgt;
	Inst* res = this;
	const InstL* ch = get_children();
	if (ch) {
		bool changed = false;
		InstL newl;
		for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it) {
			Inst* e = (*it)->replace_child(src, tgt);
			newl.push_back(e);
			changed = changed || (e != *it);
		}
		if (changed)
			res = apply_children(newl);
	}
	assert(res != 0);
	return res;
}

int Inst::instcmp(Inst* e) {
	InstType t = get_type();
	InstType t2 = e->get_type();
	if (t < t2)
		return -1;
	else if (t > t2)
		return 1;
	else if (m_size < e->get_size())
		return -1;
	else if (m_size > e->get_size())
		return 1;
	else
		return 0;
}

int SigInst::instcmp(Inst* e) {
	int cmp = Inst::instcmp(e);
	if (cmp != 0)
		return cmp;
	SigInst* sig = SigInst::as(e);
	assert(sig != 0);
	return strcmp(m_name.c_str(), sig->get_name().c_str());
}

int NumInst::instcmp(Inst* e) {
	int cmp = Inst::instcmp(e);
	if (cmp != 0)
		return cmp;
	NumInst* num = NumInst::as(e);
	assert(num != 0);
	return m_mpz < *(num->get_mpz());
}

// string NumInst::get_string_num() {
// 	return m_mpz.get_str(10);
// }

/// Aman
int WireInst::instcmp(Inst* e) {
	int cmp = Inst::instcmp(e);
	if (cmp != 0)
		return cmp;
	WireInst* c = WireInst::as(e);
	assert(c != 0);
	return strcmp(m_name.c_str(), c->get_name().c_str());
}

int ConstInst::instcmp(Inst* e) {
	int cmp = Inst::instcmp(e);
	if (cmp != 0)
		return cmp;
	ConstInst* c = ConstInst::as(e);
	assert(c != 0);
	return strcmp(m_name.c_str(), c->get_name().c_str());
}
/// END

int OpInst::instcmp(Inst* e) {
	int cmp = Inst::instcmp(e);
	if (cmp != 0)
		return cmp;
	OpInst* op = OpInst::as(e);
	assert(op != 0);

	if (m_op < op->get_op())
		return -1;
	else if (m_op > op->get_op())
		return 1;

	const InstL* ch1 = get_children();
	const InstL* ch2 = e->get_children();

	if (ch1->size() < ch2->size())
		return -1;
	else if (ch1->size() > ch2->size())
		return 1;

	InstL::const_iterator it = ch1->begin(), end_it = ch1->end(), it2 = ch2->begin();

	for (; it != end_it; ++it, ++it2) {
		int cmp = (*it)->instcmp(*it2);
		if (cmp != 0)
			return cmp;
	}
	return 0;
}

int ExInst::instcmp(Inst* e) {
	int cmp = Inst::instcmp(e);
	if (cmp != 0)
		return cmp;
	ExInst* ex = ExInst::as(e);
	assert(ex != 0);

	if (m_hi < ex->get_hi())
		return -1;
	else if (m_hi > ex->get_hi())
		return 1;

	if (m_lo < ex->get_lo())
		return -1;
	else if (m_lo > ex->get_lo())
		return 1;

	return get_exp()->instcmp(ex->get_exp());
}

int UFInst::instcmp(Inst* e) {
	int cmp = Inst::instcmp(e);
	if (cmp != 0)
		return cmp;
	UFInst* uf = UFInst::as(e);
	assert(uf != 0);

	int namecmp = strcmp(m_name.c_str(), uf->get_name().c_str());
	if (namecmp != 0)
		return namecmp;

	const InstL* ch1 = get_children();
	const InstL* ch2 = e->get_children();

	if (ch1->size() < ch2->size())
		return -1;
	else if (ch1->size() > ch2->size())
		return 1;

	InstL::const_iterator it = ch1->begin(), end_it = ch1->end(), it2 = ch2->begin();

	for (; it != end_it; ++it, ++it2) {
		int cmp = (*it)->instcmp(*it2);
		if (cmp != 0)
			return cmp;
	}
	return 0;
}

void Inst::serve(RecService*srv) {
	serve(srv, true);
}

void Inst::serve(RecService*srv, bool init) {
	if (init) {
		init_visit();
	}

	if (get_visit())
		return;
	set_visit();

	if (!(srv->postorder))
		srv->serve(this);

	const InstL* ch = get_children();
	if (ch) {
		for (InstL::const_iterator it = ch->begin(), end_it = ch->end(); it != end_it; ++it)
			(*it)->serve(srv, false);
	}

	if (srv->postorder)
		srv->serve(this);
}

Inst* LambdaInst::create(InstL lambdas, Inst*arg, unsigned size) {
	for (InstL::iterator it = lambdas.begin(), end_it = lambdas.end(); it != end_it; ++it)
		assert(*it);
	assert(arg);
	InstL l = lambdas;
	l.push_back(arg);
	LambdaInst* e = new LambdaInst(l, size);
	m_exps_pool.push_back(e);
	unsigned hash = 0;
	for (InstL::iterator it = l.begin(), end_it = l.end(); it != end_it; ++it)
		hash += (*it)->get_hash1();
	e->set_hash1(hash);
	return e;
}

Inst* ArrayInst::create(string name, unsigned size) {
	ArrayInst* e = new ArrayInst(name, size);
	m_exps_pool.push_back(e);
	e->set_hash1(1);
	return e;
}

void LambdaInst::print(ostream&out) {
	assert(m_children.size() >= 2);
	out << "Lambda(";
	InstL::iterator it = m_children.begin();
	out << *(*it++);
	InstL::iterator end_it = m_children.end();
	end_it--;
	for (; it != end_it; ++it)
		out << "," << *(*it);
	out << ")." << *(*end_it);

}

void ArrayInst::print(ostream&out) {
	out << m_name;
}


//####################################################################
//DUMP_BLIF
//####################################################################
string Inst::get_blif_name() {
	ostringstream ss;
	ss << "n" << get_id();
	return ss.str();
}

string SigInst::get_blif_name() {
	return m_name;
}

string Inst::blif_suffix(unsigned idx) {
	ostringstream ss;
	ss << "_" << idx;
	return ss.str();
}

void TransElem::print_blif_latch(ostream&out, string edge, string q, unsigned q_width, string d, unsigned d_width, string clk, string init) {
	//TODO currently, edge is ignored
	assert(q_width == d_width);
	if (q_width == 1) {
		out << ".latch " << d << " " << q;
		if (init != "3"){
			out << " " << init;
		}
		out << endl;
	} else {
		for (unsigned i = 0; i < q_width; i++) {
			string suffix = Inst::blif_suffix(i);
			if (init.length() == q_width && (init.at(i) == '0' || init.at(i) == '1')) {
				print_blif_latch(out, edge, q + suffix, 1, d + suffix, 1, clk, init.substr(q_width - i - 1, 1));
			} else {
				print_blif_latch(out, edge, q + suffix, 1, d + suffix, 1, clk, init);
			}
		}
	}
}

void SigInst::print_blif(std::ostream& out){
}

void NumInst::print_blif(std::ostream& out){
	out << "# NumInst: " << get_blif_name() << " (val=" << *this << ")" << endl;

	if (get_size() == 1) {
		OpInst::print_blif_table(out, (m_mpz == 1) ? OpInst::LogTrue : OpInst::LogFalse, "", 0, "", 0, "", 0, get_blif_name(), 1);
	} else {
		string tsnum = m_mpz.get_str(2);
		

		if(tsnum[0] == '-'){
			// TODO support negative values (do we need this?)
			tsnum = tsnum.substr(1);
		}
		string extended_snum((m_size - tsnum.length()), '0');
		extended_snum.append(tsnum);
		
		int j = 0;
		for (int i = get_size() - 1; i >= 0; i--, j++) {
			OpInst::OpType opt;
			if (extended_snum[i] == '1') {
				opt = OpInst::LogTrue;
			} else {
				opt = OpInst::LogFalse;	
			}
			OpInst::print_blif_table(out, opt, "", 0, "", 0, "", 0, get_blif_name() + blif_suffix(j), 1);
		}
	}
	out << endl;
}

void WireInst::print_blif(std::ostream& out){
	string i0 = get_port()->get_blif_name();
	string o = get_blif_name();
	if (is_rhs) {
		out << "# WireInst: " << o << " = " << i0 << " [";
		if (get_size() > 1) {
			out << (get_size() - 1) << ":";
		}
		out << "0" << "]" << endl;
	} else {
		out << "# ExInst: " << i0 << " [";
		if (get_size() > 1){
			out << (get_size() - 1) << ":";
		}
		out << "0" << "] = " << get_blif_name() << endl;
	}

	if (get_size() > 1){
		for (unsigned i = 0; i < get_size(); i++) {
			string i0_bname = i0 + blif_suffix(i);
			string o_bname = o + blif_suffix(i);
			if (is_rhs){
				OpInst::print_blif_table(out, OpInst::Identity, i0_bname, 1, "", 0, "", 0, o_bname, 1);
			}else{
				OpInst::print_blif_table(out, OpInst::Identity, o_bname, 1, "", 0, "", 0, i0_bname, 1);
			}
		}
	} else {
		string i0_bname = i0;
//		string i0_bname = i0 + blif_suffix(0);
		if (is_rhs){
			OpInst::print_blif_table(out, OpInst::Identity, i0_bname, 1, "", 0, "", 0, o, 1);
		}else{
			OpInst::print_blif_table(out, OpInst::Identity, o, 1, "", 0, "", 0, i0_bname, 1);
		}
	}
	out << endl;

//	assert(0);
}

void ConstInst::print_blif(std::ostream& out){
	assert(0);
}


void ExInst::print_blif(std::ostream& out){
	assert(m_exps.size()==1);
	string i0 = (*m_exps.begin())->get_blif_name();
	string o = get_blif_name();
	if (is_rhs) {
		out << "# ExInst: " << o << " = " << i0 << " [";
		if (get_size() > 1) {
			out << m_hi << ":";
		}
		out << m_lo << "]" << endl;
	} else {
		out << "# ExInst: " << i0 << " [";
		if (get_size() > 1){
			out << m_hi << ":";
		}
		out << m_lo << "] = " << get_blif_name() << endl;
	}

	if (get_size() > 1){
		for (unsigned i = 0; i < get_size(); i++) {
			string i0_bname = i0 + blif_suffix(i + m_lo);
			string o_bname = o + blif_suffix(i);
			if (is_rhs){
				OpInst::print_blif_table(out, OpInst::Identity, i0_bname, 1, "", 0, "", 0, o_bname, 1);
			}else{
				OpInst::print_blif_table(out, OpInst::Identity, o_bname, 1, "", 0, "", 0, i0_bname, 1);
			}
		}
	} else {
		string i0_bname = i0 + blif_suffix(m_lo);
		if (is_rhs){
			OpInst::print_blif_table(out, OpInst::Identity, i0_bname, 1, "", 0, "", 0, o, 1);
		}else{
			OpInst::print_blif_table(out, OpInst::Identity, o, 1, "", 0, "", 0, i0_bname, 1);
		}
	}
	out << endl;
}

void OpInst::print_blif(std::ostream& out){
	string i0, i1, i2, o;
	unsigned w_i0, w_i1, w_i2, w_o;

	o = get_blif_name();
	w_o = get_size();
	
	if (m_op == Concat) {
		InstL::reverse_iterator rit = m_exps.rbegin();
		//out << "Inst: " << *(*rit) << endl;
		out << "# OpInst: "<< get_blif_name() << " = {" << (*rit)->get_blif_name();
		for (rit++; rit != m_exps.rend(); rit++)
			out << ", " << (*rit)->get_blif_name();
		out << "}" << endl;

		unsigned idx = 0;
		for (InstL::iterator it = m_exps.begin(); it != m_exps.end(); it++) {
			string i1 = (*it)->get_blif_name();
			unsigned w_i1 = (*it)->get_size();
			if (w_i1 == 1) {
				print_blif_table(out, Identity, i1, 1, "", 0, "", 0, o + blif_suffix(idx), 1, this);
				idx++;
			} else {
				for (unsigned i = 0; i < w_i1; i++, idx++) {
					print_blif_table(out, Identity, i1 + blif_suffix(i), 1, "", 0, "", 0, o + blif_suffix(idx), 1, this);
				}
			}
		}
		assert(idx==w_o);
	} else if (m_op == Ternary) {
		assert(m_exps.size() == 3);

		InstL::iterator it = m_exps.begin();
		i0 = (*it)->get_blif_name();
		w_i0 = (*it++)->get_size();
		
		i1 = (*it)->get_blif_name();
		w_i1 = (*it++)->get_size();
		
		i2 = (*it)->get_blif_name();
		w_i2 = (*it)->get_size();

		out << "# OpInst: " << o << "=" << i0 << " ? " << i1 << " : " << i2 << endl;
		print_blif_table(out, Ternary, i0, w_i0, i1, w_i1, i2, w_i2, o, w_o, this);
	} else if (m_op == Future) {
		cout << "BLIF: implicit latch" << endl;
		//assert(0);
	} else {
//		out << "# OpInst: " << o << "[" << (w_o - 1) << ":0] = (" << op2str(m_op) << " with " <<  m_exps.size() << " operands)"<< endl;
		{
			out << "# OpInst: " << o << "[" << (w_o - 1) << ":0] = (" << op2str(m_op);
			InstL::iterator it = m_exps.begin();
			for (; it != m_exps.end(); it++) {
				out << " " << (*it)->get_blif_name();
			}
			out << ")"<< endl;
		}
		
		unsigned exps_size = m_exps.size();
		if (exps_size == 1) {
			i0 = (m_exps.front())->get_blif_name();
			print_blif_table(out, m_op, i0, (m_exps.front())->get_size(), "", 0, "", 0, o, w_o, this);
		} else {
			InstL::iterator it = m_exps.begin();
			i0 = (*it)->get_blif_name();
			w_i0 = (*it++)->get_size();
			
			i1 = (*it)->get_blif_name();
			w_i1 = (*it)->get_size();
			if (exps_size == 2) {
				print_blif_table(out, m_op, i0, w_i0, i1, w_i1, "", 0, o, w_o, this);
			} else {
				assert(m_size==1);
				if ((m_size==1) && ((m_op == LogAnd) || (m_op == LogOr))) {
					//TODO use print_blif_table
					out << ".names";
					for (InstL::iterator it2 = m_exps.begin(); it2 != m_exps.end(); it2++){
						out << " " << (*it2)->get_blif_name();
					}
					out << " " << o << endl;
					if (m_op == LogAnd) {
						for (unsigned i = 0; i < exps_size; i++) {
							out << "1";
						}
						out << " 1" << endl;
					} else if (m_op == LogOr) {
						for (unsigned j = 1; j <= exps_size; j++) {
							for (unsigned i = exps_size; i > 0; i--) {
								out << ((i == j) ? "1" : "-");
							}
							out << " 1" << endl;
						}
					}
				} else if ((w_i0 == w_i1) && (w_i0 == w_o) && (w_o == 1)) {
					if((m_op == ReductionXNor) || (m_op == ReductionNand) || (m_op == ReductionNor)){
						assert(0);
					}
					if((m_op == Eq) || (m_op == LogNand) || (m_op == LogNor) || (m_op == LogXNor)){
						assert(0);
					}
//					assert(0);
//					out << "Inst: " << *(this) << endl;
					out << "#	CHECK	#" << endl;
					unsigned wop_idx = 1;
					string base_wop =  o + string("_wop");
					print_blif_table(out, m_op, i0, w_i0, i1, w_i1, "", 0, base_wop +  blif_suffix(wop_idx), w_o);
					InstL::iterator it2 = m_exps.begin(); it2++; it2++;
					for (; it2 != m_exps.end(); it2++){
						wop_idx++;
						i0 = (*it2)->get_blif_name();
						w_i0 = (*it2)->get_size();
						if (it2 == m_exps.end()) {
							print_blif_table(out, m_op, i0, w_i0, base_wop +  blif_suffix(wop_idx-1), w_o, "", 0, o, w_o);
						} else {
							print_blif_table(out, m_op, i0, w_i0, base_wop +  blif_suffix(wop_idx-1), w_o, "", 0, base_wop +  blif_suffix(wop_idx), w_o);
						}
					}
					out << ".names " << base_wop +  blif_suffix(wop_idx) << " " << o << endl;
					out << "1 1" << endl;
// .names n429_0 n431_0
// 1 1
				} else {
					assert(0);
				}
			}
		}
	}
	out << endl;
}
set<string> hash_blif_table;
void OpInst::print_blif_table(ostream&out, OpType op_type, string i0, unsigned w_i0, string i1, unsigned w_i1, string i2, unsigned w_i2, string o, unsigned w_o, Inst *e) {
	switch (op_type) {
	case Minus:
		assert(w_i0==w_o);
		if (w_o == 1) {
			print_blif_table(out, Identity, i0, 1, "", 0, "", 0, o, 1);
		} else {
			print_blif_table(out, BitWiseNot, i0, w_i0, "", 0, "", 0, i0 + "_not" + blif_suffix(0), w_i0);
//			print_blif_table(out, LogNot, i0 + "_not" + blif_suffix(0), 1, "", 0, "", 0, o + blif_suffix(0), 1);
			print_blif_table(out, Identity, i0 + blif_suffix(0), 1, "", 0, "", 0, o + blif_suffix(0), 1);
			print_blif_table(out, Identity, i0 + "_not" + blif_suffix(0), 1, "", 0, "", 0, o + "_carry" + blif_suffix(0), 1);
			for (unsigned i = 1; i < w_o; i++) {
				string suffix = blif_suffix(i);
				print_blif_table(out, BitWiseNot, i0 + suffix, w_i0, "", 0, "", 0, i0 + "_not" + suffix, w_i0);
				print_blif_table(out, LogXor, o + "_carry" + blif_suffix(i - 1), 1, i0 + "_not" + suffix, 1, "", 0, o + suffix, 1);
				if (i != (w_o - 1))
					print_blif_table(out, LogAnd, o + "_carry" + blif_suffix(i - 1), 1, i0 + "_not" + suffix, 1, "", 0, o + "_carry" + suffix, 1);
			}
		}
		break;
/*
	case AddC:
		if (w_i2 == 0){
			//assert((w_i0==w_i1) && (w_i0==w_o));
			if (w_o == 1)
				print_blif_table(out, LogXor, i0, 1, i1, 1, "", 0, o, 1);
			else {
				print_blif_table(out, LogXor, i0 + blif_suffix(0), 1, i1 + blif_suffix(0), 1, "", 0, o + blif_suffix(0), 1);
				print_blif_table(out, LogAnd, i0 + blif_suffix(0), 1, i1 + blif_suffix(0), 1, "", 0, o + "_carry" + blif_suffix(0), 1);
				for (unsigned i = 1; i < w_o-1; i++) {
					string suffix = blif_suffix(i);
					print_blif_table(out, LogXor, o + "_carry" + blif_suffix(i - 1), 1, i0 + suffix, 1, i1 + suffix, 1, o + suffix, 1);
					if (i != (w_o - 2))
						print_blif_table(out, Add, o + "_carry" + blif_suffix(i - 1), 1, i0 + suffix, 1, i1 + suffix, 1, o + "_carry" + suffix, 1);
				}
				{
					string suffix = blif_suffix(w_o-2);
					string out_suffix = blif_suffix(w_o-1);
					print_blif_table(out, Add, o + "_carry" + blif_suffix(w_o - 3), 1, i0 + suffix, 1, i1 + suffix, 1, o + out_suffix, 1);
				}
			}
		} else {
			assert((w_i0==1) && (w_i1==1) && (w_i2==1) && (w_o==1));
			out << ".names " << i0 << " " << i1 << " " << i2 << " " << o << endl;
			out << "-11 1" << endl << "1-1 1" << endl << "11- 1" << endl;
		}
		break;
*/
	case Mult: {
		
// 		if (w_o == 1) {
// 			out << ".names " << i0 << " " << o << endl;
// 			out << "1 1" << endl;
// 		}

		int a_idx = 0;
		int b_idx = 0;
		int t_idx = 0;
		list<int> l_to_add;
		
		
// 		cout << "BEFORE	##	w_o: " << w_o << ", w_i0: " << w_i0 << ", w_i1: " << w_i1 << endl;
		// width adjustments
		int w_o_original = w_o;
		if((w_i0 > w_i1) && (w_o < (2*w_i0))){
			w_o = (2*w_i0);
		}else if((w_i0 <= w_i1) && (w_o < (2*w_i1))){
			w_o = (2*w_i1);
		}
		int half_w_o = w_o / 2;
		if(half_w_o > (int)w_i0){
			for(int i = w_i0; i < half_w_o; ++i){
				if(hash_blif_table.find(i0 + blif_suffix(i)) == hash_blif_table.end()){
					OpInst::print_blif_table(out, OpInst::LogFalse, "", 0, "", 0, "", 0, i0 + blif_suffix(i), 1);
					hash_blif_table.insert(i0 + blif_suffix(i));
				}
			}
		}
		if(half_w_o > (int)w_i1){
			for(int i = w_i1; i < half_w_o; ++i){
				if(hash_blif_table.find(i1 + blif_suffix(i)) == hash_blif_table.end()){
					OpInst::print_blif_table(out, OpInst::LogFalse, "", 0, "", 0, "", 0, i1 + blif_suffix(i), 1);
					hash_blif_table.insert(i1 + blif_suffix(i));
				}
			}
		}
		w_i0 = half_w_o;
		w_i1 = half_w_o;
		
// 		cout << "AFTER	##	w_o: " << w_o << ", w_i0: " << w_i0 << ", w_i1: " << w_i1 << endl;
		
		for(int o_idx = 0; o_idx < ((int)w_o-1); o_idx++){
			list<int> l_to_add_next;
			int ta_idx = a_idx;
			int tb_idx = b_idx;
			for(; tb_idx <= a_idx; tb_idx++, ta_idx--){
				l_to_add.push_back(t_idx);
				print_blif_table(out, LogAnd, i0 + blif_suffix(ta_idx), 1, i1 + blif_suffix(tb_idx), 1, "", 0, o + "_t" + blif_suffix(t_idx++), 1);
			}

			while(!l_to_add.empty()){
				if(l_to_add.size() == 1){
					if(o_idx >= w_o_original){
						if(hash_blif_table.find(o + blif_suffix(o_idx)) == hash_blif_table.end()){
							OpInst::print_blif_table(out, OpInst::LogFalse, "", 0, "", 0, "", 0, o + blif_suffix(o_idx), 1);
							hash_blif_table.insert(o + blif_suffix(o_idx));
						}
					}else{
						print_blif_table(out, Identity, o + "_t" + blif_suffix(l_to_add.front()), 1, "", 0, "", 0, o + blif_suffix(o_idx), 1);
					}
					l_to_add.clear();
				}else if(l_to_add.size() == 2){
					if(o_idx >= w_o_original){
						if(hash_blif_table.find(o + blif_suffix(o_idx)) == hash_blif_table.end()){
							OpInst::print_blif_table(out, OpInst::LogFalse, "", 0, "", 0, "", 0, o + blif_suffix(o_idx), 1);
							hash_blif_table.insert(o + blif_suffix(o_idx));
						}
					}else{
						print_blif_table(out, LogXor, o + "_t" + blif_suffix(l_to_add.front()), 1, o + "_t" + blif_suffix(l_to_add.back()), 1, "", 0, o + blif_suffix(o_idx), 1);
					}
					l_to_add_next.push_back(t_idx);
					print_blif_table(out, LogAnd, o + "_t" + blif_suffix(l_to_add.front()), 1, o + "_t" + blif_suffix(l_to_add.back()), 1, "", 0, o + "_t" + blif_suffix(t_idx++), 1);
					l_to_add.clear();
				}else{	//(l_to_add.size() >= 3)
					list<int>::iterator it0 = l_to_add.begin();
					list<int>::iterator it1 = it0;
					it1++;
					list<int>::iterator it2 = it1;
					it2++;
					// carry
					l_to_add_next.push_back(t_idx);
					print_blif_table(out, Add, o + "_t" + blif_suffix(*it0), 1, o + "_t" + blif_suffix(*it1), 1, o + "_t" + blif_suffix(*it2), 1, o + "_t" + blif_suffix(t_idx++), 1);
// 					out << ".names " << o + "_t" + blif_suffix(*it0) << " " << o + "_t" + blif_suffix(*it1) << " " << o + "_t" + blif_suffix(*it2) << " " << o + "_t" + blif_suffix(t_idx++) << endl;
// 					out << "-11 1" << endl << "1-1 1" << endl << "11- 1" << endl;
					// sum
					l_to_add.push_back(t_idx);
					print_blif_table(out, LogXor, o + "_t" + blif_suffix(*it0), 1, o + "_t" + blif_suffix(*it1), 1, o + "_t" + blif_suffix(*it2), 1, o + "_t" + blif_suffix(t_idx++), 1);
					l_to_add.pop_front();
					l_to_add.pop_front();
					l_to_add.pop_front();
				}
			}

			if(a_idx < ((int)w_i0-1)){
				a_idx++;
			}else{
				b_idx++;
			}
			l_to_add = l_to_add_next;
		}
		
		print_blif_table(out, Identity, o + "_t" + blif_suffix(l_to_add.front()), 1, "", 0, "", 0, o + blif_suffix(w_o-1), 1);
	}
		break;
	case Add:
		if (w_i2 == 0){
			if(!((w_i0==w_i1) && (w_i0==w_o))){
				assert(0);
			}
			//assert((w_i0==w_i1) && (w_i0==w_o));
			if (w_o == 1)
				print_blif_table(out, LogXor, i0, 1, i1, 1, "", 0, o, 1);
			else {
				print_blif_table(out, LogXor, i0 + blif_suffix(0), 1, i1 + blif_suffix(0), 1, "", 0, o + blif_suffix(0), 1);
				print_blif_table(out, LogAnd, i0 + blif_suffix(0), 1, i1 + blif_suffix(0), 1, "", 0, o + "_carry" + blif_suffix(0), 1);
				for (unsigned i = 1; i < w_o; i++) {
					string suffix = blif_suffix(i);
					print_blif_table(out, LogXor, o + "_carry" + blif_suffix(i - 1), 1, i0 + suffix, 1, i1 + suffix, 1, o + suffix, 1);
					if (i != (w_o - 1))
						print_blif_table(out, Add, o + "_carry" + blif_suffix(i - 1), 1, i0 + suffix, 1, i1 + suffix, 1, o + "_carry" + suffix, 1);
				}
			}
		} else {
			assert((w_i0==1) && (w_i1==1) && (w_i2==1) && (w_o==1));
			out << ".names " << i0 << " " << i1 << " " << i2 << " " << o << endl;
			out << "-11 1" << endl << "1-1 1" << endl << "11- 1" << endl;
		}
		break;
	case Sub:
		assert((w_i0==w_i1) && (w_i0==w_o));
		if (w_o == 1)
			print_blif_table(out, LogXor, i0, 1, i1, 1, "", 0, o, 1);
		else {
			if(hash_blif_table.find(i1 + "_not") == hash_blif_table.end()){
				hash_blif_table.insert(i1 + "_not");
				print_blif_table(out, BitWiseNot, i1, w_i1, "", 0, "", 0, i1 + "_not", w_o);
			}
			i1 += "_not";
			print_blif_table(out, LogXNor, i0 + blif_suffix(0), 1, i1 + blif_suffix(0), 1, "", 0, o + blif_suffix(0), 1);
			print_blif_table(out, LogOr, i0 + blif_suffix(0), 1, i1 + blif_suffix(0), 1, "", 0, o + "_carry" + blif_suffix(0), 1);
			for (unsigned i = 1; i < w_o; i++) {
				string suffix = blif_suffix(i);
				print_blif_table(out, LogXor, o + "_carry" + blif_suffix(i - 1), 1, i0 + suffix, 1, i1 + suffix, 1, o + suffix, 1);
				if (i != (w_o - 1))
					print_blif_table(out, Add, o + "_carry" + blif_suffix(i - 1), 1, i0 + suffix, 1, i1 + suffix, 1, o + "_carry" + suffix, 1);
			}
		}
		break;
	case Eq:
		if(w_i0 != w_i1){
			cout << "e: " << *e << endl;
		}
		
		assert((w_i0==w_i1) && (w_o==1));
		if (w_i0 == 1) {
			print_blif_table(out, LogXNor, i0, 1, i1, 1, "", 0, o, 1);
		} else {
			for (unsigned i = 0; i < w_i0; i++) {
				string suffix = blif_suffix(i);
				print_blif_table(out, LogXNor, i0 + suffix, 1, i1 + suffix, 1, "", 0, o + "_eq_xnor" + suffix, 1);
			}
			print_blif_table(out, ReductionAnd, o + "_eq_xnor", w_i0, "", 0, "", 0, o, 1);
		}
		break;
	case NotEq:
		assert((w_i0==w_i1) && (w_o==1));
		if (w_i0 == 1) {
			print_blif_table(out, LogXor, i0, 1, i1, 1, "", 0, o, 1);
		} else {
			for (unsigned i = 0; i < w_i0; i++) {
				string suffix = blif_suffix(i);
				print_blif_table(out, LogXor, i0 + suffix, 1, i1 + suffix, 1, "", 0, o + "_neq_xor" + suffix, 1);
			}
			print_blif_table(out, ReductionOr, o + "_neq_xor", w_i0, "", 0, "", 0, o, 1);
		}
		break;
	case Gr:
		assert((w_i0==w_i1) && (w_o==1));
		if (w_i0 == 1) {
			out << ".names " << i0 << " " << i1 << " " << o << endl;
			out << "10 1" << endl;
		} else {
			out << ".names " << i0 + blif_suffix(0) << " " << i1 + blif_suffix(0) << " " << o + "_eq" + blif_suffix(1) << " " << o + "_gt" + blif_suffix(1)
					<< " " << o << endl;
			out << "---1 1" << endl << "1010 1" << endl;
			for (unsigned i = 1; i < (w_i0 - 1); i++) {
				out << ".names " << i0 + blif_suffix(i) << " " << i1 + blif_suffix(i) << " " << o + "_eq" + blif_suffix(i + 1) << " " << o + "_gt"
						+ blif_suffix(i + 1) << " " << o + "_gt" + blif_suffix(i) << endl;
				out << "---1 1" << endl << "1010 1" << endl;
				out << ".names " << i0 + blif_suffix(i) << " " << i1 + blif_suffix(i) << " " << o + "_eq" + blif_suffix(i + 1) << " " << o + "_eq"
						+ blif_suffix(i) << endl;
				out << "001 1" << endl << "111 1" << endl;
			}
			out << ".names " << i0 + blif_suffix(w_i0 - 1) << " " << i1 + blif_suffix(w_i0 - 1) << " " << o + "_gt" + blif_suffix(w_i0 - 1) << endl;
			out << "10 1" << endl;
			out << ".names " << i0 + blif_suffix(w_i0 - 1) << " " << i1 + blif_suffix(w_i0 - 1) << " " << o + "_eq" + blif_suffix(w_i0 - 1) << endl;
			out << "00 1" << endl << "11 1" << endl;
		}
		break;
	case Le:
		assert((w_i0==w_i1) && (w_o==1));
		if (w_i0 == 1) {
			out << ".names " << i0 << " " << i1 << " " << o << endl;
			out << "01 1" << endl;
		} else {
			out << ".names " << i0 + blif_suffix(0) << " " << i1 + blif_suffix(0) << " " << o + "_eq" + blif_suffix(1) << " " << o + "_lt" + blif_suffix(1)
					<< " " << o << endl;
			out << "---1 1" << endl << "0110 1" << endl;
			for (unsigned i = 1; i < (w_i0 - 1); i++) {
				out << ".names " << i0 + blif_suffix(i) << " " << i1 + blif_suffix(i) << " " << o + "_eq" + blif_suffix(i + 1) << " " << o + "_lt"
						+ blif_suffix(i + 1) << " " << o + "_lt" + blif_suffix(i) << endl;
				out << "---1 1" << endl << "0110 1" << endl;
				out << ".names " << i0 + blif_suffix(i) << " " << i1 + blif_suffix(i) << " " << o + "_eq" + blif_suffix(i + 1) << " " << o + "_eq"
						+ blif_suffix(i) << endl;
				out << "001 1" << endl << "111 1" << endl;
			}
			out << ".names " << i0 + blif_suffix(w_i0 - 1) << " " << i1 + blif_suffix(w_i0 - 1) << " " << o + "_lt" + blif_suffix(w_i0 - 1) << endl;
			out << "01 1" << endl;
			out << ".names " << i0 + blif_suffix(w_i0 - 1) << " " << i1 + blif_suffix(w_i0 - 1) << " " << o + "_eq" + blif_suffix(w_i0 - 1) << endl;
			out << "00 1" << endl << "11 1" << endl;
		}
		break;
	case GrEq:
		assert((w_i0==w_i1) && (w_o==1));
		if (w_i0 == 1) {
			out << ".names " << i0 << " " << i1 << " " << o << endl;
			out << "1- 1" << endl;
		} else {
			out << ".names " << i0 + blif_suffix(0) << " " << i1 + blif_suffix(0) << " " << o + "_eq" + blif_suffix(1) << " " << o + "_gt" + blif_suffix(1)
					<< " " << o << endl;
			out << "---1 1" << endl << "1-10 1" << endl << "0010 1" << endl;
			for (unsigned i = 1; i < (w_i0 - 1); i++) {
				out << ".names " << i0 + blif_suffix(i) << " " << i1 + blif_suffix(i) << " " << o + "_eq" + blif_suffix(i + 1) << " " << o + "_gt"
						+ blif_suffix(i + 1) << " " << o + "_gt" + blif_suffix(i) << endl;
				out << "---1 1" << endl << "1010 1" << endl;
				out << ".names " << i0 + blif_suffix(i) << " " << i1 + blif_suffix(i) << " " << o + "_eq" + blif_suffix(i + 1) << " " << o + "_eq"
						+ blif_suffix(i) << endl;
				out << "001 1" << endl << "111 1" << endl;
			}
			out << ".names " << i0 + blif_suffix(w_i0 - 1) << " " << i1 + blif_suffix(w_i0 - 1) << " " << o + "_gt" + blif_suffix(w_i0 - 1) << endl;
			out << "10 1" << endl;
			out << ".names " << i0 + blif_suffix(w_i0 - 1) << " " << i1 + blif_suffix(w_i0 - 1) << " " << o + "_eq" + blif_suffix(w_i0 - 1) << endl;
			out << "00 1" << endl << "11 1" << endl;
		}
		break;
	case LeEq:
		assert((w_i0==w_i1) && (w_o==1));
		if (w_i0 == 1) {
			out << ".names " << i0 << " " << i1 << " " << o << endl;
			out << "-1 1" << endl;
		} else {
			out << ".names " << i0 + blif_suffix(0) << " " << i1 + blif_suffix(0) << " " << o + "_eq" + blif_suffix(1) << " " << o + "_lt" + blif_suffix(1)
					<< " " << o << endl;
			out << "---1 1" << endl << "-110 1" << endl << "0010 1" << endl;
			for (unsigned i = 1; i < (w_i0 - 1); i++) {
				out << ".names " << i0 + blif_suffix(i) << " " << i1 + blif_suffix(i) << " " << o + "_eq" + blif_suffix(i + 1) << " " << o + "_lt"
						+ blif_suffix(i + 1) << " " << o + "_lt" + blif_suffix(i) << endl;
				out << "---1 1" << endl << "0110 1" << endl;
				out << ".names " << i0 + blif_suffix(i) << " " << i1 + blif_suffix(i) << " " << o + "_eq" + blif_suffix(i + 1) << " " << o + "_eq"
						+ blif_suffix(i) << endl;
				out << "001 1" << endl << "111 1" << endl;
			}
			out << ".names " << i0 + blif_suffix(w_i0 - 1) << " " << i1 + blif_suffix(w_i0 - 1) << " " << o + "_lt" + blif_suffix(w_i0 - 1) << endl;
			out << "01 1" << endl;
			out << ".names " << i0 + blif_suffix(w_i0 - 1) << " " << i1 + blif_suffix(w_i0 - 1) << " " << o + "_eq" + blif_suffix(w_i0 - 1) << endl;
			out << "00 1" << endl << "11 1" << endl;
		}
		break;
	case BitWiseAnd:
		if(!((w_i0==w_i1) && (w_i0==w_o))){
			cout << "BITWiseAnd ERR: " << i0 << ", " << i1 << ", " << o << endl;
			cout << w_i0 << ", " << w_i1 << ", " << w_o << endl;
			cout << *e << endl;
			assert(0);
		}
		//assert((w_i0==w_i1) && (w_i0==w_o));
		if(w_o == 1){
			print_blif_table(out, LogAnd, i0, 1, i1, 1, "", 0, o, 1);	
		}else{
			for (unsigned i = 0; i < w_o; i++) {
				string suffix = blif_suffix(i);
				print_blif_table(out, LogAnd, i0 + suffix, 1, i1 + suffix, 1, "", 0, o + suffix, 1);
			}
		}
		break;
	case BitWiseOr:
		assert((w_i0==w_i1) && (w_i0==w_o));
		if(w_o == 1){
			print_blif_table(out, LogOr, i0, 1, i1, 1, "", 0, o, 1);	
		}else{
			for (unsigned i = 0; i < w_o; i++) {
				string suffix = blif_suffix(i);
				print_blif_table(out, LogOr, i0 + suffix, 1, i1 + suffix, 1, "", 0, o + suffix, 1);
			}
		}
		break;
	case BitWiseNot:
		assert(w_i0==w_o);
		if(w_o == 1){
			print_blif_table(out, LogNot, i0, 1, "", 0, "", 0, o, 1);	
		}else{
			for (unsigned i = 0; i < w_o; i++) {
				string suffix = blif_suffix(i);
				print_blif_table(out, LogNot, i0 + suffix, 1, "", 0, "", 0, o + suffix, 1);
			}
		}
		break;
	case BitWiseXor:
		assert((w_i0==w_i1) && (w_i0==w_o));
		if (w_o == 1){
			print_blif_table(out, LogXor, i0, 1, i1, 1, "", 0, o, 1);
		}else {
			for (unsigned i = 0; i < w_o; i++) {
				string suffix = blif_suffix(i);
				print_blif_table(out, LogXor, i0 + suffix, 1, i1 + suffix, 1, "", 0, o + suffix, 1);
			}
		}
		break;
	case BitWiseXNor:
		assert((w_i0==w_i1) && (w_i0==w_o));
		if(w_o == 1){
			print_blif_table(out, LogXNor, i0, 1, i1, 1, "", 0, o, 1);	
		}else{
			for (unsigned i = 0; i < w_o; i++) {
				string suffix = blif_suffix(i);
				print_blif_table(out, LogXNor, i0 + suffix, 1, i1 + suffix, 1, "", 0, o + suffix, 1);
			}
		}
		break;
	case BitWiseNor:
		assert((w_i0==w_i1) && (w_i0==w_o));
		if(w_o == 1){
			print_blif_table(out, LogNor, i0, 1, i1, 1, "", 0, o, 1);	
		}else{
			for (unsigned i = 0; i < w_o; i++) {
				string suffix = blif_suffix(i);
				print_blif_table(out, LogNor, i0 + suffix, 1, i1 + suffix, 1, "", 0, o + suffix, 1);
			}
		}
		break;
	case BitWiseNand:
		assert((w_i0==w_i1) && (w_i0==w_o));
		if(w_o == 1){
			print_blif_table(out, LogNand, i0, 1, i1, 1, "", 0, o, 1);	
		}else{
			for (unsigned i = 0; i < w_o; i++) {
				string suffix = blif_suffix(i);
				print_blif_table(out, LogNand, i0 + suffix, 1, i1 + suffix, 1, "", 0, o + suffix, 1);
			}
		}
		break;
	case LogTrue:
		out << ".names " << o << endl;
		out << "1" << endl;
		break;
	case LogFalse:
		out << ".names " << o << endl;
		break;
	case LogNot:
		assert(w_i0==w_o);
		assert(w_o==1);
		out << ".names " << i0 << " " << o << endl;
		out << "0 1" << endl;
		break;
	case LogAnd:
		assert((w_i0==w_i1) && (w_o==1));
		out << ".names " << i0 << " " << i1 << " " << o << endl;
		out << "11 1" << endl;
		break;
	case Identity:
	case LogOr:
		if (w_i1 == 0){
			assert(w_i0==w_o);
			if (w_o == 1) {
				out << ".names " << i0 << " " << o << endl;
				out << "1 1" << endl;
			} else {
				for (unsigned i = 0; i < w_o; i++) {
					string suffix = blif_suffix(i);
					print_blif_table(out, Identity, i0 + suffix, 1, "", 0, "", 0, o + suffix, 1);
				}
			}
		} else {
			assert((w_i0==w_i1) && (w_o==1));
			out << ".names " << i0 << " " << i1 << " " << o << endl;
			out << "1- 1" << endl << "-1 1" << endl;
		}
		break;
	case LogNand:
		assert((w_i0==w_i1) && (w_o==1));
		out << ".names " << i0 << " " << i1 << " " << o << endl;
		out << "0- 1" << endl << "-0 1" << endl;
		break;
	case LogNor:
		assert((w_i0==w_i1) && (w_o==1));
		out << ".names " << i0 << " " << i1 << " " << o << endl;
		out << "00 1" << endl;
		break;
	case LogXor:
		if (w_i2 == 0) {
			assert((w_i0==w_i1) && (w_o==1));
			out << ".names " << i0 << " " << i1 << " " << o << endl;
			out << "10 1" << endl << "01 1" << endl;
		} else {
			assert((w_i0==1) && (w_i1==1) && (w_i2==1) && (w_o==1));
			out << ".names " << i0 << " " << i1 << " " << i2 << " " << o << endl;
			out << "100 1" << endl << "010 1" << endl << "001 1" << endl << "111 1" << endl;
		}
		break;
	case LogXNor:
		assert((w_i0==w_i1) && (w_o==1));
		out << ".names " << i0 << " " << i1 << " " << o << endl;
		out << "00 1" << endl << "11 1" << endl;
		break;
	case ReductionAnd:
		assert(w_o==1);
		out << ".names";
		for (unsigned i = w_i0; i > 0; i--) {
			string suffix = blif_suffix(i - 1);
			out << " " << i0 << suffix;
		}
		out << " " << o << endl;
		for (unsigned i = w_i0; i > 0; i--) {
			out << "1";
		}
		out << " 1" << endl;
		break;
	case ReductionOr:
		assert(w_o==1);
		out << ".names";
		for (unsigned i = w_i0; i > 0; i--) {
			string suffix = blif_suffix(i - 1);
			out << " " << i0 << suffix;
		}
		out << " " << o << endl;
		for (unsigned j = 1; j <= w_i0; j++) {
			for (unsigned i = w_i0; i > 0; i--) {
				out << ((i == j) ? "1" : "-");
			}
			out << " 1" << endl;
		}
		break;
	case ReductionNand:
		assert(w_o==1);
		out << ".names";
		for (unsigned i = w_i0; i > 0; i--) {
			string suffix = blif_suffix(i - 1);
			out << " " << i0 << suffix;
		}
		out << " " << o << endl;
		for (unsigned j = 1; j <= w_i0; j++) {
			for (unsigned i = w_i0; i > 0; i--) {
				out << ((i == j) ? "0" : "-");
			}
			out << " 1" << endl;
		}
		break;
	case ReductionNor:
		assert(w_o==1);
		out << ".names";
		for (unsigned i = w_i0; i > 0; i--) {
			string suffix = blif_suffix(i - 1);
			out << " " << i0 << suffix;
		}
		out << " " << o << endl;
		for (unsigned i = w_i0; i > 0; i--) {
			out << "0";
		}
		out << " 1" << endl;
		break;
	case ReductionXor:
	{
		assert(w_o==1);
		if (w_i0 == 1) {
			print_blif_table(out, Identity, i0 + blif_suffix(0), 1, "", 0, "", 0, o, 1);
		} else if (w_i0 == 2) {
			print_blif_table(out, LogXor, i0 + blif_suffix(1), 1, i0 + blif_suffix(0), 1, "", 0, o, 1);
		} else {
			print_blif_table(out, LogXor, i0 + blif_suffix(w_i0 - 1), 1, i0 + blif_suffix(w_i0 - 2), 1, "", 0, o + "_rxor" + blif_suffix(w_i0 - 3), 1);
			for (unsigned i = w_i0 - 3; i > 0; i--)
				print_blif_table(out, LogXor, o + "_rxor" + blif_suffix(i), 1, i0 + blif_suffix(i), 1, "", 0, o + "_rxor" + blif_suffix(i - 1), 1);
			print_blif_table(out, LogXor, o + "_rxor" + blif_suffix(0), 1, i0 + blif_suffix(0), 1, "", 0, o, 1);
		}
	}
		break;
	case ReductionXNor:
	{
		assert(w_o==1);
		if (w_i0 == 1) {
			print_blif_table(out, Identity, i0 + blif_suffix(0), 1, "", 0, "", 0, o, 1);
		} else if (w_i0 == 2) {
			print_blif_table(out, LogXNor, i0 + blif_suffix(1), 1, i0 + blif_suffix(0), 1, "", 0, o, 1);
		} else {
			print_blif_table(out, LogXNor, i0 + blif_suffix(w_i0 - 1), 1, i0 + blif_suffix(w_i0 - 2), 1, "", 0, o + "_rxnor" + blif_suffix(w_i0 - 3), 1);
			for (unsigned i = w_i0 - 3; i > 0; i--)
				print_blif_table(out, LogXNor, o + "_rxnor" + blif_suffix(i), 1, i0 + blif_suffix(i), 1, "", 0, o + "_rxnor" + blif_suffix(i - 1), 1);
			print_blif_table(out, LogXNor, o + "_rxnor" + blif_suffix(0), 1, i0 + blif_suffix(0), 1, "", 0, o, 1);
		}
	}
		break;
	case ShiftL:
		assert(w_i0==w_o);
		for (unsigned pos = w_o; pos > 0; pos--) {
			out << ".names";
			for (unsigned i = w_i0; i > 0; i--)
				out << " " << i0 << blif_suffix(i - 1);
			if(w_i1 != 1){
				for (unsigned i = w_i1; i > 0; i--)
					out << " " << i1 << blif_suffix(i - 1);
			}else{
				out << " " << i1;
			}
			out << " " << o << blif_suffix(pos - 1);
			out << endl;
			for (unsigned num = 0; (num < pos) && (num < (0x1U << w_i1)); num++) {
				for (unsigned i = w_i0; i > 0; i--)
					out << (((i - 1) == (pos - 1 - num)) ? "1" : "-");
				for (unsigned i = w_i1; i > 0; i--)
					out << ((num >> (i - 1)) & 0x1U);
				out << " 1";
				out << endl;
			}
		}
		break;
	case ShiftR:
		assert(w_i0==w_o);
		for (unsigned pos = w_o; pos > 0; pos--) {
			out << ".names";
			for (unsigned i = w_i0; i > 0; i--)
				out << " " << i0 << blif_suffix(i - 1);
			if(w_i1 != 1){
				for (unsigned i = w_i1; i > 0; i--)
					out << " " << i1 << blif_suffix(i - 1);
			}else{
				out << " " << i1;
			}
			out << " " << o << blif_suffix(pos - 1);
			out << endl;
			for (unsigned num = 0; (num < (w_i0 - pos + 1)) && (num < (0x1U << w_i1)); num++) {
				for (unsigned i = w_i0; i > 0; i--)
					out << (((i - 1) == (pos - 1 + num)) ? "1" : "-");
				for (unsigned i = w_i1; i > 0; i--)
					out << ((num >> (i - 1)) & 0x1U);
				out << " 1";
				out << endl;
			}
		}
		break;
	case Ternary:
		if(!((w_i0==1) && (w_i1==w_i2) && (w_i1==w_o))){
			cout << ".names " << i0 << " " << i1 << " " << i2 << " " << o << endl;
			cout << "11- 1" << endl << "0-1 1" << endl;
			cout << "w_i0: " << w_i0 << ", w_i1: " << w_i1 << ", w_i2: " << w_i2 << ", w_o: " << w_o << endl;
			cout << w_i0 << ", " << w_i1 << ", " << w_i2 << ", " << w_o << endl;
// 			cout << *e << endl;
// 			assert(0);
		}

//		assert((w_i0==1) && (w_i1==w_i2) && (w_i1==w_o));
		if (w_o == 1) {
			out << ".names " << i0 << " " << i1 << " " << i2 << " " << o << endl;
			out << "11- 1" << endl << "0-1 1" << endl;
		} else {
			for (unsigned i = 0; i < w_o; i++) {
				string suffix = blif_suffix(i);
				print_blif_table(out, Ternary, i0, 1, i1 + suffix, 1, i2 + suffix, 1, o + suffix, 1);
			}
		}
		break;
	default:
		out << "# OpType (" << op2str(op_type) << ") is not supported" << endl;
	}
}


//TODO memory part is incomplete
void MemInst::print_blif(std::ostream& out){
	out << "# MemInst: blif_name:	" << get_blif_name();
	out << "[" << get_size() << "]: name: " << get_name() << endl;

	for (InstL::iterator it = m_ports.begin(); it != m_ports.end(); it++) {
		out << "# port " << (*it)->get_blif_name() << "[" << (*it)->get_size() << "]" << endl;
	}
	switch (m_memtype) {
	case Init: {
		out << "# MEM_INIT(" << endl;
		assert(0);
		return;
	}
		break;
	case Read: {
		Inst * v_idx = *(m_ports.begin());
		int addr_hi = v_idx->get_size();
		int addr_lo = 0;
		int entry_end = 1 << v_idx->get_size();
		int entry_start = 0;
		out << "# MEM_READ: " << get_blif_name() << "[" << get_size()-1 << ":0] = " << get_name();
		out << "[ " << v_idx->get_blif_name() << "[" << addr_hi-1 << ":0] ]" << endl;
		for (unsigned c = 0; c < get_size(); c++) {
			out << ".names ";
			for(int i = addr_lo; i < addr_hi; i++) {
				out << v_idx->get_blif_name() << blif_suffix(i) << " ";
			}
			for(int i = entry_start; i < entry_end; i++) {
				out << get_name() << blif_suffix(i) << blif_suffix(c) << " ";
			}
			out << get_blif_name() << blif_suffix(c) << endl;
			for(int i = entry_start; i < entry_end; i++) {
				for(int j = addr_lo; j < addr_hi; j++) {
					int t = i >> j;
					if (t & 1) {
						out << "1";
					} else {
						out << "0";
					}
				}
				for(int j = entry_start; j < entry_end; j++) {
					if (i == j) {
						out << "1";
					} else {
						out << "0";
					}
				}
				out << " 1" << endl;
			}
		}
	}
		break;
	case Write: {
		assert(m_ports.size() >= 3);
		InstL::iterator it = m_ports.begin();
		Inst * v_idx = *(it++);
		Inst * v_con = *(it++);
		Inst * v_data = *(it);
		assert(v_con->get_size() == 1);
		
		int addr_hi = v_idx->get_size();
		int addr_lo = 0;
		int entry_end = 1 << v_idx->get_size();
		//int entry_start = 0;
		
		out << "# MEM_WRITE: " << get_blif_name() << "[" << get_size()-1 << ":0] = " << get_name();
		out << "[ " << v_idx->get_blif_name() << "[" << addr_hi-1 << ":" << addr_lo << "] ]" << endl;
		
		for(int c = 0; c < entry_end; c++) {
			for (unsigned i = 0; i < get_size(); i++) {
				out << ".names ";
				for(int j = addr_lo; j < addr_hi; j++) {
					out << v_idx->get_blif_name() << blif_suffix(j) << " ";
				}
				out << v_con->get_blif_name() << " ";
				out << v_data->get_blif_name() << blif_suffix(i) << " ";
				out << get_name() << blif_suffix(c) << blif_suffix(i) << " ";
				out << get_blif_name() << blif_suffix(c) << blif_suffix(i) << endl;
				for(int j = addr_lo; j < addr_hi; j++) {
					int t = c >> j;
					if (t & 1)
						out << "1";
					else
						out << "0";
				}
				out << "11- 1" << endl;
				for(int j = addr_lo; j < addr_hi; j++) {
					int t = c >> j;
					if (t & 1)
						out << "1";
					else
						out << "0";
				}
				out << "0-1 1" << endl;
				out << ".latch " << get_blif_name() << blif_suffix(c) << blif_suffix(i) << " ";
				out << get_name() << blif_suffix(c) << blif_suffix(i);
				out << endl;
			}
		}
	}
		break;
	default:
		assert(0);
	}
}


void UFInst::print_blif(std::ostream& out){
	out << "# UFInst: " << get_blif_name() << endl;
	assert(0);
}


//####################################################################
//PARTIAL_BIT_BLAST
//####################################################################
Inst *SigInst::bit_blast(InstToInstM& bb_map, bool init_visit){
	if(init_visit){
		Inst::init_visit();
	}
	if(get_visit()){
		if(m_size == 1){
			return this;
		}else{
			return bb_map[this];
		}
	}
	set_visit();
	Inst *ve_res;

	if((m_size == 1) || ((m_name.length() > 5) && (m_name.substr(m_name.length()-5) == "$next"))){
		return this;
	}else{
		InstL vel_concat;

		map<std::string, Inst*>::iterator hm_it = SigInst::hm_SigInst.find(m_name+"$next");
		if(hm_it != SigInst::hm_SigInst.end()){	// meaning state variables !!
//		if((m_name.substr(m_name.length()-5) == "$next") || (hm_it != SigInst::hm_SigInst.end())){	// meaning state variables !!
#if 1
			for(int i = 0; i < (int)m_size; ++i){
				Inst *ve_bit = ExInst::create(this, i, i);
				vel_concat.push_back(ve_bit);
			}
#else
			
			if((m_name.size() > 5) && (m_name.substr(m_name.size() - 5) == "$next")){
				for(int i = 0; i < (int)m_size; ++i){
					ostringstream oss;
					oss << m_name.substr(0, m_name.size() - 5) << "$" << i << "$next";
					
					Inst *ve_bit = SigInst::create(oss.str(), 1);
					vel_concat.push_back(ve_bit);
					
				}
			}else
			{
				for(int i = 0; i < (int)m_size; ++i){
					ostringstream oss;
					oss << m_name << "$" << i;
					
					Inst *ve_bit = SigInst::create(oss.str(), 1);
					vel_concat.push_back(ve_bit);
					
				}
				
				InstL vel_concat2;
				// We should bit-blast $next signal
				Inst *ve_next_sig = SigInst::create(m_name+"$next", m_size);
				for(int i = 0; i < (int)m_size; ++i){
					ostringstream oss;
					oss << m_name << "$" << i << "$next";
					
					Inst *ve_bit = SigInst::create(oss.str(), 1);
					vel_concat2.push_back(ve_bit);
				}
				ve_res = OpInst::create(OpInst::Concat, vel_concat2);
				bb_map[ve_next_sig] = ve_res;
				
			}
#endif			
		}else{
			for(int i = 0; i < (int)m_size; ++i){
				ostringstream oss;
				oss << m_name << "$" << i;
				
				Inst *ve_bit = SigInst::create(oss.str(), 1, SORT());
				vel_concat.push_back(ve_bit);
				
			}
		}
		ve_res = OpInst::create(OpInst::Concat, vel_concat);
	}
	bb_map[this] = ve_res;
	return ve_res;
}

Inst *NumInst::bit_blast(InstToInstM& bb_map, bool init_visit){
	if(init_visit){
		Inst::init_visit();
	}
	if(get_visit()){
		return bb_map[this];
	}
	set_visit();

	
	if(m_size == 1){
		bb_map[this] = this;
		return this;
	}
	
	string tsnum = m_mpz.get_str(2);
	

	if(tsnum[0] == '-'){
		// TODO support negative values (do we need this?)
		tsnum = tsnum.substr(1);
	}

	string extended_snum((m_size - tsnum.length()), '0');
	extended_snum.append(tsnum);
	InstL vel_concat;
	for (int i = get_size() - 1; i >= 0; --i) {
		Inst *ve_bit;

		if (extended_snum[i] == '1') {
			ve_bit = NumInst::create(1, 1, SORT());
		} else {
			ve_bit = NumInst::create(0, 1, SORT());
		}
		vel_concat.push_back(ve_bit);
	}

	Inst *ve_res = OpInst::create(OpInst::Concat, vel_concat);
	bb_map[this] = ve_res;
	return ve_res;
}

/// Aman
Inst *WireInst::bit_blast(InstToInstM& bb_map, bool init_visit){
	assert(0);
	return NULL;
}

Inst *ConstInst::bit_blast(InstToInstM& bb_map, bool init_visit){
	assert(0);
	return NULL;
}
/// END

Inst *ExInst::bit_blast(InstToInstM& bb_map, bool init_visit){
	if(init_visit){
		Inst::init_visit();
	}
	if(get_visit()){
		return bb_map[this];
	}
	set_visit();
	
	InstL vel_concat;
	const InstL* ch = get_children();
	if (ch) {
		Inst *ve_bit = (ch->front())->bit_blast(bb_map);
		if(ve_bit->get_type() == Op && (OpInst::as(ve_bit)->get_op() == OpInst::Concat)){
			assert(ve_bit->get_size() == ve_bit->get_children()->size());
			const InstL* concat_ch = ve_bit->get_children();
			if(concat_ch){
				InstL::const_iterator cit = concat_ch->begin();
				for(int i = 0; i < (int)m_lo; ++i){
					++cit;
				}
				for(int i = 0; i < (int)m_size; ++i){
					vel_concat.push_back(*cit);
					++cit;
				}
			}
		}else{
			// bit_blast should return the concatenation of bits
			assert(0);
		}
	}else{
// 		cout << "MM" << *this << endl;
// 		return this;
		// extraction of a single bit signal	?? Can this happen?
		Inst *ve_bit = this->bit_blast(bb_map);
		return ve_bit;
	}
	
	Inst *ve_res = OpInst::create(OpInst::Concat, vel_concat);
	bb_map[this] = ve_res;
	return ve_res;
}

void new_print2(ostream& fout, Inst* e, bool init_visit = false) {
	if (init_visit) {
		Inst::init_visit2();
	}

// 	if(e->get_type() == Num){
// 		NumInst* ve_num = NumInst::as(e);
// 		fout << ve_num->get_size() << "'d" << ve_num->get_num();
// 	}else if(e->get_type() == Sig){
// 		SigInst* ve_sig = SigInst::as(e);
// 		fout << ve_sig->get_name();
// 	}
	
	if (e->get_visit2()){
		return;
	}
	e->set_visit2();

	if(e->get_type() == Num){
		fout << "n" << e->get_id() << "n" << " " << e->get_size() << " : ";
		NumInst* ve_num = NumInst::as(e);
		fout << ve_num->get_size() << "'d" << ve_num->get_num();
		fout << endl;
	}else if(e->get_type() == Sig){
		fout << "n" << e->get_id() << "n" << " " << e->get_size() << " : ";
		SigInst* ve_sig = SigInst::as(e);
		fout << ve_sig->get_name();
		fout << endl;
	}else if(e->get_type() == Op){
		OpInst *ve_op = OpInst::as(e);
		const InstL* chs = e->get_children();
		OpInst::OpType e_op = ve_op->get_op();
		
		{
			InstL::const_iterator it = chs->begin();
			for (InstL::const_iterator end_it = chs->end(); it != end_it; ++it) {
				Inst *ch = *it;
				new_print2(fout, ch);
			}
		}
		
		fout << "n" << e->get_id() << "n" << " " << e->get_size() << " : ";
		if (e_op == OpInst::Future) {
			fout << OpInst::op2str(e_op) << "(";
			fout << "n" << (*(chs->begin()))->get_id() << "n";
			fout << ")";
		} else if (e_op == OpInst::Concat) {
			fout << "{";
			InstL::const_reverse_iterator it = chs->rbegin();
			fout << "n" << (*it)->get_id() << "n";
			it++;
			for (InstL::const_reverse_iterator end_it = chs->rend(); it != end_it; ++it){
				fout << " , " << "n" << (*it)->get_id() << "n";
			}
			fout << "}";
		} else if (e_op == OpInst::Ternary) {
			assert(chs->size() == 3);
			InstL::const_iterator it = chs->begin();
			fout << "(";
			fout << "n" << (*it)->get_id() << "n";
			fout << "?";
			it++;
			fout << "n" << (*it)->get_id() << "n";
			fout << ":";
			it++;
			fout << "n" << (*it)->get_id() << "n";
			fout << ")";
		} else if (e_op == OpInst::LogAnd) {
			InstL::const_iterator it = chs->begin();
	//		fout << "(" << endl << "	" << (*it)->get_id();
			fout << "(" << "n" << (*it)->get_id() << "n";
			it++;
			for (InstL::const_iterator end_it = chs->end(); it != end_it; ++it) {
	//			fout << " " << OpInst::op2str(e_op) << " " << endl << "	" << (*it)->get_id();
				fout << " " << OpInst::op2str(e_op) << " " << "n" << (*it)->get_id() << "n";
			}
			fout << ")";
		} else {
			unsigned sz = chs->size();
// 			if (sz == 1) {
// 				fout << OpInst::OpInst::op2str(e_op);
// 				ostringstream ss;
// 				ss << *(*(chs->begin()));
// 				if ((*(chs->begin()))->get_type() == Op || (*(chs->begin()))->get_type() == Ex)
// 					fout << "(" << ss.str() << ")";
// 				else
// 					fout << ss.str();
// 			} else 
			{
				assert(sz != 0);
				InstL::const_iterator it = chs->begin();
				fout << "(";
				if(chs->size() == 1){
					fout << OpInst::op2str(e_op);
				}
				fout << "n" << (*it)->get_id() << "n";
				it++;
				for (InstL::const_iterator end_it = chs->end(); it != end_it; ++it) {
					fout << " " << OpInst::op2str(e_op) << " " << "n" << (*it)->get_id() << "n";
				}
				fout << ")";
			}
		}
		fout << endl;
	}else if(e->get_type() == Ex){
		const InstL* chs = e->get_children();
		Inst *ch = chs->front();
		new_print2(fout, ch);
		fout << "n" << e->get_id() << "n" << " " << e->get_size() << " : ";
		ExInst *ve_ex = ExInst::as(e);
		bool complex = (ch->get_type() != Sig && ch->get_type() != Num);
		if (complex)
			fout << "(";
		fout << "n" << ch->get_id() << "n";
		if (complex)
			fout << ")";
		fout << "[" << ve_ex->get_hi() << ":" << ve_ex->get_lo() << "]";
		fout << endl;
	}else{
		assert(0);
	}
}

//TODO full implementation
Inst *OpInst::bit_blast(InstToInstM& bb_map, bool init_visit){
	if(init_visit){
		Inst::init_visit();
	}
	if(get_visit()){
		return bb_map[this];
	}
	set_visit();
	
	InstL chs_top;
	const InstL* ch = get_children();
	if (ch) {
		for (InstL::const_iterator cit = ch->begin(); cit != ch->end(); ++cit) {
			Inst *ve_bit = (*cit)->bit_blast(bb_map);
			if(!ve_bit){
				//cout << *this << endl;
				new_print2(cout, this, true);
				return NULL;
			}
			chs_top.push_back(ve_bit);
		}
	}
	
	Inst *ve_res;
	if((chs_top.size() < 3) || (m_op == Concat) || (m_op == Ternary)){
		//cout << "op: " << *this << endl;
		ve_res = bit_blast_table(m_op, chs_top);
		if(!ve_res){
//			int idx = 0;
// 			for(InstToInstM::iterator mit = bb_map.begin(); mit != bb_map.end(); ++mit){
// 				cout << "bb_map: " << idx++ << endl;
// 				cout << *(mit->first) << endl;
// 				cout << *(mit->second) << endl;
// 			}
			assert(0);

			//cout << *this << endl;
			return NULL;
		}
		//cout << "ve_res: " << *ve_res << endl;
	}else{
		InstL chs_top_new;
		InstL::iterator cit = chs_top.begin();
		chs_top_new.push_back(*cit++);
		while(1){
			chs_top_new.push_back(*cit++);
			ve_res = bit_blast_table(m_op, chs_top_new);
			
			if(cit == chs_top.end()){
				break;
			}
			chs_top_new.clear();
			chs_top_new.push_back(ve_res);
		}
	}

	bb_map[this] = ve_res;
	return ve_res;
}

Inst *MemInst::bit_blast(InstToInstM& bb_map, bool init_visit){
	assert(0);
}

Inst *UFInst::bit_blast(InstToInstM& bb_map, bool init_visit){
	assert(0);
}

Inst *OpInst::bit_blast_table(OpType op_type, InstL &chs_top){
	InstL::const_iterator cit = chs_top.begin();
	InstL vel_concat;
	Inst *ve_ch0 = *cit++;
	int op_size = ve_ch0->get_size();
	
	switch (op_type) {
	case Minus:
		if(m_size == 1){
			return ve_ch0;
		}else{
#if 0	// this one has many double-negations
			InstL::const_iterator cit_1 = ve_ch0->get_children()->begin();
			Inst *ve_bit = *cit_1++;
			Inst *ve_out = ve_bit;
			Inst *ve_not = OpInst::create(OpInst::LogNot, ve_bit);
			Inst *ve_carry = ve_not;
			vel_concat.push_back(ve_out);
			for (int i = 1; i < (int)m_size; ++i) {
				ve_bit = *cit_1++;
				ve_not = OpInst::create(OpInst::LogNot, ve_bit);
				ve_out = OpInst::create(OpInst::LogXor, ve_carry, ve_not);
				vel_concat.push_back(ve_out);
				if (i != ((int)m_size - 1)){
					ve_carry = OpInst::create(OpInst::LogAnd, ve_carry, ve_not);
				}
			}
			Inst *ve_res = OpInst::create(OpInst::Concat, vel_concat, 0, false);
			//bb_map[this] = ve_res;
			return ve_res;
#else
			InstL::const_iterator cit_1 = ve_ch0->get_children()->begin();
			Inst *ve_bit = *cit_1++;
			Inst *ve_out = ve_bit;
			Inst *ve_carry = ve_bit;
			vel_concat.push_back(ve_out);
			for (int i = 1; i < (int)m_size; ++i) {
				ve_bit = *cit_1++;
				ve_out = OpInst::create(OpInst::LogXor, ve_carry, ve_bit);
				vel_concat.push_back(ve_out);
				if (i != ((int)m_size - 1)){
					ve_carry = OpInst::create(OpInst::LogOr, ve_carry, ve_bit);
				}
			}
			Inst *ve_res = OpInst::create(OpInst::Concat, vel_concat, 0, false);
			//bb_map[this] = ve_res;
			return ve_res;
#endif
		}
	//TODO check correctness
	case Mult: {
		Inst *ve_ch1 = *cit;
		InstL::const_iterator cit_0 = (ve_ch0)->get_children()->begin();
		InstL::const_iterator cit_1 = (ve_ch1)->get_children()->begin();
		vector<Inst*> vec_ch0;
		vector<Inst*> vec_ch1;
		vector<Inst*> vec_temp;
		for(; cit_0 != (ve_ch0)->get_children()->end(); ++cit_0){
			vec_ch0.push_back(*cit_0);
		}
		for(; cit_1 != (ve_ch1)->get_children()->end(); ++cit_1){
			vec_ch1.push_back(*cit_1);
		}
		
		int a_idx = 0;
		int b_idx = 0;
		int t_idx = 0;
		list<int> l_to_add;
		Inst *ve_bit;
		
// 		cout << "BEFORE	##	w_o: " << w_o << ", w_i0: " << w_i0 << ", w_i1: " << w_i1 << endl;
		// width adjustments
		
		int w_i0 = (ve_ch0)->get_children()->size();
		int w_i1 = (ve_ch1)->get_children()->size();
		int w_o = m_size;
		int w_o_original = w_o;
		if((w_i0 > w_i1) && (w_o < (2*w_i0))){
			w_o = (2*w_i0);
		}else if((w_i0 <= w_i1) && (w_o < (2*w_i1))){
			w_o = (2*w_i1);
		}
		int half_w_o = w_o / 2;
		if(half_w_o > (int)w_i0){
			for(int i = w_i0; i < half_w_o; ++i){
				vec_ch0.push_back(NumInst::create(0,1, SORT()));
			}
		}
		if(half_w_o > (int)w_i1){
			for(int i = w_i1; i < half_w_o; ++i){
				vec_ch1.push_back(NumInst::create(0,1, SORT()));
			}
		}
		w_i0 = half_w_o;
		w_i1 = half_w_o;
		m_size = w_o;
		
		
		
		for(int o_idx = 0; o_idx < ((int)m_size-1); o_idx++){
			list<int> l_to_add_next;
			int ta_idx = a_idx;
			int tb_idx = b_idx;
			for(; tb_idx <= a_idx; tb_idx++, ta_idx--){
				l_to_add.push_back(t_idx);
				Inst *ve_temp = OpInst::create(OpInst::LogAnd, vec_ch0[ta_idx], vec_ch1[tb_idx]);
				vec_temp.push_back(ve_temp);
				t_idx++;
			}

			while(!l_to_add.empty()){
				if(l_to_add.size() == 1){
					if(o_idx >= w_o_original){
						ve_bit = NumInst::create(0,1, SORT());
					}else{
						ve_bit = vec_temp[l_to_add.front()];
					}
					vel_concat.push_back(ve_bit);
					l_to_add.clear();
				}else if(l_to_add.size() == 2){
					Inst *ve_temp0 = vec_temp[l_to_add.front()];
					Inst *ve_temp1 = vec_temp[l_to_add.back()];
					if(o_idx >= w_o_original){
						ve_bit = NumInst::create(0,1, SORT());
					}else{
						ve_bit = OpInst::create(OpInst::LogXor, ve_temp0, ve_temp1);
					}
					vel_concat.push_back(ve_bit);
					Inst *ve_temp = OpInst::create(OpInst::LogAnd, ve_temp0, ve_temp1);
					vec_temp.push_back(ve_temp);
					l_to_add_next.push_back(t_idx);
					t_idx++;
					l_to_add.clear();
				}else{	//(l_to_add.size() >= 3)
					list<int>::iterator it0 = l_to_add.begin();
					list<int>::iterator it1 = it0;
					it1++;
					list<int>::iterator it2 = it1;
					it2++;
					// carry
					l_to_add_next.push_back(t_idx);
					
					Inst *ve_temp0 = vec_temp[*it0];
					Inst *ve_temp1 = vec_temp[*it1];
					Inst *ve_temp2 = vec_temp[*it2];

					Inst *ve_temp;
					
					Inst *ve_and1 = OpInst::create(OpInst::LogAnd, ve_temp0, ve_temp1);
					Inst *ve_and2 = OpInst::create(OpInst::LogAnd, ve_temp0, ve_temp2);
					Inst *ve_or = OpInst::create(OpInst::LogOr, ve_and1, ve_and2);
					ve_and2 = OpInst::create(OpInst::LogAnd, ve_temp1, ve_temp2);
					ve_temp = OpInst::create(OpInst::LogOr, ve_or, ve_and2);

					vec_temp.push_back(ve_temp);
					t_idx++;
					
					// sum
					l_to_add.push_back(t_idx);
					ve_temp = OpInst::create(OpInst::LogXor, ve_temp0, ve_temp1);
					ve_temp = OpInst::create(OpInst::LogXor, ve_temp, ve_temp2);
					vec_temp.push_back(ve_temp);
					t_idx++;
					l_to_add.pop_front();
					l_to_add.pop_front();
					l_to_add.pop_front();
				}
			}

			if(a_idx < (w_i0-1)){
				a_idx++;
			}else{
				b_idx++;
			}
			l_to_add = l_to_add_next;
		}
		
// 		cout << "l_to_add.front(): " << l_to_add.front() << endl;
// 		cout << "vec_temp.size()" << vec_temp.size() << endl;
		ve_bit = vec_temp[l_to_add.front()];
		vel_concat.push_back(ve_bit);
		
		InstL::iterator cit_begin = vel_concat.begin();
		InstL::iterator cit_end = cit_begin;
		for(int i=0; i < w_o_original; ++i){
			++cit_end;
		}
		InstL vel_concat_new(cit_begin, cit_end);
		
		Inst *ve_res = OpInst::create(OpInst::Concat, vel_concat_new, 0, false);
		return ve_res;
	}
	case Add:{
		Inst *ve_ch1 = *cit;
		// NO carry_in
		if(m_size == 1){
			Inst *ve_res = OpInst::create(OpInst::LogXor, ve_ch0, ve_ch1);
			return ve_res;
		}else{
			InstL::const_iterator cit_0 = (ve_ch0)->get_children()->begin();
			InstL::const_iterator cit_1 = (ve_ch1)->get_children()->begin();
			ve_ch0 = *cit_0++;
			ve_ch1 = *cit_1++;

			Inst *ve_sout = OpInst::create(OpInst::LogXor, ve_ch0, ve_ch1);
			Inst *ve_cout = OpInst::create(OpInst::LogAnd, ve_ch0, ve_ch1);
			vel_concat.push_back(ve_sout);
			for (int i = 1; i < (int)m_size; ++i) {
				ve_ch0 = *cit_0++;
				ve_ch1 = *cit_1++;
				Inst *ve_temp = OpInst::create(OpInst::LogXor, ve_cout, ve_ch0);
				ve_sout = OpInst::create(OpInst::LogXor, ve_temp, ve_ch1);
				vel_concat.push_back(ve_sout);
				if (i != ((int)m_size - 1)){
					// (ch0 & ch1) + (ch0 & cin) + (ch1 & cin)
					Inst *ve_and1 = OpInst::create(OpInst::LogAnd, ve_ch0, ve_ch1);
					Inst *ve_and2 = OpInst::create(OpInst::LogAnd, ve_ch0, ve_cout);
					Inst *ve_or = OpInst::create(OpInst::LogOr, ve_and1, ve_and2);
					ve_and2 = OpInst::create(OpInst::LogAnd, ve_ch1, ve_cout);
					ve_cout = OpInst::create(OpInst::LogOr, ve_or, ve_and2);
				}
			}
			Inst *ve_res = OpInst::create(OpInst::Concat, vel_concat, 0, false);
			return ve_res;
		}
	}
	case Sub:{
		Inst *ve_ch1 = *cit;
		// NO carry_in
		if(m_size == 1){
			Inst *ve_res = OpInst::create(OpInst::LogXor, ve_ch0, ve_ch1);
			return ve_res;
		}else{
//			ve_out = ve_ch1 - ve_ch0
// 			InstL::const_iterator cit_0 = (ve_ch0)->get_children()->begin();
// 			InstL::const_iterator cit_1 = (ve_ch1)->get_children()->begin();

//			ve_out = ve_ch0 - ve_ch1
			InstL::const_iterator cit_0 = (ve_ch1)->get_children()->begin();
			InstL::const_iterator cit_1 = (ve_ch0)->get_children()->begin();
			ve_ch0 = *cit_0++;
			ve_ch0 = OpInst::create(OpInst::LogNot, ve_ch0);
			ve_ch1 = *cit_1++;

			Inst *ve_sout = OpInst::create(OpInst::LogXNor, ve_ch0, ve_ch1);
			Inst *ve_cout = OpInst::create(OpInst::LogOr, ve_ch0, ve_ch1);
			
			//cout << "ve_ch0: " << *ve_ch0 << ", ve_ch1: " << *ve_ch1 << endl;
			
			vel_concat.push_back(ve_sout);
			for (int i = 1; i < (int)m_size; ++i) {
				ve_ch0 = *cit_0++;
				ve_ch0 = OpInst::create(OpInst::LogNot, ve_ch0);
				ve_ch1 = *cit_1++;
				//cout << "ve_ch0: " << *ve_ch0 << ", ve_ch1: " << *ve_ch1 << endl;

				Inst *ve_temp = OpInst::create(OpInst::LogXor, ve_cout, ve_ch0);
				ve_sout = OpInst::create(OpInst::LogXor, ve_temp, ve_ch1);
				vel_concat.push_back(ve_sout);
				if (i != ((int)m_size - 1)){
					// (ch0 & ch1) + (ch0 & cin) + (ch1 & cin)
					Inst *ve_and1 = OpInst::create(OpInst::LogAnd, ve_ch0, ve_ch1);
					Inst *ve_and2 = OpInst::create(OpInst::LogAnd, ve_ch0, ve_cout);
					Inst *ve_or = OpInst::create(OpInst::LogOr, ve_and1, ve_and2);
					ve_and2 = OpInst::create(OpInst::LogAnd, ve_ch1, ve_cout);
					ve_cout = OpInst::create(OpInst::LogOr, ve_or, ve_and2);
				}
			}
			Inst *ve_res = OpInst::create(OpInst::Concat, vel_concat, 0, false);
			return ve_res;
		}
	}
	//TODO optimize (a == 1'b1) -> a
	case Eq:{
		Inst *ve_ch1 = *cit;
		Inst *num_true = NumInst::create(1, 1, SORT());
		Inst *num_false = NumInst::create(0, 1, SORT());
		if(op_size == 1){
			Inst *ve_res;
			if(ve_ch1 == num_true){
				ve_res = ve_ch0;
			}else if(ve_ch1 == num_false){
				ve_res = OpInst::create(OpInst::LogNot, ve_ch0);
			}else{
				ve_res = OpInst::create(OpInst::LogXNor, ve_ch0, ve_ch1);
			}
			//cout << "table, ve_res1: " << *ve_res << endl;
			return ve_res;
		}else{
			Inst *ve_res;
			//if ve_ch0 is a $next reg (next signal of a register)
			SigInst *sve = SigInst::as(ve_ch0);
			if(sve){
				string sig_name = sve->get_name();
				if((sig_name.length() > 5) &&(sig_name.substr(sig_name.length() - 5) == "$next")){
					ve_res = OpInst::create(OpInst::Eq, ve_ch0, ve_ch1);
					return ve_res;
				}
			}

			for (int i = 0; i < op_size; ++i){
				Inst *lhs = ExInst::create(ve_ch0, i, i);
				Inst *rhs = ExInst::create(ve_ch1, i, i);
				Inst *ve_bit;
				if(ve_ch1 == num_true){
					ve_bit = lhs;
				}else if(ve_ch1 == num_false){
					ve_bit = OpInst::create(OpInst::LogNot, lhs);
				}else{
					ve_bit = OpInst::create(OpInst::LogXNor, lhs, rhs);
				}
				if(i != 0){
					ve_res = OpInst::create(OpInst::LogAnd, ve_res, ve_bit);
				}else{
					ve_res = ve_bit;
				}
			}


// if(!ve_ch0->get_children() || !ve_ch1->get_children() || ((ve_ch0)->get_children()->size() != (ve_ch1)->get_children()->size())){
// 	cout << *ve_ch0 << endl;
// 	cout << *ve_ch1 << endl;
// 	cout << *this << endl;
// 	return NULL;
// }
//
// 			InstL::const_iterator cit_0 = (ve_ch0)->get_children()->begin();
// 			InstL::const_iterator cit_1 = (ve_ch1)->get_children()->begin();
// 			Inst *ve_res;
// 			for (int i = 0; i < op_size; ++i, ++cit_0, ++cit_1) {
// 				ve_ch0 = *cit_0;
// 				ve_ch1 = *cit_1;
//
// 				Inst *ve_bit = OpInst::create(OpInst::LogXNor, ve_ch0, ve_ch1);
// 				if(i != 0){
// 					ve_res = OpInst::create(OpInst::LogAnd, ve_res, ve_bit);
// 				}else{
// 					ve_res = ve_bit;
// 				}
// 			}
			//cout << "table, ve_res2: " << *ve_res << ", ve_ch0->get_size():" << op_size << endl;
			return ve_res;
		}
	}
	case NotEq:{
		Inst *ve_ch1 = *cit;
		Inst *num_true = NumInst::create(1, 1, SORT());
		Inst *num_false = NumInst::create(0, 1, SORT());
		if(op_size == 1){
			Inst *ve_res;
			if(ve_ch1 == num_true){
				ve_res = OpInst::create(OpInst::LogNot, ve_ch0);
			}else if(ve_ch1 == num_false){
				ve_res = ve_ch0;
			}else{
				ve_res = OpInst::create(OpInst::LogXor, ve_ch0, ve_ch1);
			}
			return ve_res;
		}else{
			Inst *ve_res;
			for (int i = 0; i < op_size; ++i){
				Inst *lhs = ExInst::create(ve_ch0, i, i);
				Inst *rhs = ExInst::create(ve_ch1, i, i);
				Inst *ve_bit;
				if(ve_ch1 == num_true){
					ve_bit = OpInst::create(OpInst::LogNot, lhs);
				}else if(ve_ch1 == num_false){
					ve_bit = lhs;
				}else{
					ve_bit = OpInst::create(OpInst::LogXor, lhs, rhs);
				}
				if(i != 0){
					ve_res = OpInst::create(OpInst::LogOr, ve_res, ve_bit);
				}else{
					ve_res = ve_bit;
				}
			}
			return ve_res;
		}
	}
	case Le:{
		Inst *ve_ch1 = *cit;
		if(op_size == 1){
			Inst *ve_gt = OpInst::create(OpInst::LogAnd, ve_ch0, OpInst::create(OpInst::LogNot, ve_ch1));
			return ve_gt;
		}else{
			InstL::const_reverse_iterator rcit_0 = (ve_ch0)->get_children()->rbegin();
			InstL::const_reverse_iterator rcit_1 = (ve_ch1)->get_children()->rbegin();
			ve_ch0 = *rcit_0++;
			ve_ch1 = *rcit_1++;
			Inst *ve_gt = OpInst::create(OpInst::LogAnd, ve_ch0, OpInst::create(OpInst::LogNot, ve_ch1));
			Inst *ve_eq = OpInst::create(OpInst::LogXNor, ve_ch0, ve_ch1);
			
			for (int i = 1; i < op_size; ++i) {
				ve_ch0 = *rcit_0++;
				ve_ch1 = *rcit_1++;
				Inst *ve_gt_temp = OpInst::create(OpInst::LogAnd, ve_ch0, OpInst::create(OpInst::LogNot, ve_ch1));
				ve_gt_temp = OpInst::create(OpInst::LogAnd, ve_eq, ve_gt_temp);
				ve_gt = OpInst::create(OpInst::LogOr, ve_gt, ve_gt_temp);

				if(i != (op_size - 1)){
					Inst *ve_eq_temp = OpInst::create(OpInst::LogXNor, ve_ch0, ve_ch1);
					ve_eq = OpInst::create(OpInst::LogAnd, ve_eq, ve_eq_temp);
				}
			}
			return ve_gt;
		}
	}
	case Gr:{
		Inst *ve_ch1 = *cit;
		if(op_size == 1){
			Inst *ve_le = OpInst::create(OpInst::LogAnd, OpInst::create(OpInst::LogNot, ve_ch0), ve_ch1);
			return ve_le;
		}else{
			InstL::const_reverse_iterator rcit_0 = (ve_ch0)->get_children()->rbegin();
			InstL::const_reverse_iterator rcit_1 = (ve_ch1)->get_children()->rbegin();
			ve_ch0 = *rcit_0++;
			ve_ch1 = *rcit_1++;
			Inst *ve_le = OpInst::create(OpInst::LogAnd, OpInst::create(OpInst::LogNot, ve_ch0), ve_ch1);
			Inst *ve_eq = OpInst::create(OpInst::LogXNor, ve_ch0, ve_ch1);
			
			for (int i = 1; i < op_size; ++i) {
				ve_ch0 = *rcit_0++;
				ve_ch1 = *rcit_1++;
				Inst *ve_le_temp = OpInst::create(OpInst::LogAnd, OpInst::create(OpInst::LogNot, ve_ch0), ve_ch1);
				ve_le_temp = OpInst::create(OpInst::LogAnd, ve_eq, ve_le_temp);
				ve_le = OpInst::create(OpInst::LogOr, ve_le, ve_le_temp);

// 				cout << "ve_eq: " << *ve_eq << endl;
// 				cout << "ve_le_temp: " << *ve_le_temp << endl;
// 				cout << "Le: " << *ve_le << endl;

				if(i != (op_size - 1)){
					Inst *ve_eq_temp = OpInst::create(OpInst::LogXNor, ve_ch0, ve_ch1);
					ve_eq = OpInst::create(OpInst::LogAnd, ve_eq, ve_eq_temp);
				}
			}
			return ve_le;
		}
	}
	case GrEq:{	// negation of Le
		Inst *ve_ch1 = *cit;
		if(op_size == 1){
			Inst *ve_gt = OpInst::create(OpInst::LogAnd, ve_ch0, OpInst::create(OpInst::LogNot, ve_ch1));
			return ve_gt;
		}else{
			InstL::const_reverse_iterator rcit_0 = (ve_ch0)->get_children()->rbegin();
			InstL::const_reverse_iterator rcit_1 = (ve_ch1)->get_children()->rbegin();
			ve_ch0 = *rcit_0++;
			ve_ch1 = *rcit_1++;
			Inst *ve_gt = OpInst::create(OpInst::LogAnd, ve_ch0, OpInst::create(OpInst::LogNot, ve_ch1));
			Inst *ve_eq = OpInst::create(OpInst::LogXNor, ve_ch0, ve_ch1);
			
			for (int i = 1; i < op_size; ++i) {
				ve_ch0 = *rcit_0++;
				ve_ch1 = *rcit_1++;
				Inst *ve_gt_temp = OpInst::create(OpInst::LogAnd, ve_ch0, OpInst::create(OpInst::LogNot, ve_ch1));
				ve_gt_temp = OpInst::create(OpInst::LogAnd, ve_eq, ve_gt_temp);
				ve_gt = OpInst::create(OpInst::LogOr, ve_gt, ve_gt_temp);

				if(i != (op_size - 1)){
					Inst *ve_eq_temp = OpInst::create(OpInst::LogXNor, ve_ch0, ve_ch1);
					ve_eq = OpInst::create(OpInst::LogAnd, ve_eq, ve_eq_temp);
				}
			}
			return OpInst::create(OpInst::LogNot, ve_gt);
		}
	}
	case LeEq:{
		Inst *ve_ch1 = *cit;
		if(op_size == 1){
			Inst *ve_le = OpInst::create(OpInst::LogAnd, OpInst::create(OpInst::LogNot, ve_ch0), ve_ch1);
			return ve_le;
		}else{
			InstL::const_reverse_iterator rcit_0 = (ve_ch0)->get_children()->rbegin();
			InstL::const_reverse_iterator rcit_1 = (ve_ch1)->get_children()->rbegin();
			ve_ch0 = *rcit_0++;
			ve_ch1 = *rcit_1++;
			Inst *ve_le = OpInst::create(OpInst::LogAnd, OpInst::create(OpInst::LogNot, ve_ch0), ve_ch1);
			Inst *ve_eq = OpInst::create(OpInst::LogXNor, ve_ch0, ve_ch1);
			
			for (int i = 1; i < op_size; ++i) {
				ve_ch0 = *rcit_0++;
				ve_ch1 = *rcit_1++;
				Inst *ve_le_temp = OpInst::create(OpInst::LogAnd, OpInst::create(OpInst::LogNot, ve_ch0), ve_ch1);
				ve_le_temp = OpInst::create(OpInst::LogAnd, ve_eq, ve_le_temp);
				ve_le = OpInst::create(OpInst::LogOr, ve_le, ve_le_temp);

// 				cout << "ve_eq: " << *ve_eq << endl;
// 				cout << "ve_le_temp: " << *ve_le_temp << endl;
// 				cout << "Le: " << *ve_le << endl;

				if(i != (op_size - 1)){
					Inst *ve_eq_temp = OpInst::create(OpInst::LogXNor, ve_ch0, ve_ch1);
					ve_eq = OpInst::create(OpInst::LogAnd, ve_eq, ve_eq_temp);
				}
			}
			return OpInst::create(OpInst::LogNot, ve_le);
		}
	}
 	case BitWiseAnd:{
		Inst *ve_ch1 = *cit;
		if(m_size == 1){
			Inst *ve_res = OpInst::create(OpInst::LogAnd, ve_ch0, ve_ch1);
			return ve_res;
		}else{
			InstL::const_iterator cit_0 = (ve_ch0)->get_children()->begin();
			InstL::const_iterator cit_1 = (ve_ch1)->get_children()->begin();
			for (int i = 0; i < (int)m_size; ++i, ++cit_0, ++cit_1) {
				ve_ch0 = *cit_0;
				ve_ch1 = *cit_1;
				Inst *ve_bit = OpInst::create(OpInst::LogAnd, ve_ch0, ve_ch1);
				vel_concat.push_back(ve_bit);
			}
			Inst *ve_res = OpInst::create(OpInst::Concat, vel_concat, 0, false);
			return ve_res;
		}
	}
	case BitWiseOr:{
		Inst *ve_ch1 = *cit;
		if(m_size == 1){
			Inst *ve_res = OpInst::create(OpInst::LogOr, ve_ch0, ve_ch1);
			return ve_res;
		}else{
			InstL::const_iterator cit_0 = (ve_ch0)->get_children()->begin();
			InstL::const_iterator cit_1 = (ve_ch1)->get_children()->begin();
			for (int i = 0; i < (int)m_size; ++i, ++cit_0, ++cit_1) {
				ve_ch0 = *cit_0;
				ve_ch1 = *cit_1;
				Inst *ve_bit = OpInst::create(OpInst::LogOr, ve_ch0, ve_ch1);
				vel_concat.push_back(ve_bit);
			}
			Inst *ve_res = OpInst::create(OpInst::Concat, vel_concat, 0, false);
			return ve_res;
		}
	}
	case BitWiseNot:{
		if(m_size == 1){
			Inst *ve_res = OpInst::create(OpInst::LogNot, ve_ch0);
			return ve_res;
		}else{
			InstL::const_iterator cit_0 = (ve_ch0)->get_children()->begin();
			for (int i = 0; i < (int)m_size; ++i, ++cit_0) {
				ve_ch0 = *cit_0;
				Inst *ve_bit = OpInst::create(OpInst::LogNot, ve_ch0);
				vel_concat.push_back(ve_bit);
			}
			Inst *ve_res = OpInst::create(OpInst::Concat, vel_concat, 0, false);
			return ve_res;
		}
	}
	case BitWiseXor:{
		Inst *ve_ch1 = *cit;
		if(m_size == 1){
			Inst *ve_res = OpInst::create(OpInst::LogXor, ve_ch0, ve_ch1);
			return ve_res;
		}else{
			InstL::const_iterator cit_0 = (ve_ch0)->get_children()->begin();
			InstL::const_iterator cit_1 = (ve_ch1)->get_children()->begin();
			for (int i = 0; i < (int)m_size; ++i, ++cit_0, ++cit_1) {
				ve_ch0 = *cit_0;
				ve_ch1 = *cit_1;
				Inst *ve_bit = OpInst::create(OpInst::LogXor, ve_ch0, ve_ch1);
				vel_concat.push_back(ve_bit);
			}
			Inst *ve_res = OpInst::create(OpInst::Concat, vel_concat, 0, false);
			return ve_res;
		}
	}
	case BitWiseXNor:{
		Inst *ve_ch1 = *cit;
		if(m_size == 1){
			Inst *ve_res = OpInst::create(OpInst::LogXNor, ve_ch0, ve_ch1);
			return ve_res;
		}else{
			InstL::const_iterator cit_0 = (ve_ch0)->get_children()->begin();
			InstL::const_iterator cit_1 = (ve_ch1)->get_children()->begin();
			for (int i = 0; i < (int)m_size; ++i, ++cit_0, ++cit_1) {
				ve_ch0 = *cit_0;
				ve_ch1 = *cit_1;
				Inst *ve_bit = OpInst::create(OpInst::LogXNor, ve_ch0, ve_ch1);
				vel_concat.push_back(ve_bit);
			}
			Inst *ve_res = OpInst::create(OpInst::Concat, vel_concat, 0, false);
			return ve_res;
		}
	}
	case BitWiseNor:{
		Inst *ve_ch1 = *cit;
		if(m_size == 1){
			Inst *ve_res = OpInst::create(OpInst::LogNor, ve_ch0, ve_ch1);
			return ve_res;
		}else{
			InstL::const_iterator cit_0 = (ve_ch0)->get_children()->begin();
			InstL::const_iterator cit_1 = (ve_ch1)->get_children()->begin();
			for (int i = 0; i < (int)m_size; ++i, ++cit_0, ++cit_1) {
				ve_ch0 = *cit_0;
				ve_ch1 = *cit_1;
				Inst *ve_bit = OpInst::create(OpInst::LogNor, ve_ch0, ve_ch1);
				vel_concat.push_back(ve_bit);
			}
			Inst *ve_res = OpInst::create(OpInst::Concat, vel_concat, 0, false);
			return ve_res;
		}
	}
	case BitWiseNand:{
		Inst *ve_ch1 = *cit;
		if(m_size == 1){
			Inst *ve_res = OpInst::create(OpInst::LogNand, ve_ch0, ve_ch1);
			return ve_res;
		}else{
			InstL::const_iterator cit_0 = (ve_ch0)->get_children()->begin();
			InstL::const_iterator cit_1 = (ve_ch1)->get_children()->begin();
			for (int i = 0; i < (int)m_size; ++i, ++cit_0, ++cit_1) {
				ve_ch0 = *cit_0;
				ve_ch1 = *cit_1;
				Inst *ve_bit = OpInst::create(OpInst::LogNand, ve_ch0, ve_ch1);
				vel_concat.push_back(ve_bit);
			}
			Inst *ve_res = OpInst::create(OpInst::Concat, vel_concat, 0, false);
			return ve_res;
		}
	}
	case LogTrue:
		return NumInst::create(1,1, SORT());
	case LogFalse:
		return NumInst::create(0,1, SORT());
	case Identity:
	case LogNot:
	case LogAnd:
	case LogOr:
	case LogNand:
	case LogNor:
	case LogXor:
	case LogXNor:
		return OpInst::create(op_type, chs_top);
	case ReductionAnd:{
		if(op_size == 1){
			return ve_ch0;
		}else{
			InstL::const_iterator cit_0 = (ve_ch0)->get_children()->begin();
			Inst *ve_res = *cit_0++;
			for (int i = 1; i < op_size; ++i) {
				ve_ch0 = *cit_0++;
				ve_res = OpInst::create(OpInst::LogAnd, ve_res, ve_ch0);
			}
			return ve_res;
		}
	}
	case ReductionOr:{
		if(op_size == 1){
			return ve_ch0;
		}else{
			InstL::const_iterator cit_0 = (ve_ch0)->get_children()->begin();
			Inst *ve_res = *cit_0++;
			for (int i = 1; i < op_size; ++i) {
				ve_ch0 = *cit_0++;
				ve_res = OpInst::create(OpInst::LogOr, ve_res, ve_ch0);
			}
			return ve_res;
		}
	}
	case ReductionXor:{
		if(op_size == 1){
			return ve_ch0;
		}else{
			InstL::const_iterator cit_0 = (ve_ch0)->get_children()->begin();
			Inst *ve_res = *cit_0++;
			for (int i = 1; i < op_size; ++i) {
				ve_ch0 = *cit_0++;
				ve_res = OpInst::create(OpInst::LogXor, ve_res, ve_ch0);
			}
			return ve_res;
		}
	}
	case ReductionNand:{
		if(op_size == 1){
			return ve_ch0;
		}else{
			InstL::const_iterator cit_0 = (ve_ch0)->get_children()->begin();
			Inst *ve_res = *cit_0++;
			for (int i = 1; i < op_size; ++i) {
				ve_ch0 = *cit_0++;
				ve_res = OpInst::create(OpInst::LogAnd, ve_res, ve_ch0);
			}
			return OpInst::create(OpInst::LogNot, ve_res);
		}
	}
	case ReductionNor:{
		if(op_size == 1){
			return ve_ch0;
		}else{
			InstL::const_iterator cit_0 = (ve_ch0)->get_children()->begin();
			Inst *ve_res = *cit_0++;
			for (int i = 1; i < op_size; ++i) {
				ve_ch0 = *cit_0++;
				ve_res = OpInst::create(OpInst::LogOr, ve_res, ve_ch0);
			}
			return OpInst::create(OpInst::LogNot, ve_res);
		}
	}
	case ReductionXNor:{
		if(op_size == 1){
			return ve_ch0;
		}else{
			InstL::const_iterator cit_0 = (ve_ch0)->get_children()->begin();
			Inst *ve_res = *cit_0++;
			for (int i = 1; i < op_size; ++i) {
				ve_ch0 = *cit_0++;
				ve_res = OpInst::create(OpInst::LogXor, ve_res, ve_ch0);
			}
			return OpInst::create(OpInst::LogNot, ve_res);
		}
	}
	case ShiftL:{
    Inst *ve_ch1 = *cit;
    InstL::const_iterator cit_0 = (ve_ch0)->get_children()->begin();
    InstL::const_iterator cit_1;

    for (int pos = (int)m_size; pos > 0; --pos) {
//      cout << "c" << (m_size - pos) << " = ";
      Inst *ve_bit;
      for (int num = 0; (num < ((int)ve_ch0->get_size() - pos + 1)) && (num < (int)(0x1U << ve_ch1->get_size())); num++) {
        int i = (int)ve_ch0->get_size();
        InstL::const_iterator rcit_0 = (ve_ch0)->get_children()->begin();
        while((i - 1) != (pos - 1 + num)){
          ++rcit_0;
          --i;
        }
//        cout << "a" << (ve_ch0->get_size() - i) << ".";
        Inst* ve_and = *rcit_0;

        InstL::const_reverse_iterator rcit_1 = (ve_ch1)->get_children()->rbegin();
        for (int i = (int)ve_ch1->get_size(); i > 0; --i, ++rcit_1){
          Inst *ve_cnt;
          if((num >> (i - 1)) & 0x1U){
            ve_cnt = *rcit_1;
//            cout << "b" << (i - 1) << ".";
          }else{
            ve_cnt = OpInst::create(OpInst::LogNot, *rcit_1);
//            cout << "~b" << (i - 1) << ".";
          }
          ve_and = OpInst::create(OpInst::LogAnd, ve_and, ve_cnt);
        }
//        cout << " + ";

        if(num == 0){
          ve_bit = ve_and;
        }else{
          ve_bit = OpInst::create(OpInst::LogOr, ve_bit, ve_and);
        }
      }
//      cout << endl;
      vel_concat.push_back(ve_bit);
    }
//    cout << vel_concat << endl;
    Inst *ve_res = OpInst::create(OpInst::Concat, vel_concat, 0, false);
    return ve_res;
	}
	case ShiftR:{
		Inst *ve_ch1 = *cit;
		InstL::const_iterator cit_0 = (ve_ch0)->get_children()->begin();
		InstL::const_iterator cit_1;

		for (int pos = (int)m_size; pos > 0; --pos) {
//		  cout << "c" << (pos - 1) << " = ";
			Inst *ve_bit;
			for (int num = 0; (num < ((int)ve_ch0->get_size() - pos + 1)) && (num < (int)(0x1U << ve_ch1->get_size())); num++) {
				int i = (int)ve_ch0->get_size();
	      InstL::const_reverse_iterator rcit_0 = (ve_ch0)->get_children()->rbegin();
				while((i - 1) != (pos - 1 + num)){
					++rcit_0;
					--i;
				}
//	      cout << "a" << (i - 1) << ".";
        Inst* ve_and = *rcit_0;

        InstL::const_reverse_iterator rcit_1 = (ve_ch1)->get_children()->rbegin();
				for (int i = (int)ve_ch1->get_size(); i > 0; --i, ++rcit_1){
					Inst *ve_cnt;
					if((num >> (i - 1)) & 0x1U){
						ve_cnt = *rcit_1;
//		        cout << "b" << (i - 1) << ".";
					}else{
						ve_cnt = OpInst::create(OpInst::LogNot, *rcit_1);
//            cout << "~b" << (i - 1) << ".";
					}
					ve_and = OpInst::create(OpInst::LogAnd, ve_and, ve_cnt);
				}
//        cout << " + ";

				if(num == 0){
					ve_bit = ve_and;
				}else{
				  ve_bit = OpInst::create(OpInst::LogOr, ve_bit, ve_and);
				}
			}
//      cout << endl;
			vel_concat.push_front(ve_bit);
		}
//    cout << vel_concat << endl;
		Inst *ve_res = OpInst::create(OpInst::Concat, vel_concat, 0, false);
		return ve_res;
	}
	case Ternary:{
		Inst *ve_ch_cond = ve_ch0;
		Inst *ve_ch_true = *cit++;
		Inst *ve_ch_false = *cit;
#if 0
		if(m_size == 1){
			Inst *ve_and0 = OpInst::create(OpInst::LogAnd, ve_ch_cond, ve_ch_true);
			Inst *ve_and1 = OpInst::create(OpInst::LogAnd, OpInst::create(OpInst::LogNot, ve_ch_cond), ve_ch_false);
			Inst *ve_res = OpInst::create(OpInst::LogOr, ve_and0, ve_and1);
			return ve_res;
		}else{
			for (int i = 0; i < (int)m_size; ++i) {
				//ve_ch_cond = *cit_0;
				Inst *ve_ch_true_bit = ExInst::create(ve_ch_true, i, i);;
				Inst *ve_ch_false_bit = ExInst::create(ve_ch_false, i, i);;
				Inst *ve_and0 = OpInst::create(OpInst::LogAnd, ve_ch_cond, ve_ch_true_bit);
				Inst *ve_and1 = OpInst::create(OpInst::LogAnd, OpInst::create(OpInst::LogNot, ve_ch_cond), ve_ch_false_bit);
				Inst *ve_bit = OpInst::create(OpInst::LogOr, ve_and0, ve_and1);
				vel_concat.push_back(ve_bit);
			}
			Inst *ve_res = OpInst::create(OpInst::Concat, vel_concat, 0, false);
			return ve_res;
		}
#else
		if(m_size == 1){
			Inst *ve_res = OpInst::create(OpInst::Ternary, ve_ch_cond, ve_ch_true, ve_ch_false);
			return ve_res;
		}else{
			for (int i = 0; i < (int)m_size; ++i) {
				Inst *ve_ch_true_bit = ExInst::create(ve_ch_true, i, i);;
				Inst *ve_ch_false_bit = ExInst::create(ve_ch_false, i, i);;
				Inst *ve_bit = OpInst::create(OpInst::Ternary, ve_ch_cond, ve_ch_true_bit, ve_ch_false_bit);
				vel_concat.push_back(ve_bit);
			}
			Inst *ve_res = OpInst::create(OpInst::Concat, vel_concat, 0, false);
			return ve_res;
		}
#endif
	}
	case Concat:{
		while(1){
			if(ve_ch0->get_type() == Op && (OpInst::as(ve_ch0)->get_op() == OpInst::Concat)){
			//if((ve_ch0)->get_children()){
				InstL::const_iterator cit_0 = (ve_ch0)->get_children()->begin();
				for(; cit_0 != (ve_ch0)->get_children()->end(); ++cit_0){
					vel_concat.push_back(*cit_0);
				}
			}else{
				vel_concat.push_back(ve_ch0);
			}
			if(cit == chs_top.end()){
				break;
			}
			ve_ch0 = *cit++;
		}
		Inst *ve_res = OpInst::create(OpInst::Concat, vel_concat, 0, false);
// 		cout << "CONCAT-IN:" << *this << endl;
// 		cout << "CONCAT-OUT:" << *ve_res << endl;
		return ve_res;
	}
	default:
		cout << "\t(warning: operation " << op2str(op_type) << " is not supported for partial interpretation)" << endl;
		num_warnings++;
//		assert(0);
		return this;
	}
	
}


Inst* SigInst::bit_blast_version() {
	if(m_size == 1) {
		return this;
	}
	else {
		InstL vel_concat;

		for(int i = 0; i < (int)m_size; ++i){
			Inst *ve_bit = ExInst::create(this, i, i);
			vel_concat.push_back(ve_bit);
		}
		return OpInst::create(OpInst::Concat, vel_concat);
	}
}

Inst* NumInst::bit_blast_version() {
	if(m_size == 1) {
		return this;
	}
	else {
		string tsnum = m_mpz.get_str(2);

		if(tsnum[0] == '-'){
			cout << "\t(error: cannot handle negative numbers for now)" << endl;
			assert(0);
		}

		string extended_snum((m_size - tsnum.length()), '0');
		extended_snum.append(tsnum);
		InstL vel_concat;
		for (int i = get_size() - 1; i >= 0; --i) {
			Inst *ve_bit;

			if (extended_snum[i] == '1') {
				ve_bit = NumInst::create(1, 1, SORT());
			} else {
				ve_bit = NumInst::create(0, 1, SORT());
			}
			vel_concat.push_back(ve_bit);
		}

		return OpInst::create(OpInst::Concat, vel_concat, 0, false);
	}
}

Inst* WireInst::bit_blast_version() {
	if(m_size == 1) {
		return this;
	}
	else {
		InstL vel_concat;

		for(int i = 0; i < (int)m_size; ++i){
			Inst *ve_bit = ExInst::create(this, i, i);
			vel_concat.push_back(ve_bit);
		}
		return OpInst::create(OpInst::Concat, vel_concat);
	}
}

Inst* ConstInst::bit_blast_version() {
	assert(0);
}

Inst* OpInst::bit_blast_version() {
	if (get_euf_func_name() == "0") {
		return this;
	}
	else {
		const InstL* ch = get_children();
		assert(ch);

		InstL newCh;
		for (InstL::const_iterator cit = ch->begin(); cit != ch->end(); cit++) {
//			Inst* tve = (*cit)->bit_blast_version();
			Inst* tve = (*cit);
			InstL tveCh;
			for (int i = 0; i < tve->get_size(); i++) {
				Inst *ve_bit = ExInst::create(tve, i, i);
				tveCh.push_back(ve_bit);
			}
			tve = OpInst::create(Concat, tveCh);
			newCh.push_front(tve);
		}
		return bit_blast_table(m_op, newCh);
	}
}

Inst* ExInst::bit_blast_version() {
	if(m_size == 1) {
		return this;
	}
	else {
		if (get_exp()->get_type() != Op && get_exp()->get_type() != Ex)
			return this;

		InstL vel_concat;
		Inst* tve = get_exp()->bit_blast_version();
		assert (tve->get_type() == Op && OpInst::as(tve)->get_op() == OpInst::Concat);
		const InstL* ch = tve->get_children();
		assert(ch);
		assert(ch->size() == tve->get_size());
		InstL::const_iterator cit = ch->begin();
		for(int i = 0; i <= get_hi(); ++i){
			if (i >= get_lo())
				vel_concat.push_back(*cit);
			cit++;
		}
		return OpInst::create(OpInst::Concat, vel_concat);
	}
}

Inst* MemInst::bit_blast_version() {
	assert(0);
}

Inst* UFInst::bit_blast_version() {
	assert(0);
}

Inst* LambdaInst::bit_blast_version() {
	assert(0);
}

Inst* ArrayInst::bit_blast_version() {
	assert(0);
}


Inst* Inst::add_missing_wires() {
  Inst* topRet = this;

  const InstL* ch = topRet->get_children();
  if (ch) {
    InstL new_ch;
    bool need_new = false;
    for (InstL::const_iterator cit = ch->begin(); cit != ch->end(); cit++) {
      Inst* tve = (*cit);
      Inst* newTve = tve->add_missing_wires();

      if (OpInst::as(topRet) && OpInst::as(newTve)) {
//    	  cout << "\t(error: missing wire)\tin " << *topRet << endl;
//    	  assert(0);

    	  OpInst* op = OpInst::as(newTve);
    	  if (op) {
    	    Inst* w = op->get_wire();
    	    if (w == NULL)
    	    {
    	      switch(op->get_op()) {
    	//      case OpInst::Eq:
    	//      case OpInst::NotEq:
    	//      case OpInst::LogNot:
    	//        break;
    	      default: {
    	        string name = AVR_WIRE_NAME_PREFIX + to_string(++Inst::avr_wid);
    	        w = WireInst::create(name, newTve->get_size(), newTve);
    	        cout << "\t(creating wire " << *w << " for " << *newTve << ")" << endl;
    	        newTve = w;
    	      }
    	      }
    	    }
    	  }
      }

      if (newTve != tve)
        need_new = true;
      new_ch.push_back(newTve);
    }
    if (need_new)
      topRet = topRet->apply_children(new_ch);
  }


//  cout << *top << "\t->\t" << *topRet << endl;

  return topRet;
}


bool SigInst::interpret() {
#ifdef INTERPRET_UF_SIG
	if (m_size <= Config::g_interpret_uf_max_width && m_size <= INTERPRET_UF_SIG_LIMIT) {
		t_simple = bit_blast_version();
//		t_simple = t_simple->add_missing_wires();
		return true;
	}
#endif
	return false;
}

bool NumInst::interpret() {
#ifdef INTERPRET_UF_NUM
	if (m_size <= Config::g_interpret_uf_max_width && m_size <= INTERPRET_UF_NUM_LIMIT) {
		t_simple = bit_blast_version();
//		t_simple = t_simple->add_missing_wires();
	return true;
}
#endif
return false;
}

bool OpInst::interpret() {
#ifdef INTERPRET_UF_OP
  switch (m_op) {
  case Mult:
  case Concat:
  	return false;
  }
	if (m_size <= Config::g_interpret_uf_max_width && m_size <= INTERPRET_UF_OP_OUTLIMIT) {
		unsigned max_sz = 0;
		for (auto& v: m_exps)
			max_sz = max(max_sz, v->get_size());

		if (m_size <= Config::g_interpret_uf_max_width && max_sz <= INTERPRET_UF_OP_INPLIMIT) {
			t_simple = bit_blast_version();
//			t_simple = t_simple->add_missing_wires();
			return true;
		}
	}
#endif
	return false;
}

bool ExInst::interpret() {
//#ifdef INTERPRET_UF_OP
//	if (m_size <= Config::g_interpret_uf_max_width && m_size <= INTERPRET_UF_OP_OUTLIMIT) {
//		t_simple = bit_blast_version();
////		cout << *this << " -> " << *t_simple << endl;
//
////		t_simple = t_simple->add_missing_wires();
//		return true;
//	}
//#endif
	return false;
}


