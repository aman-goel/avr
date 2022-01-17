/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


#include "vwn.h"

// the simplification routine in Inst::create() converts the concatenation of extraction
// into identity. This conflicts with the routines in partial bit-blast functions


// AVR_NEW_CLT_MODE = new_clt_mode
// 0 : non calypto benchmarks
// 1 : calypto default	- turn on partitioning and partial bitblasting
// 2 : 154 series
// 3 : c17 series
static int new_clt_mode;

Config* config;

int num_warnings;

ofstream _resFile;
string _benchmark;

bool CompareBySz (Inst *first, Inst *second) {
	if (first->get_size() == second->get_size())
	{
		return !(first->get_id() < second->get_id());
	}
	else
		return first->get_size() < second->get_size();
}

void new_print(ostream& fout, Inst* e, bool init_visit = false) {
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

// 		if(e_op == OpInst::Mult && e->get_size() == 32){
// 			assert(0);
// 		}
		
		
		{
			InstL::const_iterator it = chs->begin();
			for (InstL::const_iterator end_it = chs->end(); it != end_it; ++it) {
				Inst *ch = *it;
				new_print(fout, ch);
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
		new_print(fout, ch);
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

// map_net_op<to, from> contains net-connections among Insts
// Our goal is to eliminate the intermediate nodes, so check
// map_net_op[ map_net_op[ ... map_net_op [to] ] ] until it reaches a leaf node
// connect_insts() updates map_net_op during computation like the following.
// new_from = map_net_op[ map_net_op[ ... map_net_op [to] ] ];
// ...
// map_net_op [ map_net_op [to] ] = new_from
// map_net_op [to] = new_from
static Inst *connect_insts(Inst *ve, InstToStringM& map_eq_str, InstToInstM& map_net_op, bool init){
	VWN_COUT_1("ve: " << *ve << endl);
	
	if (ve->find_next() && ve->get_type() == Sig)
		return ve;

	if (init) {
		Inst::init_visit();
	}

	if (ve->get_visit()){
		VWN_COUT_1("already visited" << endl);
		InstToInstM::iterator mit = map_net_op.find(ve);
		if(mit == map_net_op.end()){
			// means that "ve" is a signal
			return ve;
		}else{
			return mit->second;
		}
	}
	ve->set_visit();

	// skip intermediate nets
	Inst *new_ve = ve;
	while(1){
		InstToInstM::iterator mit = map_net_op.find(new_ve);
		if(mit == map_net_op.end()){
			break;
		}
		new_ve = mit->second;
		VWN_COUT_1("new_ve: " << *new_ve << endl);
	}

	// derive new children
	Inst *applied_ve = new_ve;
	const InstL* chs = new_ve->get_children();
	if(chs && !chs->empty()){
		InstL new_chs;
//		int i = 0;
		for(InstL::const_iterator cit = chs->begin(); cit != chs->end(); ++cit){
			Inst *ch = connect_insts(*cit, map_eq_str, map_net_op, false);
			new_chs.push_back(ch);
			VWN_COUT_1("ch: " << *ch << endl);
			//cout << "ch: " << *ch << endl;
// 			cout << "ch: " << i << endl;
// 			new_print(cout, ch, true);
// 			i++;
		}
		
#if 1
		{
			Inst *ve_in = new_chs.front();
			Inst *ve_in_back = new_chs.back();
			if(		// !(a ^ b) => (a == b)
				((new_ve->get_type() == Op) && (OpInst::as(new_ve)->get_op() == OpInst::LogNot)) &&
				((ve_in->get_type() == Op) && (OpInst::as(ve_in)->get_op() == OpInst::LogXor)) &&
				((ve_in->get_children())->size() == 2)
			){
				applied_ve = OpInst::create(OpInst::Eq, *(ve_in->get_children()));
			}else if(	// 1 ? a : b => a
				((new_ve->get_type() == Op) && (OpInst::as(new_ve)->get_op() == OpInst::Ternary)) &&
				((ve_in->get_type() == Num) && (NumInst::as(ve_in)->get_num() == 1))
			){
				InstL::iterator temp_it = new_chs.begin();
				++temp_it;
				applied_ve = *temp_it;
			}else if(	// 0 ? a : b => b
				((new_ve->get_type() == Op) && (OpInst::as(new_ve)->get_op() == OpInst::Ternary)) &&
				((ve_in->get_type() == Num) && (NumInst::as(ve_in)->get_num() == 0))
			){
				InstL::iterator temp_it = new_chs.begin();
				++temp_it;
				++temp_it;
				applied_ve = *temp_it;
			}else if(
				0 //(new_ve->get_type() == Op) && (OpInst::as(new_ve)->get_op() == OpInst::Concat)
			){
				// NOTE q = {a, b, c} OpInst::Concat : chs[0] = c, chs[1] = b, chs[2] = a
				// 1. // {q, (a? b[2]: c[2]), (a? b[1]: c[1]), (a? b[0]: c[0]), r} => {q, (a ? b[2:0] : c[2:0]), r}
				InstL new_chs_1;
				InstL thn_exps, els_exps;
				InstL::iterator temp_it = new_chs.begin();
				Inst *ve_pre = *temp_it;
				Inst *ve_pre_cond = NULL;
				//cout << "ve_pre: " << *ve_pre << endl;
				ve_pre = ((ve_pre->get_type() == Op) && (OpInst::as(ve_pre)->get_op() == OpInst::Ternary)) ? ve_pre : NULL;
				if(ve_pre){
					InstL::const_iterator t_chs = (ve_pre->get_children())->begin();
					ve_pre_cond = *t_chs;
					++t_chs;
					Inst *tve_thn = *t_chs;
					++t_chs;
					Inst *tve_els = *t_chs;
					thn_exps.push_back(tve_thn);
					els_exps.push_back(tve_els);
				}else{
					new_chs_1.push_back(*temp_it);
				}
				++temp_it;
				for(; temp_it != new_chs.end(); ++temp_it){
					bool update_pre = false;
					Inst *ve_curr_cond = NULL;
					Inst *ve_curr = *temp_it;
					Inst *tve_thn = NULL;
					Inst *tve_els = NULL;
					ve_curr = ((ve_curr->get_type() == Op) && (OpInst::as(ve_curr)->get_op() == OpInst::Ternary)) ? ve_curr : NULL;
					if(ve_curr){
						InstL::const_iterator t_chs = (ve_curr->get_children())->begin();
						ve_curr_cond = *t_chs;
						++t_chs;
						tve_thn = *t_chs;
						++t_chs;
						tve_els = *t_chs;
						if(ve_curr_cond == ve_pre_cond){
							thn_exps.push_back(tve_thn);
							els_exps.push_back(tve_els);
							continue;
						}else{
							update_pre = true;
						}
					}
					if(thn_exps.size() >= 2){
						Inst *tve_thn = OpInst::create(OpInst::Concat, thn_exps);
						Inst *tve_els = OpInst::create(OpInst::Concat, els_exps);
						Inst *tve_ite = OpInst::create(OpInst::Ternary, ve_pre_cond, tve_thn, tve_els);
						new_chs_1.push_back(tve_ite);
					}else{
						if(thn_exps.size() == 1){
							new_chs_1.push_back(ve_pre);
						}
					}
					thn_exps.clear();
					els_exps.clear();

					if(update_pre == true){
						thn_exps.push_back(tve_thn);
						els_exps.push_back(tve_els);
						ve_pre = ve_curr;
						ve_pre_cond = ve_curr_cond;
					}else{
						new_chs_1.push_back(*temp_it);
					}
				}
				if(thn_exps.size() >= 2){
// 					cout << "thn_exps: " << thn_exps << endl;
// 					cout << "els_exps: " << els_exps << endl;
					
					Inst *tve_thn = OpInst::create(OpInst::Concat, thn_exps);
					Inst *tve_els = OpInst::create(OpInst::Concat, els_exps);
					
// 					cout << "tve_thn: " << *tve_thn << endl;
// 					cout << "tve_els: " << *tve_els << endl;
					
					Inst *tve_ite = OpInst::create(OpInst::Ternary, ve_pre_cond, tve_thn, tve_els);
					new_chs_1.push_back(tve_ite);
				}else if(thn_exps.size() == 1){
					new_chs_1.push_back(ve_pre);
				}
//				cout << "new_chs_1: " << new_chs_1 << endl;

				
				// 2. {a[3], a[3], a[3], a[3] a[3], a[2], a[1], a[0]} => a[3] ? {4'b1111, a} : {4'd0, a}
				InstL new_chs_2;
				ve_in = new_chs_1.front();
				ve_in_back = new_chs_1.back();
				InstL::reverse_iterator temp_rit = new_chs_1.rbegin();
				++temp_rit;
				if((ve_in_back->get_size() == 1) && (ve_in_back == *temp_rit)){
					int num_length = 1;
//					unsigned long num_value = 1;
					string num_value_str = "1";
					for(; temp_rit != new_chs_1.rend(); ++temp_rit){
						if(ve_in_back != *temp_rit){
							break;
						}					
//						num_value += (unsigned long)((unsigned long)1 << num_length);
						num_value_str = "1" + num_value_str;
						num_length++;
					}
					//--temp_rit;
					for(; temp_rit != new_chs_1.rend(); ++temp_rit){
						new_chs_2.push_front(*temp_rit);
					}
//					new_chs_2.push_back(NumInst::create(num_value, num_length));
					new_chs_2.push_back(NumInst::create(num_value_str, num_length, 2));

					Inst *ve_c1 = OpInst::create(OpInst::Concat, new_chs_2);
					new_chs_2.pop_back();
					new_chs_2.push_back(NumInst::create(0, num_length));
					Inst *ve_c0 = OpInst::create(OpInst::Concat, new_chs_2);
					Inst *ve_concat = OpInst::create(OpInst::Ternary, ve_in_back, ve_c1, ve_c0);
					applied_ve = ve_concat;
				}else{
					applied_ve = new_ve->apply_children(new_chs_1);
				}
			}else{
				
// 				//if(new_chs.empty())
// 				{
// 					cout << "new_ve: " << new_chs.size() << endl;
// 					new_print(cout, new_ve, true);
// 					
// 				}
				applied_ve = new_ve->apply_children(new_chs);
			}
		}
#else
		applied_ve = new_ve->apply_children(new_chs);
#endif
		VWN_COUT_1("applied_ve: " << *applied_ve << endl);
	}

	// update map_net_op along the path from this function's input, ve, to its bottom node.
	new_ve = ve;
	while(1)
	{
		InstToInstM::iterator mit = map_net_op.find(new_ve);
		if(mit == map_net_op.end()){
			break;
		}
		Inst*old_ve = new_ve;
		new_ve = mit->second;
		map_net_op.erase(mit);
		map_net_op[old_ve] = applied_ve;
		VWN_COUT_1("map_net_op[" << *old_ve << "] = " << *applied_ve << endl);
	}

	VWN_COUT_1("applied_ve: " << *applied_ve << endl);

	if(ve != applied_ve)
	{
		InstToInstM::iterator mit = map_net_op.find(ve);
		if(mit == map_net_op.end())
		{
			map_net_op[ve] = applied_ve;
//			cout << *ve << "  " << *new_ve << "  " << *applied_ve << endl;
		}

		OpInst* op_applied = OpInst::as(applied_ve);
		if (op_applied)
		{
			OpInst* op_new = OpInst::as(new_ve);
			assert (op_new);
			string name;
			InstToStringM::iterator mit = map_eq_str.find(new_ve);
			if (mit != map_eq_str.end())
			{
				name = (*mit).second;
			}
			else
			{
				name = AVR_WIRE_NAME_PREFIX + to_string(++avr_wid);
			}


			map_eq_str[op_applied] = name;
			VWN_COUT_1("changed_to: " << *applied_ve << endl);
//			cout << *ve << "  " << *new_ve << "  " << *applied_ve << endl;
		}
	}

	return applied_ve;
}

// map_net_op<to, from> contains net-connections among Insts
// Our goal is to eliminate the intermediate nodes, so check
// map_net_op[ map_net_op[ ... map_net_op [to] ] ] until it reaches a leaf node
// connect_insts() updates map_net_op during computation like the following.
// new_from = map_net_op[ map_net_op[ ... map_net_op [to] ] ];
// ...
// map_net_op [ map_net_op [to] ] = new_from
// map_net_op [to] = new_from

Inst* connect_wires(Inst *ve, InstToStringM& map_eq_str, bool init)
{
	VWN_COUT_1("ve: " << *ve << " " << ve->get_type() << endl);

	if (init) {
		Inst::init_visit();
	}

	if (ve->get_visit()){
		VWN_COUT_1("already visited" << endl);
		return ve->acex_coi;
	}
	ve->set_visit();


//	cout << "Connecting " << *ve << endl;
	Inst* veNew = ve;

	// derive new children
	const InstL* chs = ve->get_children();
	InstL new_chs;
	bool mod = false;
	if(chs && !chs->empty()){
		InstL new_chs;
		for(InstL::const_iterator cit = chs->begin(); cit != chs->end(); ++cit){

			Inst* newCh = connect_wires(*cit, map_eq_str, false);
			if (newCh != (*cit))
				mod = true;
			new_chs.push_back(newCh);
		}
		if (mod)
		{
			veNew = ve->apply_children(new_chs);
		}
	}

//	cout << "(e: " << *veNew << ")" << endl;

	OpInst* op = OpInst::as(ve);
	if (op)
	{
//		string euf_func_name = op->get_euf_func_name();
//		if ((euf_func_name != "0") || op->get_op() == OpInst::Ternary)
//		if ((op->get_op() != OpInst::LogNot) && (op->get_op() != OpInst::Eq) && (op->get_op() != OpInst::NotEq))
		{
			InstToStringM::iterator mit = map_eq_str.find(op);
			Inst* w;
			if (mit != map_eq_str.end())
			{
				w = WireInst::create((*mit).second, ve->get_size(), veNew);
			}
			else
			{
				string name = AVR_WIRE_NAME_PREFIX + to_string(++avr_wid);
				w = WireInst::create(name, ve->get_size(), veNew);
//				avr_log("missing name, adding as " << name);
			}
			veNew = w;
		}
	}
	ve->acex_coi = veNew;

	return veNew;
}

Inst* add_missing_wires(Inst* top) {
  if (top->get_visit()){
    VWN_COUT_1("already visited: " << *top << endl);
    return top->acex_coi;
  }
  top->set_visit();

  VWN_COUT_1("top: " << *top << " type: " << top->get_type() << endl);

  Inst* topRet = top;
  assert(topRet);

  const InstL* ch = topRet->get_children();
  if (ch) {
    InstL new_ch;
    bool need_new = false;
    for (InstL::const_iterator cit = ch->begin(); cit != ch->end(); cit++) {
      Inst* tve = (*cit);
      assert(tve);

      Inst* newTve = add_missing_wires(tve);
      assert(newTve);


      if (OpInst::as(topRet) && OpInst::as(newTve)) {
//    	  cout << "\t(error: missing wire)\tin " << *topRet << endl;
//    	  assert(0);

    	  OpInst* op = OpInst::as(newTve);
    	  if (op) {
    	    Inst* w = op->get_wire();
//    	    if (w == NULL)
    	    {
    	      switch(op->get_op()) {
    	//      case OpInst::Eq:
    	//      case OpInst::NotEq:
    	//      case OpInst::LogNot:
    	//        break;
    	      default: {
    	        string name = AVR_WIRE_NAME_PREFIX + to_string(++avr_wid);
    	        w = WireInst::create(name, newTve->get_size(), newTve);
    	        VWN_COUT_1("\t(creating wire " << *w << " for " << *newTve << ")" << endl);
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
      topRet = topRet->apply_children(new_ch, false);
  }

  OpInst* op = OpInst::as(topRet);
  if (op) {
    Inst* w = op->get_wire();
    if (w == NULL) {
      switch(op->get_op()) {
//      case OpInst::Eq:
//      case OpInst::NotEq:
//      case OpInst::LogNot:
//        break;
      default: {
        string name = AVR_WIRE_NAME_PREFIX + to_string(++avr_wid);
        w = WireInst::create(name, topRet->get_size(), topRet);
        VWN_COUT_1("\t(creating wire " << *w << " for " << *topRet << ")" << endl);
        topRet = w;
      }
      }
    }
  }

//  cout << *top << "\t->\t" << *topRet << endl;

  top->acex_coi = topRet;
  return topRet;
}

// derive the formulas of I, T, and P from the netlist from Verific
InstToInstM map_net_op;	// map_net_op[output] = input, was originally defined within derive_ITP()
InstL initials;

/// Map to get verific instance name from an Inst
InstToStringM map_inst_vinst;

map<string, Inst*> map_sig;
InstL next_states;
Inst *prop_ve =  NULL;
InstL properties;
InstL assumptions;

/// Map to find if a signal is user defined
map<string, bool> map_sig_user_defined;

bool collect_inputs(Inst *top, map<string, Inst*>& regs, bool init_visit) {
	if (init_visit) {
		Inst::init_visit();
	}
	if (top->get_visit()) {
		// if already visited, the return value of the initial call of derive_euf_func_list_debug
		// does not depend on this return value.
		return 0;
	}

	bool ret = true;
	top->set_visit();

	switch (top->get_type()) {
	case Sig:
	{
		SigInst* sig = SigInst::as(top);
		assert(sig);
		string name = sig->get_name();
		if (name != config->get_arg(PROP_SIG_ARG))
		{
			size_t len = name.length();
			if (!((len > NEXT_SUFFIX_LENGTH) && (name.substr(len - NEXT_SUFFIX_LENGTH, NEXT_SUFFIX_LENGTH) == NEXT_SUFFIX)))
			{
				if (regs.find(sig->get_name()) == regs.end())
				{
					inputs.insert(top);
				}
			}
		}
	}
		break;
	case Num:
//		constants.insert(top);
		break;
	case Wire:
		break;
	case Op:
		break;
	case Ex:
		break;
	case Mem:
		break;
	case UF:
		break;
	default:
		assert(0);
		ret = false;
	}

	const InstL* tch = top->get_children();
	if (tch) {
		for (InstL::const_iterator tit = tch->begin(); tit != tch->end(); ++tit) {
			bool t_ret = collect_inputs(*tit, regs, false);
			ret = ret | t_ret;
		}
	}
	return ret;
}

void collect_func_stat(Inst* top, int& numSig, int& numConst, int& numCF, int& numUF, int& numMux, int& numCc, int& numEx, map< string, int >& ufType, map< string, int >& ccType, map< string, int >& exType, bool init_visit = false)
{
  if (init_visit) {
    Inst::init_visit();
  }
  if (top->get_visit()) {
    return;
  }
  top->set_visit();

  ExInst* ex = ExInst::as(top);
  if (ex)
  {
    numEx++;
    string eufName = ex->get_euf_func_name();
    map< string, int >::iterator mit = exType.find(eufName);
    if (mit != exType.end())
      (*mit).second++;
    else
      exType[eufName] = 1;
  }
  else
  {
    OpInst* op = OpInst::as(top);
    if (op)
    {
      string eufName = op->get_euf_func_name();
      if (op->get_op() == OpInst::Concat)
      {
        numCc++;
        map< string, int >::iterator mit = ccType.find(eufName);
        if (mit != ccType.end())
          (*mit).second++;
        else
          ccType[eufName] = 1;
      }
      else if (eufName != "0")
      {
        numUF++;
        map< string, int >::iterator mit = ufType.find(eufName);
        if (mit != ufType.end())
          (*mit).second++;
        else
          ufType[eufName] = 1;
      }
      else
      {
        if (op->get_op() == OpInst::Ternary)
          numMux++;
        numCF++;
      }
    }
    else if (top->get_type() == Num)
      numConst++;
    else if (top->get_type() == Sig)
      numSig++;
  }

  const InstL* tch = top->get_children();
  if (tch) {
    for (InstL::const_iterator tit = tch->begin(); tit != tch->end(); ++tit) {
      collect_func_stat(*tit, numSig, numConst, numCF, numUF, numMux, numCc, numEx, ufType, ccType, exType);
    }
  }
}

void collect_nsfs(Inst *top, InstL &vel_nsfs, bool init_visit) {
  if (init_visit) {
    vel_nsfs.clear();
  }
  OpInst* op = OpInst::as(top);
  if (op && (op->get_op() == OpInst::LogAnd)) {
    const InstL* ch = top->get_children();
    for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it) {
      Inst * tve = *it;
      OpInst* op2 = OpInst::as(tve);
      if (op2 && (op2->get_op() == OpInst::LogAnd)) {
        collect_nsfs(tve, vel_nsfs, false);
      } else {
        vel_nsfs.push_back(tve);
      }
    }
  } else {
    Inst * tve = top;
    vel_nsfs.push_back(tve);
  }
  return;
}


//void print_header(void)
//{
//		outFile << "--------------------------" << endl;
//		outFile << " Results After Parse Stage " << endl;
//		outFile << "--------------------------" << endl;
//		outFile << endl;
//}

void print_internals(ofstream& outFile)
{
	for (auto& s: WireInst::hm_WireInst)
	{
		WireInst* w = WireInst::as(s.second);
		assert(w);

		ostringstream lhs;
		lhs << *w;
		string lhsName = lhs.str();

		Inst* port = w->get_port();
		OpInst* op_port = OpInst::as(port);
		if (op_port)
		{
			ostringstream rhs;
			op_port->print(rhs);
			string rhsName = rhs.str();

			string type = op_port->get_euf_type_name();
			if (type == "0")
				type = "control";
			VWN_COUT_FILE("(type: " << setw(8) << left << type << ")\t");
			VWN_COUT_FILE(setw(8) << left << lhsName << " = " << rhsName << endl);
		}
	}
	return;
}

void print_summary(void)
{
  bool allowPrint = false;
#ifdef AVR_PARTIAL_BIT_BLAST
  allowPrint = true;
#endif

  if (Config::g_split_signals)
  	allowPrint = true;

  string fname;
  ofstream outFile;

	if(PRINT_VWN_RESULTS && allowPrint)
	{
		fname = config->get_working_dir() + "/data/design_original.txt";
		outFile.open(fname.c_str());

		VWN_COUT_FILE("---------------------" << endl);
		VWN_COUT_FILE("WITHOUT PREPROCESSING" << endl);
		VWN_COUT_FILE("---------------------" << endl);
		VWN_COUT_FILE(endl);

		VWN_COUT_FILE("-------------------------------" << endl);
		VWN_COUT_FILE("Function Blocks ( out = F(in) )" << endl);
		VWN_COUT_FILE("-------------------------------" << endl);

		print_internals(outFile);

		VWN_COUT_FILE(endl);

		VWN_COUT_FILE("------------------" << endl);
		VWN_COUT_FILE("Initial Conditions" << endl);
		VWN_COUT_FILE("------------------" << endl);
		VWN_COUT_FILE(tsb_init << " out of " << tsb << " initialized" << endl);

		InstL conjunct_init;
		collect_nsfs(ve_init, conjunct_init, true);
		VWN_COUT_FILE(conjunct_init << endl);

		VWN_COUT_FILE(endl);

		outFile.close();
	}

	collect_inputs(ve_init, states, true);
	collect_inputs(ve_prop, states, false);
	collect_inputs(ve_model_nsf, states, false);
	collect_inputs(ve_assume, states, false);

	InstL svs;
	for (auto& s : states)
		svs.push_back(s.second);
	InstL inps;
	for (auto& s : inputs)
		inps.push_back(s);
	InstL cts;
	for (auto& s : constants)
		cts.push_back(s);
	svs.sort(CompareBySz);
	inps.sort(CompareBySz);
	cts.sort(CompareBySz);

	if(PRINT_VWN_RESULTS && allowPrint)
	{
		fname = config->get_working_dir() + "/data/parse_original.results";
		outFile.open(fname.c_str());

		VWN_COUT_FILE("---------------------" << endl);
		VWN_COUT_FILE("WITHOUT PREPROCESSING" << endl);
		VWN_COUT_FILE("---------------------" << endl);
		VWN_COUT_FILE(endl);

//		VWN_COUT_FILE("--------------------" << endl);
//		VWN_COUT_FILE("User Defined Signals" << endl);
//		VWN_COUT_FILE("--------------------" << endl);
//		int numUDS = 0;
//		for (map<string, Inst*>::iterator i = map_sig.begin(); i != map_sig.end(); i++)
//		{
////			if (map_cr_name_ve.find((*i).first) == map_cr_name_ve.end()
////					&& (*i).second != prop_ve)
////			{
//				if (map_sig_user_defined[((*i).first)] == true)
//				{
//					numUDS++;
//					VWN_COUT_FILE(setw(28) << left << (*i).first << "    (" << (*i).second->get_size() << "-bit)" << endl);
//				}
////			}
//		}
//		VWN_COUT_FILE(endl);
////		_resFile << "#user-defined-signals:\t" << numUDS << endl;
//
//		VWN_COUT_FILE("----------------" << endl);
//		VWN_COUT_FILE("Internal Signals" << endl);
//		VWN_COUT_FILE("----------------" << endl);
//		int numIS = 0;
//		for (map<string, Inst*>::iterator i = map_sig.begin(); i != map_sig.end(); i++)
//		{
////			if (map_cr_name_ve.find((*i).first) == map_cr_name_ve.end()
////					&& (*i).second != prop_ve)
////			{
//				if (map_sig_user_defined[((*i).first)] == false)
//				{
//					numIS++;
//					VWN_COUT_FILE(setw(28) << left << *((*i).second) << "    (" << (*i).second->get_size() << "-bit)" << endl);
//				}
////			}
//		}
//		VWN_COUT_FILE(endl);
////		_resFile << "#internal-signals:\t" << numIS << endl;

		map < int, int > stateSizes;
		map < int, int > inputSizes;
		map < int, int > constSizes;

		for (auto& s : states)
		{
			if (stateSizes.find(s.second->get_size()) != stateSizes.end())
				stateSizes[s.second->get_size()]++;
			else
				stateSizes[s.second->get_size()] = 1;
		}
		for (auto& s : inputs)
		{
			if (inputSizes.find(s->get_size()) != inputSizes.end())
				inputSizes[s->get_size()]++;
			else
				inputSizes[s->get_size()] = 1;
		}
		for (auto& s : constants)
		{
			if (constSizes.find(s->get_size()) != constSizes.end())
				constSizes[s->get_size()]++;
			else
				constSizes[s->get_size()] = 1;
		}

		VWN_COUT_FILE("------------" << endl);
		VWN_COUT_FILE("Size Summary" << endl);
		VWN_COUT_FILE("------------" << endl);
		VWN_COUT_FILE(endl);

		VWN_COUT_FILE("State variables (#" << svs.size() << ")" << endl);
		for (auto& s: stateSizes)
		{
			VWN_COUT_FILE("\t(" << s.first << "-bit)\t" << s.second << endl);
		}
		VWN_COUT_FILE(endl);

		VWN_COUT_FILE("Inputs (#" << inps.size() << ")" << endl);
		for (auto& s: inputSizes)
		{
			VWN_COUT_FILE("\t(" << s.first << "-bit)\t" << s.second << endl);
		}
		VWN_COUT_FILE(endl);

		VWN_COUT_FILE("Constants (#" << cts.size() << ")" << endl);
		for (auto& s: constSizes)
		{
			VWN_COUT_FILE("\t(" << s.first << "-bit)\t" << s.second << endl);
		}
		VWN_COUT_FILE(endl);


		VWN_COUT_FILE("---------------" << endl);
		VWN_COUT_FILE("State Variables" << endl);
		VWN_COUT_FILE("---------------" << endl);
	}

  int numBits = 0;
  int numInpBits = 0;
  int numSvars = 0;
  int maxBitsz = 0;
  for (auto& s: svs)
  {
    int sz = s->get_size();
    if(PRINT_VWN_RESULTS && allowPrint)
    {
			VWN_COUT_FILE(setw(28) << left << *s << "    (" << sz << "-bit)" << endl);
    }

    numSvars++;
    numBits += sz;
    if (sz > maxBitsz)
      maxBitsz = sz;
  }

  if(PRINT_VWN_RESULTS && allowPrint)
  {
    VWN_COUT_FILE(endl);

    VWN_COUT_FILE("------" << endl);
    VWN_COUT_FILE("Inputs" << endl);
    VWN_COUT_FILE("------" << endl);
  }
  int numInp = 0;
  for (auto& s: inps)
  {
    int sz = s->get_size();
    if(PRINT_VWN_RESULTS && allowPrint)
    {
      VWN_COUT_FILE(setw(28) << left << *s << "    (" << sz << "-bit)" << endl);
    }
    numInpBits += sz;
    numInp++;
  }

  if(PRINT_VWN_RESULTS && allowPrint)
  {
		VWN_COUT_FILE(endl);

		VWN_COUT_FILE("---------" << endl);
		VWN_COUT_FILE("Constants" << endl);
		VWN_COUT_FILE("---------" << endl);
  }
  int numConst = 0;
  for (auto& s: cts)
  {
    if(PRINT_VWN_RESULTS && allowPrint)
      VWN_COUT_FILE( *s << endl);
    numConst++;
  }

  if(PRINT_VWN_RESULTS && allowPrint)
  {
    VWN_COUT_FILE(endl);
    outFile.close();
  }

//  _resFile << "i-has-memory:\t" << "false" << endl;
  _resFile << "i-#state-variables:\t" << numSvars << endl;
  _resFile << "i-total-state-bits:\t" << numBits << endl;
  _resFile << "i-max-state-bit-size:\t" << maxBitsz << endl;
  _resFile << "i-#inputs:\t" << numInp << endl;
  _resFile << "i-total-input-bits:\t" << numInpBits << endl;
  _resFile << "i-#constants:\t" << numConst << endl;
}

void print_T(void)
{
	if(PRINT_VWN_RESULTS)
	{
    int numSig = 0;
    int numConst = 0;
		int numCF = 0;
		int numUF = 0;
    int numMux = 0;
    int numCc = 0;
		int numEx = 0;
		map< string, int > ufType, ccType, exType;
		collect_func_stat(ve_prop, numSig, numConst, numCF, numUF, numMux, numCc, numEx, ufType, ccType, exType, true);
    int propUF = numUF;
    int propMux = numMux;
    int propConst = numConst;
		collect_func_stat(ve_model_nsf, numSig, numConst, numCF, numUF, numMux, numCc, numEx, ufType, ccType, exType, false);

		_resFile << "i-#control:\t" << numCF << endl;
		_resFile << "i-#uf:\t" << numUF << endl;
		_resFile << "i-#concat:\t" << numCc << endl;
		_resFile << "i-#extract:\t" << numEx << endl;
		_resFile << "i-#uf-types:\t" << ufType.size() << endl;
		_resFile << "i-#concat-types:\t" << ccType.size() << endl;
		_resFile << "i-#extract-types:\t" << exType.size() << endl;

    _resFile << "i-#mux:\t" << numMux << endl;

    _resFile << "i-comb-prop-#uf:\t" << propUF << endl;
    _resFile << "i-comb-prop-#const:\t" << propConst << endl;
    _resFile << "i-comb-prop-#mux:\t" << propMux << endl;

#ifdef AVR_PARTIAL_BIT_BLAST
		string fname = config->get_working_dir() + "/parse_original.results";
		ofstream outFile;
		outFile.open(fname.c_str(), ios_base::app);

		VWN_COUT_FILE("-----------------------------" << endl);
		VWN_COUT_FILE("Uninterpreted Functions (UFs)" << endl);
		VWN_COUT_FILE("-----------------------------" << endl);
    for (map< string, int >::iterator it = ufType.begin(); it != ufType.end(); it++)
    {
      VWN_COUT_FILE((*it).first << "\t#" << (*it).second << endl);
    }
//		for (set<string>::iterator it = ccType.begin(); it != ccType.end(); it++)
//		{
//			VWN_COUT_FILE(*it << endl);
//		}
//		for (set<string>::iterator it = exType.begin(); it != exType.end(); it++)
//		{
//			VWN_COUT_FILE(*it << endl);
//		}
		VWN_COUT_FILE(endl);

//		VWN_COUT_FILE("--------" << endl);
//		VWN_COUT_FILE("Property" << endl);
//		VWN_COUT_FILE("--------" << endl);
//		VWN_COUT_FILE(*ve_prop << endl);
//		VWN_COUT_FILE(endl);
//
//		VWN_COUT_FILE("------------------" << endl);
//		VWN_COUT_FILE("Initial Conditions" << endl);
//		VWN_COUT_FILE("------------------" << endl);
//		VWN_COUT_FILE(conjunct_init << endl);
//		VWN_COUT_FILE(endl);
//
//#ifndef AVOID_LARGE_PRINTING
//		VWN_COUT_FILE("-------------------" << endl);
//		VWN_COUT_FILE("Transition Relation" << endl);
//		VWN_COUT_FILE("-------------------" << endl);
//		VWN_COUT_FILE(conjunct_nsf << endl);
//		VWN_COUT_FILE(endl);
//#endif

		outFile.close();
#else
	  if (Config::g_split_signals)
	  {
			string fname = config->get_working_dir() + "/data/parse_original.results";
			ofstream outFile;
			outFile.open(fname.c_str(), ios_base::app);

			VWN_COUT_FILE("-----------------------------" << endl);
			VWN_COUT_FILE("Uninterpreted Functions (UFs)" << endl);
			VWN_COUT_FILE("-----------------------------" << endl);
			for (map< string, int >::iterator it = ufType.begin(); it != ufType.end(); it++)
			{
				VWN_COUT_FILE((*it).first << "\t#" << (*it).second << endl);
			}
	//    for (set<string>::iterator it = ccType.begin(); it != ccType.end(); it++)
	//    {
	//      VWN_COUT_FILE(*it << endl);
	//    }
	//    for (set<string>::iterator it = exType.begin(); it != exType.end(); it++)
	//    {
	//      VWN_COUT_FILE(*it << endl);
	//    }
			VWN_COUT_FILE(endl);

	//    VWN_COUT_FILE("--------" << endl);
	//    VWN_COUT_FILE("Property" << endl);
	//    VWN_COUT_FILE("--------" << endl);
	//    VWN_COUT_FILE(*ve_prop << endl);
	//    VWN_COUT_FILE(endl);
	//
	//    VWN_COUT_FILE("------------------" << endl);
	//    VWN_COUT_FILE("Initial Conditions" << endl);
	//    VWN_COUT_FILE("------------------" << endl);
	//    VWN_COUT_FILE(conjunct_init << endl);
	//    VWN_COUT_FILE(endl);
	//
	//#ifndef AVOID_LARGE_PRINTING
	//    VWN_COUT_FILE("-------------------" << endl);
	//    VWN_COUT_FILE("Transition Relation" << endl);
	//    VWN_COUT_FILE("-------------------" << endl);
	//    VWN_COUT_FILE(conjunct_nsf << endl);
	//    VWN_COUT_FILE(endl);
	//#endif

			outFile.close();
	  }
#endif
	}
}

void connect_all_instances(void)
{
	if (prop_ve != NULL) {
		avr_log("selecting property: " << *prop_ve);
		avr_logcerr("property: " << *prop_ve);
		properties.clear();
		properties.push_back(prop_ve);
	}
	else {
		avr_logcerr("property: all (" << properties.size() << " assertions)");
	}
	if (properties.size() == 0) {
		avr_logcerr("unable to fetch property, exiting");
		avr_loge("unable to fetch property, exiting");
	}

	Inst *ret_ve;
	for (auto& p: properties)
	{
		VWN_COUT_2("sub prop_before: " << *p << endl);
		Inst *ret_ve = connect_insts(p, gate_names, map_net_op, false);
		gate_names[ret_ve] = SigInst::as(p)->get_name();
		VWN_COUT_2("sub prop_after: " << *ret_ve << endl);
	}

	for (auto& p: assumptions)
	{
		VWN_COUT_2("sub assume_before: " << *p << endl);
		Inst *ret_ve = connect_insts(p, gate_names, map_net_op, false);
		gate_names[ret_ve] = SigInst::as(p)->get_name();
		VWN_COUT_2("sub assume_after: " << *ret_ve << endl);
	}

	for(InstL::iterator vel_it = next_states.begin(); vel_it != next_states.end(); vel_it++){
		Inst *tve = *vel_it;
		VWN_COUT_2("tve_before: " << *tve << endl);
		ret_ve = map_net_op[tve];
		VWN_COUT_2("rhs_before: " << *ret_ve << endl);
		assert(ret_ve);
		ret_ve = connect_insts(ret_ve, gate_names, map_net_op, false);
		map_net_op[tve] = ret_ve;
		gate_names[ret_ve] = SigInst::as(tve)->get_name() + "_rhs";
		VWN_COUT_2("tve_after: " << *ret_ve << endl);
//		Inst *teq = OpInst::create(OpInst::Eq, tve, ret_ve);
//		conjunct_nsf.push_back(teq);
	}

//	for (auto& m: map_net_op)
//		cout << "[" << *(m.first) << "] = " << *(m.second) << endl;

	Inst::init_visit();

	InstL properties_new;
	for (auto& p: properties)
	{
		VWN_COUT_2("sub prop_before: " << *p << endl);
		assert(p != NULL);
		InstToInstM::iterator mit = map_net_op.find(p);
		if (mit != map_net_op.end())
			ret_ve = (*mit).second;
		else
			ret_ve = p;
		assert(ret_ve);
		ret_ve = connect_wires(ret_ve, gate_names, false);
		VWN_COUT_2("sub prop_after: " << *ret_ve << endl);
		properties_new.push_back(ret_ve);
	}
	properties = properties_new;

	InstL assumptions_new;
	for (auto& p: assumptions)
	{
		VWN_COUT_2("sub assume_before: " << *p << endl);
		assert(p != NULL);
		InstToInstM::iterator mit = map_net_op.find(p);
		if (mit != map_net_op.end())
			ret_ve = (*mit).second;
		else
			ret_ve = p;
		assert(ret_ve);
		ret_ve = connect_wires(ret_ve, gate_names, false);
		VWN_COUT_2("sub assume_after: " << *ret_ve << endl);
		assumptions_new.push_back(ret_ve);
	}
	assumptions = assumptions_new;

	for(InstL::iterator vel_it = next_states.begin(); vel_it != next_states.end(); vel_it++){
		Inst *tve = *vel_it;
		VWN_COUT_2("tve_before: " << *tve << endl);
		ret_ve = map_net_op[tve];
		assert(ret_ve);
		VWN_COUT_2("\trhs_before: " << *ret_ve << endl);
//		if (!ret_ve->find_next())
		ret_ve = connect_wires(ret_ve, gate_names, false);
		VWN_COUT_2("\trhs_after: " << *ret_ve << endl);
		WireInst* w = WireInst::as(ret_ve);
		if (!w)
		{
			OpInst* op = OpInst::as(ret_ve);
//			if (op && (op->get_op() != OpInst::LogNot) && (op->get_op() != OpInst::Eq) && (op->get_op() != OpInst::NotEq))
      if (op)
			{
				string name = SigInst::as(tve)->get_name() + "_rhs";
				Inst* w_rhs = WireInst::create(name, tve->get_size(), ret_ve);
				ret_ve = w_rhs;
			}
		}
		VWN_COUT_2("tve_after: " << *ret_ve << endl);
		InstToInstM::iterator mit = transitions.find(tve);
		if (mit != transitions.end()) {
			assert((*mit).second == ret_ve);
		}
		else {
//			cout << "adding transition: " << *tve << " = " << *ret_ve << endl;
			transitions[tve] = ret_ve;
			tsb += tve->get_size();
		}
	}
	avr_logcerr("problem size: " << tsb << " bits");
}

void finalize_ITP(void)
{
	compile_initial(true);
	compile_transition();
	compile_property();
	compile_assumptions();
}

void derive_ITP(void)
{
//	print_header();
	connect_all_instances();
	finalize_ITP();
	print_summary();
	print_T();
}

void compile_initial(bool allow_file_read)
{
	initials.clear();
	tsb_init = 0;

	if (allow_file_read && (config->get_arg(INIT_FILE) != "-")) {
		map_init.clear();

		string fname_init = config->get_arg(INIT_FILE);
		InitParser* in = new InitParser(fname_init);
//		in->help();
		in->execute();
//		assert(0);
	}

	InstToInstM::iterator init_it = map_init.begin();
	for(; init_it != map_init.end(); ++init_it){
		Inst *ve_lhs = init_it->first;
		Inst *ve_rhs = init_it->second;
		tsb_init += ve_lhs->get_size();

		if(ve_lhs->get_size() == 1){
			if((ve_rhs->get_type() == Num) && (NumInst::as(ve_rhs)->get_num() == 0)){
				initials.push_back(OpInst::create(OpInst::LogNot, ve_lhs));
			}else if((ve_rhs->get_type() == Num) && (NumInst::as(ve_rhs)->get_num() == 1)){
				initials.push_back(ve_lhs);
			}
			else {
				initials.push_back(OpInst::create(OpInst::Eq, ve_lhs, ve_rhs));
			}
		}else{
			initials.push_back(OpInst::create(OpInst::Eq, ve_lhs, ve_rhs));
		}
	}

	if (initials.empty())
		ve_init = NumInst::create(1, 1);
	else
		ve_init = OpInst::create(OpInst::LogAnd, initials);

	if (allow_file_read) {
		if (config->get_arg(INIT_FILE) != "-") {
			string fname = config->get_arg(INIT_FILE);
			size_t found = fname.find_last_of("/");
			if (found != string::npos)
				fname = fname.substr(found + 1);
//			avr_logcerr(tsb_init << " / " << tsb << " flops initialized from " << fname);
		}
		else {
//			avr_logcerr(tsb_init << " / " << tsb << " flops initialized");
		}
	}
}

void compile_transition(void)
{
	if(transitions.empty()){
		VWN_COUT_ITP("conjunct_nsf is empty !!" << endl);
		ve_model_nsf = NumInst::create(1, 1);
	}else{
		InstL conjunct_t;
		for (auto& m: transitions) {
			conjunct_t.push_back(OpInst::create(OpInst::Eq, m.first, m.second));
		}
		VWN_COUT_ITP("conjunct_nsf: " << transitions << endl);
		ve_model_nsf = OpInst::create(OpInst::LogAnd, conjunct_t);
	}
}

void compile_property(void)
{
	Inst* rhs;
	if (properties.size() > 1)
		rhs = OpInst::create(OpInst::LogAnd, properties);
	else
		rhs = properties.front();

	Inst* prop_ve = SigInst::create(config->get_arg(PROP_SIG_ARG), 1, SORT());
	WireInst* w = WireInst::as(rhs);
	if (!w)
	{
		OpInst* op = OpInst::as(rhs);
//		if (op && (op->get_op() != OpInst::LogNot) && (op->get_op() != OpInst::Eq) && (op->get_op() != OpInst::NotEq))
    if (op)
		{
			string name = SigInst::as(prop_ve)->get_name() + "_rhs";
			Inst* w_rhs = WireInst::create(name, prop_ve->get_size(), rhs);
			rhs = w_rhs;
		}
	}
	ve_prop = OpInst::create(OpInst::Eq, prop_ve, rhs);
}

void compile_assumptions(void)
{
	if(assumptions.empty()){
		VWN_COUT_ITP("assumptions is empty !!" << endl);
		ve_assume = NumInst::create(1, 1);
	}else{
		VWN_COUT_ITP("assumptions: " << assumptions << endl);
		ve_assume = OpInst::create(OpInst::LogAnd, assumptions);
	}
}


void init_flow() {
#if 1
	Inst::wn_simplify_extract_adv = true;
	Inst::wn_simplify_extract = true;
	Inst::wn_simplify_concat = false;
	Inst::wn_simplify_const_pred = true;
	Inst::wn_simplify_const_num = true;
	Inst::wn_simplify_ite = true;
	Inst::wn_simplify_repetition = true;
	Inst::wn_1bit_dp_to_control = true;
	Inst::wn_simplify_eq = true;
#else
	Inst::wn_simplify_extract_adv = true;
	Inst::wn_simplify_extract = true;
	Inst::wn_simplify_concat = true;
	Inst::wn_simplify_const_pred = false;
	Inst::wn_simplify_const_num = false;
	Inst::wn_simplify_ite = false;
	Inst::wn_simplify_repetition = false;
	Inst::wn_1bit_dp_to_control = true;
	Inst::wn_simplify_eq = false;
#endif
}

void write_wn() {
	ofstream fout;
#ifdef BUILD_STANDALONE
	string fname = "./wn_orig.dump";
#else
	string fname = config->get_working_dir() + "/data/wn_orig.dump";
#endif

    fout.open(fname.c_str());
	if(!fout.good()){
		cout<<"Could not access file: "<<fname<<endl;
		return;
	}
	
	Trans::st_out = &fout;

	Trans::write_int(static_cast<int> (WN_VERSION * 10));

	Trans::write_str(Trans::m_module_name);
	Trans::st_ptr_to_id.clear();
	Trans::reachable.clear();
	Inst::init_visit();

	VWN_COUT_3("write_wn()" << endl);
	
	Inst* tmpNum = NumInst::create(0, 1);
	Trans::collect_reachable(tmpNum);
	tmpNum = NumInst::create(1, 1);
	Trans::collect_reachable(tmpNum);


	if(ve_init){
		VWN_COUT_3("ve_init:" << endl << *ve_init << endl);
		Trans::collect_reachable(ve_init);
	}

	if(ve_model_nsf){
		VWN_COUT_3("ve_model_nsf:" << endl << *ve_model_nsf << endl);
		Trans::collect_reachable(ve_model_nsf);
	}
	
	if(ve_prop){
		VWN_COUT_3("ve_prop:" << endl << *ve_prop << endl);
		Trans::collect_reachable(ve_prop);
	}

	if(ve_assume){
		VWN_COUT_3("ve_assume:" << endl << *ve_assume << endl);
		Trans::collect_reachable(ve_assume);
	}
	Trans::write_int(Trans::reachable.size());

//	for (auto& r: Trans::reachable)
//		cout << "r: " << *r << " s:" << r->get_size() << endl;

	// writes types
	unsigned i = 0;
//	for (InstL::iterator it = Trans::reachable.begin(), end_it = Trans::reachable.end(); it != end_it; ++it, i++) {
//		Trans::st_ptr_to_id.insert(make_pair(*it, i));
//	}
//	i = 0;
	for (InstL::iterator it = Trans::reachable.begin(), end_it = Trans::reachable.end(); it != end_it; ++it, i++) {
		Trans::write_int(static_cast<int> ((*it)->get_type()));
		(*it)->write_bin();
		Trans::st_ptr_to_id.insert(make_pair(*it, i));
	}

// 	if(ve_init)	Trans::write_int(Trans::ptr_to_id(ve_init));
// 	if(ve_model_nsf)	Trans::write_int(Trans::ptr_to_id(ve_model_nsf));
// 	if(ve_prop)	Trans::write_int(Trans::ptr_to_id(ve_prop));
	Trans::write_int(Trans::ptr_to_id(ve_init));
	Trans::write_int(Trans::ptr_to_id(ve_model_nsf));
	Trans::write_int(Trans::ptr_to_id(ve_prop));
	Trans::write_int(Trans::ptr_to_id(ve_assume));

	if (MOVED_TO_DPA)
	{
		for (InstS::iterator it = s_data.begin(), end_it = s_data.end(); it != end_it; ++it)
		{
			if (Trans::st_ptr_to_id.find(*it) == Trans::st_ptr_to_id.end())
			{
				cout << "Warning: Unreachable s_data entry for Instance " << (*it) << endl;
				num_warnings++;
				s_data.erase(it);
			}
		}

		Trans::write_int(s_data.size());
		for (InstS::iterator it = s_data.begin(), end_it = s_data.end(); it != end_it; ++it)
		{
			Trans::write_int(Trans::ptr_to_id(*it));
		}

		for (InstToInstM::iterator it = map_init.begin(), end_it = map_init.end(); it != end_it; ++it)
		{
			if (Trans::st_ptr_to_id.find((*it).first) == Trans::st_ptr_to_id.end()
					|| Trans::st_ptr_to_id.find((*it).second) == Trans::st_ptr_to_id.end())
			{
				cout << "Warning: Unreachable map_init entry for map_init[" << *(*it).first << "] = " << *(*it).second << endl;
				num_warnings++;
				map_init.erase(it);
				assert(0);
			}
		}

		Trans::write_int(map_init.size());
		for (InstToInstM::iterator it = map_init.begin(), end_it = map_init.end(); it != end_it; ++it)
		{
//			cout << "Writing map_init[" << *(*it).first << "] = " << *(*it).second << endl;

			Trans::write_int(Trans::ptr_to_id((*it).first));
			Trans::write_int(Trans::ptr_to_id((*it).second));
		}
	}

	fout.close();
	VWN_COUT_3("Deisgn WN is dumped to " << fname << endl);
	
// 	cout << "vwn ve_init:" << endl;
// 	new_print(cout, ve_init, true);
// 	cout << "vwn ve_model_nsf:" << endl;
// 	new_print(cout, ve_model_nsf, true);
// 	cout << "vwn ve_prop:" << endl;
// 	new_print(cout, ve_prop, true);

	
}

//####################################################################
//	PARTIAL BIT BLAST
//####################################################################
static InstToSetM m_pars;

void dump_to_bb(Inst *ve_top, InstToInstM& bb_map, bool init_visit = false) {
	if (init_visit) {
		Inst::init_visit();
	}
	if (ve_top->get_visit()){
		return;
	}
	ve_top->set_visit();

	//cout << "ve_top: " << *ve_top << endl;
	const InstL* chs = ve_top->get_children();
	if(chs){
		InstL::const_iterator it = chs->begin();
		for(; it != chs->end(); ++it) {
			dump_to_bb(*it, bb_map, false);
		}
	}
	InstToInstM::iterator mit = bb_map.find(ve_top);
	if(mit != bb_map.end()){
		Inst *ve_orig = mit->first;
		Inst *ve_new = mit->second;
		cout << "bb_map: ve_orig:" << endl;
		cout << *ve_orig << endl;
		//new_print(cout, ve_orig, true);
		cout << "bb_map: ve_new:" << endl;
		//new_print(cout, ve_new, true);
		cout << *ve_new << endl;
		
	}
	
}

Inst *update_chs_pbb(Inst *ve_top, InstToInstM& bb_map, bool init_visit = false) {
	if (init_visit) {
		Inst::init_visit2();
	}
	if (ve_top->get_visit2()){
		return ve_top->acex_coi;
	}
	ve_top->set_visit2();
	ve_top->acex_coi = ve_top;	//TODO temporary use of acex_coi

	if((ve_top->get_type() == Num) || (ve_top->get_type() == Sig))
	{
		InstToInstM::iterator mit = bb_map.find(ve_top);
		Inst *ve_res=NULL;
		if(mit != bb_map.end()){
			ve_res = mit->second;
		}else{
			ve_res = ve_top;
		}
		ve_top->acex_coi = ve_res;
		return ve_res;
	}else{
		InstToInstM::iterator mit = bb_map.find(ve_top);
		if(mit != bb_map.end()){
			Inst *ve_res=NULL;
			ve_res = mit->second;
			ve_top->acex_coi = ve_res;
			return ve_res;
		}
	}

	InstL new_ch;
	bool need_new = false;
	const InstL* chs = ve_top->get_children();
	if(chs){
		InstL::const_iterator it = chs->begin();
		for(; it != chs->end(); ++it) {
			Inst *ch = *it;
			Inst *ch_new = update_chs_pbb(ch, bb_map);
			if(ch != ch_new){
				need_new = true;
			}
			new_ch.push_back(ch_new);
		}
	}else{
		assert(0);
	}

	// for the (mult_bit_reg == width'd0) in init
	if((ve_top->get_type() == Op) && (OpInst::as(ve_top)->get_op() == OpInst::Eq)){
		InstL::iterator cit = new_ch.begin();
		Inst *ve_ch0 = *cit++;
		Inst *ve_ch1 = *cit;
// 		cout << "####$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$" << endl;
//  		cout << "ve_ch0: " << *ve_ch0 << ", size: " << ve_ch0->get_size() << endl;
//  		cout << "ve_ch1: " << *ve_ch1 << ", size: " << ve_ch1->get_size() << endl;
		int op_size = ve_ch0->get_size();
		if(op_size == 1){
			Inst *ve_res = OpInst::create(OpInst::LogXNor, ve_ch0, ve_ch1);
			//cout << "table, ve_res1: " << *ve_res << endl;
			ve_top->acex_coi = ve_res;
			return ve_res;
		}else{
			if((ve_ch0->get_type() == Op) && (OpInst::as(ve_ch0)->get_op() == OpInst::Concat)){
				if( ((ve_ch1->get_type() == Op) && (OpInst::as(ve_ch1)->get_op() == OpInst::Concat)) &&
					((ve_ch0->get_children())->size() == (ve_ch1->get_children())->size()) && (op_size == (ve_ch0->get_children())->size()) ){
					InstL::const_iterator cit_0 = (ve_ch0)->get_children()->begin();
					InstL::const_iterator cit_1 = (ve_ch1)->get_children()->begin();
					Inst *ve_res;
					for (int i = 0; i < op_size; ++i, ++cit_0, ++cit_1) {
						ve_ch0 = *cit_0;
						ve_ch1 = *cit_1;
						Inst *ve_bit = OpInst::create(OpInst::LogXNor, ve_ch0, ve_ch1);
	// 					if(!ve_bit){
	// 						cout << "ve_ch0: " << *ve_ch0 << ", size: " << ve_ch0->get_size() << endl;
	// 						cout << "ve_ch1: " << *ve_ch1 << ", size: " << ve_ch1->get_size() << endl;	
	// 					}
						if(i != 0){
							ve_res = OpInst::create(OpInst::LogAnd, ve_res, ve_bit);
						}else{
							ve_res = ve_bit;
						}
					}
					//cout << "table, ve_res2: " << *ve_res << ", ve_ch0->get_size():" << op_size << endl;
					ve_top->acex_coi = ve_res;
					return ve_res;
				}else if(op_size == ve_ch0->get_children()->size()){
					InstL::const_iterator cit_0 = ve_ch0->get_children()->begin();
					Inst *ve_res = NULL;
// 					if(op_size != ve_ch0->get_children()->size()){
// 						cout << *ve_ch0 << endl;
// 						cout << "op_size: " << op_size << ", ve_ch0->get_children()->size(): " << ve_ch0->get_children()->size() << endl;
// 						assert(0);
// 					}
					
					for (int i = 0; i < op_size; ++i, ++cit_0) {
						ve_ch0 = *cit_0;
						Inst *ve_bit = OpInst::create(OpInst::LogXNor, ve_ch0, ExInst::create(ve_ch1, i, i));
						if(i != 0){
							ve_res = OpInst::create(OpInst::LogAnd, ve_res, ve_bit);
						}else{
							ve_res = ve_bit;
						}
					}
					//cout << "table, ve_res2: " << *ve_res << ", ve_ch0->get_size():" << op_size << endl;
					ve_top->acex_coi = ve_res;
					return ve_res;
				}
			}
		}
	}
	
	// if need_new is false, we don't need to proceed this routine.
	// however, I'm checking two cases just in case (this should be unnecessary
	//	due to the simplification routines in vwn).
	
	if(need_new == true){	// TODO check possible BUG s
		if(ve_top->get_type() == Ex){
			ExInst *ve_ex = ExInst::as(ve_top);
			InstL vel_concat;
			Inst *ve_ch = new_ch.front();
			if((ve_ch->get_type() == Op) && (OpInst::as(ve_ch)->get_op() == OpInst::Concat) && (ve_ch-> get_size() == ve_ch->get_children()->size())){
				const InstL* concat_ch = ve_ch->get_children();
				if(concat_ch){
	// 				cout << "ve_top: " << *ve_top << endl;
	// 				cout << "concat_ch->size(): " << concat_ch->size() << endl;
	// 				cout << "ve_ch->get_size(): " << ve_ch->get_size() << endl;
					
					InstL::const_iterator cit = concat_ch->begin();
					for(int i = 0; i < (int)ve_ex->get_lo(); ++i){
						++cit;
					}
					for(int i = 0; i < (int)ve_ex->get_size(); ++i){
						vel_concat.push_back(*cit);
						++cit;
					}
				}else{
					assert(0);
				}
				Inst *ve_res = OpInst::create(OpInst::Concat, vel_concat);
				ve_top->acex_coi = ve_res;
				return ve_res;
			}
		}
		
		if((ve_top->get_type() == Op) && (OpInst::as(ve_top)->get_op() == OpInst::Concat)){
			InstL vel_concat;
			for(InstL::iterator cit = new_ch.begin(); cit != new_ch.end(); ++cit){
				Inst *ve_ch = *cit;
				if((ve_ch->get_type() == Op) && (OpInst::as(ve_ch)->get_op() == OpInst::Concat)){
					const InstL* concat_ch = ve_ch->get_children();
					if(concat_ch){
						for(InstL::const_iterator cit2 = concat_ch->begin(); cit2 != concat_ch->end(); ++cit2){
							vel_concat.push_back(*cit2);
						}
					}else{
						assert(0);
					}
				}else{
					vel_concat.push_back(ve_ch);
				}
			}
			Inst *ve_res = OpInst::create(OpInst::Concat, vel_concat);
			ve_top->acex_coi = ve_res;
			return ve_res;
		}
	}
	
	if(need_new){
		//if(new_ch.size() == 0)
// 		{
// 			cout << "ve_top: " << *ve_top << endl;
// 			cout << "new_ch (" << new_ch.size() << "): " << new_ch << endl;
// 		}
		
		Inst *ve_res = ve_top->apply_children(new_ch);
		bb_map[ve_top] = ve_res;
		ve_top->acex_coi = ve_res;
		return ve_res;
	}
	return ve_top;
}



// TODO return ve_out, bit-blasted version of ve_in ?
void collect_parents(Inst *ve_top, bool init_visit) {
	if(init_visit){
		m_pars.clear();
		Inst::init_visit2();
	}
	if(ve_top->get_visit2()){
		return;
	}
	ve_top->set_visit2();

	const InstL* chs = ve_top->get_children();

	if(chs){
		InstL::const_iterator it = chs->begin();
		for (InstL::const_iterator end_it = chs->end(); it != end_it; ++it) {
			Inst *ch = *it;
			if(m_pars[ch].find(ve_top) == m_pars[ch].end()){
				m_pars[ch].insert(ve_top);
			}
			collect_parents(ch, false);
		}
	}
}


void collect_splits(Inst *ve_top, set<int>& pbb, bool init_visit) {
	if(init_visit){
		Inst::init_visit2();
	}
	if(ve_top->get_visit2()){
		return;
	}
	ve_top->set_visit2();

	OpInst* op = OpInst::as(ve_top);
	if (op) {
		const InstL* chs = ve_top->get_children();
		assert(chs);
		InstL::const_iterator it = chs->begin();

		if (op->get_op() == OpInst::Concat) {
			return;

			int accum_width = 0;
			for (InstL::const_iterator end_it = chs->end(); it != end_it; ++it) {
				Inst *ch = *it;
				int width_ch = ch->get_size();

				set<int> t_pbb;
				collect_splits(ch, t_pbb, false);

				for (auto& i: t_pbb) {
					pbb.insert(accum_width + i);
				}
				accum_width += width_ch;
			}
		}
		else if (op->get_op() == OpInst::Extract) {
			return;

			ExInst* ex = ExInst::as(op);
			int hi = ex->get_hi();
			int lo = ex->get_lo();
			Inst* exp = ex->get_exp();

			set<int> t_pbb;
			collect_splits(exp, t_pbb, false);
			for (auto& i: t_pbb) {
				if (i > lo && i < hi )
				pbb.insert(i - lo);
			}
		}
		else if (op->get_op() == OpInst::Ternary) {
			it++;
			collect_splits(*it, pbb, false);
			it++;
			collect_splits(*it, pbb, false);
		}
		else {

		}
	}
	else if (ve_top->get_type() == Wire) {
		collect_splits(ve_top->get_port(), pbb, false);
	}
	else {
//		return;

		if (ve_top->get_type() == Sig)
			for (auto& i: ve_top->m_pbb)
				pbb.insert(i);
	}
}

#ifdef AVR_DUMP_DOT
string shapes[30] = {
    "box", "ellipse",
    "triangle", "diamond", "trapezium", "parallelogram", "house",
    "pentagon", "hexagon", "septagon", "octagon", "doublecircle",
    "doubleoctagon", "tripleoctagon", "invtriangle", "invtrapezium", "invhouse",
    "Mdiamond", "Msquare", "Mcircle", "rect", "rectangle",
    "square", "note", "tab", "folder", "circle", "egg", "polygon"
};

string colors[7] = {
    "violet", "red", "blue", "yellow", "green", "orange", "indigo"
};

unsigned dump_dot(ostream& fout, Inst* top, int depth, bool init_visit){
	unsigned id = top->get_id();
	if (init_visit) {
		Inst::init_visit2();
	}
	if (top->get_visit2()) {
		return id;
	}
	top->set_visit2();
	int width = top->get_size();
	string color = (width == 1) ? "blue" : "red";
	
	if(top->get_type() == Sig){
		string sname = SigInst::as(top)->get_name();
		fout << "\t" << id << "[label = \"" << *top;
		for(set<int>::iterator it = (top->m_pbb).begin(); it != (top->m_pbb).end(); ++it){
			fout << *it << "_";
		}
		fout << "\" shape = \"" << shapes[0] << "\" color = " << "green" << "];" << endl;
	}else if(top->get_type() == Num){
		string snum = (NumInst::as(top)->get_mpz())->get_str();
		fout << "\t" << id << "[label = \"" << *top;
		for(set<int>::iterator it = (top->m_pbb).begin(); it != (top->m_pbb).end(); ++it){
			fout << *it << "_";
		}
		fout << "\" shape = \"" << shapes[0] << "\" color = " << "yellow" << "];" << endl;
	}else if(top->get_type() == Op){
		OpInst* op = OpInst::as(top);
		OpInst::OpType e_op = op->get_op();
		string name = "";
		Inst* w = op->get_wire();
		if (w)
			name = WireInst::as(w)->get_name() + "\n";
		fout << "\t" << id << "[label = \"" << name;
		for(set<int>::iterator it = (top->m_pbb).begin(); it != (top->m_pbb).end(); ++it){
			fout << *it << "_";
		}
		fout << " (" << OpInst::op2str(e_op) << ") " << "\" shape = \"" << shapes[0] << "\" color = " << color << "];" << endl;
	}else if(top->get_type() == Ex){
		ExInst *vex = ExInst::as(top);
		string name = "";
		Inst* w = vex->get_wire();
		if (w)
			name = WireInst::as(w)->get_name() + "\n";
		fout << "\t" << id << "[label = \"" << name;
		for(set<int>::iterator it = (top->m_pbb).begin(); it != (top->m_pbb).end(); ++it){
			fout << *it << "_";
		}
		fout << "\" shape = \"" << shapes[0] << "\" color = " << color << "];" << endl;
	}
	else if(top->get_type() == Wire){
//		fout << "\t" << id << "[ label = \"" << "";
//		fout << "\" shape = \"" << shapes[26] << "\" fixedsize = \"" << "true" << "\" width = \"" << 0.05 << "\" height = \"" << 0.05 << "\" style = \"" << "filled" << "\" color = " << "black" << "];" << endl;
	}
	else{
		fout << "\t" << id << "[label = \"" << *top;
		for(set<int>::iterator it = (top->m_pbb).begin(); it != (top->m_pbb).end(); ++it){
			fout << *it << "_";
		}
		fout << "\" shape = \"" << shapes[0] << "\" color = " << color << "];" << endl;
	}
	if(--depth == 0){
		return id;
	}
	
	const InstL* ch = top->get_children();
	if (ch) {
		if(ch->size() == 1){
			Inst* tve = ch->front();
			if (tve->get_type() == Wire)
			{
				WireInst* w = WireInst::as(tve);
				assert(w);
				tve = w->get_port();
			}
			unsigned ret = dump_dot(fout, tve, depth, false);
			fout << "\t" << ret <<" -> " << id << ";" << endl;
		}else{
			int idx = 0;
			for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it)
			{
				Inst* tve = *it;
				if (tve->get_type() == Wire)
				{
					WireInst* w = WireInst::as(tve);
					assert(w);
					tve = w->get_port();
				}
				unsigned ret = dump_dot(fout, tve, depth, false);

				if (top->get_type() == Op)
				{
					OpInst* op = OpInst::as(top);
					assert(op);
					switch(op->get_op())
					{
					case OpInst::Ternary:
						if (idx == 0)
							fout << "\t" << ret <<" -> " << id << "[label = \"" << "C" << "\"";
						else if (idx == 1)
							fout << "\t" << ret <<" -> " << id << "[label = \"" << "T" << "\"";
						else if (idx == 2)
							fout << "\t" << ret <<" -> " << id << "[label = \"" << "F" << "\"";
						else
							assert(0);
						idx++;
						break;
					default:
						fout << "\t" << ret <<" -> " << id << "[label = \"" << idx++ << "\"";
					}
				}
				else
				{
					fout << "\t" << ret <<" -> " << id << "[label = \"" << idx++ << "\"";
				}
				fout << "];" << endl;
			}
		}
	}

	return id;
}

// return the Inst* whose id is the same as the input "id"
Inst *find_node(Inst *top, unsigned id, bool init_visit) {
	if (init_visit) {
		Inst::init_visit2();
	}
	if (top->get_visit2()) {
		return NULL;
	}
	top->set_visit2();

	if(top->get_id() == id){
		return top;
	}else{
		const InstL* ch = top->get_children();
		if (ch) {
			for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it) {
				Inst *tve = find_node(*it, id, false);
				if(tve != NULL){
					return tve;
				}
			}
		}
		return NULL;
	}
}

void draw_graph(string fname, string sname, int depth){
	if(m_pars.empty()){
		collect_parents(ve_model_nsf, true);
		collect_parents(ve_prop, false);
		//collect_parents(ve_init, false);
	}

	Inst *top;
	if(sname == config->get_arg(PROP_SIG_ARG)){
		top = ve_prop;
	}else if(sname == "nsf"){
		top = ve_model_nsf;
	}else{
		map<std::string, Inst*>::iterator hm_it = SigInst::hm_SigInst.find(sname);
		if(hm_it != SigInst::hm_SigInst.end()){
			Inst *ve_sig = hm_it->second;
			int width = ve_sig->get_size();
			SORT sort = ve_sig->get_sort();
			cout << "draw_graph: reg_name: " << sname << ", width: " << width << endl;
			top = SigInst::create(sname+"$next", width, sort);
			top = *(m_pars[top].begin());
		}else{
			unsigned id = atoi(sname.c_str());
			top = find_node(OpInst::create(OpInst::LogAnd, ve_prop, ve_model_nsf), id, true);
		}
	}
	assert(top != NULL);

	string of_name, gif_name;
	of_name = fname + ".dot";
	gif_name = fname + ".gif";

	ofstream ofile;
	ofile.open (of_name.c_str());
	ofile<<"digraph tmp {"<<endl;

	//ofile<<"ratio=0.625;"<<endl;
	ofile<<"node[fontsize=16];"<<endl;
	ofile<<"rankdir=LR;"<<endl;

	dump_dot(ofile, top, depth, true);

	ofile<<"}"<<endl;

	//dot -Tgif scu_sym_v3.dot -o scu_sym_v3.gif
	string cmd = "dot -Tgif "+of_name+" -o "+gif_name;
	cout<<cmd<<endl;
	if (0 != system(cmd.c_str())) {
		cout<<"dot error!!!"<<endl;
	}
	ofile.close();
	cout << "draw_graph() succeed!!!" << endl;

}

void draw_graph(string prefix, string sname, int depth, InstToInstM& bb_map, bool check_bb_map = false){
	collect_parents(ve_model_nsf, true);
	collect_parents(ve_prop, false);
	//collect_parents(ve_init, false);

	
	
	string sname2 = sname;
	size_t found = sname.find_first_of("/\\$");
	while (found!=string::npos)
	{
		sname[found]='_';
		found=sname.find_first_of("/\\$",found+1);
	}
	string sname3 = sname;
	sname = sname2; // optimize this later
	
	Inst *top;
	ostringstream ostr;
	ostr << config->get_working_dir() << "/" << prefix << "_" << sname3 << "_" << depth;
	string fname = ostr.str();
	map<std::string, Inst*>::iterator hm_it = SigInst::hm_SigInst.find(sname);
	if(hm_it != SigInst::hm_SigInst.end()){
		Inst *ve_sig = hm_it->second;
		
		if(sname != config->get_arg(PROP_SIG_ARG)){
			int width = ve_sig->get_size();
			SORT sort = ve_sig->get_sort();
			cout << "draw_graph: reg_name: " << *ve_sig << ", width: " << width << endl;
			ve_sig = SigInst::create(sname+"$next", width, sort);
			if(check_bb_map){
				if(bb_map.find(ve_sig) == bb_map.end()){
					cout << *ve_sig << endl;
					assert(0);
				}else{
					ve_sig = bb_map[ve_sig];
					cout << *ve_sig << endl;
				}
				//ve_sig = bb_map[ve_sig];
				ve_sig = ve_sig->get_children()->front();
			}
		}
		if(m_pars.find(ve_sig) != m_pars.end()){
			top = *(m_pars[ve_sig].begin());
		}else{
			assert(0);
		}
//		cout << "top:" << *top << endl;
	}
	//if(top == NULL)
	{
		//top = bb_map[top];
	}

	assert(top != NULL);
	
	new_print(cout, top, true);

	string of_name, gif_name;
	of_name = fname + ".dot";
	gif_name = fname + ".gif";

	cout << "fname: " << fname << endl;
	ofstream ofile;
	ofile.open (of_name.c_str());
	ofile<<"digraph tmp {"<<endl;
// 	ofile<<"page=\"8.5,11\";"<<endl;
// 	ofile<<"ratio=auto;"<<endl;
	//ofile<<"ratio=0.625;"<<endl;
	ofile<<"node[fontsize=18];"<<endl;
	
	dump_dot(ofile, top, depth, true);

	ofile<<"}"<<endl;
	ofile.close();

	//dot -Tgif scu_sym_v3.dot -o scu_sym_v3.gif
	string cmd = "dot -Tgif "+of_name+" -o "+gif_name;
	cout<<cmd<<endl;
	if (0 != system(cmd.c_str())) {
		cout<<"dot error!!!"<<endl;
	}
	cout << "draw_graph() succeed!!!" << endl;
}
#endif


Inst *update_chs(Inst *ve_top, InstToInstM& bb_map, bool init_visit = false) {
	if (init_visit) {
		Inst::init_visit2();
	}
	if (ve_top->get_visit2()){
		return ve_top->acex_coi;
	}
	ve_top->set_visit2();
	ve_top->acex_coi = ve_top;	//TODO temporary use of acex_coi

	if((ve_top->get_type() == Num) || (ve_top->get_type() == Sig))
	{
		InstToInstM::iterator mit = bb_map.find(ve_top);
		Inst *ve_res;
		if(mit != bb_map.end()){
			ve_res = mit->second;
		}else{
			ve_res = ve_top;
		}
		ve_top->acex_coi = ve_res;
//		cout << "CHS: " << *ve_top << " -> " << *ve_res << endl;
		return ve_res;
	}else{
		InstToInstM::iterator mit = bb_map.find(ve_top);
		if(mit != bb_map.end()){
			Inst *ve_res;
			ve_res = mit->second;
			ve_top->acex_coi = ve_res;
//	    cout << "CHS: " << *ve_top << " -> " << *ve_res << endl;
			return ve_res;
		}
	}

	InstL new_ch;
	bool need_new = false;
	const InstL* chs = ve_top->get_children();
	if(chs){
		InstL::const_iterator it = chs->begin();
		for(; it != chs->end(); ++it) {
			Inst *ch = *it;
			Inst *ch_new = update_chs(ch, bb_map);
			if(ch != ch_new){
				need_new = true;
			}
			new_ch.push_back(ch_new);
		}
	}else{
		assert(0);
	}

	// for the (mult_bit_reg == width'd0) in init
	if((ve_top->get_type() == Op) && (OpInst::as(ve_top)->get_op() == OpInst::Eq)){
		InstL::iterator cit = new_ch.begin();
		Inst *ve_ch0 = *cit++;
		Inst *ve_ch1 = *cit;
// 		cout << "####$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$" << endl;
// 		cout << "ve_ch0: " << *ve_ch0 << ", size: " << ve_ch0->get_size() << endl;
// 		cout << "ve_ch1: " << *ve_ch1 << ", size: " << ve_ch1->get_size() << endl;
		int op_size = ve_ch0->get_size();
		if(op_size == 1){
			Inst *ve_res = OpInst::create(OpInst::LogXNor, ve_ch0, ve_ch1);
			//cout << "table, ve_res1: " << *ve_res << endl;
			ve_top->acex_coi = ve_res;
//	    cout << "CHS: " << *ve_top << " -> " << *ve_res << endl;
			return ve_res;
		}else{
			if((ve_ch0->get_type() == Op) && (OpInst::as(ve_ch0)->get_op() == OpInst::Concat)){
// 				if(ve_ch0->get_children()->size() == 3){
// 					cout << "ve_ch0: "	 << *ve_ch0 << endl;
// 				}
				
				if( ((ve_ch1->get_type() == Op) && (OpInst::as(ve_ch1)->get_op() == OpInst::Concat)) &&
					((ve_ch0->get_children())->size() == (ve_ch1->get_children())->size()) &&
					(OpInst::as(ve_ch0)->get_euf_func_name() == OpInst::as(ve_ch1)->get_euf_func_name()) ) {
					InstL::const_iterator cit_0 = (ve_ch0)->get_children()->begin();
					InstL::const_iterator cit_1 = (ve_ch1)->get_children()->begin();
					Inst *ve_res;
					InstL conjunctAnd;
					for (; cit_0 != (ve_ch0)->get_children()->end(); ++cit_0, ++cit_1) {
						Inst *ve_bit = OpInst::create(OpInst::Eq, *cit_0, *cit_1);
						conjunctAnd.push_back(ve_bit);
					}
					if (conjunctAnd.size() == 1)
					  ve_res = conjunctAnd.front();
					else
					  ve_res = OpInst::create(OpInst::LogAnd, conjunctAnd);
					//cout << "table, ve_res2: " << *ve_res << ", ve_ch0->get_size():" << op_size << endl;
					ve_top->acex_coi = ve_res;
//			    cout << "CHS: " << *ve_top << " -> " << *ve_res << endl;
					return ve_res;
				}
				else if((ve_ch0->m_pbb.size() - 1) == ve_ch0->get_children()->size()){
					InstL::const_iterator cit_0 = ve_ch0->get_children()->begin();
					Inst *ve_res;
					int i = 0;
					int idx_begin = 0;
					int idx_end = 0;
					for (; cit_0 != (ve_ch0)->get_children()->end(); ++cit_0) {
						Inst *tve = *cit_0;
						idx_end += tve->get_size();
						Inst *ve_bit = OpInst::create(OpInst::Eq, tve, ExInst::create(ve_ch1, (idx_end-1), idx_begin));
						if(i != 0){
							ve_res = OpInst::create(OpInst::LogAnd, ve_res, ve_bit);
						}else{
							ve_res = ve_bit;
						}
						i++;
						idx_begin = idx_end;
					}
					//cout << "table, ve_res2: " << *ve_res << ", ve_ch0->get_size():" << op_size << endl;
					ve_top->acex_coi = ve_res;
//          cout << "CHS1.1: " << *ve_top << " -> " << *ve_res << endl;
					return ve_res;
				}
			}
		}
		
// 		else{
// 			if((ve_ch0->get_type() == Op) && (OpInst::as(ve_ch0)->get_op() == OpInst::Concat)){
// 				if( ((ve_ch1->get_type() == Op) && (OpInst::as(ve_ch1)->get_op() == OpInst::Concat)) &&
// 					((ve_ch0->get_children())->size() == (ve_ch1->get_children())->size()) ){
// 					InstL::const_iterator cit_0 = (ve_ch0)->get_children()->begin();
// 					InstL::const_iterator cit_1 = (ve_ch1)->get_children()->begin();
// 					Inst *ve_res;
// 					for (int i = 0; i < op_size; ++i, ++cit_0, ++cit_1) {
// 						ve_ch0 = *cit_0;
// 						ve_ch1 = *cit_1;
// 						Inst *ve_bit = OpInst::create(OpInst::LogXNor, ve_ch0, ve_ch1);
// 	// 					if(!ve_bit){
// 	// 						cout << "ve_ch0: " << *ve_ch0 << ", size: " << ve_ch0->get_size() << endl;
// 	// 						cout << "ve_ch1: " << *ve_ch1 << ", size: " << ve_ch1->get_size() << endl;	
// 	// 					}
// 						if(i != 0){
// 							ve_res = OpInst::create(OpInst::LogAnd, ve_res, ve_bit);
// 						}else{
// 							ve_res = ve_bit;
// 						}
// 					}
// 					//cout << "table, ve_res2: " << *ve_res << ", ve_ch0->get_size():" << op_size << endl;
// 					ve_top->acex_coi = ve_res;
// 					return ve_res;
// 				}else if(op_size == ve_ch0->get_children()->size()){
// 					InstL::const_iterator cit_0 = ve_ch0->get_children()->begin();
// 					Inst *ve_res;
// // 					if(op_size != ve_ch0->get_children()->size()){
// // 						cout << *ve_ch0 << endl;
// // 						cout << "op_size: " << op_size << ", ve_ch0->get_children()->size(): " << ve_ch0->get_children()->size() << endl;
// // 						assert(0);
// // 					}
// 					
// 					for (int i = 0; i < op_size; ++i, ++cit_0) {
// 						ve_ch0 = *cit_0;
// 						Inst *ve_bit = OpInst::create(OpInst::LogXNor, ve_ch0, ExInst::create(ve_ch1, i, i));
// 						if(i != 0){
// 							ve_res = OpInst::create(OpInst::LogAnd, ve_res, ve_bit);
// 						}else{
// 							ve_res = ve_bit;
// 						}
// 					}
// 					//cout << "table, ve_res2: " << *ve_res << ", ve_ch0->get_size():" << op_size << endl;
// 					ve_top->acex_coi = ve_res;
// 					return ve_res;
// 				}
// 			}
// 		}
	}
	
	// if need_new is false, we don't need to proceed this routine.
	// however, I'm checking two cases just in case (this should be unnecessary
	//	due to the simplification routines in vwn).
	
	if(need_new == true){	// TODO check possible BUG s
		if(ve_top->get_type() == Ex){
			ExInst *ve_ex = ExInst::as(ve_top);
			InstL vel_concat;
			Inst *ve_ch = new_ch.front();
			if((ve_ch->get_type() == Op) && (OpInst::as(ve_ch)->get_op() == OpInst::Concat) && (ve_ch-> get_size() == ve_ch->get_children()->size())){
				const InstL* concat_ch = ve_ch->get_children();
				if(concat_ch){
	// 				cout << "ve_top: " << *ve_top << endl;
	// 				cout << "concat_ch->size(): " << concat_ch->size() << endl;
	// 				cout << "ve_ch->get_size(): " << ve_ch->get_size() << endl;
					
					InstL::const_iterator cit = concat_ch->begin();
					for(int i = 0; i < (int)ve_ex->get_lo(); ++i){
						++cit;
					}
					for(int i = 0; i < (int)ve_ex->get_size(); ++i){
						vel_concat.push_back(*cit);
						++cit;
					}
				}else{
					assert(0);
				}
				Inst *ve_res = OpInst::create(OpInst::Concat, vel_concat);
				ve_top->acex_coi = ve_res;
//		    cout << "CHS2: " << *ve_top << " -> " << *ve_res << endl;
				return ve_res;
			}
		}
		
		if((ve_top->get_type() == Op) && (OpInst::as(ve_top)->get_op() == OpInst::Concat)){
			InstL vel_concat;
			for(InstL::iterator cit = new_ch.begin(); cit != new_ch.end(); ++cit){
				Inst *ve_ch = *cit;
				if((ve_ch->get_type() == Op) && (OpInst::as(ve_ch)->get_op() == OpInst::Concat)){
					const InstL* concat_ch = ve_ch->get_children();
					if(concat_ch){
						for(InstL::const_iterator cit2 = concat_ch->begin(); cit2 != concat_ch->end(); ++cit2){
							vel_concat.push_back(*cit2);
						}
					}else{
						assert(0);
					}
				}else{
					vel_concat.push_back(ve_ch);
				}
			}
			Inst *ve_res = OpInst::create(OpInst::Concat, vel_concat);
			ve_top->acex_coi = ve_res;
//	    cout << "CHS3: " << *ve_top << " -> " << *ve_res << endl;
			return ve_res;
		}
	}
	
	if(need_new){
		//if(new_ch.size() == 0)
// 		{
// 			cout << "ve_top: " << *ve_top << endl;
// 			cout << "new_ch (" << new_ch.size() << "): " << new_ch << endl;
// 		}
		
		Inst *ve_res = ve_top->apply_children(new_ch);
		ve_top->acex_coi = ve_res;
		
		bb_map[ve_top] = ve_res;
//    cout << "CHS4: " << *ve_top << " -> " << *ve_res << endl;
		return ve_res;
	}
	return ve_top;
}

// inputs: T, P, expr that needs to be bit-blasted
// TODO return ve_out, bit-blasted version of ve_in ?
void partial_bit_blast(Inst **ve_prop, Inst **ve_nsf, Inst *ve_in) {
	collect_parents(*ve_nsf, true);
	collect_parents(*ve_prop, false);
	
	InstToInstM to_bb;
	ve_in->bit_blast(to_bb, true);

	*ve_nsf = update_chs_pbb(*ve_nsf, to_bb, true);
	*ve_prop = update_chs_pbb(*ve_prop, to_bb, false);
	//*ve_init = update_chs_pbb(ve_init, to_bb, false);
}

void count_pars(Inst *top_orig, bool init_visit) {
  Inst* top = top_orig->get_port();
  top->inc_count();
//	cout << "top: n" << top->get_id() << "n	" << top->get_count() << endl;
//	cout << "top: " << *top << "  " << top->get_count() << endl;

//  cout << "top: " << *top << "  " << top->get_count() << endl;
//  if (top != top_orig)
//    cout << "top: " << *top_orig << "  " << top_orig->get_count() << endl;

	if(init_visit){
		Inst::init_visit2();
	}
	if(top->get_visit2()){
		return;
	}
	top->set_visit2();

	const InstL* chs = top->get_children();

	if(chs){
		InstL::const_iterator it = chs->begin();
		for (InstL::const_iterator end_it = chs->end(); it != end_it; ++it) {
			Inst *ch = *it;
			count_pars(ch, false);
		}
	}
}

#if 0
int max_width(Inst *top, bool init_visit, int width = 0) {
	if(init_visit){
		Inst::init_visit2();
	}
	if(top->get_visit2()){
		return width;
	}
	top->set_visit2();

	int top_size = top->get_size();
	if(width < top_size){
		width = top_size;
	}
	
	const InstL* chs = top->get_children();
	if(chs){
		InstL::const_iterator it = chs->begin();
		for (InstL::const_iterator end_it = chs->end(); it != end_it; ++it) {
			Inst *ch = *it;
			width = max_width(ch, false, width);
		}
	}
	return width;
}
#else
int max_width(Inst *top, bool init_visit, int width = 0){
	if(init_visit){
		Inst::init_visit2();
	}
	if(top->get_visit2()){
		return width;
	}
	top->set_visit2();

	const InstL* chs = top->get_children();
	if(chs){

//		if((top->get_type() == Op) && ((OpInst::as(top))->get_op() == OpInst::Mult)){
//			cout << "(not abstracting cone with Mult)" << endl;
//			return 1000; // meaning that we should not bit-blast
//		}
//
//		if((top->get_type() == Op) && ((OpInst::as(top))->get_op() == OpInst::AShiftR)){
//			cout << "(not abstracting cone with AShiftR)" << endl;
//			return 1000; // meaning that we should not bit-blast
//		}

		InstL::const_iterator it = chs->begin();
		for (InstL::const_iterator end_it = chs->end(); it != end_it; ++it) {
			Inst *ch = *it;
			width = max_width(ch, false, width);
		}
	}else if(top->get_type() != Num){
		int top_size = top->get_size();
		if(width < top_size){
			width = top_size;
		}
	}
	return width;
}
#endif

bool contain_big_mux(Inst *top, bool init_visit) {
	if(init_visit){
		Inst::init_visit2();
	}
	if(top->get_visit2()){
		return false;
	}
	top->set_visit2();

	if(s_data.find(top) != s_data.end()){
		return true;
	}
	
	const InstL* chs = top->get_children();
	if(chs){
		InstL::const_iterator it = chs->begin();
		for (InstL::const_iterator end_it = chs->end(); it != end_it; ++it) {
			Inst *ch = *it;
			if(contain_big_mux(ch, false) == true){
				return true;
			}
		}
	}
	return false;
}

void derive_pbbs(Inst *top_orig, set<int>& pbb) {
// 	if(top->get_size() == 1){
// 		return;
// 	}

	Inst* top = top_orig->get_port();

	if(top->get_size() != 1){
		for(set<int>::iterator it = pbb.begin(); it != pbb.end(); ++it){
			if(*it < top->get_size()){
				(top->m_pbb).insert(*it);
			}
		}
	}

#ifdef DEBUG_DERIVE_PBBS
	cout << "top: n" << top->get_id() << "n	" << top->get_count();
	for(set<int>::iterator it = top->m_pbb.begin(); it != top->m_pbb.end(); ++it){
		cout << "	" << *it;
	}
	cout << endl;
#endif

//	cout << "top: " << top->get_size() << "\t" << *top << " 	" << top->get_count() << " => ";
//	for(set<int>::iterator it = top->m_pbb.begin(); it != top->m_pbb.end(); ++it){
//		cout << "	" << *it;
//	}
//	cout << endl;
	
	if(top->dec_count() == true){
// 		set<int> t_pbb;
// 		const InstL* chs = top->get_children();
// 		if(chs){
// 			InstL::const_iterator it = chs->begin();
// 			derive_pbbs(*it, t_pbb);	// pass empty set to the control signal
// 			++it;
// 			for (; it != chs->end(); ++it) {
// 				derive_pbbs(*it, t_pbb);
// 			}
// 		}
// 		return;
		
		
		if((top->get_type() == Op) && ((OpInst::as(top))->get_op() == OpInst::Concat)){
			const InstL* chs = top->get_children();
			if(chs){
				InstL::const_iterator it = chs->begin();
				set<int>::iterator pbb_it = (top->m_pbb).begin();
				int accum_width_pre = 0;
				int accum_width = 0;
				for (InstL::const_iterator end_it = chs->end(); it != end_it; ++it) {
					Inst *ch = (*it);
					set<int> t_pbb;
					int width_ch = ch->get_size();
					accum_width += width_ch;
					if(width_ch != 1){
						for(; pbb_it != (top->m_pbb).end(); ++pbb_it){
							int idx = *pbb_it;
							if(accum_width < idx){
								//t_pbb.insert(accum_width-accum_width_pre);
								break;
							}else if(accum_width == idx){
//								++pbb_it;
								//t_pbb.insert(*pbb_it-accum_width_pre);
								break;
							}else{
								t_pbb.insert(*pbb_it-accum_width_pre);
							}
						}
					}
//					else{
//						for(; pbb_it != (top->m_pbb).end(); ++pbb_it){
//							int idx = *pbb_it;
//							if(accum_width <= idx){
//								//t_pbb.insert(accum_width-accum_width_pre);
//								break;
//							}
//						}
//					}
					
					derive_pbbs(ch, t_pbb);
					accum_width_pre = accum_width;
				}
			}
		}else{
			
// 		case BitWiseNot:
// 
// 		case BitWiseAnd:
// 		case BitWiseOr:
// 		case BitWiseXor:
// 		case BitWiseXNor:
// 		case BitWiseNor:
// 		case BitWiseNand:{

			
			
			set<int> t_pbb;
			if((top->get_type() == Op) && ((OpInst::as(top))->get_op() == OpInst::Ternary)){
				const InstL* chs = top->get_children();
				InstL::const_iterator it = chs->begin();
				derive_pbbs((*it), t_pbb);	// pass empty set to the control signal
				t_pbb = (top->m_pbb);
				++it;
				for (; it != chs->end(); ++it) {
					derive_pbbs((*it), t_pbb);
				}
			}else{
				if(top->get_type() == Ex){
					ExInst *vex = ExInst::as(top);
					unsigned hi = vex->get_hi() + 1;
					unsigned lo = vex->get_lo();
					
// 					set<int>::iterator pbb_it = (top->m_pbb).begin();
// 					set<int>::iterator pbb_it_end = --(top->m_pbb).end();
// 					++pbb_it;
// 					for(; pbb_it != pbb_it_end; ++pbb_it){
// 						int idx = *pbb_it + lo;
// 						t_pbb.insert(idx);
// 						//cout << "	" << idx;
// 					}

					for(set<int>::iterator pbb_it = (top->m_pbb).begin(); pbb_it != (top->m_pbb).end(); ++pbb_it){
						int idx = *pbb_it + lo;
						t_pbb.insert(idx);
						//cout << "	" << idx;
					}
					
					t_pbb.insert(hi);
					t_pbb.insert(lo);
				}
// TODO implement this !!
// Aman (dangerous), do not uncomment
// 				else{
// 					t_pbb = (top->m_pbb);
// 				}
				
				set<int> empty_pbb;
				const InstL* chs = top->get_children();
				if(chs){
					InstL::const_iterator it = chs->begin();
					for (InstL::const_iterator end_it = chs->end(); it != end_it; ++it) {
						Inst *ch = (*it);
						if(ch->get_size() == 1){
							derive_pbbs(ch, empty_pbb);
						}else{
							derive_pbbs(ch, t_pbb);
						}
					}
				}
			}
		}
		(top->m_pbb).insert(0);
		(top->m_pbb).insert(top->get_size());

//		if (top != top_orig)
//		{
//			top_orig->m_pbb = top->m_pbb;
//		}

//		if (top->m_pbb.size() > 2)
//		{
//      cout << *top << " []> ";
//      for (auto& p: top->m_pbb)
//        cout << "  " << p;
//      cout << endl;
//		}

	  if (top->get_type() == Op || top->get_type() == Ex) {
	    OpInst* op = OpInst::as(top);
	    Inst* w = op->get_wire();
	    if (w) {
	      w->m_pbb = top->m_pbb;

//	      if (w->m_pbb.size() > 2)
//	      {
//          cout << *w << " []> ";
//          for (auto& p: w->m_pbb)
//            cout << "  " << p;
//          cout << endl;
//	      }
	    }
	  }

	}

////	if (top->m_pbb.size() > 2)
//  {
//    cout << *top << " -[]> ";
//    for (auto& p: top->m_pbb)
//      cout << "  " << p;
//    cout << endl;
//  }
//
//  if (top->get_type() == Op || top->get_type() == Ex) {
//    OpInst* op = OpInst::as(top);
//    Inst* w = op->get_wire();
//    if (w) {
//      w->m_pbb = top->m_pbb;
//
////      if (w->m_pbb.size() > 2)
//      {
//        cout << *w << " -[]> ";
//        for (auto& p: w->m_pbb)
//          cout << "  " << p;
//        cout << endl;
//      }
//    }
//  }

//	if (top->get_type() == Wire)
//	{
//		WireInst* w = WireInst::as(top);
//		cout << *w << " []> ";
//		for (auto& p: w->m_pbb)
//			cout << "  " << p;
//		cout << endl;
//
//		Inst* port = w->get_port();
//		cout << *port << " []> ";
//		for (auto& p: port->m_pbb)
//			cout << "  " << p;
//		cout << endl;
//
//		assert(port->m_pbb.size() <= w->m_pbb.size());
//
//		port->m_pbb = w->m_pbb;
//	}
}

// for the quick and easy use
// for AVR_PARTIAL_BIT_BLAST
void partial_bit_blast(InstL &in_sigs, bool bb_prop) {
		int idx = 0;
		collect_parents(ve_model_nsf, true);
		collect_parents(ve_prop, false);
		collect_parents(ve_assume, false);
		//collect_parents(ve_init, false);
		
		InstToInstM to_bb;
		Inst::init_visit();
		InstL to_examine;
		bool bb_prop2 = false;
		if(!in_sigs.empty()){
			bb_prop2 = true;
		}
		for(InstL::iterator ir_it = in_sigs.begin(); ir_it != in_sigs.end(); ++ir_it){
			SigInst *ve_reg = SigInst::as(*ir_it);
			bool is_reg = false;
			if(ve_reg){
				string str = ve_reg->get_name();
				int width = ve_reg->get_size();
				SORT sort = ve_reg->get_sort();
				Inst *ve_sig = SigInst::create(str+"$next", width, sort);
				if(m_pars.find(ve_sig) != m_pars.end()){
					is_reg = true;
					Inst *ve_in = *(m_pars[ve_sig].begin());
					int max_width_ve_in = max_width(ve_in, true, 0);
					if((ve_in->get_type() == Op) && (OpInst::as(ve_in)->get_op() == OpInst::Eq)){
						cout << "partial_bit_blast, ve_sig: " << *ve_sig << ", width:" << width << ", max_width: " << max_width_ve_in;
						
						bool clt_cond = true;
#ifndef BIT_LEVEL_AVR
						// AVR_NEW_CLT_MODE = new_clt_mode
						// 0 : non calypto benchmarks
						// 1 : calypto default	- turn on partitioning and partial bitblasting
						// 2 : 154 series
						// 3 : c17 series
						if(new_clt_mode == 3){
							clt_cond = false;
						}else if(new_clt_mode == 2){
//							clt_cond = ((max_width_ve_in < 33) && (str.substr(0,30) != "r2y_beu_ln386_d_out_out_0_0_24")) ? true : false;
							clt_cond = ((max_width_ve_in < 32) || ((width < 12) && contain_big_mux(ve_in, true))) ? true : false;
						}else{
							clt_cond = ((max_width_ve_in < 32) || ((width < 12) && contain_big_mux(ve_in, true))) ? true : false;
						}
#endif

#ifdef PATCH_FOR_C17
clt_cond = (((max_width_ve_in < 32) || ((width < 12) && contain_big_mux(ve_in, true))) || (str.substr(0,15) == "fifo_full_trig_")) ? true : false;
#endif
// 		s_reg_names.insert("fifo_full_trig_reg/q");
// 		s_reg_names.insert("fifo_full_trig_88707_reg/q");


						if(clt_cond)
						{
							cout << " << bit_blasted" << endl;
							to_examine.push_back(ve_in);
							//cout << "partial_bit_blast, ve_in: " << *ve_in << endl;
							if(width > 1){
							//	cout << "partial_bit_blast, ve_in: " << *ve_in << endl;
								
								InstL vel_concat;
								for(int i = 0; i < (int)width; ++i){
									ostringstream oss;
									oss << str << "$" << i << "$next";
									
									Inst *ve_bit = SigInst::create(oss.str(), 1, SORT());
									vel_concat.push_back(ve_bit);
									
								}
								Inst *ve_res = OpInst::create(OpInst::Concat, vel_concat);
								ve_sig->set_visit();
								to_bb[ve_sig] = ve_res;

								vel_concat.clear();
								ve_sig = SigInst::create(str, width, sort);
								
								Inst* ve_num = NULL;
								if(map_init.find(ve_sig) != map_init.end()){
									ve_num = map_init[ve_sig];
									map_init.erase(ve_sig);
								}
								for(int i = 0; i < (int)width; ++i){
									ostringstream oss;
									oss << str << "$" << i;
									
									Inst *ve_bit = SigInst::create(oss.str(), 1, SORT());
									vel_concat.push_back(ve_bit);
									
									if(ve_num != NULL){
										Inst* ve_num_bit = ExInst::create(ve_num, i, i);
										map_init[ve_bit] = ve_num_bit;
									}
								}
								ve_res = OpInst::create(OpInst::Concat, vel_concat);
								ve_sig->set_visit();
								to_bb[ve_sig] = ve_res;		
							}
						}else{
							bb_prop2 = false;
							cout << endl;
						}
					}
				}
			}
			
			if(is_reg == false){
				if(m_pars.find(*ir_it) == m_pars.end()){
					cout << "Unable to find a mux." << endl;
					//cout << "muxes, m_pars[] of" << *(*ir_it) << endl;
					//assert(0);
				}else{
					#if 1
						to_examine.push_back(*(m_pars[*ir_it].begin()));
						cout << "added a mux to concretized." << endl;
					#else
						InstS::iterator t_sit = m_pars[*ir_it].begin();
						
						cout << "added a mux to concretized.";
						for(; t_sit != m_pars[*ir_it].end(); ++t_sit){
							Inst *ve_in = *t_sit;
							to_examine.push_back(ve_in);
							cout << "#";
						}
						cout << endl;
					#endif				
					//cout << "muxes, sel: " << *(*ir_it) << endl;
					//cout << "muxes:" << endl << *ve_in << endl << endl;
				}
			}
		}
		
		for(InstL::iterator eit = to_examine.begin(); eit != to_examine.end(); ++eit){
			//cout << "(*eit)" << *(*eit) << endl;
			(*eit)->bit_blast(to_bb, false);
		}
		
		int max_width_prop = max_width(ve_prop, true, 0);
		cout << "partial_bit_blast, ve_sig: prop, max_width: " << max_width_prop;

		
		bool clt_cond = true;
#ifndef BIT_LEVEL_AVR
		// AVR_NEW_CLT_MODE = new_clt_mode
		// 0 : non calypto benchmarks
		// 1 : calypto default	- turn on partitioning and partial bitblasting
		// 2 : 154 series
		// 3 : c17 series
		if(new_clt_mode == 3){
			clt_cond = false;
		}else if(new_clt_mode == 2){
//			clt_cond = true;
			clt_cond = (max_width_prop < 32) ? true : false;
		}else{
			clt_cond = (max_width_prop < 32) ? true : false;
		}
#endif
		if(clt_cond)
		{
			ve_prop->bit_blast(to_bb, false);
			cout << " << bit_blasted" << endl;
		}else{
			cout << endl;
		}
		
// 		idx = 0;
// 		for(InstToInstM::iterator mit = to_bb.begin(); mit != to_bb.end(); ++mit){
// 			cout << "to_bb: " << idx++ << endl;
// 			cout << *(mit->first) << endl;
// 			cout << *(mit->second) << endl;
// 		}
		//M1TU__P_1051$0
		
		//cout << "NOW UPDATE CHS" << endl;

//		cout << "to_bb sz: " << to_bb.size() << endl;
//		for (auto& m: to_bb)
//		{
//			cout << *(m.first) << " => ";
//			if (m.first == m.second)
//				cout << "same" << endl;
//			else
//			cout << *(m.second) << endl;
//		}

		ve_model_nsf = update_chs_pbb(ve_model_nsf, to_bb, true);
		ve_prop = update_chs_pbb(ve_prop, to_bb, false);
		ve_assume = update_chs_pbb(ve_assume, to_bb, false);
		//ve_init = update_chs_pbb(ve_init, to_bb, false);


// {
// 
// 	collect_parents(ve_model_nsf, true);
// 	collect_parents(ve_prop, false);
// 	//collect_parents(ve_init, false);
// 
// 	
// 	string sname = "fld_bottom_mode_88800_reg/q";
// 	
// 	Inst *top;
// 	map<std::string, Inst*>::iterator hm_it = SigInst::hm_SigInst.find(sname);
// 	if(hm_it != SigInst::hm_SigInst.end()){
// 		Inst *ve_sig = hm_it->second;
// 		
// 		if(sname != config->get_arg(PROP_SIG_ARG)){
// 			int width = ve_sig->get_size();
// 			cout << "debug: reg_name: " << *ve_sig << ", width: " << width << endl;
// 			ve_sig = SigInst::create(sname+"$next", width);
// // 			if(to_bb.find(ve_sig) == to_bb.end()){
// // 				cout << *ve_sig << endl;
// // 				assert(0);
// // 			}else{
// // 				ve_sig = to_bb[ve_sig];
// // 				cout << *ve_sig << endl;
// // 			}
// // 			//ve_sig = to_bb[ve_sig];
// // 			ve_sig = ve_sig->get_children()->front();
// 		}
// 		if(m_pars.find(ve_sig) != m_pars.end()){
// 			top = *(m_pars[ve_sig].begin());
// 		}else{
// 			assert(0);
// 		}
// 		cout << "top:" << *top << endl;
// 
// 		dump_to_bb(top, to_bb, true);
// 		assert(0);
// 
// 	}
// 	
// }
		
}

void collect_regs2(Inst *top, set<string> &s_reg_names, bool init_visit=false) {
	if (init_visit) {
		Inst::init_visit2();
	}
	if (top->get_visit2()) {
		return;
	}
	top->set_visit2();

	SigInst *sve = SigInst::as(top);
//	if((top->get_size() > 1) && sve){	// we are considering to bit-blast the NSF of a single-bit FF
	if(sve){
		string reg_name = sve->get_name();
		map<std::string, Inst*>::iterator hm_it = SigInst::hm_SigInst.find(reg_name+"$next");
		if(hm_it != SigInst::hm_SigInst.end()){
//			cout << "Cone: " << reg_name << endl;
			s_reg_names.insert(reg_name);
		}
	}else{
		const InstL* ch = top->get_children();
		if (ch) {
			for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it) {
				collect_regs2(*it, s_reg_names);
			}
		}
	}
}

void collect_cone(Inst *top, set<string> &s_reg_names, int& numCF, int& numUF, int& numEx, int& numCc, bool init_visit) {
	if (init_visit) {
		Inst::init_visit2();
	}
	if (top->get_visit2()) {
		return;
	}
	top->set_visit2();

	SigInst *sve = SigInst::as(top);
//	if((top->get_size() > 1) && sve){	// we are considering to bit-blast the NSF of a single-bit FF
	if(sve){
		string reg_name = sve->get_name();
		map<std::string, Inst*>::iterator hm_it = SigInst::hm_SigInst.find(reg_name+"$next");
		if(hm_it != SigInst::hm_SigInst.end()){
			s_reg_names.insert(reg_name);
		}
	}
	else
	{
		ExInst *ex = ExInst::as(top);
		if (ex)
			numEx++;
		else
		{
			OpInst *op = OpInst::as(top);
			if (op)
			{
				string euf_func_name = op->get_euf_func_name();
				if (euf_func_name == "0")
					numCF++;
				else if (op->get_op() == OpInst::Concat)
					numCc++;
				else
					numUF++;
			}
		}

		const InstL* ch = top->get_children();
		if (ch) {
			for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it) {
				collect_cone(*it, s_reg_names, numCF, numUF, numEx, numCc);
			}
		}
	}
}


int main(int argc, char **argv){
	VWN_COUT_A("Running vwn" << endl);

	argc-- , argv++;
	if(argc!=2){
	cerr<<"Syntax: vwn "<<"<word_dir> <bin_dir>"<<endl;
		return 1;
	}
	Config inst_config(argv[0],argv[1]);
	inst_config.load_args();
	config = &inst_config;
	
#ifdef BIT_LEVEL_AVR
	new_clt_mode = 1;
#else
	new_clt_mode = atoi(config->get_arg(AVR_NEW_CLT_MODE).c_str());
#endif
	
//	new_clt_mode = 2;
	
    string fname = config->get_arg(DESIGN_ARG).c_str();
    string path = get_path_from_fname(fname);
    const char *file_name = fname.c_str();

    cout << fname  << "  " << path << endl;

	string tmp = remove_path_from_fname(argv[0]);
	_benchmark = tmp.substr(tmp.find("work_") + 5);

	string fname_reach = config->get_working_dir() + "/" + _benchmark + ".results";

	_resFile.open(fname_reach.c_str());

	_resFile << "i-benchmark:\t" << _benchmark << endl;

#ifdef ENABLE_SAL
	_resFile << "frontend:\tsally" << endl;
	string fname_sal = config->get_working_dir() + "/" + _benchmark + ".mcmt";
	SalFrontend* sf = new SalFrontend(fname_sal);
//	sf->help();
	sf->execute();
	derive_ITP();
#endif

	string frontend = config->get_arg(SELECT_FRONTEND);

	if (frontend == FRONTEND_YOSYS) {
#ifndef ENABLE_YOS
		AVR_COUT <<"\t(yosys frontend unavailable)"<<endl;
		assert(0);
#else
		_resFile << "frontend:\tyosys" << endl;
		string fname_ilang = config->get_working_dir() + "/" + _benchmark + ".ilang";
		IlangFrontend il(fname_ilang);
		il.execute();
		derive_ITP();
#endif
	}
	else if (frontend == FRONTEND_VMT) {
#ifndef ENABLE_VMT
		AVR_COUT <<"\t(vmt frontend unavailable)"<<endl;
		assert(0);
#else
		_resFile << "frontend:\tvmt" << endl;
		string fname_vmt = config->get_working_dir() + "/" + _benchmark + ".vmt";
		VmtFrontend vm(fname_vmt);
		vm.execute();
		derive_ITP();
#endif
	}
	else if (frontend == FRONTEND_JG)
	{
#ifndef ENABLE_JG
		AVR_COUT <<"\t(jg frontend unavailable)"<<endl;
		assert(0);
#else
		_resFile << "frontend:\tjg" << endl;
		string fname_wif = config->get_working_dir() + "/" + _benchmark + ".wif";
		string wif_options = config->get_arg(JG_PREPROCESS);
		WifFrontend jg(fname_wif, wif_options);
		jg.execute();
		derive_ITP();
#endif
	}
	else if (frontend == FRONTEND_BTOR2) {
#ifndef ENABLE_BTOR2
		AVR_COUT <<"\t(btor2 frontend unavailable)"<<endl;
		assert(0);
#else
		_resFile << "frontend:\tbtor2" << endl;
		string fname_bt2 = config->get_working_dir() + "/" + _benchmark + ".btor2";
		Btor2Frontend bt(fname_bt2);
		bt.execute();
		derive_ITP();
#endif
	}
	else {
		AVR_COUT <<"\t(unknown argument value for "<< SELECT_FRONTEND <<")"<<endl;
		assert(0);
	}

InstToInstM to_bb;


/// When MOVED_TO_DPA is true, the below if is not executed.
/// This part of code has been moved to dpa.cpp
/// Note- updation of s_data is performed as a separate elseif case.
/// But updation of list_mux... is not performed in moved code (not required)
///
if(!MOVED_TO_DPA){
  if (Config::g_split_signals)
  {
    avr_log("performing splitting nodes at extract points");
	set<string> s_reg_names;

	Inst *debug_top;

	
#ifdef DEBUG_DERIVE_PBBS
	cout << "vwn ve_init:" << endl;
	new_print(cout, ve_init, true);
	cout << "vwn ve_model_nsf:" << endl;
	new_print(cout, ve_model_nsf, true);
	cout << "vwn ve_prop:" << endl;
	new_print(cout, ve_prop, true);
#endif

  collect_regs2(ve_prop, s_reg_names, true);
#ifndef PROPERTY_DIRECTED_SPLIT
	collect_regs2(ve_model_nsf, s_reg_names, false);
#endif
	
	InstL in_sigs;

	for(set<string>::iterator sit = s_reg_names.begin(); sit != s_reg_names.end(); ++sit){
		string reg_name = *sit;
//    cout << "reg_name: " << reg_name << endl;

		map<std::string, Inst*>::iterator hm_it = SigInst::hm_SigInst.find(reg_name);
		if(hm_it != SigInst::hm_SigInst.end()){
			Inst *ve_sig = hm_it->second;
			int width = ve_sig->get_size();

			VWN_COUT_A("reg_name: " << reg_name << ", width: " << width << endl);
			in_sigs.push_back(SigInst::create(reg_name, width, ve_sig->get_sort()));
			VWN_COUT_A(*in_sigs.back() << endl);
		}				
	}

	/// Sets the count of times a sub-expression appears in an expression

	set<int> temp;
	/// Derives m_pbb for each node in given graph
	count_pars(ve_model_nsf, true);
	derive_pbbs(ve_model_nsf, temp);

	count_pars(ve_prop, true);
	derive_pbbs(ve_prop, temp);
	
	count_pars(ve_assume, true);
	derive_pbbs(ve_assume, temp);

  int idx = 0;
  collect_parents(ve_model_nsf, true);
  collect_parents(ve_prop, false);
  collect_parents(ve_assume, false);

	{
		InstToInstM to_bb;
		Inst::init_visit();
		InstL to_examine;
		for(InstL::iterator ir_it = in_sigs.begin(); ir_it != in_sigs.end(); ++ir_it){
			SigInst *ve_reg = SigInst::as(*ir_it);
			VWN_COUT_A("in_sigs: " << *(*ir_it) << ", width: " << (*ir_it)->get_size() << endl);
//      cout << "in_sigs: " << *(*ir_it) << ", width: " << (*ir_it)->get_size() << endl;
			
			bool is_reg = false;
			if(ve_reg){
				string str = ve_reg->get_name();
				
				int width = ve_reg->get_size();
				Inst *ve_regNext = SigInst::create(str+"$next", width, ve_reg->get_sort());
				if(m_pars.find(ve_regNext) != m_pars.end()){
					is_reg = true;
					InstToInstM::iterator mit = transitions.find(ve_regNext);
					assert(mit != transitions.end());
					Inst *ve_in = OpInst::create(OpInst::Eq, ve_regNext, (*mit).second);
//					Inst *ve_in = *(m_pars[ve_regNext].begin());

					if(width > 1){
						VWN_COUT_A("split signals, ve_in: " << *ve_in << endl);
//            cout << "\nsplit signals, ve_in: " << *ve_in << "\n" << endl;
						
//            cout << "split signals, ve_in: " << *ve_in << endl;

						InstL vel_concat;
						set<int>& pbb = (SigInst::create(str, width, ve_reg->get_sort()))->m_pbb;

						{
							ve_regNext->m_pbb = pbb;
							ve_in->get_children()->back()->get_port()->m_pbb = pbb;
							to_examine.push_back(ve_in);

							assert((*(pbb.begin()) == 0) && (*(--pbb.end()) == width));
							set<int>::iterator sit = pbb.begin();
							++sit;
							int idx_begin = 0;
							int idx_end = 0;
							for(; sit != pbb.end(); ++sit){
								idx_end = *sit - 1;
								ostringstream oss;
			          if (idx_begin == 0 && idx_end == (ve_regNext->get_size()-1))
	                oss << str << "$next";
			          else
			            oss << str << "$" << ve_regNext->get_size() << "$[" << idx_end << ":" << idx_begin << "]" << "$next";
								
								Inst *ve_bit = SigInst::create(oss.str(), (idx_end - idx_begin + 1), SORT());
								vel_concat.push_back(ve_bit);
								idx_begin = idx_end+1;
							}
							Inst *ve_res = OpInst::create(OpInst::Concat, vel_concat);
							ve_regNext->set_visit();
							to_bb[ve_regNext] = ve_res;
							VWN_COUT_A("to_bb[" << *ve_regNext << "]" << " = " << *ve_res << endl);

							vel_concat.clear();

							set<int>& pbb2 = ve_reg->m_pbb;
							VWN_COUT_A("m_pbb for " << *ve_reg << " is ");
							for (set<int>::iterator pbbIt = pbb2.begin(); pbbIt != pbb2.end(); pbbIt++)
							{
								VWN_COUT_A(*pbbIt << "  ");
							}
							VWN_COUT_A(endl);

							if(pbb2.size() >= 2){
								assert((*(pbb2.begin()) == 0) && (*(--pbb2.end()) == width));
								set<int>::iterator sit = pbb2.begin();
								++sit;
								int idx_begin = 0;
								int idx_end = 0;
								
								Inst* ve_num = NULL;
								if(map_init.find(ve_reg) != map_init.end()){
									ve_num = map_init[ve_reg];
									map_init.erase(ve_reg);
								}
								for(; sit != pbb2.end(); ++sit){
									idx_end = *sit - 1;
									ostringstream oss;
	                if (idx_begin == 0 && idx_end == (ve_reg->get_size()-1))
	                  oss << str;
	                else
	                  oss << str << "$" << ve_reg->get_size() << "$[" << idx_end << ":" << idx_begin << "]";
									
									Inst *ve_bit = SigInst::create(oss.str(), (idx_end - idx_begin + 1), SORT());
									vel_concat.push_back(ve_bit);
									
									if(ve_num != NULL){
										Inst* ve_num_bit = ExInst::create(ve_num, idx_end, idx_begin);
										map_init[ve_bit] = ve_num_bit;
									}
									idx_begin = idx_end+1;
								}							
								ve_res = OpInst::create(OpInst::Concat, vel_concat);
								ve_reg->set_visit();
								to_bb[ve_reg] = ve_res;
                VWN_COUT_A("to_bb[" << *ve_reg << "]" << " = " << *ve_res << endl);
//                				cout << "to_bb[" << *ve_reg << "]" << " = " << *ve_res << endl;
                				assert(ve_reg->get_size() == ve_res->get_size());
							}
						}
					}
				}
			}
		}
    for(InstL::iterator eit = to_examine.begin(); eit != to_examine.end(); ++eit){
      Inst* ve_in = (*eit);
      count_pars(ve_in, true);
      set<int> temp;
      derive_pbbs(ve_in, temp);
    }

		ve_prop->split_signals(to_bb, false);

		for(InstL::iterator eit = to_examine.begin(); eit != to_examine.end(); ++eit){
		  Inst* v = (*eit);
		  OpInst* op = OpInst::as(v);
		  assert(op);
		  assert(op->get_op() == OpInst::Eq);
		  Inst* lhs = v->get_children()->front();
      Inst* rhs = v->get_children()->back();
		  assert(lhs->get_type() == Sig);

      InstToInstM::iterator mit = to_bb.find(lhs);
      assert(mit != to_bb.end());

      rhs->split_signals(to_bb, false);
      Inst* rhsNew = to_bb[rhs];

      set<int>::iterator sit = lhs->m_pbb.begin();
      ++sit;
      int idx_begin = 0;
      int idx_end = 0;
      InstL vel_concat;
      for(; sit != lhs->m_pbb.end(); ++sit){
        idx_end = *sit - 1;
//        cout << "Extracting [" << idx_end << ":" << idx_begin << "] from sz: " << rhsNew->get_size() << "  " << *rhsNew << endl;
        Inst *ve_bit_sliced = ExInst::create(rhsNew, idx_end, idx_begin);
        ve_bit_sliced->split_signals(to_bb, false);
        vel_concat.push_back(ve_bit_sliced);
        idx_begin = idx_end+1;
      }

      if (vel_concat.size() == 1)
        rhsNew = vel_concat.front();
      else
        rhsNew = OpInst::create(OpInst::Concat, vel_concat, 0, false);
      to_bb[rhs] = rhsNew;
      v->split_signals(to_bb, false);
		}

		VWN_COUT_A(*ve_model_nsf << " is now ");
		ve_model_nsf = update_chs(ve_model_nsf, to_bb, true);
		VWN_COUT_A(*ve_model_nsf << endl);

		VWN_COUT_A(*ve_prop << "is now ");
		ve_prop = update_chs(ve_prop, to_bb, false);
		VWN_COUT_A(*ve_prop << endl);

		VWN_COUT_A(*ve_assume << "is now ");
		ve_assume = update_chs(ve_assume, to_bb, false);
		VWN_COUT_A(*ve_assume << endl);
		//ve_init = update_chs(ve_init, to_bb, false);	
		
	}
	
	}	//AVR_SPLIT_SIGNALS

#ifdef AVR_PARTIAL_BIT_BLAST

	/// TODO: Aman
	/// When MOVED_TO_DPA is true, the below updation of s_data and list_mux...
	/// is not performed in moved code.
	/// This may cause some issues.


	InstS s_data_temp;
	
	for(InstS::iterator sit = s_data.begin(); sit != s_data.end(); ++sit){
		Inst *tve = *sit;
		InstToInstM::iterator mit = map_net_op.find(tve);
		if(mit != map_net_op.end()){
			tve = map_net_op[tve];
			//cout << "map_net_op output : " << endl << *tve << endl;
			if((tve->get_type() == Op) && (OpInst::as(tve)->get_op() == OpInst::Concat)){
				const InstL* chs = tve->get_children();
				for(InstL::const_iterator cit = chs->begin(); cit != chs->end(); ++cit){
					Inst *tve2 = *cit;
					InstToInstM::iterator mit2 = map_net_op.find(tve2);
					if(mit2 != map_net_op.end()){
						s_data_temp.insert(map_net_op[tve2]);
					}else{
						s_data_temp.insert(tve2);
						//cout << "map_net_op does not contain : " << endl << *tve2 << endl;
					}
					
				}
			}else{
				s_data_temp.insert(tve);
				//cout << "map_net_op output : " << endl << *tve << endl;
			}
		}else{
			//cout << "map_net_op does not contain : " << endl << *tve << endl;
			assert(0);
		}
	}
	s_data = s_data_temp;

	
	list<Inst*> list_mux_sels;
	list<Inst*> list_mux_sels2;
	for(InstS::iterator sit = s_sels.begin(); sit != s_sels.end(); ++sit){
		Inst *tve = *sit;
		InstToInstM::iterator mit = map_net_op.find(tve);
		if(mit != map_net_op.end()){
			tve = map_net_op[tve];
			//cout << "map_net_op output : " << endl << *tve << endl;
			if((tve->get_type() == Op) && (OpInst::as(tve)->get_op() == OpInst::Concat)){
				const InstL* chs = tve->get_children();
				for(InstL::const_iterator cit = chs->begin(); cit != chs->end(); ++cit){
					Inst *tve2 = *cit;
					InstToInstM::iterator mit2 = map_net_op.find(tve2);
					if(mit2 != map_net_op.end()){
						list_mux_sels.push_back(map_net_op[tve2]);
					}else{
						list_mux_sels.push_back(tve2);
						//cout << "map_net_op does not contain : " << endl << *tve2 << endl;
					}
					
				}
			}else{
				list_mux_sels.push_back(tve);
				//cout << "map_net_op output : " << endl << *tve << endl;
			}
		}else{
			//cout << "map_net_op does not contain : " << endl << *tve << endl;
			assert(0);
		}
	}

// 	cout << "vwn ve_init:" << endl;
// 	new_print(cout, ve_init, true);
// 	cout << "vwn ve_model_nsf:" << endl;
// 	new_print(cout, ve_model_nsf, true);
// 	cout << "vwn ve_prop:" << endl;
// 	new_print(cout, ve_prop, true);

	
	
#ifdef BIT_LEVEL_AVR
	string str_to_concretize = "all";
#else
	//string str_to_concretize = "all";
	//string str_to_concretize = config->get_arg(AVR_TO_CONCRETIZE_ARG);
	string str_to_concretize = config->get_arg(PROP_SIG_ARG);
#endif
	if(str_to_concretize != "none"){
	// 	cout << "ve_model_nsf:" << endl;
	// 	new_print(cout, ve_model_nsf, true);	
		
		cout << "#################################################################" << endl;
		cout << "#################################################################" << endl << endl;
		
	// 	AVR_COUT(0, 0, "pdrs.ve_init:" << endl);
	// 	new_print(cout, pdrs.ve_init, true);
	// 	cout << "ve_model_nsf:" << endl;
	// 	new_print(cout, ve_model_nsf, true);
	// 	AVR_COUT(0, 0, "pdrs.ve_model:" << endl);
	// 	new_print(cout, pdrs.ve_model, true);
		
		set<string> s_reg_names;
		bool all_or_prop = false;
		if(str_to_concretize == "all"){
			collect_regs2(ve_model_nsf, s_reg_names, true);
			collect_regs2(ve_prop, s_reg_names, false);
			all_or_prop = true;
		}else if(str_to_concretize == config->get_arg(PROP_SIG_ARG)){
			collect_regs2(ve_prop, s_reg_names, true);
			all_or_prop = true;
		}
		InstL in_sigs;
		
// 		s_reg_names.clear();
// 		s_reg_names.insert("HoldSel_88646_reg/q");
// 		s_reg_names.insert("HoldSel_reg/q");

#ifdef PATCH_FOR_C17
		s_reg_names.insert("fifo_full_trig_reg/q");
		s_reg_names.insert("fifo_full_trig_88707_reg/q");
#endif

		bool bb_prop = false;
#if 1
		if(all_or_prop == true){
			if(!s_reg_names.empty()){
				bb_prop = true;
			}
			
			for(set<string>::iterator sit = s_reg_names.begin(); sit != s_reg_names.end(); ++sit){
				string reg_name = *sit;
				map<std::string, Inst*>::iterator hm_it = SigInst::hm_SigInst.find(reg_name);
				if(hm_it != SigInst::hm_SigInst.end()){
					Inst *ve_sig = hm_it->second;
					int width = ve_sig->get_size();
//					cout << "PBB reg_name: " << reg_name << ", width: " << width << endl;
	//				if((width > 1) && (width < 8)){
					//if((width <= 3) || (reg_name == "regQ_11_8_reg/q"))
					//if(width <= 8)
					if(1)
					{
						//cout << " >> bit-blasted" << endl;
						in_sigs.push_back(SigInst::create(reg_name, width));
					}else{
						bb_prop = false;
						cout << endl;
					}
				}				
			}
		}else{	//(str_to_concretize != "none")
			size_t loc_s = 0;
			size_t loc_e = 0;
			while(loc_e != string::npos){
				loc_e=str_to_concretize.find_first_of(" \t",loc_s);
				string reg_name;
				if(loc_e == string::npos){
					reg_name = str_to_concretize.substr(loc_s);
				}else{
					reg_name = str_to_concretize.substr(loc_s, loc_e-loc_s);
					loc_s = loc_e+1;
				}
				
				map<std::string, Inst*>::iterator hm_it = SigInst::hm_SigInst.find(reg_name);
				if(hm_it != SigInst::hm_SigInst.end()){
					Inst *ve_sig = hm_it->second;
					int width = ve_sig->get_size();
					cout << "reg_name: " << reg_name << ", width: " << width << endl;
					in_sigs.push_back(SigInst::create(reg_name, width));
				}
			}
		}
#endif
		
// 		map<std::string, Inst*>::iterator hm_it = SigInst::hm_SigInst.find("M1TU__P_992");
// 		if(hm_it != SigInst::hm_SigInst.end()){
// 			Inst *ve_sig = hm_it->second;
// 			int width = ve_sig->get_size();
// 			cout << "reg_name: " << *ve_sig << ", width: " << width << endl;
// 			in_sigs.push_back(ve_sig);
// 		}


		
#if 0
		/// TODO: Aman
		/// When MOVED_TO_DPA is true, the below updation of s_data and list_mux...
		/// is not performed in moved code.
		/// This may cause some issues.
		Inst::init_visit2();
		for(list<Inst*>::iterator tit = list_mux_sels2.begin(); tit != list_mux_sels2.end(); ++tit){
			Inst* tve = *tit;
			in_sigs.push_back(tve);
			collect_regs2(tve, s_reg_names, false);
		}
// 		for(set<string>::iterator sit = s_reg_names.begin(); sit != s_reg_names.end(); ++sit){
// 			string reg_name = *sit;
// 			map<std::string, Inst*>::iterator hm_it = SigInst::hm_SigInst.find(reg_name);
// 			if(hm_it != SigInst::hm_SigInst.end()){
// 				Inst *ve_sig = hm_it->second;
// 				int width = ve_sig->get_size();
// 				
// //				if((width > 1) && (width < 8)){
// 				if(width <= 8)
// 				{
// 					cout << "reg_name: " << reg_name << ", width: " << width << endl;	
// 					in_sigs.push_front(SigInst::create(reg_name, width));
// 				}
// 			}				
// 		}

// 		for(InstS::iterator sit = s_sels.begin(); sit != s_sels.end(); ++sit){
// 			Inst *tve = *sit;
// 			InstToInstM::iterator mit = map_net_op.find(tve);
// 			if(mit != map_net_op.end()){
// 				in_sigs.push_back(map_net_op[tve]);
// 	// 			cout << "map_net_op input : " << endl << *tve << endl;
// 	// 			cout << "map_net_op output : " << endl << *(map_net_op[tve]) << endl;
// 			}else{
// 				cout << "map_net_op does not contain : " << endl << *tve << endl;
// 				assert(0);
// 			}
// 		}
#endif
		cout << "bb_prop: " << bb_prop << endl;
		partial_bit_blast(in_sigs, bb_prop);
		cout << endl << "#################################################################" << endl;
		cout << "#################################################################" << endl;

	}
#endif	//AVR_PARTIAL_BIT_BLAST
}
else if (MOVED_TO_DPA)
{
#ifdef AVR_PARTIAL_BIT_BLAST

	/// When MOVED_TO_DPA is true, the below updation of s_data
	/// is performed (required for partial bit blast).

	InstS s_data_temp;
//	cout << "s_data: " << endl;
//	for (auto& s: s_data)
//	{
//		cout << *s << endl;
//	}

	for(InstS::iterator sit = s_data.begin(); sit != s_data.end(); ++sit){
		Inst *tve = *sit;
		InstToInstM::iterator mit = map_net_op.find(tve);
		if(mit != map_net_op.end()){
			tve = map_net_op[tve];
//			cout << "map_net_op output : " << endl << *tve << endl;
			if((tve->get_type() == Op) && (OpInst::as(tve)->get_op() == OpInst::Concat)){
				const InstL* chs = tve->get_children();
				for(InstL::const_iterator cit = chs->begin(); cit != chs->end(); ++cit){
					Inst *tve2 = *cit;
					InstToInstM::iterator mit2 = map_net_op.find(tve2);
					if(mit2 != map_net_op.end()){
						s_data_temp.insert(map_net_op[tve2]);
					}else{
						s_data_temp.insert(tve2);
//						cout << "map_net_op does not contain : " << endl << *tve2 << endl;
					}

				}
			}else{
				s_data_temp.insert(tve);
//				cout << "map_net_op output : " << endl << *tve << endl;
			}
		}else{
//			cout << "map_net_op does not contain : " << endl << *tve << endl;
			assert(0);
		}
	}
	s_data = s_data_temp;


	list<Inst*> list_mux_sels;
	list<Inst*> list_mux_sels2;
	for(InstS::iterator sit = s_sels.begin(); sit != s_sels.end(); ++sit){
		Inst *tve = *sit;
		InstToInstM::iterator mit = map_net_op.find(tve);
		if(mit != map_net_op.end()){
			tve = map_net_op[tve];
			//cout << "map_net_op output : " << endl << *tve << endl;
			if((tve->get_type() == Op) && (OpInst::as(tve)->get_op() == OpInst::Concat)){
				const InstL* chs = tve->get_children();
				for(InstL::const_iterator cit = chs->begin(); cit != chs->end(); ++cit){
					Inst *tve2 = *cit;
					InstToInstM::iterator mit2 = map_net_op.find(tve2);
					if(mit2 != map_net_op.end()){
						list_mux_sels.push_back(map_net_op[tve2]);
					}else{
						list_mux_sels.push_back(tve2);
						//cout << "map_net_op does not contain : " << endl << *tve2 << endl;
					}

				}
			}else{
				list_mux_sels.push_back(tve);
				//cout << "map_net_op output : " << endl << *tve << endl;
			}
		}else{
			//cout << "map_net_op does not contain : " << endl << *tve << endl;
			assert(0);
		}
	}

#endif	//AVR_PARTIAL_BIT_BLAST
}

  InstL conjunct_nsf;
  collect_nsfs(ve_model_nsf, conjunct_nsf, false);

  Inst::init_visit();
  ve_prop = add_missing_wires(ve_prop)->get_port();
  ve_assume = add_missing_wires(ve_assume)->get_port();

  InstL conjunct_nsf_new;
  for (auto& v: conjunct_nsf) {
    Inst* vNew = add_missing_wires(v)->get_port();
//    OpInst* op = OpInst::as(vNew);
//    if (op && op->get_op() == OpInst::Eq) {
//      Inst* lhs = v->get_children()->front();
//      Inst* rhs = v->get_children()->back();
////      op = OpInst::as(rhs);
////      if (op && (op->get_op() != OpInst::LogNot) && (op->get_op() != OpInst::Eq) && (op->get_op() != OpInst::NotEq))
////      if (op)
//      if (rhs->get_type() == Op || rhs->get_type() == Ex || rhs->get_type() == Wire)
//      {
//        SigInst* sig = SigInst::as(lhs);
//        assert(sig);
//        string name = sig->get_name() + "_rhs";
//        Inst* w_rhs = WireInst::create(name, sig->get_size(), rhs->get_port());
//        rhs = w_rhs;
//      }
//      vNew = OpInst::create(OpInst::Eq, lhs, rhs);
//    }
//    else
//     vNew = add_missing_wires(v)->get_port();
    conjunct_nsf_new.push_back(vNew);
  }
  conjunct_nsf.swap(conjunct_nsf_new);
  ve_model_nsf = OpInst::create(OpInst::LogAnd, conjunct_nsf);

	compile_initial(false);

	VWN_COUT_A("P: " << *ve_prop << endl);
	VWN_COUT_A("I: " << *ve_init << endl);
	VWN_COUT_A("T: " << *ve_model_nsf << endl);
	VWN_COUT_A("A: " << *ve_assume << endl);

	write_wn();
	
	_resFile << "i-#warnings:\t" << num_warnings << endl;

	_resFile.close();

	// All done.  Wasn't that easy ?
    return 0;
}

