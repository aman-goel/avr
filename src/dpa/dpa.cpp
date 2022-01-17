/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


#include "dpa.h"

// the simplification routine in Inst::create() converts the concatenation of extraction
// into identity. This conflicts with the routines in partial bit-blast functions


// AVR_NEW_CLT_MODE = new_clt_mode
// 0 : non calypto benchmarks
// 1 : calypto default	- turn on partitioning and partial bitblasting
// 2 : 154 series
// 3 : c17 series
static int new_clt_mode;

ofstream _resFile;
string _benchmark;

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

void init_flow() {
#if 1
	Inst::wn_simplify_extract_adv = true;
	Inst::wn_simplify_extract = true;
	Inst::wn_simplify_concat = true;
	Inst::wn_simplify_const_pred = true;
	Inst::wn_simplify_const_num = true;
	Inst::wn_simplify_ite = true;
	Inst::wn_simplify_repetition = true;
	Inst::wn_1bit_dp_to_control = true;
	Inst::wn_simplify_eq = true;
#else
	Inst::wn_simplify_extract_adv = false;
	Inst::wn_simplify_extract = false;
	Inst::wn_simplify_concat = false;
	Inst::wn_simplify_const_pred = false;
	Inst::wn_simplify_const_num = false;
	Inst::wn_simplify_ite = false;
	Inst::wn_simplify_repetition = false;
	Inst::wn_1bit_dp_to_control = false;
	Inst::wn_simplify_eq = false;
#endif
}

void write_wn() {
	ofstream fout;
#ifdef BUILD_STANDALONE
	string fname = "./wn.dump";
#else
	string fname = config->get_working_dir() + "/data/wn.dump";
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

	// writes types
	unsigned i = 0;
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

	fout.close();
	VWN_COUT_3("Deisgn WN is dumped to " << fname << endl);
	
// 	cout << "vwn ve_init:" << endl;
// 	new_print(cout, ve_init, true);
// 	cout << "vwn ve_model_nsf:" << endl;
// 	new_print(cout, ve_model_nsf, true);
// 	cout << "vwn ve_prop:" << endl;
// 	new_print(cout, ve_prop, true);

}

bool CompareBySz (Inst *first, Inst *second) {
	if (first->get_size() == second->get_size())
	{
		return !(first->get_id() < second->get_id());
	}
	else
		return first->get_size() < second->get_size();
}


void read_wn() {
	ifstream fin;
	string fname = config->get_working_dir() + "/data/wn_orig.dump";
    fin.open(fname.c_str());
	if(!fin.good()){
		cout<<"Could not access file: "<<fname<<endl;
		return;
	}
	
	Trans::st_in = &fin;

	int ver = Trans::read_int();
	if (ver != static_cast<int> (WN_VERSION * 10)) {
		cerr << "Warning: incompatible WN-reading version " << static_cast<int> (WN_VERSION * 10) / 10.0 << "x and WN-file version " << ver / 10.0 << "x" << endl;
	}

	Trans::m_module_name = Trans::read_str();
	Trans::st_id_to_ptr.clear();

	int nodes_num = Trans::read_int();
	// read types & construct nodes
	for (int i = 0; i < nodes_num; i++) {
		Inst* e = 0;
		InstType type = static_cast<InstType> (Trans::read_int());
		switch (type) {
		case Sig:
			e = SigInst::read_bin();
			break;
		case Num:
			e = NumInst::read_bin();
			break;
		case Wire:
			e = WireInst::read_bin();
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
		Trans::st_id_to_ptr.push_back(e);
//		cout << type << " e: " << *e << endl;
	}

	ve_init = Trans::id_to_ptr(Trans::read_int());
	ve_model_nsf = Trans::id_to_ptr(Trans::read_int());
	ve_prop = Trans::id_to_ptr(Trans::read_int());
	ve_assume = Trans::id_to_ptr(Trans::read_int());

	if (MOVED_TO_DPA)
	{
		int nodes_num = Trans::read_int();
		for (int i = 0; i < nodes_num; i++)
			s_data.insert(Trans::id_to_ptr(Trans::read_int()));

		nodes_num = Trans::read_int();
		for (int i = 0; i < nodes_num; i++)
		{
			Inst* lhs = Trans::id_to_ptr(Trans::read_int());
//			cout << "Reading map_init - lhs is " << *lhs << endl;
			Inst* rhs = Trans::id_to_ptr(Trans::read_int());
//			cout << "Reading map_init - rhs is " << *rhs << endl;
			map_init[lhs] = rhs;
		}
		cout << "s_data: " << endl;
		for (auto& s: s_data)
		{
			cout << *s << endl;
		}
	}

	fin.close();
	AVR_LOG(0, 1, "Deisgn WN is loaded from " << fname << endl);

#if 0	//read_wn()
 	AVR_COUT(0, 0, "_ve_init:" << endl);
 	new_print(cout, _ve_init, true);
	AVR_COUT(0, 0, "_ve_model_nsf:" << endl);
	new_print(cout, _ve_model_nsf, true);
 	AVR_COUT(0, 0, "_ve_model:" << endl);
 	new_print(cout, _ve_model, true);
 	AVR_COUT(0, 0, "_ve_model:" << endl << *_ve_model << endl);
	//assert(0);
//  	AVR_COUT(0, 0, "_ve_model:" << endl << *_ve_model << endl);
//  	AVR_COUT(0, 0, "_ve_model_nsf:" << endl << *_ve_model_nsf << endl);
#else
// 	AVR_COUT(0, 0, "_ve_init:" << endl << *_ve_init << endl);
// 	AVR_COUT(0, 0, "_ve_model_nsf:" << endl << *_ve_model_nsf << endl);
// 	AVR_COUT(0, 0, "_ve_model:" << endl << *_ve_model << endl);
#endif

	
// 	node_count(_ve_model, true);
// 	cout << "ve_model" << endl;
// 	cout << "int : " << _int_node_cnt << endl;
// 	cout << "bool : " << _bool_node_cnt << endl;
// 	cout << "sum : " << _node_cnt << endl;
// 
// 	node_count(_ve_model_nsf, true);
// 	cout << "ve_model_nsf" << endl;
// 	cout << "int : " << _int_node_cnt << endl;
// 	cout << "bool : " << _bool_node_cnt << endl;
// 	cout << "sum : " << _node_cnt << endl;
// 
// 	Inst *anded_models = OpInst::create(OpInst::LogAnd, _ve_model, _ve_model_nsf);
// 	node_count(anded_models, true);
// 	cout << "anded_models" << endl;
// 	cout << "int : " << _int_node_cnt << endl;
// 	cout << "bool : " << _bool_node_cnt << endl;
// 	cout << "sum : " << _node_cnt << endl;
// 	
//	assert(0);
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
//	cout << "ve_top: " << *ve_top << endl;
	if (init_visit) {
		Inst::init_visit2();
	}
	if (ve_top->get_visit2()){
//		cout << "1 Returned: " << *ve_top->acex_coi << endl;
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
//		cout << "2 Returned: " << *ve_res << endl;
		return ve_res;
	}else{
		InstToInstM::iterator mit = bb_map.find(ve_top);
		if(mit != bb_map.end()){
			Inst *ve_res=NULL;
			ve_res = mit->second;
			ve_top->acex_coi = ve_res;
//			cout << "3 Returned: " << *ve_res << endl;
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
//			cout << "4 Returned: " << *ve_res << endl;
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
//					cout << "5 Returned: " << *ve_res << endl;
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
//					cout << "6 Returned: " << *ve_res << endl;
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
//				cout << "7 Returned: " << *ve_res << endl;
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
//			cout << "8 Returned: " << *ve_res << endl;
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
//		cout << "9 Returned: " << *ve_res << endl;
		return ve_res;
	}
//	cout << "10 Returned: " << *ve_top << endl;
	return ve_top;
}

Inst *remove_unnecessary_concat(Inst *ve_top, InstToInstM& bb_map, bool init_visit = false) {
//	cout << "ve_top: " << *ve_top << endl;
	if (init_visit) {
		Inst::init_visit2();
	}
	if (ve_top->get_visit2()){
		cout << "1 Returned: " << *ve_top->acex_coi << endl;
		return ve_top->acex_coi;
	}
	ve_top->set_visit2();
	ve_top->acex_coi = ve_top;	//TODO temporary use of acex_coi


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
	}
	else{
		assert(0);
	}

	if((ve_top->get_type() == Op) && (OpInst::as(ve_top)->get_op() == OpInst::Concat))
	{
		InstToInstM::iterator mit = bb_map.find(ve_top);
		Inst *ve_res=NULL;
		if(mit != bb_map.end()){
			ve_res = mit->second;
		}else{
			ve_res = ve_top;
		}
		ve_top->acex_coi = ve_res;
//		cout << "2 Returned: " << *ve_res << endl;
		return ve_res;
	}

	if(need_new)
	{
		Inst *ve_res = ve_top->apply_children(new_ch);
		bb_map[ve_top] = ve_res;
		ve_top->acex_coi = ve_res;
//		cout << "3 Returned: " << *ve_res << endl;
		return ve_res;
	}
//	cout << "4 Returned: " << *ve_top << endl;
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
		return ve_res;
	}else{
		InstToInstM::iterator mit = bb_map.find(ve_top);
		if(mit != bb_map.end()){
			Inst *ve_res;
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
			return ve_res;
		}else{
			if((ve_ch0->get_type() == Op) && (OpInst::as(ve_ch0)->get_op() == OpInst::Concat)){
// 				if(ve_ch0->get_children()->size() == 3){
// 					cout << "ve_ch0: "	 << *ve_ch0 << endl;
// 				}
				
				if( ((ve_ch1->get_type() == Op) && (OpInst::as(ve_ch1)->get_op() == OpInst::Concat)) &&
					((ve_ch0->get_children())->size() == (ve_ch1->get_children())->size()) ){
					InstL::const_iterator cit_0 = (ve_ch0)->get_children()->begin();
					InstL::const_iterator cit_1 = (ve_ch1)->get_children()->begin();
					Inst *ve_res;
					int i = 0;
					for (; cit_0 != (ve_ch0)->get_children()->end(); ++cit_0, ++cit_1) {
						Inst *ve_bit = OpInst::create(OpInst::Eq, *cit_0, *cit_1);
	// 					if(!ve_bit){
	// 						cout << "ve_ch0: " << *ve_ch0 << ", size: " << ve_ch0->get_size() << endl;
	// 						cout << "ve_ch1: " << *ve_ch1 << ", size: " << ve_ch1->get_size() << endl;	
	// 					}
						if(i != 0){
							ve_res = OpInst::create(OpInst::LogAnd, ve_res, ve_bit);
						}else{
							ve_res = ve_bit;
						}
						i++;
					}
					//cout << "table, ve_res2: " << *ve_res << ", ve_ch0->get_size():" << op_size << endl;
					ve_top->acex_coi = ve_res;
					return ve_res;
				}else if((ve_ch0->m_pbb.size() - 1) == ve_ch0->get_children()->size()){
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
		ve_top->acex_coi = ve_res;
		
		bb_map[ve_top] = ve_res;
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

void count_pars(Inst *top, bool init_visit) {
	top->inc_count();
//	cout << "top: n" << top->get_id() << "n	" << top->get_count() << endl;
//	cout << "top: " << *top << "  " << top->get_count() << endl;
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
		if((top->get_type() == Op) && ((OpInst::as(top))->get_op() == OpInst::Mult)){
			return 1000; // meaning that we should not bit-blast
		}
		
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

void derive_pbbs(Inst *top, set<int>& pbb) {
// 	if(top->get_size() == 1){
// 		return;
// 	}

	
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
					Inst *ch = *it;
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
								++pbb_it;
								//t_pbb.insert(*pbb_it-accum_width_pre);
								break;
							}else{
								t_pbb.insert(*pbb_it-accum_width_pre);
							}
						}
					}else{
						for(; pbb_it != (top->m_pbb).end(); ++pbb_it){
							int idx = *pbb_it;
							if(accum_width <= idx){
								//t_pbb.insert(accum_width-accum_width_pre);
								break;
							}
						}
					}
					
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
				derive_pbbs(*it, t_pbb);	// pass empty set to the control signal
				t_pbb = (top->m_pbb);
				++it;
				for (; it != chs->end(); ++it) {
					derive_pbbs(*it, t_pbb);
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
// 				else{
// 					t_pbb = (top->m_pbb);
// 				}
				
				set<int> empty_pbb;
				const InstL* chs = top->get_children();
				if(chs){
					InstL::const_iterator it = chs->begin();
					for (InstL::const_iterator end_it = chs->end(); it != end_it; ++it) {
						Inst *ch = *it;
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
	}
//	DPA_COUT_A("m_pbb for " << *top << " is ");
//	for (set<int>::iterator pbbIt = top->m_pbb.begin(); pbbIt != top->m_pbb.end(); pbbIt++)
//	{
//		DPA_COUT_A(*pbbIt << "  ");
//	}
//	DPA_COUT_A(endl);
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
					{
//						cout << "partial_bit_blast, ve_sig: " << *ve_sig << ", width:" << width << ", max_width: " << max_width_ve_in;
					}
						
#ifdef PATCH_FOR_BIT_LEVEL_AVR
						if(1)
#else
	#ifdef PATCH_FOR_154
						if((max_width_ve_in < 33) && (str.substr(0,30) != "r2y_beu_ln386_d_out_out_0_0_24"))	// <= latest one
	#else
		#ifdef PATCH_FOR_C17
						if(0)
						//if((str.substr(7,9) == "rdata_reg") || (str.substr(0,15) == "rdata_88690_reg"))
						//if((max_width_ve_in < 8) || ((width < 8) && contain_big_mux(ve_in, true)))
						//if(1)
		#else
						//if((max_width_ve_in < 8) || ((width < 25) && contain_big_mux(ve_in, true)))
						//if((max_width_ve_in < 35) || ((width < 27) && contain_big_mux(ve_in, true)))
						//if((max_width_ve_in < 35) && (width < 27))
						//if((max_width_ve_in < 35) && (width < 12))
						//if((max_width_ve_in < 35) || ((width < 12) && contain_big_mux(ve_in, true)))
						//if((max_width_ve_in < 24) || ((width < 12) && contain_big_mux(ve_in, true)))
						if((max_width_ve_in < 32) || ((width < 12) && contain_big_mux(ve_in, true)))	//<= currently using 0204 2015
						//if(1)
		#endif
	#endif
#endif
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
//								cout << "ve_res: " << *ve_res << endl;

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
//								cout << "ve_res: " << *ve_res << endl;
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
		
#ifndef BIT_LEVEL_AVR
#ifdef REMOVE_UNNECESSARY_CONCAT
		cout << "Pre-blasted: " << endl;
		InstS blastedSigs;
		for (InstToInstM::iterator it_to_bb = to_bb.begin(); it_to_bb != to_bb.end(); it_to_bb++)
		{
			blastedSigs.insert((*it_to_bb).first);
			cout << "\t" << *((*it_to_bb).first) << " -> " << *((*it_to_bb).second) << endl;
		}
#endif
#endif

		for(InstL::iterator eit = to_examine.begin(); eit != to_examine.end(); ++eit){
			//cout << "(*eit)" << *(*eit) << endl;
			(*eit)->bit_blast(to_bb, false);
		}
		
		int max_width_prop = max_width(ve_prop, true, 0);
		cout << "partial_bit_blast, ve_sig: prop, max_width: " << max_width_prop;
#ifdef PATCH_FOR_BIT_LEVEL_AVR
		if(1)
#else
	#ifdef PATCH_FOR_154
		if(1)
	#else
		#ifdef PATCH_FOR_C17
		//if(1)
		if(0)
		#else
		//new_print(cout, ve_prop, true);
		//if(bb_prop){
//		if(bb_prop2 && (max_width_prop < 8))
		//if(max_width_prop <= 8)	//<= currently using 0204 2015
		if(max_width_prop < 32)
//		if(max_width_prop < 7)
		#endif
	#endif
#endif
		{
			ve_prop->bit_blast(to_bb, false);
//			cout << " << bit_blasted" << endl;
		}else{
//			cout << endl;
		}
		
// 		idx = 0;
// 		for(InstToInstM::iterator mit = to_bb.begin(); mit != to_bb.end(); ++mit){
// 			cout << "to_bb: " << idx++ << endl;
// 			cout << *(mit->first) << endl;
// 			cout << *(mit->second) << endl;
// 		}
		//M1TU__P_1051$0
		
#ifndef BIT_LEVEL_AVR
#ifdef REMOVE_UNNECESSARY_CONCAT
		InstToInstM to_bb_reverse;
		for (InstToInstM::iterator it_to_bb = to_bb.begin(); it_to_bb != to_bb.end(); it_to_bb++)
		{
			Inst* lhs = (*it_to_bb).first;
			Inst* rhs = (*it_to_bb).second;
			if((lhs->get_type() == Num) || (lhs->get_type() == Sig))
			{
				if (blastedSigs.find(lhs) == blastedSigs.end())
					to_bb_reverse[rhs] = lhs;
			}
		}
#endif
#endif

//		DPA_COUT_A("\nPrinting Map to_bb" << endl);
//		for (InstToInstM::iterator it_to_bb = to_bb.begin(); it_to_bb != to_bb.end(); it_to_bb++)
//			DPA_COUT_A("\tmap[" << *((*it_to_bb).first) << "] = [" << *((*it_to_bb).second) << "]" << endl);
//		DPA_COUT_A(endl);

//		DPA_COUT_A("\nPrinting Map to_bb_reverse" << endl);
//		for (InstToInstM::iterator it_to_bb = to_bb_reverse.begin(); it_to_bb != to_bb_reverse.end(); it_to_bb++)
//			DPA_COUT_A("\tmap[" << *((*it_to_bb).first) << "] = [" << *((*it_to_bb).second) << "]" << endl);
//		DPA_COUT_A(endl);

		//cout << "NOW UPDATE CHS" << endl;
		ve_model_nsf = update_chs_pbb(ve_model_nsf, to_bb, true);
		ve_prop = update_chs_pbb(ve_prop, to_bb, false);
		ve_assume = update_chs_pbb(ve_assume, to_bb, false);
		//ve_init = update_chs_pbb(ve_init, to_bb, false);

#ifndef BIT_LEVEL_AVR
#ifdef REMOVE_UNNECESSARY_CONCAT
		ve_model_nsf = remove_unnecessary_concat(ve_model_nsf, to_bb_reverse, true);
#endif
#endif

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

void collect_sig(Inst *top, InstS& s, bool init_visit)
{
	if (init_visit) {
		Inst::init_visit();
	}
	if (top->get_visit()) {
		return;
	}
	top->set_visit();

//	cout << "top: " << *top << endl;

	OpInst* op = OpInst::as(top);
	if (op)
	{
		const InstL* ch = top->get_children();
		if (ch)
		{
			for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it)
			{
				Inst * tve = *it;
				collect_sig(tve, s, false);
			}
		}
	}
	else
	{
		SigInst* sig = SigInst::as(top);
		if (sig)
		{
			s.insert(sig);
		}
	}
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
				collect_nsfs(tve, vel_nsfs);
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


// returns term_type;
// 		0: term of constants (i.e. no states and no inputs)
// 		1: includes only states and constants (no inputs)
// 		2: includes only inputs and constants (no states)
//		3: includes both states and inputs
// Note that top->term_type is Inst::not_yet_computed if the term_type of top has not been computed
int check_term_type(Inst *top) {
	if(top->term_type != Inst::not_yet_computed){
		return top->term_type;
	}

	int top_term_type = 0;
	if (top->get_type() == Sig) {
		if((_m_sn.find(top) == _m_sn.end()) && (_s_reg.find(top) == _s_reg.end())){	// inputs
			top_term_type = 2;
		}else{	// registers
			top_term_type = 1;
		}
	} else {
		const InstL* ch = top->get_children();
		if (ch) {
			for (InstL::const_iterator it = ch->begin(); it != ch->end(); ++it) {
				int ch_term_type = check_term_type(*it);
				top_term_type = top_term_type | ch_term_type;
			}
		}else{ // constants
			top_term_type = 0;
		}
	}
	top->term_type = top_term_type;
	return top->term_type;
}

//bool derive_euf_func_list_2(Inst *top, bool init_visit) {
//	if (init_visit) {
//		Inst::init_visit();
//	}
//	if (top->get_visit()) {
//		// if already visited, the return value of the initial call of derive_euf_func_list_debug
//		// does not depend on this return value.
//		return 0;
//	}
//	bool ret = false;
//	top->set_visit();
//
//	OpInst *op_inst = OpInst::as(top);
//	if(op_inst){
//		string euf_func_name;
//		ExInst *ex_inst = ExInst::as(top);
//		if(ex_inst){
//			euf_func_name = ex_inst->get_euf_func_name();
//		}else{
//			euf_func_name = op_inst->get_euf_func_name();
//		}
//		if(euf_func_name != "0"){
//			int tt = check_term_type(top);
//			if((tt & 2) != 2)
//			{	// if top is not an input
//			//if((top->is_invalid_state_term == 0) || (top->is_invalid_state_term == Inst::not_yet_computed)){
//				// top->is_invalid_state_term == Inst::not_yet_computed if derive_euf_func_list_debug() was called
//				// at the beginning to fill "_func_list"
//				bool matched = false;
//				for(InstL::iterator lit = _func_list[euf_func_name].begin(); lit != _func_list[euf_func_name].end(); ++lit){
//					if(top == *lit){
//						matched = true;
//						break;
//					}
//				}
//				if(matched == false){
//					op_inst->set_term_type(tt);
//					_func_list[euf_func_name].push_back(top);
//					//cout << "_func_list added: " << *top << endl;
//					ret = true;
//				}
//			}
//		}
//	}
//
//	const InstL* tch = top->get_children();
//	if (tch) {
//		for (InstL::const_iterator tit = tch->begin(); tit != tch->end(); ++tit) {
//			bool t_ret = derive_euf_func_list_2(*tit, false);
//			ret = ret | t_ret;
//		}
//	}
//	return ret;
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
			DPA_COUT_FILE("(type: " << setw(8) << left << type << ")\t");
			DPA_COUT_FILE(setw(8) << left << lhsName << " = " << rhsName << endl);
		}
	}
	return;
}

bool collect_inputs(Inst *top, InstS& regs, bool init_visit) {
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
				if (regs.find(top) == regs.end())
				{
					inputs.insert(top);
				}
			}
		}
	}
		break;
	case Num:
		constants.insert(top);
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

void collect_func_stat(Inst* top, int& numConst, int& numCF, int& numUF, int& numMux, int& numCc, int& numEx, map< string, int >& ufType, map< string, int >& ccType, map< string, int >& exType, bool init_visit = false)
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
	}

	const InstL* tch = top->get_children();
	if (tch) {
		for (InstL::const_iterator tit = tch->begin(); tit != tch->end(); ++tit) {
			collect_func_stat(*tit, numConst, numCF, numUF, numMux, numCc, numEx, ufType, ccType, exType);
		}
	}
}

int main(int argc, char **argv){
	cout << "Running dpa" << endl;

#ifdef BUILD_STANDALONE
    if (argc < 2) Message::PrintLine("reading default input file: paper_v3.v. Specify command line argument to override");

    const char *file_name = 0;
    if (argc>1) {
        file_name = argv[1]; // Set the file name as specified by the user
    } else {
        file_name = "./paper_v3.v"; // Set default file name
        // The default top-level design we're going to read in has some `include
        // directives, so we need to set the include path now.
//        veri_reader.AddIncludeDir("../../../example_designs/verilog");
        veri_reader.AddIncludeDir("./");
    }
#else
	argc-- , argv++;
	if(argc!=2){
	cerr<<"Syntax: dpa "<<"<word_dir> <bin_dir>"<<endl;
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

#endif

    string tmp = remove_path_from_fname(argv[0]);
	_benchmark = tmp.substr(tmp.find("work_") + 5);
	string fname_reach = config->get_working_dir() + "/" + _benchmark + ".results";
//	_resFile.open(fname_reach.c_str());
	_resFile.open(fname_reach.c_str(), std::ofstream::app);

	//  yices_set_verbosity(100);
	init_flow();

	read_wn();

	InstL conjunct_init;
	collect_nsfs(ve_init, conjunct_init, true);


//	DPA_COUT_A("Init: " << *ve_init << endl);
//	DPA_COUT_A("Prop: " << *ve_prop << endl);
//	DPA_COUT_A("NSF: " << *ve_model_nsf << endl);
//
//	DPA_COUT_A("\nPrinting hm_SigInst" << endl);
//	for(map<std::string, Inst*>::iterator it = SigInst::hm_SigInst.begin(); it != SigInst::hm_SigInst.end(); ++it)
//	{
//		string lhs = it->first;
//		Inst *ve_rhs = it->second;
//		DPA_COUT_A("\t" << lhs << " = " << *ve_rhs << endl);
//	}
//	DPA_COUT_A(endl);

	/// CCD and PDC

//	DPA_COUT_A("new_clt_mode = " << new_clt_mode << endl);
//
//	DPA_COUT_A("Printing s_data in DPA" << endl);
//	for(InstS::iterator sit = s_data.begin(); sit != s_data.end(); ++sit)
//		DPA_COUT_A(**sit << endl);

//	DPA_COUT_A("\nPrinting map_init" << endl);
//	for(InstToInstM::iterator init_it = map_init.begin(); init_it != map_init.end(); ++init_it)
//	{
//		Inst *ve_lhs = init_it->first;
//		Inst *ve_rhs = init_it->second;
//		DPA_COUT_A("\t" << *ve_lhs << " = " << *ve_rhs << endl);
//	}
//	DPA_COUT_A(endl);

if(new_clt_mode > 0 && MOVED_TO_DPA)
{

#ifdef AVR_SPLIT_SIGNALS
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

#if 0
	collect_regs2(ve_prop, s_reg_names, true);
	count_pars(ve_prop, true);
	set<int> temp;
	derive_pbbs(ve_prop, temp);

#else
#ifdef PROPERTY_DIRECTED_SPLIT
	collect_regs2(ve_prop, s_reg_names, true);
#else
	collect_regs2(ve_model_nsf, s_reg_names, true);
#endif

//	cout << "NSF: " << *ve_model_nsf << endl;

//	DPA_COUT_A("\nPrinting reg_names" << endl);
//	for(set<string>::iterator it = s_reg_names.begin(); it != s_reg_names.end(); ++it)
//	{
//		DPA_COUT_A("\t" << *it << endl);
//	}
//	DPA_COUT_A(endl);

#endif
	
	InstL in_sigs;

	
// reg_name: intp2clc_in_alpha_49638_reg/q, width: 8
// reg_name: intp2clc_in_alpha_reg/q, width: 8
// reg_name: intp2clc_in_data_49637_reg/q, width: 24
// reg_name: intp2clc_in_data_reg/q, width: 24

	for(set<string>::iterator sit = s_reg_names.begin(); sit != s_reg_names.end(); ++sit){
		string reg_name = *sit;
		map<std::string, Inst*>::iterator hm_it = SigInst::hm_SigInst.find(reg_name);
		if(hm_it != SigInst::hm_SigInst.end()){
			Inst *ve_sig = hm_it->second;
			int width = ve_sig->get_size();

			//if((width != 8) && (width != 24))
//			if((reg_name != "intp2clc_in_alpha_49638_reg/q") && (reg_name != "intp2clc_in_alpha_reg/q") && (reg_name != "intp2clc_in_data_49637_reg/q") && (reg_name != "intp2clc_in_data_reg/q"))
//			if((reg_name != "intp2clc_in_data_49637_reg/q") && (reg_name != "intp2clc_in_data_reg/q"))
			//if(reg_name != "intp2clc_in_alpha_reg/q")
			
			//if((width == 8) || (width == 24))	
			//if((width != 8) && (width != 24))	
			//if(width <= 8)	//	258.44
			if(width < 7)		//	250.10
			{
				for(int i = 0; i <= width; ++i){
					ve_sig->m_pbb.insert(i);
				}
			}
			
//			DPA_COUT_A("reg_name: " << reg_name << ", width: " << width << endl);
			in_sigs.push_back(SigInst::create(reg_name, width));
//			DPA_COUT_A(*in_sigs.back() << endl);
		}				
	}

//	DPA_COUT_A("\nPrinting in_sigs" << endl);
//	for(InstL::iterator it = in_sigs.begin(); it != in_sigs.end(); ++it)
//	{
//		DPA_COUT_A("\t" << **it << endl);
//	}
//	DPA_COUT_A(endl);

	/// Sets the count of times a sub-expression appears in an expression
	count_pars(ve_model_nsf, true);

	set<int> temp;
	/// Derives m_pbb for each node in given graph
	derive_pbbs(ve_model_nsf, temp);

//	cout << "##################################" << endl;
//	cout << "count_pars(ve_prop, true) begins" << endl;
	count_pars(ve_prop, true);
	derive_pbbs(ve_prop, temp);
	
	{
		int idx = 0;
		collect_parents(ve_model_nsf, true);
		collect_parents(ve_prop, false);
		
// {
// 
// 	string sname = "fld_bottom_mode_88800_reg/q";
// 	
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
// 			debug_top = *(m_pars[ve_sig].begin());
// 		}else{
// 			assert(0);
// 		}
// 		cout << "debug_top:" << endl;
// 		new_print(cout, debug_top, true);
// 
// 		cout << "debug_top:" << *debug_top << endl;
// 		assert(0);
// 	}
// 	
// }
		//collect_parents(ve_init, false);

// 		for(list<Inst*>::iterator tit = list_mux_sels.begin(); tit != list_mux_sels.end(); ++tit){
// 			Inst *tve = *tit;
// 			
// 			if(m_pars.find(tve) == m_pars.end()){
// 				cout << "##	Unable to find a mux." << endl;
// 				//cout << "muxes, m_pars[] of" << *tve << endl;
// 				//assert(0);
// 			}else{
// 				cout << "##	mux found." << endl;
// 				//cout << "mux found: " << *(*(m_pars[tve].begin())) << endl;
// 			}
// 		}

		InstToInstM to_bb;
		Inst::init_visit();
		InstL to_examine;
		for(InstL::iterator ir_it = in_sigs.begin(); ir_it != in_sigs.end(); ++ir_it){
			SigInst *ve_reg = SigInst::as(*ir_it);
//			DPA_COUT_A("in_sigs: " << *(*ir_it) << ", width: " << (*ir_it)->get_size() << endl);
			
			bool is_reg = false;
			if(ve_reg){
				string str = ve_reg->get_name();
// 				if(str.substr(0, 14) == "mux_dither_err"){
// 					continue;
// 				}
				
				int width = ve_reg->get_size();
				Inst *ve_sig = SigInst::create(str+"$next", width);
				if(m_pars.find(ve_sig) != m_pars.end()){
					is_reg = true;
					Inst *ve_in = *(m_pars[ve_sig].begin());

					if(width > 1){
						DPA_COUT_A("partial_bit_blast, ve_in: " << *ve_in << endl);
						
						InstL vel_concat;
						set<int>& pbb = (SigInst::create(str, width))->m_pbb;
						
//						for (set<int>::iterator it = pbb.begin(); it != pbb.end(); it++)
//							cout << (*it) << endl;

//						if (pbb.size() == 2)
//						{
//							set<int>::iterator it = pbb.begin();
//							int n1 = *(it);
//							it++;
//							int n2 = (*it);
//							if (n1 == 0 && n2 == ve_reg->get_size())
//							{
//								DPA_COUT_A("No need for spliting " << *ve_reg << endl);
//								continue;
//							}
//						}

// 						if(pbb.size() < 2){//TODO remove this
// 							pbb.insert(0);
// 							pbb.insert(width);
// 						}
						{
							ve_sig->m_pbb = pbb;
							ve_in->get_children()->back()->m_pbb = pbb;
							
							ve_in->get_children()->back()->m_pbb.erase(ve_in->get_children()->back()->m_pbb.begin());
							ve_in->get_children()->back()->m_pbb.erase(--ve_in->get_children()->back()->m_pbb.end());


// 							if(pbb.size() == (width+1))
// 							{
// 								pbb.clear();
// 	//  							pbb.insert(0);
// 	//  							pbb.insert(width);
// 								cout << "name: " << str << endl;
// 								cout << "(SigInst::create(str, width))->m_pbb: " << (SigInst::create(str, width))->m_pbb.size() << ", width: " << width << endl;
// 								continue;
// 							}

							
//							cout << "ve_in->get_children()->back(): " << *(ve_in->get_children()->back()) << endl;
//							cout << "ve_in->get_children()->front(): " << *(ve_in->get_children()->front()) << endl;

							count_pars(ve_in, true);
							set<int> temp;
							derive_pbbs(ve_in, temp);
							to_examine.push_back(ve_in);

							assert((*(pbb.begin()) == 0) && (*(--pbb.end()) == width));
							set<int>::iterator sit = pbb.begin();
							++sit;
							int idx_begin = 0;
							int idx_end = 0;
							for(; sit != pbb.end(); ++sit){
								idx_end = *sit - 1;
								ostringstream oss;
								oss << str << "$" << idx_end << "_" << idx_begin << "$next";
								
								Inst *ve_bit = SigInst::create(oss.str(), (idx_end - idx_begin + 1));
								vel_concat.push_back(ve_bit);
								idx_begin = idx_end+1;
							}
							Inst *ve_res = OpInst::create(OpInst::Concat, vel_concat);
							ve_sig->set_visit();
							to_bb[ve_sig] = ve_res;
							DPA_COUT_A("to_bb[" << *ve_sig << "]" << " = " << *ve_res << endl);

							vel_concat.clear();
							ve_sig = SigInst::create(str, width);
							set<int>& pbb2 = ve_sig->m_pbb;

//							DPA_COUT_A("m_pbb for " << *ve_sig << " is ");
//							for (set<int>::iterator pbbIt = pbb2.begin(); pbbIt != pbb2.end(); pbbIt++)
//							{
//								DPA_COUT_A(*pbbIt << "  ");
//							}
//							DPA_COUT_A(endl);

							if(pbb2.size() >= 2){
								assert((*(pbb2.begin()) == 0) && (*(--pbb2.end()) == width));
								set<int>::iterator sit = pbb2.begin();
								++sit;
								int idx_begin = 0;
								int idx_end = 0;
								
								Inst* ve_num = NULL;
								if(map_init.find(ve_sig) != map_init.end()){
									ve_num = map_init[ve_sig];
									map_init.erase(ve_sig);
								}
								for(; sit != pbb2.end(); ++sit){
									idx_end = *sit - 1;
									ostringstream oss;
									oss << str << "$" << idx_end << "_" << idx_begin;
									
									Inst *ve_bit = SigInst::create(oss.str(), (idx_end - idx_begin + 1));
									vel_concat.push_back(ve_bit);
									
									if(ve_num != NULL){
										Inst* ve_num_bit = ExInst::create(ve_num, idx_end, idx_begin);
										map_init[ve_bit] = ve_num_bit;
									}
									idx_begin = idx_end+1;
								}							
								ve_res = OpInst::create(OpInst::Concat, vel_concat);
								ve_sig->set_visit();
								to_bb[ve_sig] = ve_res;
  								DPA_COUT_A("to_bb[" << *ve_sig << "]" << " = " << *ve_res << endl);
							}
						}
					}
				}
			}
			
// 			if(is_reg == false){
// 				if(m_pars.find(*ir_it) == m_pars.end()){
// 					cout << "Unable to find a mux." << endl;
// 					//cout << "muxes, m_pars[] of" << *(*ir_it) << endl;
// 					//assert(0);
// 				}else{
// 					Inst *ve_in = *(m_pars[*ir_it].begin());
// 					to_examine.push_back(ve_in);
// 					cout << "added a mux to concretized." << endl;
// 					//cout << "muxes, sel: " << *(*ir_it) << endl;
// 					//cout << "muxes:" << endl << *ve_in << endl << endl;
// 				}
// 			}
		}
// draw_graph("post", "rpf_dout_alpha_49645_reg/q", 0, to_bb);
// draw_graph("post", "rpf_dout_alpha_reg/q", 0, to_bb);

// 	draw_graph("pre", "HoldSel_88646_reg/q", 0, to_bb);
// 	draw_graph("pre", "HoldSel_reg/q", 0, to_bb);
// 		draw_graph("pre", config->get_arg(PROP_SIG_ARG), 0, to_bb);

 		//draw_graph("pre", "r2y_beu_ln386_d_out_out_0_0_24_0_reg/q", 15, to_bb);
// 		draw_graph("pre", config->get_arg(PROP_SIG_ARG), 0, to_bb);

// 		ostringstream ostr;
// 		ostr << config->get_working_dir() << "/before_graph_intp2clc_in_data_49637_reg_0";
// 		draw_graph(ostr.str(), "intp2clc_in_data_49637_reg/q", 0);
		
//		DPA_COUT_A("\nPrinting Map to_bb" << endl);
//		for (InstToInstM::iterator it_to_bb = to_bb.begin(); it_to_bb != to_bb.end(); it_to_bb++)
//			DPA_COUT_A("\tmap[" << *((*it_to_bb).first) << "] = [" << *((*it_to_bb).second) << "]" << endl);
//		DPA_COUT_A(endl);

		//#############################################################################################

//		cout << "\nPrinting Map to_bb" << endl;
//		for (InstToInstM::iterator it_to_bb = to_bb.begin(); it_to_bb != to_bb.end(); it_to_bb++)
//			cout << "\tmap[" << *((*it_to_bb).first) << "] = [" << *((*it_to_bb).second) << "]" << endl;
//		cout << endl;

//		cout << "prop split_signals() begins." << endl;
//		cout << *ve_prop << endl;
		ve_prop->split_signals(to_bb, false);
//		cout << *ve_prop << endl;
//		cout << "prop split_signals() is done." << endl;

//		cout << "\nPrinting Map to_bb" << endl;
//		for (InstToInstM::iterator it_to_bb = to_bb.begin(); it_to_bb != to_bb.end(); it_to_bb++)
//			cout << "\tmap[" << *((*it_to_bb).first) << "] = [" << *((*it_to_bb).second) << "]" << endl;
//		cout << endl;

		for(InstL::iterator eit = to_examine.begin(); eit != to_examine.end(); ++eit){
			cout << "split_signals() begins: " << **eit << endl;
			(*eit)->split_signals(to_bb, false);
			cout << "split_signals() is done: " << **eit << endl;
		}
		//#############################################################################################
			
// 		idx = 0;
// 		for(InstToInstM::iterator mit = to_bb.begin(); mit != to_bb.end(); ++mit){
// 			cout << "to_bb: " << idx++ << endl;
// 			cout << *(mit->first) << endl;
// 			cout << *(mit->second) << endl;
// 		}
		//M1TU__P_1051$0
		
		//cout << "NOW UPDATE CHS" << endl;

//		cout << "\nPrinting Map to_bb" << endl;
//		for (InstToInstM::iterator it_to_bb = to_bb.begin(); it_to_bb != to_bb.end(); it_to_bb++)
//			cout << "\tmap[" << *((*it_to_bb).first) << "] = [" << *((*it_to_bb).second) << "]" << endl;
//		cout << endl;

//		DPA_COUT_A("\nPrinting Map to_bb" << endl);
//		for (InstToInstM::iterator it_to_bb = to_bb.begin(); it_to_bb != to_bb.end(); it_to_bb++)
//			DPA_COUT_A("\tmap[" << *((*it_to_bb).first) << "] = [" << *((*it_to_bb).second) << "]" << endl);
//		DPA_COUT_A(endl);

		DPA_COUT_A(*ve_model_nsf << " is now " << endl);
		ve_model_nsf = update_chs(ve_model_nsf, to_bb, true);
		DPA_COUT_A(*ve_model_nsf << endl);

		DPA_COUT_A(*ve_prop << "is now " << endl);
		ve_prop = update_chs(ve_prop, to_bb, false);
		DPA_COUT_A(*ve_prop << endl);

		//ve_init = update_chs(ve_init, to_bb, false);	

// 		for(list<Inst*>::iterator tit = list_mux_sels.begin(); tit != list_mux_sels.end(); ++tit){
// 			Inst *tve = *tit;
// 			
// 			if(to_bb.find(tve) != to_bb.end()){
// 				tve = to_bb[tve];
// 				
// 				if((tve->get_type() == Op) && (OpInst::as(tve)->get_op() == OpInst::Concat)){
// 					const InstL* chs = tve->get_children();
// 					for(InstL::const_iterator cit = chs->begin(); cit != chs->end(); ++cit){
// 						Inst *tve2 = *cit;
// 						list_mux_sels2.push_back(tve2);
// 					}
// 				}else{
// 					list_mux_sels2.push_back(tve);
// 				}
// 				
// 				//cout << "#	to_bb[]: mux found" << endl;
// 				//cout << "list_mux_sels: [to_bb] " << *tve << endl;
// 			}else{
// 				list_mux_sels2.push_back(tve);
// 				//cout << "#	to_bb[]: cannot found a mux" << endl;
// 				//cout << "list_mux_sels: " << *tve << endl;
// 			}
// 		}
// 		draw_graph("post", "HoldSel_reg/q", 0, to_bb);
// 		draw_graph("post", "HsizemHold_88652_reg/q$0_0", 0, to_bb);
// 		draw_graph("post", "HsizemHold_88652_reg/q$1_1", 0, to_bb);
// 		draw_graph("post", "HsizemHold_88652_reg/q$2_2", 0, to_bb);
// 		draw_graph("post", "HsizemHold_reg/q$0_0", 0, to_bb);
// 		draw_graph("post", "HsizemHold_reg/q$1_1", 0, to_bb);
// 		draw_graph("post", "HsizemHold_reg/q$2_2", 0, to_bb);
		
// 		draw_graph("post", "msr_driver_flop_reg/q", 0, to_bb);
// 		draw_graph("post", "reg_reset/q", 0, to_bb);

// 		draw_graph("post", "vo_d601_88669_reg/q", 0, to_bb);
//draw_graph("post", "en_line_88611_reg/q", 0, to_bb);
/*		
{
		cout << "debug_top:" << endl;
		new_print(cout, debug_top, true);

		cout << "debug_top:" << *debug_top << endl;

		dump_to_bb(debug_top, to_bb, true);
		assert(0);
	
}*/
		
		
	}
	
// 	ostringstream ostr;
// 	ostr << config->get_working_dir() << "/t_graph_prop_0";
// 	draw_graph(ostr.str(), config->get_arg(PROP_SIG_ARG), 0);

// 	cout << "vwn ve_init:" << endl;
// 	new_print(cout, ve_init, true);
// 	cout << "vwn ve_model_nsf:" << endl;
// 	new_print(cout, ve_model_nsf, true);
// 	cout << "vwn ve_prop:" << endl;
// 	new_print(cout, ve_prop, true);

#endif	//AVR_SPLIT_SIGNALS

#ifdef AVR_PARTIAL_BIT_BLAST

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
		
//		cout << "#################################################################" << endl;
//		cout << "#################################################################" << endl << endl;
		
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
//		cout << "sreg_sz: " << s_reg_names.size() << endl;

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
					//cout << "reg_name: " << reg_name << ", width: " << width;	
	//				if((width > 1) && (width < 8)){
					//if((width <= 3) || (reg_name == "regQ_11_8_reg/q"))
					//if(width <= 8)
					if(1)
					{
						//cout << " >> bit-blasted" << endl;
//						cout << "reg_name: " << reg_name << ", width: " << width << endl;
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
//					cout << "reg_name: " << reg_name << ", width: " << width << endl;
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
//		cout << "bb_prop: " << bb_prop << endl;
		partial_bit_blast(in_sigs, bb_prop);
//		cout << endl << "#################################################################" << endl;
//		cout << "#################################################################" << endl;

	}
#endif	//AVR_PARTIAL_BIT_BLAST
}

//	DPA_COUT_A("\nPrinting map_init" << endl);
//	for(InstToInstM::iterator init_it = map_init.begin(); init_it != map_init.end(); ++init_it)
//	{
//		Inst *ve_lhs = init_it->first;
//		Inst *ve_rhs = init_it->second;
//		DPA_COUT_A("\t" << *ve_lhs << " = " << *ve_rhs << endl);
//	}
//	DPA_COUT_A(endl);

	if (MOVED_TO_DPA)
	{
		conjunct_init.clear();
		InstToInstM::iterator init_it = map_init.begin();
		for(; init_it != map_init.end(); ++init_it){
			Inst *ve_lhs = init_it->first;
			Inst *ve_rhs = init_it->second;

			if(ve_lhs->get_size() == 1){
				if((ve_rhs->get_type() == Num) && (NumInst::as(ve_rhs)->get_num() == 0)){
					conjunct_init.push_back(OpInst::create(OpInst::LogNot, ve_lhs));
				}else if((ve_rhs->get_type() == Num) && (NumInst::as(ve_rhs)->get_num() == 1)){
					conjunct_init.push_back(ve_lhs);
				}
				else {
					conjunct_init.push_back(OpInst::create(OpInst::Eq, ve_lhs, ve_rhs));
				}
			}else{
				conjunct_init.push_back(OpInst::create(OpInst::Eq, ve_lhs, ve_rhs));
			}
		}
	}

//	{
//		ostringstream ostr;
//		ostr << config->get_working_dir() << "/prop_dpa";
//		draw_graph(ostr.str(), config->get_arg(PROP_SIG_ARG), 0);
//	}
//	{
//		ostringstream ostr;
//		ostr << config->get_working_dir() << "/T_dpa";
//		draw_graph(ostr.str(), "nsf", 0);
//	}

	if (conjunct_init.empty())
		ve_init = NumInst::create(1, 1);
	else
		ve_init = OpInst::create(OpInst::LogAnd, conjunct_init);

	DPA_COUT_A("P: " << *ve_prop << endl);
	DPA_COUT_A("I: " << *ve_init << endl);
	DPA_COUT_A("T: " << *ve_model_nsf << endl);

/// END (CCD and PDC)

//	InstL conjunct_init;
//	collect_nsfs(ve_init, conjunct_init, true);

	InstL conjunct_nsf;
	collect_nsfs(ve_model_nsf, conjunct_nsf, true);

//	cout << "nsf: " << conjunct_nsf << endl;

	for (InstL::iterator it = conjunct_nsf.begin(); it != conjunct_nsf.end(); ++it) {
		Inst *tve = *it;
		if (tve == NumInst::create(1, 1))
			continue;

		Inst *lhs;
		Inst *rhs;
		if(tve->get_children()){
			InstL::const_iterator it2 = tve->get_children()->begin();
			lhs = *it2++;

			if((tve->get_type() == Op) && (OpInst::as(tve)->get_op() == OpInst::LogNot)){
				rhs = NumInst::create(0, 1);
			}else{
				rhs = *it2;
			}
		}else{
			lhs = tve;
			rhs = NumInst::create(1, 1);
		}

		SigInst* sig = SigInst::as(lhs);
		if(!sig) {
		  cout << *lhs << endl;
      cout << *lhs->get_children()->front() << endl;
      cout << *rhs << endl;
      cout << *rhs->get_children()->front() << endl;
		}
		assert(sig);
		string str_lhs = sig->get_name();

// 		if(str_lhs == "msr_driver_flop_reg/q$next"){
// 			cout << "_m_sn, lhs: " << *lhs << endl;
// 			cout << "_m_sn, rhs: " << *rhs << endl;
// 			assert(0);
// 		}

		_m_sn[lhs] = rhs;
		string str_lhs_wo_next = str_lhs.substr(0, str_lhs.find_last_of('$'));
#ifdef INSERT_ZERO_LEMMAS
		add_zero_lemmas(rhs);
#endif
		Inst* pre = SigInst::create(str_lhs_wo_next, sig->get_size(), sig->get_sort());
		_s_reg.insert(pre);
	}

//	derive_euf_func_list_2(ve_init, true);
//	derive_euf_func_list_2(ve_prop, true);
//	derive_euf_func_list_2(ve_model_nsf, false);
//
//	for (map<string, InstL>::iterator it = _func_list.begin(); it != _func_list.end(); it++)
//	{
//		string euf_func_name = (*it).first;
//		InstL* instList = &((*it).second);
////		cout << euf_func_name << " -> " << endl;
//		for(InstL::iterator lit = instList->begin(); lit != instList->end(); ++lit)
//		{
//			Inst* inst = *lit;
////			cout << "    " << *inst << endl;
//			if (map_inst_euf.find(inst) == map_inst_euf.end())
//				map_inst_euf[inst] = euf_func_name;
//		}
////		cout << endl;
//	}

	if(PRINT_DPA_RESULTS)
	{
		string fname_dpa;
		ofstream outFile;
#if PRINT_DESIGN
		fname_dpa = config->get_working_dir() + "/data/design.txt";
		outFile.open(fname_dpa.c_str());

		DPA_COUT_FILE("-------------------------------" << endl);
		DPA_COUT_FILE("Function Blocks ( out = F(in) )" << endl);
		DPA_COUT_FILE("-------------------------------" << endl);
		print_internals(outFile);
		DPA_COUT_FILE(endl);
		outFile.close();
#endif


		collect_inputs(ve_init, _s_reg, true);
		collect_inputs(ve_prop, _s_reg, false);
		collect_inputs(ve_model_nsf, _s_reg, false);

		map < int, int > stateSizes;
		map < int, int > inputSizes;
		map < int, int > constSizes;

		InstL svs;
		for (auto& s : _s_reg)
		{
			svs.push_back(s);
			if (stateSizes.find(s->get_size()) != stateSizes.end())
				stateSizes[s->get_size()]++;
			else
				stateSizes[s->get_size()] = 1;
		}
		InstL inps;
		for (auto& s : inputs)
		{
			inps.push_back(s);
			if (inputSizes.find(s->get_size()) != inputSizes.end())
				inputSizes[s->get_size()]++;
			else
				inputSizes[s->get_size()] = 1;
		}
		InstL cts;
		for (auto& s : constants)
		{
			cts.push_back(s);
			if (constSizes.find(s->get_size()) != constSizes.end())
				constSizes[s->get_size()]++;
			else
				constSizes[s->get_size()] = 1;
		}
		svs.sort(CompareBySz);
		inps.sort(CompareBySz);
		cts.sort(CompareBySz);

		fname_dpa = config->get_working_dir() + "/data/parse.results";
		outFile.open(fname_dpa.c_str());

		DPA_COUT_FILE("------------" << endl);
		DPA_COUT_FILE("Size Summary" << endl);
		DPA_COUT_FILE("------------" << endl);
		DPA_COUT_FILE(endl);

		DPA_COUT_FILE("State variables (#" << svs.size() << ")" << endl);
		for (auto& s: stateSizes)
		{
			DPA_COUT_FILE("\t(" << s.first << "-bit)\t" << s.second << endl);
		}
		DPA_COUT_FILE(endl);

		DPA_COUT_FILE("Inputs (#" << inps.size() << ")" << endl);
		for (auto& s: inputSizes)
		{
			DPA_COUT_FILE("\t(" << s.first << "-bit)\t" << s.second << endl);
		}
		DPA_COUT_FILE(endl);

		DPA_COUT_FILE("Constants (#" << cts.size() << ")" << endl);
		for (auto& s: constSizes)
		{
			DPA_COUT_FILE("\t(" << s.first << "-bit)\t" << s.second << endl);
		}
		DPA_COUT_FILE(endl);

		DPA_COUT_FILE("---------------" << endl);
		DPA_COUT_FILE("State Variables" << endl);
		DPA_COUT_FILE("---------------" << endl);
		int numBits = 0;
		int numSvars = 0;
		int maxBitsz = 0;
		int numControlBits = 0;
		int numControlSvars = 0;
		int maxControlBitsz = 0;

		int controlThreshold = 1;
		if (Config::g_ab_interpret) {
			if (Config::g_ab_interpret_limit == 0)
				controlThreshold = INT_MAX;
			else
				controlThreshold = Config::g_ab_interpret_limit;
		}

		for (InstL::iterator i = svs.begin(); i != svs.end(); i++)
		{
			int sz = (*i)->get_size();
			DPA_COUT_FILE(setw(28) << left << *(*i) << "    (" << sz << "-bit)" << endl);
			numSvars++;
			numBits += sz;
			if (sz > maxBitsz)
				maxBitsz = sz;
			if (sz <= controlThreshold) {
				numControlSvars++;
				numControlBits += sz;
				if (sz > maxControlBitsz)
					maxControlBitsz = sz;
			}
		}
		DPA_COUT_FILE(endl);
		_resFile << "#state-variables:\t" << numSvars << endl;
		_resFile << "total-state-bits:\t" << numBits << endl;
		_resFile << "max-state-bit-size:\t" << maxBitsz << endl;

		_resFile << "interpret-#state-variables:\t" << numControlSvars << endl;
		_resFile << "interpret-total-state-bits:\t" << numControlBits << endl;
		_resFile << "interpret-max-state-bit-size:\t" << maxControlBitsz << endl;

		DPA_COUT_FILE("------" << endl);
		DPA_COUT_FILE("Inputs" << endl);
		DPA_COUT_FILE("------" << endl);
    int numInp = 0;
    int numInpBits = 0;
		for (InstL::iterator i = inps.begin(); i != inps.end(); i++)
		{
			int sz = (*i)->get_size();
			DPA_COUT_FILE(setw(28) << left << *(*i) << "    (" << sz << "-bit)" << endl);
			numInpBits += sz;
      numInp++;
		}
		DPA_COUT_FILE(endl);
    _resFile << "#inputs:\t" << numInp << endl;
    _resFile << "total-input-bits:\t" << numInpBits << endl;

		DPA_COUT_FILE("---------" << endl);
		DPA_COUT_FILE("Constants" << endl);
		DPA_COUT_FILE("---------" << endl);
		int numConst = 0;
		for (InstL::iterator i = cts.begin(); i != cts.end(); i++)
		{
			DPA_COUT_FILE(*(*i) << endl);
			numConst++;
		}
		DPA_COUT_FILE(endl);
		_resFile << "#constants:\t" << numConst << endl;

		int totalUF = 0;
		int totalEx = 0;
		int totalCc = 0;
		int totalCF = 0;
		int totalMux = 0;

		int propConst = 0;
		int propUF = 0;
		int propMux = 0;
		map< string, int > ufType, ccType, exType;
		collect_func_stat(ve_prop, propConst, totalCF, totalUF, totalMux, totalCc, totalEx, ufType, ccType, exType, true);

		propUF = totalUF;
		propMux = totalMux;

		for (auto& m: _m_sn)
		{
			int numUF = 0;
			int numEx = 0;
			int numCc = 0;
			int numCF = 0;
			int numMux = 0;
			int numConst = 0;
			collect_func_stat(m.second, numConst, numCF, numUF, numMux, numCc, numEx, ufType, ccType, exType, false);

			totalUF += numUF;
			totalEx += numEx;
			totalCc += numCc;
			totalCF += numCF;
			totalMux += numMux;
		}

		_resFile << "#control:\t" << totalCF << endl;
		_resFile << "#uf:\t" << totalUF << endl;
		_resFile << "#concat:\t" << totalCc << endl;
		_resFile << "#extract:\t" << totalEx << endl;
		_resFile << "#uf-types:\t" << ufType.size() << endl;
		_resFile << "#concat-types:\t" << ccType.size() << endl;
		_resFile << "#extract-types:\t" << exType.size() << endl;

		_resFile << "#mux:\t" << totalMux << endl;

		_resFile << "comb-prop-#uf:\t" << propUF << endl;
		_resFile << "comb-prop-#const:\t" << propConst << endl;
		_resFile << "comb-prop-#mux:\t" << propMux << endl;

		DPA_COUT_FILE("-----------------------------" << endl);
		DPA_COUT_FILE("Uninterpreted Functions (UFs)" << endl);
		DPA_COUT_FILE("-----------------------------" << endl);
		for (map< string, int >::iterator it = ufType.begin(); it != ufType.end(); it++)
		{
			DPA_COUT_FILE((*it).first << "\t#" << (*it).second << endl);
		}
//		for (set<string>::iterator it = ccType.begin(); it != ccType.end(); it++)
//		{
//			DPA_COUT_FILE(*it << endl);
//		}
//		for (set<string>::iterator it = exType.begin(); it != exType.end(); it++)
//		{
//			DPA_COUT_FILE(*it << endl);
//		}
		DPA_COUT_FILE(endl);

//		for (map<string, InstL>::iterator it = _func_list.begin(); it != _func_list.end(); it++)
//		{
//			string euf_func_name = (*it).first;
//			DPA_COUT_FILE(setw(8) << left << euf_func_name << "         (");
//			char * pch;
//			int count = 0;
//
//			char *cstr = new char[euf_func_name.length() + 1];
//			strcpy(cstr, euf_func_name.c_str());
//
//			pch = strtok (cstr,"_");
//
//			if (strcmp(pch, "Ex") == 0)
//			{
////				numEx++;
//				char* hi;
//				char* lo;
//				char* sz;
//				pch = strtok (NULL, "_");
//				while (pch != NULL)
//				{
//					count++;
//					if (count == 1)
//						hi = pch;
//					else if (count == 2)
//						lo = pch;
//					else if (count == 3)
//						sz = pch;
//					pch = strtok (NULL, "_");
//				}
//				DPA_COUT_FILE("Arg[" << hi << ":" << lo << "] (" << sz << "bit)");
//			}
//			else
//			{
////				if (euf_func_name.find("Concat") != std::string::npos)
////					numCc++;
////				else
////					numUF++;
//
//				pch = strtok (NULL, "_");
//				pch = strtok (NULL, "_");
//				while (pch != NULL)
//				{
//					count++;
//					DPA_COUT_FILE("Arg_" << count << " (" << pch << "bit)");
//					pch = strtok (NULL, "_");
//					if (pch != NULL)
//						DPA_COUT_FILE(", ");
//				}
//			}
////			while (pch != NULL)
////			{
////				if (count > 0)
////					DPA_COUT_FILE("Arg_" << count << " (" << pch << "bit)");
////
////				pch = strtok (NULL, "_");
////
////				if (count > 0 && pch != NULL)
////					DPA_COUT_FILE(", ");
////				count++;
////			}
//			DPA_COUT_FILE(")" << endl);
//
//			delete [] cstr;
//		}
//		DPA_COUT_FILE(endl);

//		DPA_COUT_FILE("-------" << endl);
//		DPA_COUT_FILE("Signals" << endl);
//		DPA_COUT_FILE("-------" << endl);
//		for (InstS::iterator i = signals.begin(); i != signals.end(); i++)
//		{
//				DPA_COUT_FILE(setw(18) << left <<  *(*i)  << "    (" << (*i)->get_size() << "-bit)" << endl);
//		}
//		DPA_COUT_FILE(endl);

		DPA_COUT_FILE("------------------" << endl);
		DPA_COUT_FILE("Initial Conditions" << endl);
		DPA_COUT_FILE("------------------" << endl);
		DPA_COUT_FILE(conjunct_init << endl);
		DPA_COUT_FILE(endl);

#ifndef AVOID_LARGE_PRINTING
		DPA_COUT_FILE("--------" << endl);
		DPA_COUT_FILE("Property" << endl);
		DPA_COUT_FILE("--------" << endl);
		DPA_COUT_FILE(*ve_prop << endl);
		DPA_COUT_FILE(endl);

		DPA_COUT_FILE("-------------------" << endl);
		DPA_COUT_FILE("Transition Relation" << endl);
		DPA_COUT_FILE("-------------------" << endl);
		DPA_COUT_FILE(conjunct_nsf << endl);
		DPA_COUT_FILE(endl);
#endif
		outFile.close();
	}

	_resFile.close();

	write_wn();
	
	//cout << "PRIM_END: " << (int)PRIM_END << endl;
	
	// All done.  Wasn't that easy ?
    return 0;
}
