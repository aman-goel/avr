/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


/*
 * wif_fparser.cpp
 *
 *  Created on: May 14, 2019
 *      Author: amangoel
 */


#include "wif_parser.h"

#include "wif_option.h"
#include "wif_stdio.h"
#include "wif_engine_std.h"
#include "wif_registry.h"
#include "wif_engine_int.h"
#include <cstring>
#include <new>
#include <sstream>
#include <algorithm>
#include <stack>

bool g_clock_opt = true;
bool g_local_latch = false;


extern WIF::CustomOpFactory *wpi_get_custom_op_factory(void);
WIF::CustomOpFactory* jg_factory = 0;
static const char *JG_SYSCLK_VAR_NAME = "__jg__wif__sysclk_";
static unordered_map< int, WIF::Net > g_upto_counters;
static unordered_map< int, WIF::Net > g_clk_counters;

static char usage_string[] = "Usage: wif  <file.wif>\n";
WIF::OptionEntry<WIF::IntOption> VOption("v","<int> set verbosity level");
WIF::OptionEntry<WIF::BoolOption> CexOption("cexinps","reports only inputs in the counterexample");
WIF::OptionEntry<WIF::BoolOption> EffOption("eff","turns on next_unit_decision callback messages");
WIF::OptionEntry<WIF::StringOption> FormatOption("format","<string> set input format");
WIF::SymbolTable *the_nmap;
std::ofstream os;


struct usage {
  string msg;
  usage(const string &_msg) : msg(_msg) {}
};

struct misc_error {
  string msg;
  misc_error(const string &_msg) : msg(_msg) {}
};

static void generic_help() {
  cout << "wif: word-level engine front-end\n\n";
  cout << "Options:\n";
  cout << "  -help          print help message\n";

  WIF::RegistrySummaries summaries;
  WIF::OptionRegistry<WIF::Option>::get_summaries(summaries);
  for(int i = 0; i < summaries.size(); i++){
    string name(summaries[i].first);
    cout << "  -" <<  name; for(int j = name.size(); j < 16; j++) cout << " ";
    cout << summaries[i].second << "\n";
  }

  cout << "\n";
  cout << "Available engines:\n";
  WIF::engines_summary engines;
  WIF::get_engines_summary(engines);
  for(int i = 0; i < engines.size(); i++){
    string name(engines[i].first);
    cout << name; for(int j = name.size(); j < 14; j++) cout << " ";
    cout << engines[i].second << "\n";
  }
  cout << "\nFor options of a specific engine, use \"wif -e <engine> -help\"\n";
}

static void engine_help(WIF::Engine *eng){
  cout << "Engine options:\n";
  int num_options = eng->get_num_options();
  for(int i = 0; i < num_options; i++){
    const char *cname, *description;
    WIF::Option_Type type;
    eng->get_option_info(i,cname,type,description);
    string name(cname);
    cout << "-" << name; for(int j = name.size(); j < 16; j++) cout << " ";
    cout << (type == WIF::option_int ? "(int)" : "(string)") << " " << description << "\n";
  }
}

// Look up an option of a given engine
static bool option_find(WIF::Engine *eng, const string &flag, WIF::Option_Type &type){
  int num_options = eng->get_num_options();
  for(int i = 0; i < num_options; i++){
    const char *cname, *description;
    eng->get_option_info(i,cname,type,description);
    string name(cname);
    if(name == flag) return true;
  }
  return false;
}

// Some cryptic code for ensuring all engines are available from the static linking - global variable initialization
namespace WIF {
	template <class T> class RegisterEngine;
	struct EngineBB;
	extern RegisterEngine<EngineBB> RegEngineBB;
	struct EngineClausal;
	extern RegisterEngine<EngineClausal> RegEngineClausal;
	struct EngineCut;
	extern RegisterEngine<EngineCut> RegEngineCut;
	struct EngineDomain;
	extern RegisterEngine<EngineDomain> RegEngineDomain;
	struct EngineSimp;
	extern RegisterEngine<EngineSimp> RegEngineSimp;
	struct EngineWrite;
	extern RegisterEngine<EngineWrite> RegEngineWrite;
	volatile size_t register_engine_dummy = (size_t)&RegEngineBB  +  (size_t)&RegEngineClausal  +  (size_t)&RegEngineCut  +   (size_t)&RegEngineSimp  +  (size_t)&RegEngineWrite ;
}

//-------- Do not Worry about code below this line. This is primarily for reading the WIF file into a WIFEngine
struct JGClockProp : public WIF::CustomOp {
  int num_args() override { return 1; }
  int initial, offset, width, period;
  string _name;
  const char* name() override {
    _name="CLOCK_AUTOMATON";
    char buf[50];
    sprintf(buf,"_%d_%d_%d_%d",initial,offset,width,period);
    _name += buf;
    return _name.c_str();
  }

  unsigned ceil_log2(unsigned n){
      --n;
      unsigned res = 0;
      while(n){
        n = n / 2;
        ++res;
      }
      return res;
  }

  WIF::Net gen_counter(WIF::EngineStd *e, unsigned max){
  	if (g_clk_counters.count(max))
  		return g_clk_counters[max];

    wif_log("\t(creating clock counter with limit: " << max << ")\n");
    unsigned size = ceil_log2(max);
    assert(size);
    WIF::Type type = e->word_type(size);
    WIF::Net zero = e->constant(type,e->const_value(type,mpz_class(0)));
    WIF::Net one = e->constant(type,e->const_value(type,mpz_class(1)));
    WIF::Net max_net = e->constant(type,e->const_value(type,mpz_class(max-1)));
    WIF::Net cnt = e->delay_start(type,zero);
    /* cnt_next = cnt == max-1 ? 0:cnt+1; */
    WIF::Net cnt_plus_1 = e->add(type,cnt,one);
    WIF::Net cond = e->gen_eq(cnt,max_net);
    WIF::Net cnt_next = e->gen_ite(cond,zero,cnt_plus_1);
    e->delay_end(type,cnt,cnt_next);
    g_clk_counters[max] = cnt;
    return cnt;
  }

  /* Create a counter of size 0..period-1
  ** arg[0] == ITE(I,True,false), where
  **  I = (counter >= 2phase@period) && (counter < (2phase+period/2)@period
  **  ==> I = (2phase@period <= counter) && (counter < (2phase+period/2)@period
  **  factor is stored in initial and phase in offset
  ** period = 2*factor
  */
  WIF::Net lower(WIF::EngineStd *e, const WIF::Net &n) override {
    /* generate a counter and create a constraint such that n->clock behaves as if running on this counter */ 
   int mul = g_clock_opt ? 1 : 2;
   int tp = mul*initial;
   if (tp==1)
       return e->bit_one();
   int phase = offset;
   WIF::Net cnt = gen_counter(e,tp);
   const char* name = e->net_name(n);
   if (name){
     string new_name(name);
     new_name+= "__clock_automaton";
     e->set_net_name(cnt,new_name);
   }

   WIF::Net clknet = e->net_ntharg(n,0);
   int lower = (mul*phase) % tp;
   int upper = ((mul*phase + tp/2 - 1) % tp);
   WIF::Net clk_val;
   WIF::Net eq;
   wif_log("\t(clock limit: " << lower << " <= " << _name << " <= " << upper << ")\n");

   if (upper < lower) {
     wif_loge("clock constraint limit becomes false: " << lower << " <= " << _name << " <= " << upper);
//		 clk_val = e->bit_zero();
//		 eq = e->gen_eq(clk_val,clknet);
   }
   else {
  	 WIF::Net cond1, cond2;
#if 1
			 cond1 = e->constant_of(false);
			 cond2 = e->constant_of(true);
  		 for (int i = lower; i <= upper; i++) {
  			 WIF::Net i_net = e->constant(cnt.get_type(), e->const_value(cnt.get_type(), mpz_class(i)));
  			 WIF::Net condi = e->eq(cnt, i_net);
  			 cond1 = e->gen_or(cond1, condi);
  		 }
#else
  	 if (upper == lower) {
			 WIF::Net lower_net = e->constant(cnt.get_type(), e->const_value(cnt.get_type(), mpz_class(lower)));
			 cond1 = e->eq(lower_net, cnt);
			 cond2 = e->constant_of(true);
  	 }
  	 else {
  		 if (lower != 0) {
				 WIF::Net lower_net = e->constant(cnt.get_type(), e->const_value(cnt.get_type(), mpz_class(lower)));
				 cond1 = e->le(lower_net, cnt);
			 }
			 else
				 cond1 = e->constant_of(true);
			 if (upper != (tp - 1)) {
				 WIF::Net upper_net = e->constant(cnt.get_type(), e->const_value(cnt.get_type(), mpz_class(upper)));
				 cond2 = e->le(cnt, upper_net);
			 }
			 else
				 cond2 = e->constant_of(true);
  	 }
#endif
		 WIF::Net cond = e->gen_and(cond1,cond2);
		 clk_val = e->gen_ite(cond, e->bit_one(), e->bit_zero());
		 eq = e->gen_eq(clk_val,clknet);
   }
   //e->constraint(eq);
   return eq;
  }
};

struct JGLatch : public WIF::CustomOp {
  int num_args(){return 3;}
  const char *name(){return "LATCH";}
  virtual bool has_delay(){return true;}
  virtual WIF::Net init(WIF::EngineStd* e, const WIF::Net& n) {return e->net_ntharg(n,0);}

  int arg_symmetry_class(int pos){
    int ret=0;
    assert(pos < num_args());
    switch (pos)
    {
      case 0://init
      case 1://data
       ret=0;
       break;
      case 2://enable
       ret=1;
       break;
      default:
        assert(0&&"illegal arg position to arg_symmetry_class function\n");
    }
    return ret;
  }//arg_symmetry_class

 // translate Latch into native WIF ops
  WIF::Net lower(WIF::EngineStd *e, const WIF::Net &n){
  	WIF::Net delay = e->delay_start(n.get_type(),e->net_ntharg(n,0));
  	WIF::Net en = e->net_ntharg(n,2);
    //assert(en.is_bit() || (en.word_size().get_ui()==1));
    if (en.is_word()){
      en = e->eq(en,e->constant_of(en.word_size(),1));
    }
    WIF::Net latch_out = e->gen_ite(en,e->net_ntharg(n,1),delay);
    //Net output = e->var(n.get_type()); // latch output is a constrainted input, to break cycles
    //Net cnst = e->gen_eq(latch_out,output); // this implements transparency
    //e->EngineStd::constraint(cnst);
    e->delay_end(n.get_type(),delay,latch_out);
    return latch_out;
  }

  virtual WIF::Value eval(WIF::EngineStd *eng, WIF::CexObj *cex, const WIF::Net &net, int time){
  //In case of latch, the output at 0time is not initial value - it depends on enable
/*
    if(time == 0)
      return eng->eval_net(cex,time,eng->net_ntharg(net,0),-1);
*/
  	WIF::Value enable = eng->eval_net(cex,time,eng->net_ntharg(net,2),-1);
  	WIF::Value res;
    //assert(enable.is_bit() || enable.word_size().get_ui()==1);
    bool enable_is_false = false;
    if ( enable.is_bit()){
      enable_is_false = enable.get_bit_val() == WIF::bit_0;
    }
    else {
      int eval = enable.binary_value().get_ui();
      enable_is_false = eval==0;
    }
    if(enable_is_false){
      if (time==0)
        res =  eng->eval_net(cex,time,eng->net_ntharg(net,0),-1);
      else
        res = eng->eval_net(cex,time-1,net,-1); // keep old value
    }
    else
      /* It's important only to evaluate input when enable is true,
	 else, we can get caught in a combinational cycle */
      res = eng->eval_net(cex,time,eng->net_ntharg(net,1),-1); // get input at current time
    return res;
  }
} JGLatchOp;

struct JGUptoProp : public WIF::CustomOp {
  int num_args() override { return 2; }
  int bound;
  string _name;
  const char* name() override {
    _name="SAFETY_UPTO";
    char buf[50];
    sprintf(buf,"_%d",bound);
    _name += buf;
    return _name.c_str();
  }

  unsigned ceil_log2(unsigned n){
      --n;
      unsigned res = 0;
      while(n){
        n = n / 2;
        ++res;
      }
      return res;
  }

  WIF::Net gen_counter_bounded(WIF::EngineStd *e, unsigned max){
  	if (g_upto_counters.count(max))
  		return g_upto_counters[max];

    wif_log("\t(creating upto counter with limit: " << max << ")\n");
  	unsigned size = ceil_log2(max+1);
    assert(size);
    WIF::Type type = e->word_type(size);
    WIF::Net zero = e->constant(type,e->const_value(type,mpz_class(0)));
    WIF::Net one = e->constant(type,e->const_value(type,mpz_class(1)));
    WIF::Net max_net = e->constant(type,e->const_value(type,mpz_class(max)));
    WIF::Net cnt = e->delay_start(type,zero);
    /* cnt_next = cnt == max ? max : cnt+1; */
    WIF::Net cnt_plus_1 = e->add(type,cnt,one);
    WIF::Net cond = e->gen_eq(cnt,max_net);
    WIF::Net cnt_next = e->gen_ite(cond,max_net,cnt_plus_1);
    e->delay_end(type,cnt,cnt_next);
    g_upto_counters[max] = cnt;
    return cnt;
  }

  /* Create a counter of size 0..bound
  */
  WIF::Net lower(WIF::EngineStd *e, const WIF::Net &n) override {
   int mul = g_clock_opt ? 1 : 2;
   int upper = mul*bound;

   WIF::Net uptonet = e->net_ntharg(n,0);
   WIF::Net ennet = e->net_ntharg(n,1);

   WIF::Net cnt = gen_counter_bounded(e,upper);
   const char* name = e->net_name(n);
   if (name){
     string new_name(name);
     new_name+= "__upto_automaton";
     e->set_net_name(cnt,new_name);
   }

   WIF::Net eq;
   wif_logv("\t(upto limit: " << _name << " < " << upper << ")\n");

   if (upper < 1) {
     wif_loge("upto constraint limit error: " << "1" << " <= " << _name << " < " << upper);
   }
   else {
  	 WIF::Net cond;
		 WIF::Net bound_net = e->constant(cnt.get_type(), e->const_value(cnt.get_type(), mpz_class(upper)));
		 cond = e->eq(cnt, bound_net);
		 WIF::Net ite1 = e->gen_ite(ennet, uptonet, e->bit_one());
		 eq = e->gen_ite(cond, e->bit_one(), ite1);
   }
   //e->constraint(eq);
   return eq;
  }
};

struct JGWpiOpFactory: public WIF::CustomOpFactory {
  JGClockProp* get_jg_clk(const char *name) {
    JGClockProp *jprop = new JGClockProp();
    int initial, offset, width, period;
    sscanf(name,"_%d_%d_%d_%d",&initial, &offset, &width, &period);
   jprop->initial = initial;
   jprop->offset = offset;
   jprop->width = width;
   jprop->period = period;
    return jprop;
  }
  JGUptoProp* get_jg_upto(const char *name) {
    JGUptoProp *jprop = new JGUptoProp();
    int bound;
    sscanf(name,"_%d",&bound);
   jprop->bound = bound;
    return jprop;
  }
  WIF::CustomOp *operator()(const char *name) override {
    string n(name);
    if (n.compare(0,15,"CLOCK_AUTOMATON") == 0) {
      return get_jg_clk(n.substr(15).c_str());
    }
    if(g_local_latch && n == "LATCH") return &JGLatchOp;
    if (n.compare(0,11,"SAFETY_UPTO") == 0) {
      return get_jg_upto(n.substr(11).c_str());
    }
    CustomOpFactory* factory =  wpi_get_custom_op_factory();
    WIF::CustomOp* ret = (*factory)(name);
    return ret;
  }
} TheJGWpiOpFactory;

//-------- Do not Worry about code till here 

class EngineWriteBS : public WIF::EngineStd {
  public:
    EngineWriteBS() {
    	option_add("file",WIF::option_char,"File name");
    }
    virtual bool supports_custom(WIF::CustomOp *cop){return true;}
    
    virtual WIF::Solve_Res solve(){
      const char *fname = char_option_get("file");
      if(!fname)
         writeBS(std::cout);
      else {
        std::ofstream s;
        s.open(fname);
        if(s)
          writeBS(s);
        else
          std::cerr << "cannot open " << fname << "for writing\n";
      }
      std::cout <<"BS Writer called \n";
      return WIF::open;
    }
  private:
    
    bool is_latch(const WIF::Net& n) {return net_is_custom(n) && !strcmp(net_custom_op(n)->name(), "LATCH");}
    bool is_upto(const WIF::Net& n) {return net_is_custom(n) && !strncmp(net_custom_op(n)->name(), "SAFETY_UPTO_1",12);}
    void collectNets(const WIF::Net& cn, WIF::NetSet& done) {
        WIF::Net n = cn;
        if (net_op(n) == WIF::Not)
          n = net_ntharg(n,0);
        if (done.find(n) != done.end())
          return;
        done.insert(n);
        assert(!net_is_custom(n) || is_latch(n));
        assert(n.is_bit());
        for (int i=0; i < net_numargs(n); i++) {
        	WIF::Net arg = net_ntharg(n,i);
          collectNets(arg,done);
        }
        WIF::Op op = net_op(n);
        if (all_nets.find(op) == all_nets.end()) {
        	WIF::NetVector v;
          all_nets[op] = v;
        }
        WIF::NetVector& ops = all_nets[op];
        net_ids[n] = ops.size();
        ops.push_back(n);
    }

    std::string getConstName(const WIF::Net& net, bool neg=false) {
      const char* true_str = "vTrue";
      const char* false_str = "vFalse";
      assert(net_isconst(net));
      assert(net.is_bit());
      const WIF::Value &v = net_constval(net);
      if (v.get_bit_val() == WIF::bit_1)
        return neg ? false_str : true_str;
      else if (v.get_bit_val() == WIF::bit_0)
        return ~neg ? false_str : true_str;
      assert(0);
      return "v??";
    }
    
    std::string getName(const WIF::Net& cn, bool ival = false) {
      std::string ret = getNameSafe(cn, ival);
      assert(!ret.empty());
      return ret;
    }
    
    std::string getNameSafe(const WIF::Net& cn, bool ival = false) {
    	WIF::Net n = cn;
        if (n==bit_one())
          return "vTrue";
        else if (n==bit_zero())
          return "vFalse";
        WIF::Op op = net_op(n);

        if (op==WIF::Const)
          return getConstName(n);

        if (ival && op == WIF::Var)
          return "vUndef";
    
        bool ok =(op==WIF::Var || op==WIF::Delay || op==WIF::Not || op==WIF::And || op == WIF::Eq) || is_latch(n) || is_upto(n);
        if (!ok)
          std::cout <<"--Bad Op " << WIF::op_str[op] << " for " << get_net_name(n) << "\n";
        if (!ok || is_upto(n))
          return "";
        assert(ok);
        bool negate = op==WIF::Not;
        n = negate ? net_ntharg(n,0) : n;
        op = net_op(n);
        bool islatch = is_latch(n);
        ok = op==WIF::Eq || op==WIF::Var || op==WIF::Delay || op==WIF::And || islatch;
        if (!ok)
          std::cout <<"Bad Op " << op << "\n";
        assert(ok);
        if (op==WIF::Const)
          return getConstName(n, negate);
        std::string ret;
        if (op==WIF::Var || op==WIF::Delay)
          ret = negate ? "~v" : "v";
        else if (op==WIF::And)
          ret = negate ? "~a" : "a";
        else if (op==WIF::Eq)
          ret = negate ? "~e" : "e";
        else if (islatch)
          ret = negate ? "~l" : "l";
        if (net_ids.find(n) == net_ids.end())
          return "";
        //assert(net_ids.find(n) != net_ids.end());
        int idx = net_ids[n];
        if (op==WIF::Delay)
          idx += all_nets[WIF::Var].size();
        std::stringstream ss;
        ss << ret << idx;
        return ss.str();
    }
    void collectNets() {
    	WIF::NetSet done;
        for (auto& c : checks) {
          const WIF::Net& net = check_safety_net(c);
          collectNets(net,done);
        }
        for (auto& c : constraints) {
          assert(is_upto(c) || !net_is_custom(c));
          if  (is_upto(c))
            collectNets(net_ntharg(c,0),done);
          else
            collectNets(c,done);
        }
        for (auto& v : all_nets) {
          std::cout<<"--Type Found " << WIF::op_str[v.first] <<"\n";
        }
    }
    void writeBS (std::ostream &out) {
        //Just collect all net types in a hash and then serialize CLOCKS, VARS, LATCHES, AND, MUXES, EQ, CONSTRAINT and TARGETS
        collectNets();
        out <<"CLOCK c0 = 1 0" << std::endl;
        if (all_nets.find(WIF::Var) != all_nets.end()) {
          std::string typeStr = "VAR ";
          for (auto& v : all_nets.find(WIF::Var)->second)
          {
            out <<typeStr << getName(v) << " = vUndef, vUndef @ c0\n";
          }
        }
        if (all_nets.find(WIF::Delay) != all_nets.end()) {
          std::string typeStr = "VAR ";
          for (auto& v : all_nets.find(WIF::Delay)->second)
          {
          	WIF::Net ival = net_ntharg(v,0);
          	WIF::Net next = net_ntharg(v,1);
            out << typeStr << getName(v) << " = " << getName(ival, true) << " ," << getName(next) << " @ c0\n";
          }
        }
        if (all_nets.find(WIF::OpMax) != all_nets.end()) {
          std::string typeStr = "LATCH ";
          for (auto& v : all_nets.find(WIF::OpMax)->second)
          {
            assert(is_latch(v));
            WIF::Net ival = net_ntharg(v,0);
            WIF::Net next = net_ntharg(v,1);
            WIF::Net enable = net_ntharg(v,2);
            //LATCH l0 = vTrue, ~c0 ? a121800
            out << typeStr << getName(v) << " = " << getName(ival, true) << " ," << getName(enable) << " ? " << getName(next) << " \n";
          }
        }
        if (all_nets.find(WIF::And) != all_nets.end()) {
          std::string typeStr = "AND ";
          for (auto& v : all_nets.find(WIF::And)->second)
          {
          	WIF::Net left = net_ntharg(v,0);
          	WIF::Net right = net_ntharg(v,1);
            out << typeStr << getName(v) << " = " << getName(left) << " & " << getName(right) << "\n";
          }
        }
        if (all_nets.find(WIF::Eq) != all_nets.end()) {
          std::string typeStr = "EQU ";
          for (auto& v : all_nets.find(WIF::Eq)->second)
          {
          	WIF::Net left = net_ntharg(v,0);
          	WIF::Net right = net_ntharg(v,1);
            out << typeStr << getName(v) << " = " << getName(left) << " <-> " << getName(right) << "\n";
          }
        }
        // NameMap
        for (auto& np : namemap) {
          std::string nn = getNameSafe(np.first);
          if (!nn.empty())
            out << "NAME " << "\"" << np.second << "\" = " << nn << "\n";
         }
        // NameMap for targets
        for (auto& c : checks) {
        	WIF::Net net = check_safety_net(c);
          out << "NAME " << "\"'" << check_name(c) << "'\" = " << getName(net) << "\n";
        }

        // Constraints
        for (auto& c : constraints) {
          bool isupto = is_upto(c);
          if (isupto) {
            std::string n = net_custom_op(c)->name();
            int bound = atoi(n.substr(12,n.size()).c_str());
            out << "UPTO " << bound << " " << getName(net_ntharg(c,0)) << "\n";
            continue;
          }
          assert(!net_is_custom(c));
          out << "ALL " << getName(c) <<"\n";
        }
    
        // targets
        int index = 0;
        for (auto& c : checks) {
        	WIF::Net net = check_safety_net(c);
          out << "TARGET t" << index++ << " = " << getName(net) << "\n";
        }
    }
  private:
        std::map<WIF::Op, WIF::NetVector> all_nets;
        WIF::NetMap<int>                  net_ids;
};

WIF::RegisterEngine<EngineWriteBS> RegEngineBSWrite("writebs","Write BS");

set< string > g_fast_clocks;

class MyEngine : public WIF::EngineStd {
  public:
		MyEngine():m_lower(false) {
			m_sysclk_var = var(bit_type());
			set_net_name(m_sysclk_var,JG_SYSCLK_VAR_NAME);
//			option_add("clock_opt",WIF::option_int,"Do Clock Optimization");
			option_add("inline",WIF::option_int,"Do constraint inlining Optimization");
			option_add("verb",WIF::option_int,"Verbosity");
		}
    MyEngine(bool lower):m_lower(lower) {
      m_sysclk_var = var(bit_type());
      set_net_name(m_sysclk_var,JG_SYSCLK_VAR_NAME);
    }
    bool supports_custom(WIF::CustomOp *cop){
        return !m_lower;
    }
    void traverse();
    void collect_subs();
    void replace_subs();
    void selectCheck();
//    bool hasSimpleClock(const WIF::Net& net);
//    void collectEdgesToSubstitute(WIF::NetMap<WIF::Net> &subs);
//    bool collectEdgesToSubstitute(const WIF::Net& net, WIF::NetMap< bool > &done, WIF::NetMap<WIF::Net>& subs);
//    void fixConstraints(WIF::NetMap<WIF::Net> &subs);
    void removeTrivalConstraints();
    void inlineConstraints(WIF::NetMap<WIF::Net> &subs);
    void inlineEQ(const WIF::Net& eq, WIF::NetMap<WIF::Net>& subs, WIF::NetSet& repr);
    void flattenAnd(const WIF::Net& net, std::vector<WIF::Net>& ret);
    std::string safe_net_name(const WIF::Net& n) {
      const char *name = get_net_name(n);
      if (!name) name = "???";
      return name;
    }

    virtual WIF::Pipe_Res pipe_problem (WIF::Engine *to);
    virtual const char* engine_name() {return (m_lower? "Lower" : "MyWifFixer");}
  private:
    void traverse(const WIF::Net& n, WIF::NetSet& done);
    void replace_subs(const WIF::Net& n, WIF::NetSet& done, WIF::NetMap<WIF::Net>& g_subs);
    std::string getTypeString(const WIF::Net& n);
    void dumpVar(const WIF::Net& n);
    bool m_lower;
    WIF::Net m_sysclk_var;
    WIF::NetMap< WIF::Net > m_simple_clocks;
    WIF::NetMap< bool > has_simple_clock;
};

WIF::Pipe_Res MyEngine::pipe_problem (WIF::Engine *to) {
  collect_subs();
  WIF::NetMap<WIF::Net> subs;
//  fixConstraints(subs);
  inlineConstraints(subs);
  removeTrivalConstraints();
  int v = option_get("verb");
  if (v) {
    for (auto& n : subs) {
      std::string str = n.second == bit_one() ? "True" : n.second == bit_zero() ? "False" : get_net_name(n.second);
      std::cout <<"Substituting " << get_net_name(n.first) << " = " << str << "\n";
    }
  }
  substitute(subs, true);

	WIF::EngineStd::pipe_problem(to);
	return WIF::pipe_ok;
}

WIF::RegisterEngine<MyEngine> RegMyEngine("wifpre","WIF Preprocessor");

void MyEngine::flattenAnd(const WIF::Net& net, std::vector<WIF::Net>& ret) {
  if (net_op(net) != WIF::And)
    ret.push_back(net);
  else {
    flattenAnd(net_ntharg(net, 0), ret);
    flattenAnd(net_ntharg(net, 1), ret);
  }
  return;
}

void MyEngine::removeTrivalConstraints() {
  std::vector<WIF::Net> new_constraints;
  for (auto assert_net : constraints) {
  	WIF::Net con = assert_net;
      const bool assert_net_is_custom = net_is_custom(assert_net);
      if (assert_net_is_custom)  {
        if (strcmp(net_custom_op(assert_net)->name(),"SAFETY_AUTOMATON")) {
          new_constraints.push_back(con);
          continue;
        }
        WIF::Net clock = net_ntharg(assert_net, 1);
        assert_net = net_ntharg(assert_net, 0);
      }
      if (assert_net == bit_one())
        continue;
      if (net_isconst(assert_net))
      {
        assert(net_constval(assert_net).is_bit());
        if (net_constval(assert_net).get_bit_val() == WIF::bit_1)
            continue;
        //else something wrong. How can we have a trivial false constraint
      }
      new_constraints.push_back(con);
  }
  if (new_constraints.size())
    constraints = new_constraints;
  else
    constraints.clear();
}

void MyEngine::inlineConstraints(WIF::NetMap<WIF::Net> &subs) {
    int inline_con = option_get("inline");
    int v = option_get("verb");
    WIF::NetSet repr;
    if (!inline_con) return;
    for (auto assert_net : constraints) {
    		WIF::Net orig = assert_net;
        const char *name = get_net_name(assert_net);
        if (!name) name = "??";
        const bool assert_net_is_custom = net_is_custom(assert_net);
        if (assert_net_is_custom)  {
          if (strcmp(net_custom_op(assert_net)->name(),"SAFETY_AUTOMATON")) continue;
          WIF::Net edge = net_ntharg(assert_net, 1);
          if (net_is_custom(edge))
            edge = net_ntharg(edge,0);
          bool is_simple = edge == bit_one() || m_simple_clocks.count(edge);
          if (!is_simple) {
              std::cout <<"Cannot inline constraint " << name << "\n";
              continue;
          }
          assert_net = net_ntharg(assert_net, 0);
        }
        WIF::Op op = net_op(assert_net);
        if (op == WIF::Eq) {
            inlineEQ(assert_net, subs, repr);
        }
        // We need to see if this is AND and then push it to both branches of AND. Similarly we need to treat each operator differently
        else if (op == WIF::And) {
          std::vector<WIF::Net> eqlist;
          flattenAnd(assert_net, eqlist);
          for (auto& eq : eqlist) {
            if (net_op(eq) == WIF::Eq)
              inlineEQ(eq, subs, repr);
            else if (net_op(eq) != WIF::Const) {
              subs[eq] = bit_one();
            }
          }
        } else if (op != WIF::Const)
          subs[assert_net] = bit_one();
        if (v)
          std::cout <<"Inline constraint " << name << "\n";
    }
}

void MyEngine::inlineEQ(const WIF::Net& eq, WIF::NetMap<WIF::Net>& subs, WIF::NetSet& repr) {
	WIF::Net one = net_ntharg(eq,0);
	WIF::Net two = net_ntharg(eq,1);
	WIF::Net replace, keep;
  if (subs.count(one)) {
    keep = subs[one];
    replace = two;
  } else if (subs.count(two)) {
    keep = subs[two];
    replace = one;
  } else if (net_op(one) == WIF::Var) {
    keep = two;
    replace = one;
  } else {
    repr.insert(one);
    keep = one;
    replace = two;
  }
  //keep = findRepr(keep, subs);
  subs[replace] = keep;
  int v = option_get("verb");
  if (v > 1)
    std::cout <<"inlineEQ:: replacing " << safe_net_name(replace) << " by " << safe_net_name(keep) << "\n";
}
//This is a hack and there has to be a better way

//void MyEngine::fixConstraints(WIF::NetMap<WIF::Net> &subs)
//{
//    std::vector<WIF::Net> new_constraints;
//    int do_clock = g_clock_opt;
//    for (auto assert_net : constraints) {
//        const bool assert_net_is_custom = net_is_custom(assert_net);
//        if (!assert_net_is_custom) continue;
//        if (assert_net_is_custom &&
//            (!strncmp(net_custom_op(assert_net)->name(), "CLOCK_AUTOMATON", 15))) {
//             JGClockProp* cprop = dynamic_cast<JGClockProp*>(net_custom_op(assert_net));
//             if (cprop->initial == 1) {
//            	 	 WIF::Net n = net_ntharg(assert_net,0);
//                 m_simple_clocks.insert(n);
//                 assert(n.is_bit());
//                 if (do_clock)
//                   subs[n] = bit_zero();
//                 //set_net_name(n,JG_SYSCLK_VAR_NAME);
//                 continue;
//             }
//             new_constraints.push_back(assert_net);
//             assert(cprop);
//        }
//        else
//            new_constraints.push_back(assert_net);
//    }
//    if (!do_clock)
//      return;
//    constraints = new_constraints;
//    if (subs.size())
//      collectEdgesToSubstitute(subs);
//}

void writeWIF(WIF::Engine* e, const char* name)
{
    MyEngine* leng = new MyEngine(false);
    WIF::Pipe_Res res_pipe =  e->pipe_problem(leng);
    leng->removeTrivalConstraints();
    leng->option_set("dump_map", 2);
    std::stringstream ss;
    ss << name <<"__out.wif";
    std::ofstream ofs(ss.str().c_str(), std::ofstream::out);
    leng->write(ofs);
    ofs.close();
    std::cout <<"Writing new wif file " << ss.str() <<"\n";
}

void MyEngine::selectCheck()
{
	if (Config::g_single_property) {
		std::vector<WIF::Check> new_checks;
		bool found = false;
		for (auto ck: checks) {
			string p = ck.get_name();
			if (endsWith(p, config->get_arg(SELECT_PROPERTY))) {
				if (found) {
					wif_logw("multiple checks matching with selected property " << config->get_arg(SELECT_PROPERTY));
					wif_logw("ignoring matched check " << p << " as property");
				}
				else {
					wif_log("\t(selecting matched check " << p << " as property)\n");
					found = true;
					new_checks.push_back(ck);
				}
			}
		}
		if (!found) {
			wif_loge("no check matches with property name " << config->get_arg(SELECT_PROPERTY));
	//			wif_logw("no check matches with property name " << config->get_arg(SELECT_PROPERTY));
	//			wif_logw("selecting all properties");
		}
		checks = new_checks;
	}
}

void MyEngine::collect_subs()
{
    std::vector<WIF::Net> new_constraints;
    WIF::NetMap<WIF::Net> subs;
    for (auto assert_net : constraints) {
        const bool assert_net_is_custom = net_is_custom(assert_net);
//        assert(assert_net_is_custom);
        if (assert_net_is_custom &&
            (!strncmp(net_custom_op(assert_net)->name(), "CLOCK_AUTOMATON", 15))) {
             JGClockProp* cprop = dynamic_cast<JGClockProp*>(net_custom_op(assert_net));
             if (cprop->initial == 1) {
                 WIF::Net n = net_ntharg(assert_net,0);
                 m_simple_clocks[n] = bit_one();
                 assert(n.is_bit());
                 g_fast_clocks.insert(net_name(n));
                 subs[n] = bit_zero();
                 wif_log("\tinserting simple clock: " << net_name(n) << "\n");
//                 new_constraints.push_back(eq(n, bit_zero()));
//                 continue;
             }
             new_constraints.push_back(assert_net);
             assert(cprop);
        }
        else
            new_constraints.push_back(assert_net);
    }
    constraints = new_constraints;

    new_constraints.clear();
    for (auto assert_net : constraints) {
    	const bool assert_net_is_custom = net_is_custom(assert_net);
			if (assert_net_is_custom) {
				if (!strncmp(net_custom_op(assert_net)->name(), "SAFETY_UPTO", 11)
//				if (!strncmp(net_custom_op(assert_net)->name(), "SAFETY_UPTO", 11) ||
//						!strncmp(net_custom_op(assert_net)->name(), "SAFETY_AUTOMATON", 16)
					 ) {
				 WIF::Net n = net_ntharg(assert_net,1);
				 if (net_is_custom(n)) {
					if (!strcmp(net_custom_op(n)->name(),"POSEDGE")) {
						WIF::Net edgeVar = net_ntharg(n, 0);
						if (m_simple_clocks.count(edgeVar)) {
							net_set_ntharg(assert_net, 1, bit_one());
							wif_log("\t(setting enable for upto/constraint net to true: " << net_name(assert_net) << ")\n");
						}
					}
				 }
				}
			}
		 new_constraints.push_back(assert_net);
    }
    constraints = new_constraints;

//    if (false && subs.size()) {
//      collectEdgesToSubstitute(subs);
////      clock_opt = false;
////      if (clock_opt)
//			if (false)
//      {
//				substitute(subs, true);
//				substitute(subs, true);			// required
//				for (auto& n : subs) {
//					std::string str = n.second == bit_one() ? "True" : n.second == bit_zero() ? "False" : get_net_name(n.second);
//					std::cout <<"Substituting " << get_net_name(n.first) << " = " << str << "\n";
//				}
//      }
//      else {
//      	wif_log("\t(clock opt disabled due to complex edge triggers)\n");
//      }
//    }
}
    
void MyEngine::replace_subs()
{
	return;
	if (!g_fast_clocks.empty()) {
  	WIF::NetMap<WIF::Net> g_subs;
  	WIF::NetSet done;
  	for (const auto& check : checks) {
  			const WIF::Net& cnet = check_safety_net(check);
  			replace_subs(cnet, done, g_subs);
  	}

  	for (auto assert_net : constraints) {
  		replace_subs(assert_net, done, g_subs);
  	}

  	substitute(g_subs, true);
  }
}

void MyEngine::replace_subs(const WIF::Net& n, WIF::NetSet& done, WIF::NetMap<WIF::Net>& g_subs)
{
  if (done.find(n) != done.end())
    return;
  done.insert(n);
  for (int i=0;i<net_numargs(n); i++) {
  	WIF::Net arg = net_ntharg(n,i);
  	replace_subs(arg,done,g_subs);
  }

	WIF::Net v = n;
	if (v.is_bit()) {
		WIF::Op nop = net_op(v);
//		if (nop == WIF::Not)
//			v = net_ntharg(v, 0);
		if (net_numargs(v) == 0) {
			if (g_fast_clocks.find(net_name(v)) != g_fast_clocks.end()) {
				wif_log("substituting simple clock: " << net_name(n) << "\n");
				g_subs[v] = bit_zero();
//							net_set_ntharg(n, i, bit_zero());
			}
		}
	}
}


//bool MyEngine::collectEdgesToSubstitute(const WIF::Net& net, WIF::NetMap< bool > &done, WIF::NetMap<WIF::Net>& subs)
//{
//	WIF::NetMap< bool >::iterator mit = done.find(net);
//	if (mit != done.end())
//        return (*mit).second;
//  done[net] = false;
//
//  if (has_simple_clock[net] == false)
//  	return false;
//
//  for (int i=0;i<net_numargs(net); i++) {
//  	WIF::Net arg = net_ntharg(net,i);
//    collectEdgesToSubstitute(arg,done,subs);
//  }
//
//  if (net_is_custom(net)) {
//		if (!strcmp(net_custom_op(net)->name(),"POSEDGE")) {
//			WIF::Net edgeVar = net_ntharg(net, 0);
//			{
//				bool substituted = false;
//				if (m_simple_clocks.count(edgeVar)) {
//					subs[net]=bit_one();
//					substituted = true;
//				}
//				else {
//					WIF::Op nop = net_op(edgeVar);
//					if (nop == WIF::And) {
//						WIF::Net a = net_ntharg(edgeVar,0);
//						WIF::Net b = net_ntharg(edgeVar,1);
//						if (net_is_custom(b) && !strcmp(net_custom_op(b)->name(),"LATCH")) {
//#if 0
//							if (has_simple_clock[a] == true) {
//								vector<WIF::Net> veca;
//								veca.push_back(a);
//								WIF::Net posa = custom(net_custom_op(net), bit_type(), veca);
//								collectEdgesToSubstitute(posa,done,subs);
//
//								string n;
//								if (subs.count(posa)) {
//									posa = subs[posa];
//									n = string(net_name(posa));
//								}
//								else {
//									n = "pos_" + string(net_name(a));
//									set_net_name(posa, n.c_str());
//								}
//
//								WIF::Net posa_b = net_and(bit_type(), posa, b);
//								n = n + "_and_" + net_name(b);
//								set_net_name(posa_b, n.c_str());
//								subs[net] = posa_b;
//								substituted = true;
//							}
//#else
//							WIF::Net en = net_ntharg(b,2);
//							WIF::Net nen = gen_not(en);
//							WIF::Net d = net_ntharg(b,1);
//							WIF::Net en_d = net_and(bit_type(), nen, d);
//							en_d = d;
//							if (nen == a) {
//								subs[net] = en_d;
//								substituted = true;
//								wif_log("\t(clock simplification substitution (latch): " << net_name(net) << " <- " << net_name(en_d) << ")\n");
//							}
//							else {
//								wif_logw("found possible issue with clock simplification and latch: " << net_name(net));
//								subs[net] = en_d;
//								substituted = true;
//								wif_log("\t(clock simplification substitution (latch?): " << net_name(net) << " <- " << net_name(en_d) << ")\n");
//							}
//#endif
//						}
//						else {
//							wif_logw("found possible issue with clock simplification: " << net_name(net));
//							if (m_simple_clocks.count(a)) {
//								subs[net] = b;
//								substituted = true;
//								wif_log("\t(clock simplification substitution (clk): " << net_name(net) << " <- " << net_name(b) << ")\n");
//							}
//						}
//					}
//				}
//				if (!substituted) {
//					wif_logw("unable to simplify clocking: " << net_name(net));
//					clock_opt = false;
//				}
//			}
//		}
//		else if (!strcmp(net_custom_op(net)->name(),"SAFETY_AUTOMATON")) {
//			WIF::Net edgeVar = net_ntharg(net, 1);
//			bool substituted = false;
//			if (m_simple_clocks.count(edgeVar)) {
//				net_set_ntharg(net, 1, bit_one());
////				subs[edgeVar]=bit_one();
////				substituted = true;
////				wif_log("\t(clock simplification substitution (safe): " << net_name(edgeVar) << " <- true" << ")\n");
//			}
//		}
//  }
//
//	return false;
//}
//
//void MyEngine::collectEdgesToSubstitute(WIF::NetMap<WIF::Net> &subs)
//{
//  for (auto& c : checks) {
//    const WIF::Net& net = check_safety_net(c);
//    hasSimpleClock(net);
//  }
//  for (auto& c : constraints) {
//  	hasSimpleClock(c);
//  }
//
//	WIF::NetMap< bool > done;
//  for (auto& c : checks) {
//    const WIF::Net& net = check_safety_net(c);
//    collectEdgesToSubstitute(net,done,subs);
//  }
//  for (auto& c : constraints) {
//    collectEdgesToSubstitute(c,done,subs);
//  }
//}
//
//bool MyEngine::hasSimpleClock(const WIF::Net& net) {
//	if (has_simple_clock.count(net))
//        return has_simple_clock[net];
//  has_simple_clock[net] = false;
//  bool ret_value = false;
//  for (int i=0;i<net_numargs(net); i++) {
//  	WIF::Net arg = net_ntharg(net,i);
//    ret_value |= hasSimpleClock(arg);
//  }
//
//	if (!ret_value) {
//		if (net_numargs(net) == 0) {
//			if (m_simple_clocks.count(net))
//				ret_value = true;
//		}
//	}
//	if (ret_value)
//		has_simple_clock[net] = true;
//	return ret_value;
//}

    
void MyEngine::traverse()
{
	WIF::NetSet done;
	for (const auto& check : checks) {
			const WIF::Net& cnet = check_safety_net(check);
			traverse(cnet, done);
	}

	for (auto assert_net : constraints) {
			traverse(assert_net, done);
	}
}

std::string MyEngine::getTypeString(const WIF::Net& n) {
    std::stringstream ss;
    if (n.is_bit())
        ss << "Bit";
    else
        ss << n.word_size();
     return ss.str();
}

void MyEngine::dumpVar(const WIF::Net& n)
{
    std::string name = get_net_name(n);
    std::cout <<" INPUT " << name << " -- type " << getTypeString(n) << "\n";
}

void MyEngine::traverse(const WIF::Net& n, WIF::NetSet& done)
{
    if (done.count(n))
        return;
    done.insert(n);
    WIF::Op op = net_op(n);
#ifdef _DUMP
    std::cout <<"//Traversing " << WIF::op_str[op] <<"\n";
#endif
    unsigned nargs = net_numargs(n);
    if (!nargs) {
#ifdef _DUMP
        dumpVar(n);
#endif
    }
    for (unsigned i = 0; i < nargs; i++) {
        const WIF::Net& arg = net_ntharg(n, i);
        WIF::Net v = arg;
        bool simplify = false;
        if (net_is_custom(v)) {
        	if (!strcmp(net_custom_op(v)->name(), "POSEDGE") || !strcmp(net_custom_op(v)->name(), "NEGEDGE")) {
						v = net_ntharg(v,0);
						simplify = true;
        	}
        }
//        if (!simplify) {
//        	if (v.is_bit()) {
//        		WIF::Op nop = net_op(v);
//            if (nop == WIF::Not) {
//            	v = net_ntharg(v, 0);
//  						if (net_numargs(v) == 0) {
//  							simplify = true;
//  						}
//            }
////            else {
////							if (net_numargs(v) == 0) {
////								simplify = true;
////							}
////            }
//        	}
//        }
        if (simplify) {
					bool is_simple = m_simple_clocks.count(v);
					if (is_simple)
							net_set_ntharg(n, i, bit_one());
        }
        traverse(arg, done);
    }
}

//Function to read in the WIF dump. This creates a default engine and returns it.
// All the checks are stored in the CheckTable
WIF::EngineStd* readWif(const string& filename) {
	WIF::CheckTable checksTable;
	WIF::SymbolTable naming;
	WIF::CustomOpFactory* factory =  wpi_get_custom_op_factory();
	wif_log("\t(reading WIF from " << filename << ")\n");
	WIF::EngineStd* wif = new WIF::EngineStd();
	WIF::wif_read(filename.c_str(),wif,naming,checksTable,jg_factory);
	for (auto& c : checksTable) {
		WIF::Check &ck = c.second;
		wif->set_check_name(ck, c.first);
//		WIF::Net& net = wif->check_safety_net(ck);
//		cout <<" Read check " << ck.get_name() << " Net Type " << wif->net_op(net) << " " << WIF::op_str[wif->net_op(net)] << "\n";
//		cout << "Check name " << c.first << "\t" << wif->check_name(ck) << "\n";
	}
//	for (auto& n : naming) {
//		WIF::Net& net = n.second;
//		cout << "Net name " << n.first << "\t" << wif->net_name(net) << "\n";
//	}
	return wif;
}

WIF::Engine* preprocess(WIF::Engine* e)
{
    MyEngine* leng = new MyEngine(false);
    WIF::Pipe_Res res_pipe =  e->pipe_problem(leng);
    leng->selectCheck();

//    if (clock_opt)
    {
    	// now done in pipe problem
//  		leng->collect_subs();
    }
    _resFile << "wif-simple-clock:\t" << (g_clock_opt?"true":"false") << "\n";

//			MyEngine* leng2 = new MyEngine(true);
//			res_pipe =  leng->pipe_problem(leng2);
//			leng2->replace_subs();
//			return leng2;

		return leng;
}

namespace _wif {

#define POSEDGE		0
#define NEGEDGE		1
#define LATCHEDGE 2

unsigned WifNode::_id = 0;

class WifOpEngine : public WIF::EngineStd {
  public:
		WifOpEngine(Engine* eng) {
			num_latches = 0;
			m_fastest_clk_tp = -1;
			fast_edges[POSEDGE] = false;
			fast_edges[NEGEDGE] = false;
			fast_edges[LATCHEDGE] = false;

			WIF::Pipe_Res res_pipe = eng->pipe_problem(this);
//			if (clock_opt)
				processConstraints();
		};
    bool supports_custom(WIF::CustomOp *cop) {	return true;	}
    Engine* get_engine() {	return this;	}

    list < WIF::NetSet > m_simple_clocks;
    int m_fastest_clk_tp;
    unordered_map< string, pair< int, int > > m_clk2tp;
  private:
    void processConstraints();
    void traverse(char mode);
    bool traverse(char mode, const WIF::Net& n, WIF::NetMap< bool >& done);
    bool clk_same(const WIF::Net& n1, const WIF::Net& n2);

    bool fast_edges[3];
    unsigned num_latches;
};

void WifOpEngine::processConstraints() {
	std::vector<WIF::Net> new_constraints;
	for (auto assert_net : constraints) {
		const bool assert_net_is_custom = net_is_custom(assert_net);
//		assert(assert_net_is_custom);
		if (assert_net_is_custom &&
			(!strncmp(net_custom_op(assert_net)->name(), "CLOCK_AUTOMATON", 15))) {
//			cout << "custom clk: " << net_name(assert_net) << "\n";
			JGClockProp* cprop = dynamic_cast<JGClockProp*>(net_custom_op(assert_net));
			WIF::Net n = net_ntharg(assert_net, 0);
			m_fastest_clk_tp = (m_fastest_clk_tp != -1) ? min(m_fastest_clk_tp, cprop->initial) : cprop->initial;
			m_clk2tp[net_name(n)] = make_pair(cprop->initial, cprop->offset);

			bool added = false;
			for (auto& ns: m_simple_clocks) {
				for (auto& sc: ns) {
					if (clk_same(sc, assert_net)) {
						added = true;
						ns.insert(assert_net);
						wif_logv("\t(clock: " << net_name(n) << " already present)\n");
					}
					break;
				}
				if (added)
					break;
			}
			if (!added) {
				wif_logv("\t(inserting clock: " << net_name(n) << ")\n");
				WIF::NetSet new_ns;
				new_ns.insert(assert_net);
				m_simple_clocks.push_back(new_ns);
			}
			new_constraints.push_back(assert_net);
		}
		else {
//			cout << "non-custom clk: " << net_name(assert_net) << "\n";
			new_constraints.push_back(assert_net);
		}
	}

	for (auto& ns: m_simple_clocks) {
		WIF::NetSet::iterator sit = ns.begin();
		const WIF::Net& lhs_net = (*sit);
		const WIF::Net& lhs = net_ntharg(lhs_net, 0);
		sit++;
		for (; sit != ns.end(); sit++) {
			const WIF::Net& rhs_net = (*sit);
			const WIF::Net& rhs = net_ntharg(rhs_net, 0);
			new_constraints.push_back(gen_eq(lhs, rhs));
			wif_log("\t(clock constraint: " << net_name(lhs) << " = " << net_name(rhs) << ")\n");
		}
	}

	wif_log("\t(found " << m_simple_clocks.size() << " true clocks)\n");
	constraints = new_constraints;

	_resFile << "wif-#clocks:\t" << m_simple_clocks.size() << "\n";
	wif_log("\t(found " << m_fastest_clk_tp << " to be lowest clock period, using as fastest)\n");
	if (m_fastest_clk_tp != 1) {
		m_fastest_clk_tp = 1;
		wif_logw("\t(forcing fastest clock period to 1)\n");
	}

	traverse('r');

	string edge_triggers = "";
	edge_triggers += (fast_edges[POSEDGE] ? "+_":"");
	edge_triggers += (fast_edges[NEGEDGE] ? "-_":"");
	edge_triggers += (fast_edges[LATCHEDGE] ? "l_":"");
	wif_log("\t(found edge triggers: " << edge_triggers << ")\n");

	_resFile << "wif-edge-triggers:\t" << edge_triggers << "\n";
	_resFile << "wif-#latches:\t" << num_latches << "\n";

	bool use_clk_simp = false;
//	if (m_simple_clocks.size() == 1)
	{
		if (num_latches != 0) {
			wif_log("\t(found " << num_latches << " latches)\n");
		}

		if (g_clock_opt) {
			g_clock_opt = false;
			if (!fast_edges[LATCHEDGE])
			{
				if (!fast_edges[POSEDGE] || !fast_edges[NEGEDGE]) {
					wif_log("\t(using clock simplification)\n");
					use_clk_simp = true;
					traverse('w');

					for (auto& ns: m_simple_clocks) {
						WIF::NetSet::iterator sit = ns.begin();
						const WIF::Net& lhs_net = (*sit);
						const WIF::Net& lhs = net_ntharg(lhs_net, 0);
						sit++;

						unordered_map< string, pair< int, int > >::iterator cit = m_clk2tp.find(net_name(lhs));
						if (cit != m_clk2tp.end()) {
							if ((*cit).second.first == m_fastest_clk_tp) {
								constraints.push_back(gen_eq(lhs, bit_zero()));
								wif_log("\t(clock constraint: " << net_name(lhs) << " = false" << ")\n");
							}
						}
					}
					g_clock_opt = true;
				}
			}
			else {
	//			wif_logw("design has latch / multiple edge triggers, skipping clock simplification");

	//			clock_opt = false;
			}
		}
	}

	_resFile << "wif-simple-clock2:\t" << (use_clk_simp?"true":"false") << "\n";
}

void WifOpEngine::traverse(char mode) {
    WIF::NetMap< bool > done;
    for (const auto& check : checks) {
        const WIF::Net& cnet = check_safety_net(check);
        traverse(mode, cnet, done);
    }

    for (auto& assert_net : constraints) {
        traverse(mode, assert_net, done);
    }
}

bool WifOpEngine::traverse(char mode, const WIF::Net& n, WIF::NetMap< bool >& done) {
	WIF::NetMap< bool >::iterator mit = done.find(n);
	if (mit != done.end())
        return (*mit).second;
  done[n] = false;
  bool ret_value = false;
//	cout << "Net " << net_name(n) << endl;
	WIF::Op op = net_op(n);
	unsigned nargs = net_numargs(n);
//	cout << "Net " << net_name(n) << "\t" << nargs << "\t" << op << endl;
	for (unsigned i = 0; i < nargs; i++) {
			WIF::Net arg = net_ntharg(n, i);
			if (net_is_custom(arg)) {
				if (!strcmp(net_custom_op(arg)->name(), "POSEDGE") || !strcmp(net_custom_op(arg)->name(), "NEGEDGE")) {
					if (mode == 'r') {
						WIF::Net clk = net_ntharg(arg,0);
						unordered_map< string, pair< int, int > >::iterator cit = m_clk2tp.find(net_name(clk));
						if (cit != m_clk2tp.end()) {
							if ((*cit).second.first == m_fastest_clk_tp) {
								if (net_custom_op(arg)->name() == "POSEDGE")
									fast_edges[POSEDGE] = true;
								else
									fast_edges[NEGEDGE] = true;
							}
						}
					}
					else {
						assert(mode == 'w');
						WIF::Net clk = net_ntharg(arg,0);
						unordered_map< string, pair< int, int > >::iterator cit = m_clk2tp.find(net_name(clk));
						if (cit != m_clk2tp.end()) {
							if ((*cit).second.first == m_fastest_clk_tp) {
								if ((*cit).second.second != 0) {
									wif_logw("offset for fastest clock " << net_name(clk) << " is ignored");
								}
								net_set_ntharg(n, i, bit_one());
								arg = net_ntharg(n, i);
//								wif_log("\t(clock simplification (edge): " << net_name(n) << "\t:\t" << net_name(clk) << " <- true" << ")\n");
							}
						}
					}
				}
			}
			ret_value |= traverse(mode, arg, done);
	}

	if (mode == 'w') {
		if (net_is_custom(n)) {
			if (!strcmp(net_custom_op(n)->name(), "SAFETY_AUTOMATON")) {
				WIF::Net clk = net_ntharg(n,1);
				unordered_map< string, pair< int, int > >::iterator cit = m_clk2tp.find(net_name(clk));
				if (cit != m_clk2tp.end()) {
					if ((*cit).second.first == m_fastest_clk_tp) {
						if ((*cit).second.second != 0) {
							wif_logw("offset for fastest clock " << net_name(clk) << " is ignored");
						}
						net_set_ntharg(n, 1, bit_one());
						wif_log("\t(clock simplification (safe): " << net_name(n) << "\t:\t" << net_name(clk) << " <- true" << ")\n");
					}
				}
			}
		}
	}

	if (mode == 'r') {
		if (net_is_custom(n)) {
			if (!strcmp(net_custom_op(n)->name(), "LATCH")) {
				num_latches++;

//				cout << "latch: " << net_name(n) << " #args = " << nargs << endl;
//				for (unsigned i = 0; i < nargs; i++) {
//					const WIF::Net& arg = net_ntharg(n, i);
//					cout << "\targ: " << net_name(arg) << endl;
//				}

				assert(nargs == 3);
				const WIF::Net& carg = net_ntharg(n, 2);
				WIF::NetMap< bool >::iterator cmit = done.find(carg);
				assert (cmit != done.end());
				if ((*cmit).second) {
					fast_edges[LATCHEDGE] = true;
				}
			}
		}

		if (!ret_value) {
			unordered_map< string, pair< int, int > >::iterator cit = m_clk2tp.find(net_name(n));
			if (cit != m_clk2tp.end()) {
				if ((*cit).second.first == m_fastest_clk_tp)
					ret_value = true;
			}
		}
		if (ret_value)
			done[n] = true;
	}
	return ret_value;
}

bool WifOpEngine::clk_same(const WIF::Net& n1, const WIF::Net& n2) {
	JGClockProp* c1 = dynamic_cast<JGClockProp*>(net_custom_op(n1));
	assert(c1);
	JGClockProp* c2 = dynamic_cast<JGClockProp*>(net_custom_op(n2));
	assert(c2);
	return (c1->initial == c2->initial) && (c1->offset == c2->offset) && (c1->period == c2->period) && (c1->width == c2->width);
}


class WifParser : public WIF::EngineStd {
  public:
	WifParser(string filename, string wifoptions, string ps, list< WifNode >* np = NULL, list< pair< string, WifNode* > >* sp = NULL, list< WifNode* >* ap = NULL) {
		prop_select = ps;	nodes_p = np;	safetychecks_p = sp;	assumes_p = ap;	op_eng = NULL;
    if (!read_ts(filename, wifoptions)) {
        wif_loge("unable to read input file " << filename);
    }
	}
	bool read_ts(string filename, string wifoptions);

	list< WifNode >* nodes_p;
	list< pair< string, WifNode* > >* safetychecks_p;
	list< WifNode* >* assumes_p;
  private:
		bool supports_custom(WIF::CustomOp *cop){	return false;	}
    void traverse();
    void traverse(const WIF::Net& n, WIF::NetSet& done);
    string getTypeString(const WIF::Net& n);
    void dumpVar(const WIF::Net& n);
    void process();
    WifNode* process_net(const WIF::Net& n);

    WIF::NetMap< WifNode* > net2node;
    WifOpEngine* op_eng;
    string prop_select;
};

bool WifParser::read_ts(string filename, string inoptions) {
	jg_factory = &TheJGWpiOpFactory;
	Engine* wif_eng;
	vector<Engine*> pipe;
  assert (!filename.empty());

  string wifoptions = "";
  if (inoptions != "-") {
  	wifoptions = "-" + inoptions;
  	std::replace(wifoptions.begin(), wifoptions.end(), '+', ' ');
  }

//	wifoptions += " -e simp";
//	wifoptions += " -e cut";
//	wifoptions += " -e bb";
//	wifoptions += " -e write -file " + filename + "_out.wif";
//	wifoptions += " -e simp -e cut -e bb -e lower -e lower -e writebs -file " + filename + "_out.bs";
//	wifoptions += " -e simp -e cut -e lower -no_lower SAFETY_UPTO_1 -e bb -e writebs -file " + filename + "_out.bs";

  wif_log("\t(jg preprocess options: " << wifoptions << ")\n");

  vector< string > args;
  istringstream iss(wifoptions);
  string token;
  while(iss >> token) {
//  	cout << "token: " << token << endl;
  	if (token[0] == '-') {
    	args.push_back("-");
    	token.erase(0, 1);
//    	cout << "new token: " << token << endl;
    }
    args.push_back(token);
  }
	int numc = 0;

//	wif_log("\t(wif options)\n");
//	for (auto& v: args) {
//		wif_log("\t\t" << v << "\n");
//	}

	try {
		while (numc < args.size()) {
			if (args[numc] == "-") {
				numc++;
				if(numc == args.size())
					throw usage("expecting option after -");
				string flag = args[numc];
//				cout << "flag: " << flag << "\n";
				if(flag == "help"){
					if(pipe.size() == 0)
						generic_help();
					else
						engine_help(pipe.back());
					return 0;
				}
        if (flag == "latch_opt")
         g_local_latch = !g_local_latch;
        else if (flag == "clock_opt")
					g_clock_opt = !g_clock_opt;
        else if(WIF::Option *opt = WIF::OptionRegistry<WIF::Option>::get(flag)){
          std::string argument;
          if(opt->needs_argument()){
  					numc++;
  					if(numc == args.size()) {
              std::string msg("expecting value for option ");
              msg += flag;
              throw usage(msg);
            }
            argument = args[numc];
          }
          opt->parse(argument);
        }
				else if(flag == "e") { // a new engine in the pipe
					numc++;
					if(numc == args.size())
						throw usage("expecting engine name after -e");
					Engine *eng=0;
					string eng_name = args[numc];
//					cout << "eng_name: " << eng_name << "\n";
					eng = WIF::new_engine(eng_name.c_str(),"(no name)","(no instance)");
					if(!eng)
						throw misc_error(string("unknown engine:") + args[numc]);
					pipe.push_back(eng);
				}
				else { // an engine option
					if(!pipe.size())
						throw usage("unexpected option: -" + flag);
//					cout << "option: " << args[numc] << "\n";
					WIF::Option_Type type;
					int optval;
					Engine *eng = pipe.back();
					if(option_find(eng,flag,type)){
						numc++;
						if(numc == args.size())
							throw usage("expecting value for option -" + flag);
						sscanf(args[numc].c_str(),"%d",&optval);
						if(type == WIF::option_int)
							eng->option_set(flag.c_str(),optval);
						else
							eng->char_option_set(flag.c_str(),args[numc].c_str());
					}
					else
						throw misc_error(flag + " is not valid option ");
				}
			}
			numc++;
		}
		// parse the input file
		wif_eng = readWif(filename);
	}
	catch(const WIF::wif_parse_error &p){
		if(p.filename.size())
			cerr << p.filename << ": ";
		if(p.line_number)
			cerr << p.line_number << ": ";
		cerr << p.msg << "\n";
		wif_loge("wif parse error, exiting.");
		return 1;
	}
	catch(const usage &u){
		cerr << u.msg << "\n";
		cerr << usage_string;
		wif_loge("wif usage error, exiting.");
		return 1;
	}
	catch(const misc_error &u){
		cerr << u.msg << "\n";
		wif_loge("wif misc error, exiting.");
		return 1;
	}

	wif_eng = preprocess(wif_eng);
	for(int i = 0; i < pipe.size(); i++){
		try{
			wif_log("\t(running engine: " << pipe[i]->engine_name() << ")\n");
			if (!i)
				wif_eng->pipe_problem(pipe[i]);
			else
				pipe[i-1]->pipe_problem(pipe[i]);
		}
		catch(const std::bad_alloc &b){
			printf("out of memory\n");
			return 0;
		}
	}
	if (pipe.size()) {
		try{
			pipe.back()->solve();
		}
		catch (bad_alloc){
			printf("out of memory\n");
		}
	}
	if (!pipe.empty())
		wif_eng = pipe.back();

//	if (prop_select != "-") {
//		bool found = false;
//		pair< string, WIF::Check> singleP;
//		cout << "#checks: " << checksTable.size() << endl;
//		for (auto& c : checksTable) {
//			string ckName = c.first;
//			cout << "check: " << ckName << endl;
//			if (endsWith(ckName, prop_select)) {
//				if (found) {
//					wif_logw("multiple checks matching with selected property " << prop_select);
//					wif_logw("ignoring matched check " << ckName << " as property");
//				}
//				else {
//					wif_log("\t(selecting matched check " << ckName << " as property)\n");
//					found = true;
//					singleP = make_pair(ckName, c.second);
//				}
//			}
//		}
//		if (!found) {
//			wif_loge("no check matches with property name " << prop_select);
//		}
//		else {
////			checksTable.clear();
////			checksTable[singleP.first] = singleP.second;
//
//			clear_checks();
//			checks.push_back(singleP.second);
//
////			for (std::vector<WIF::Check>::iterator m = checks.begin(); m != checks.end();) {
////				if ((*m).get_name() == singleP.first) {
////					m++;
////				}
////				else {
////				}
////			}
//		}
//	}

	op_eng = new WifOpEngine(wif_eng);
	Engine* fix_eng = op_eng->get_engine();
	WIF::Pipe_Res res_pipe = fix_eng->pipe_problem(this);
	process();
//	traverse();
//    option_set("dump_map", 2);
//    write(cout);

	delete op_eng;
	delete wif_eng;
	return true;
}

void WifParser::traverse() {
	WIF::NetSet done;
	for (const auto& check : checks) {
			const WIF::Net& cnet = check_safety_net(check);
			traverse(cnet, done);
	}
	for (auto assert_net : constraints) {
	traverse(assert_net, done);
	}
}

void WifParser::traverse(const WIF::Net& n, WIF::NetSet& done) {
	// check if net already present
	if (done.count(n))
		return;
	// insert as done
	done.insert(n);

	// get net op
	WIF::Op op = net_op(n);
	cout <<"Net " << net_name(n) << " of type " << WIF::op_str[op] <<"\n";

	// get arguments
	unsigned nargs = net_numargs(n);
	cout <<"#ch = " << nargs <<"\n";

	// no arguments means input
	if (!nargs) {
		dumpVar(n);
	}

	for (unsigned i = 0; i < nargs; i++) {
		const WIF::Net& arg = net_ntharg(n, i);
		cout <<"\tch" << i << " " << net_name(arg) <<"\n";
	}

	// iterate over arguments
	for (unsigned i = 0; i < nargs; i++) {
		const WIF::Net& arg = net_ntharg(n, i);
		traverse(arg, done);
	}
}

void WifParser::dumpVar(const WIF::Net& n) {
    string name = net_name(n);
    cout <<"input " << name << " -- type " << getTypeString(n) << "\n";
}

string WifParser::getTypeString(const WIF::Net& n) {
    stringstream ss;
    if (n.is_bit())
        ss << "bool";
    else
        ss << "bv" << n.word_size();
     return ss.str();
}

void WifParser::process() {
	WifNode::setup_op();

//	cout << "statevars: " << "\n";
//	std::vector<WIF::Net>& statevars = get_state_vars();
//	for (auto& cnet: statevars) {
//		cout << "sv: " << net_name(cnet) << "\n";
//		process_net(cnet);
//    }

	assert(safetychecks_p != NULL);
	int count = 0;
	for (const auto& check : checks) {
		count++;
		const WIF::Net& cnet = check_safety_net(check);
		string ckName = check_name(check);
		if (ckName == "")
			ckName = "check$" + to_string(count);
        safetychecks_p->push_back(make_pair(ckName, process_net(cnet)));
        wif_log("\t(check: " << ckName << ")\n");
    }

	assert(assumes_p != NULL);
	std::vector<WIF::Net>& constraints = get_constraints();
	for (auto& cnet: constraints) {
        assumes_p->push_back(process_net(cnet));
//		cout << "assume: " << net_name(cnet) << "\n";
    }
}

WifNode* WifParser::process_net(const WIF::Net& n) {
	WIF::NetMap< WifNode* >::iterator nit = net2node.find(n);
	if (nit != net2node.end())
		return (*nit).second;

	nodes_p->push_back(WifNode());
	WifNode& w = nodes_p->back();
	net2node[n] = &w;
	WifNode::_id++;

	w.name = net_name(n);
	w.size = n.is_bit() ? 1 : n.word_size().get_si();
	w.attr = "";
	string t = WIF::op_str[net_op(n)];
	unordered_map < string, WifOp >::iterator mit = m_wifop.find(t);
	if (mit == m_wifop.end()) {

	}
	w.type = (*mit).second;
	w.id = WifNode::_id;

	switch (w.type) {
	case wConst:
		{
			WIF::Value v = net_constval(n);
			if (n.is_bit()) {
				switch(v.get_bit_val()) {
				case WIF::bit_0:
					w.attr = "0";
					break;
				case WIF::bit_1:
					w.attr = "1";
					break;
				default:
			        wif_loge("unsupported binary constant value " << v.get_bit_val() << " for net " << w.name);
				}
			}
			else
				w.attr = v.binary_value().get_str(10);
		}
		break;
	case wBfe:
		{
			int lsb = net_bfe_shift(n);
			w.attr = to_string(lsb);
		}
		break;
	}

	// get arguments
	unsigned nargs = net_numargs(n);
	for (unsigned i = 0; i < nargs; i++) {
		const WIF::Net& arg = net_ntharg(n, i);
		WifNode* argWire = process_net(arg);
		w.args.push_back(argWire);
	}

	wif_logvv("(wif node) " << w.print() << "\n");
	return &w;
}


WifConvert::WifConvert(string filename, string wifoptions, string ps) {
	wp = new WifParser(filename, wifoptions, ps, &nodes, &safetychecks, &assumes);
}

WifConvert::~WifConvert() {
	delete wp;
}




}
