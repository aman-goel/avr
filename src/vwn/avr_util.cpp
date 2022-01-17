/************************************************************************************
* AVR: Abstractly Verifying Reachability
*
* Copyright (c) 2016 - Present  Aman Goel and Karem Sakallah, University of Michigan.
* All rights reserved.
*
* Author: Aman Goel (amangoel@umich.edu), University of Michigan
************************************************************************************/


#include "avr_util.h"

int global_debug_level[20];
string global_loc_tag[20] = {
// global_loc_tag[10] = "CONF"
	"PRE", "CTI", "BP", "FP", "DPR", "TB-D", "TB-BP", "CC", "RES", "EVAL", "CONF", "SOLV", "WN"
//preprocessing, CTI-check, backward-propagation, forward-propagation, datapath-refinement, trace-back_CTI, 
//trace-back_backward_propagation, containment_check, eval_formula&term, config, solver, word-leve_netlist
};
unsigned verbosity = 0;

long long Timevaldiff(struct timeval *starttime, struct timeval *finishtime)
{
  long long msec;
  msec=(finishtime->tv_sec-starttime->tv_sec)*1000000;
  msec+=(finishtime->tv_usec-starttime->tv_usec);
  return msec;
}

string get_path_from_fname(string fname){
	string res = "";
	unsigned last_slash = 0;
	for(unsigned i = 0; i < fname.size();i++){
		if(fname[i]=='/'){
			last_slash = i;
		}
	}
	if(last_slash!=0)
		res = fname.substr(0,last_slash+1);
	return res;
}

string remove_path_from_fname(string fname){
	string res = "";
	unsigned last_slash = 0;
	for(unsigned i = 0; i < fname.size();i++){
		if(fname[i]=='/'){
			last_slash = i;
		}
	}
	if(last_slash!=0)
		res = fname.substr(last_slash+1);
	return res;
}


// Bell Number computation
// source: http://www.michaelmampaey.com/stuff/bell-number-computation/
// The following piece of C++ source code calculates the natural logarithm of the n-th Bell Number, 
// i.e., the number of ways to partition a set of n elements. 
// The function is based on the triangle algorithm, and requires O(n^2) time, and O(n) memory. 
// The computations are done in double precision, so no additional libraries are necessary. 
// The results have been verified to have a relative error of at most O(10^-15) for n up to one thousand.

double log_bell_number(int n){
 if (n == 0)
  return 0.0;
 
 double * t0 = new double[n];
 double * t1 = new double[n];
 
 t0[0] = 0.0;
 
 for (int i=1; i<n; ++i) {
  t1[0] = t0[i-1];
  for (int j=0; j<i; ++j)
   t1[j+1] = log(exp(t1[j]-t0[j]) + 1.0) + t0[j];
  swap(t0, t1);
 }
 
 double result = t0[n-1];
 
 delete [] t0;
 delete [] t1;
 
 return result;
}

