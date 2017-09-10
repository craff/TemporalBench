#include "PLTLFormula.h"
#include "PLTLMisc.h"
#include <bdd.h>

#include <algorithm>
#include <assert.h>
#include <sys/time.h>
#include <stdlib.h>
#include <unistd.h>
#include <getopt.h>
#include <iostream>

std::vector<bdd> arrayBDD;
std::vector<bdd> arrayBDDdash;
std::vector<int> arrayVarLookup;

static struct{
  int satcheck    ;
  int validcheck  ;
  int verbose     ;
  int silent      ;
  int echoInput   ;
  int validStop   ;
  int satStop     ;
  int reorder     ;
  int autoreorder ;
  int reorderInit ;
  int assumeG     ;
  int normalise   ;
  int sortand     ;
  int nary        ;
} args;

void initArgs() {
  args.satcheck     = 0;
  args.validcheck   = 0;
  args.verbose      = 0;
  args.silent       = 0;
  args.echoInput    = 0;
  args.validStop    = 0;
  args.satStop      = 1;
  args.reorder      = 0;
  args.autoreorder  = 0;
  args.reorderInit  = 0;
  args.assumeG      = 1;
  args.normalise    = 1;
  args.sortand      = 1;
  args.nary         = 0;
}

#define info_msg(m,v) \
  do {if (args.verbose >= (v)) { \
	  (m);						 \
	  }							 \
  }	while(false)

float time_diff(struct timeval& t1, struct timeval& t2) {
  return ((t2.tv_sec - t1.tv_sec) +
		  (t2.tv_usec - t1.tv_usec)/(1000000.0f));
}


void silent_gbc_handler(int pre __attribute__((unused)) , bddGbcStat * stat __attribute__((unused))) {
  // do nothing
}

bool bddCompFunc(const bdd& a, const bdd& b) {
  //  std::cout << "SORTING " << a << " AND " << b  << "\n";
  if (a == bddtrue) return (b != bddtrue);
  if (b == bddtrue) return true;
  if (a == bddfalse) return (b != bddfalse);
  if (b == bddfalse) return true;
  return bdd_var2level(bdd_var(a)) < bdd_var2level(bdd_var(b));
  // If a is higher-up the BDD tree than b, put it earlier in the vector order.
  // This is because we traverse the vector backwards, and we want to handle lower-down BDDs first.
}

bool bddCompFunc2(const bdd& a, const bdd& b) {
  if (a == bddtrue) return (b != bddtrue);
  if (b == bddtrue) return true;
  if (a == bddfalse) return (b != bddfalse);
  if (b == bddfalse) return true;
  return bdd_nodecount(a) < bdd_nodecount(b);
}

bdd bigOr(std::vector<bdd>& v) {
  {
	std::vector<bdd>::iterator it = v.begin();
	while(it != v.end()){
	  if (*it == bddtrue) return bddtrue;
	  if (*it == bddfalse) {
		v.erase(it);
		it = v.begin();
	  } else {
		++it;
	  }
	}
  }
  if (v.empty()) return bddfalse;

  if (args.sortand) {
	sort(v.begin(), v.end(), bddCompFunc);
  }

  bdd ret = v.back();
  v.pop_back();

  while(!v.empty()) {
	ret |= v.back();
	v.pop_back();
  }
  return ret;
}

bdd bigAnd(std::vector<bdd>& v, int reorder = 0, bool (*compfunc)(const bdd&, const bdd&) = bddCompFunc) {
  {
	// My sort function is terrible at constants apparently! Make sure not to have any!
	std::vector<bdd>::iterator it = v.begin();
	while(it != v.end()){
	  if (*it == bddfalse) return bddfalse;
	  if (*it == bddtrue) {
		v.erase(it);
		it = v.begin();
	  } else {
		++it;
	  }
	}
  }
  if (v.empty()) return bddtrue;

  if (args.sortand) {
	sort(v.begin(),v.end(), compfunc);
  }


  bdd ret = v.back();
  v.pop_back();

  int count = reorder;
  while(!v.empty()) {
	info_msg(std::cout << "bigAnd about to and...\n",5);
	ret &= v.back();
	v.pop_back();

	if (reorder > 0) {
	  if (count == 0) {
		info_msg(std::cout << "bigAnd causing reordering...\n",5);
		bdd_reorder(BDD_REORDER_SIFT);
		if (args.sortand) {
		  sort(v.begin(),v.end(), compfunc);
		}
		count = reorder;
	  }
	  --count;
	}

  }

  info_msg(std::cout << "bigAnd finished!\n",5);

  return ret;
}

void mkbdd(int i); // forward declaration for mutual recursion!

// Perform an n-ary op, either AND or OR
void naryOp(PLTLFormula::PLTLFormulaType op, int i, std::vector<bdd>& v, std::vector<bdd>& vdash){
  if (arrayBDD[i] != bddtrue) {
	// If it is already computed, reuse it
	v.push_back(arrayBDD[i]);
	vdash.push_back(arrayBDDdash[i]);
  } else if (arrayType[i] == op) {
	// If it is this operation, collect from both sides
	naryOp(op,arrayDest1[i],v,vdash);
	naryOp(op,arrayDest2[i],v,vdash);
  } else {
	// If it is a leaf, then compute the BDD for the leaf
	mkbdd(i);
	v.push_back(arrayBDD[i]);
	vdash.push_back(arrayBDDdash[i]);
  }
}

// Construct the BDD atoms and formulae from the closure, assumed to be in the array* lists from IntKtMisc
void mkbdd(int i) {

  assert(!arrayFormula.empty());

  if (arrayBDD[i] != bddtrue) {
	// We have already handled this; no need to do it again
	return;
  } else if (arrayBDD[arrayNeg[i]] != bddtrue) {
	// We have worked with the complement already
	arrayBDD    [i] = !arrayBDD    [arrayNeg[i]];
		arrayBDDdash[i] = !arrayBDDdash[arrayNeg[i]];
	return;
  }

  switch(arrayType[i]) {
  case PLTLFormula::TRUE: arrayBDD[i] = bddtrue; arrayBDDdash[i] = bddtrue; return;
  case PLTLFormula::FALSE: arrayBDD[i] = bddfalse; arrayBDDdash[i] = bddfalse; return;
  case PLTLFormula::NOT:
	mkbdd(arrayNeg[i]);

	arrayBDD    [i] = bdd_not(arrayBDD    [arrayNeg[i]]);
	arrayBDDdash[i] = bdd_not(arrayBDDdash[arrayNeg[i]]);
	return;
  case PLTLFormula::NEXT: // Note: Some are handled by the negationing above
  case PLTLFormula::AP:
	{
	  int v = bdd_varnum();

	  arrayVarLookup.push_back(i);
	  arrayVarLookup.push_back(i); // Add v and v+1 to the var lookup table

	  assert(bdd_setvarnum(v+2) == 0);
	  assert(bdd_intaddvarblock(v,v+1,BDD_REORDER_FIXED) >= 0);

	  arrayBDD    [i] = bdd_ithvar(v+1);
	  arrayBDDdash[i] = bdd_ithvar(v  );

	  // Associate the new variable with the corresponding formula
	  arrayVarLookup.push_back(i);
	  arrayVarLookup.push_back(i);
	  
	  //std::cout << arrayFormula[i] << " v= " << v << std::endl;

	  return;
	}
  case PLTLFormula::OR:
	if (args.nary) {
	  std::vector<bdd> v;
	  std::vector<bdd> vdash;
	  naryOp(PLTLFormula::OR,i, v, vdash);
	  arrayBDD    [i] = bigOr(v    );
	  arrayBDDdash[i] = bigOr(vdash);
	  return;
	} // else fallthrough
  case PLTLFormula::UN:
	mkbdd(arrayDest1[i]);
	mkbdd(arrayDest2[i]);
	arrayBDD    [i] = arrayBDD    [arrayDest1[i]] | arrayBDD    [arrayDest2[i]];
	arrayBDDdash[i] = arrayBDDdash[arrayDest1[i]] | arrayBDDdash[arrayDest2[i]];
	return;
  case PLTLFormula::AND:
	if (args.nary) {
	  std::vector<bdd> v;
	  std::vector<bdd> vdash;
	  naryOp(PLTLFormula::AND,i, v, vdash);
	  arrayBDD    [i] = bigAnd(v    ,args.reorderInit > 0);
	  arrayBDDdash[i] = bigAnd(vdash,args.reorderInit > 0);
	  return;
	} // else fallthrough
  case PLTLFormula::BF:
	mkbdd(arrayDest1[i]);
	mkbdd(arrayDest2[i]);
	arrayBDD    [i] = arrayBDD    [arrayDest1[i]] & arrayBDD    [arrayDest2[i]];
  	arrayBDDdash[i] = arrayBDDdash[arrayDest1[i]] & arrayBDDdash[arrayDest2[i]];
	return;
  default:
	assert(false);
  }
}


// bool formulaLessInner(int a, int b) {
//   if (arrayType[a] == PLTLFormula::AP) {
// 	if (arrayType[b] == PLTLFormula::AP) {
// 	  return arrayFormula[a].compare(arrayFormula[b]) < 0;
// 	} else if (arrayType[b] == PLTLFormula::NOT) {
// 	  return arrayFormula[a].compare(arrayFormula[arrayNeg[b]]) < 0;
// 	}
//   } else if (arrayType[a] == PLTLFormula::NOT) {
// 	if (arrayType[b] == PLTLFormula::AP) {
// 	  return arrayFormula[arrayNeg[a]].compare(arrayFormula[b]) < 0;
// 	} else if (arrayType[b] == PLTLFormula::NOT) {
// 	  return arrayFormula[arrayNeg[a]].compare(arrayFormula[arrayNeg[b]]) < 0;
// 	}
//   }
//   return arrayFormula[a].compare(arrayFormula[b]) < 0;
// }

// bool formulaLess(int a, int b) {
//   assert(arrayType[a] == PLTLFormula::EX && arrayType[b] == PLTLFormula::EX);
//   return formulaLessInner(arrayDest1[a], arrayDest1[b]);
// }


void getConjuncts(int f, std::vector<bdd>& v) {
  if (arrayType[f] != PLTLFormula::AND) {
	mkbdd(f);
	v.push_back(arrayBDD[f]);
  } else {
	getConjuncts(arrayDest1[f], v);
	getConjuncts(arrayDest2[f], v);
  }
}

void cacheBDDs(int f_idx, int global_idx) {
  arrayBDD.clear();
  arrayBDDdash.clear();
  arrayVarLookup.clear();

  arrayBDD.resize(arrayFormula.size(),bddtrue);
  arrayBDDdash.resize(arrayFormula.size(),bddtrue);

  int idx;

  // std::vector<int> v;



  // // All EX atoms must exist
  // for(idx = lpos[PLTLFormula::EX]; idx <= hpos[PLTLFormula::EX]; ++idx) {
  // 	v.push_back(idx);
  // }

  // sort(v.begin(), v.end(), formulaLess);

  // for(std::vector<int>::const_iterator i = v.cbegin(); i != v.cend(); ++i) {
  // 	mkbdd(arrayDest1[*i]);
  // 	mkbdd(*i);
  // }

  // Typically global_idx is a giant conjunction of globals, or true.




  for(idx = lpos[PLTLFormula::NEXT]; idx <= hpos[PLTLFormula::NEXT]; ++idx) {
	//std::cout << "Making " << arrayFormula[idx] << std::endl;
	mkbdd(idx);
	mkbdd(arrayDest1[idx]);
	/*	if (arrayType[arrayDest1[idx]] == PLTLFormula::EU) {
	  mkbdd(arrayDest1[arrayDest1[idx]]);
	  mkbdd(arrayDest1[arrayDest2[arrayDest1[idx]]]);
	  } */
  }

  for(idx = lpos[PLTLFormula::UN]; idx <= hpos[PLTLFormula::UN]; ++idx) {
	//std::cout << "Making " << arrayFormula[idx] << std::endl;
	mkbdd(arrayDest2[arrayDest2[idx]]);
	mkbdd(arrayDest1[idx]);
	mkbdd(arrayDest1[arrayDest2[idx]]);

  }

  // Note: The OCaml version kind of builds global_idx sometime in the
  // middle of the EU section, when it hits the appropriate E(True U
  // ~p) for the AG p. This changes the order relative to this one.

  // These both have to exist!
  mkbdd(global_idx);

  mkbdd(f_idx);



  //std::cout << arrayFormula[f_idx] << std::endl;
  //std::cout << arrayFormula[global_idx]<< std::endl;


  // if (arrayType[global_idx] != PLTLFormula::TRUE){
  // 	std::vector<bdd> v;

  // 	getConjuncts(global_idx, v);

  // 	std::cout << "Got globals." << std::endl;

  // 	arrayBDD[global_idx] = bigAnd(v, 1);//(args.reorderInit >0 ? 1 : 0));
  // }

}

void extractGlobals(const PLTLFormula& f, PLTLFormula*& local, PLTLFormula*& global,bool isglobal=false) {
  switch(f.getop()) {
  case PLTLFormula::AND:
	extractGlobals(f.getleft(),local,global,isglobal);
	extractGlobals(f.getright(),local,global,isglobal);
	return;
  case PLTLFormula::BF:
	if (f.getleft().getop() == PLTLFormula::FALSE) {
	  // This is a G
	  std::unique_ptr<PLTLFormula> tmp(f.getright().nnfNeg());
	  extractGlobals(*tmp,local,global,true);
	  return;
	}
	// else fall through
  default:
	if(isglobal) {
	  if (!global) global = new PLTLFormula(f);
	  else global = new PLTLFormula(PLTLFormula::AND,global,new PLTLFormula(f));
	} else {
	  if (!local) local = new PLTLFormula(f);
	  else local = new PLTLFormula(PLTLFormula::AND,local,new PLTLFormula(f));
	}
  }
}

bdd fragun(const bdd& R, const bdd& vdash, bddPair* pairmap, const bdd& state, int idx) {
  // (f U g)
  bdd g = arrayBDD[arrayDest1[idx]];
  bdd f = arrayBDD[arrayDest1[arrayDest2[idx]]];
  
  int iter = 0;

  bdd frag = g;
  bdd oldfrag;
  do {
	oldfrag= frag;

	++iter;

	info_msg(std::cout << "fragun iteration " << iter << std::endl,4);

	bdd inner = bdd_replace(state & frag, pairmap);

	info_msg(std::cout << "Mid" << std::endl,5);

	bdd exist = bdd_appex(inner, R, bddop_and, vdash);
	info_msg(std::cout << "Mid2" << std::endl,5);
	frag = g | (f & exist);

  } while(frag != oldfrag);

  info_msg(std::cout
		   << "fragun: " << arrayFormula[idx]
		   << " -- " << iter
		   << "\n"
		   ,2);

  return frag;
}

int main(int argc, char ** argv) {

  // First, configure default options
  initArgs();

  // Then parse the command line options
  int c;
  do {
	int option_index = 0;
	static struct option long_options[] = {
	  {"sat",          0, &(args.satcheck),    1},
	  {"valid",        0, &(args.validcheck),  1},
	  {"silent",       0, &(args.silent),      1},
	  {"echo",         0, &(args.echoInput),   1},
	  {"reorder",      0, &(args.reorder),     1},
	  {"reordermore",  0, &(args.reorder),     2},
	  {"autoreorder",  0, &(args.autoreorder), 1},
	  {"reorderstart", 0, &(args.reorderInit), 1},
	  {"nonormalise",  0, &(args.normalise),   0},
	  {"nosortand",    0, &(args.sortand),     0},
	  {"noassumeG",    0, &(args.assumeG),     0},
	  {"nary",         0, &(args.nary),        1},
	  {0,0,0,0}
	};

	c = getopt_long_only(argc,argv, "v:",long_options, &option_index);

	if (c == -1) break;

	if (c == 'v') {
	  assert(optarg);
	  args.verbose = strtol(optarg,NULL,10);
	}

  } while(1);

  if (args.satcheck == 0 && args.validcheck == 0) {
	std::cout << "Error: At least one of -sat and -valid must be specified!\n";
	exit(-1);
  }

  if (args.assumeG && args.validcheck) {
	// Can't use both of these.
	args.assumeG = false;
	info_msg(std::cerr << "Checking validity: Disabling explicit assumptions" << std::endl, 1);
  }
  // Wait for input

  std::string input;
  std::getline(std::cin,input);

  struct timeval start_time;
  gettimeofday(&start_time,NULL);

  // Initialise the BDD library

  bdd_init(1000, 4000);
  if (args.silent) {bdd_gbc_hook(silent_gbc_handler);}
  else {bdd_reorder_verbose(1);}
  assert(bdd_setmaxincrease(5000000) >= 0);
  assert(bdd_setcacheratio(4) >= 0);
  if (args.autoreorder == 0) bdd_disable_reorder();
  else {
	bdd_autoreorder(BDD_REORDER_SIFT);
  }

  struct timeval init_time;
  gettimeofday(&init_time,NULL);

  info_msg(std::cout
		   << "BDD package initialised in "
		   << time_diff(start_time, init_time)
		   << " seconds.\n"
		   ,1);


  // Parse and pre-process the input formula

  std::unique_ptr<PLTLFormula> rawf(PLTLFormula::parsePLTLFormula(input.c_str()));
  std::unique_ptr<PLTLFormula> nnff(rawf->nnf());
  std::unique_ptr<PLTLFormula> normf(args.normalise
									? PLTLFormula::normalise(nnff.get())
									: new PLTLFormula(*nnff));
  
  std::unique_ptr<PLTLFormula> Gamma, Phi;

  if (args.assumeG && normf->getop() == PLTLFormula::AND) { 
	PLTLFormula* gamma = NULL;
	PLTLFormula* phi = NULL;

	extractGlobals(*normf,phi,gamma);
	
	if (gamma == NULL) {gamma = new PLTLFormula(true);}
	if (phi == NULL) {phi = new PLTLFormula(true);}

	Gamma.reset(gamma);
	Phi.reset(phi);

  } else if (args.assumeG && normf->getop() == PLTLFormula::BF && normf->getleft().getop() == PLTLFormula::FALSE){
	std::unique_ptr<PLTLFormula> tmp(normf->getright().nnfNeg()); // potentially repeat? Not yet.
	
	PLTLFormula* gamma = NULL;
	PLTLFormula* phi = NULL;
	extractGlobals(*tmp,phi,gamma,true);

	assert(gamma);

	Gamma.reset(gamma);
	Phi.reset(new PLTLFormula(true)); // everything is a global!

  } else {
	Gamma.reset(new PLTLFormula(true));
	Phi.reset(new PLTLFormula(*normf));
  }


  int fidx, globalsidx;
  ppFormula(*Phi,*Gamma,fidx,globalsidx);

  if (args.echoInput) {
	info_msg(std::cout 
			 << "Formula is   \t" << *rawf << "\n"
			 << "NNF is       \t" << *nnff << "\n"
			 << "Processed to \t" << *normf << "\n" ,1);
	if (args.assumeG) {
	  info_msg(std::cout << "Interpreted as\n"                  /*,1);
	  info_msg(std::cout */ << *Gamma << "\n |- \n" << *Phi << "\n",1);
	}
  }

  // Now to convert to BDD machinery
  cacheBDDs(fidx, globalsidx);

  bdd negf = bdd_not(arrayBDD[fidx]);
  int nBDDvars = bdd_varnum();

  // Check for early termination conditions:

  if (arrayBDD[fidx] == bddtrue && arrayBDD[globalsidx] == bddtrue) {
	// Formula is TRUE
	if (args.satcheck)
	  std::cout << "Formula is satisfiable.\n";
	if (args.validcheck)
	  std::cout << "Formula is valid.\n";

	struct timeval end_time;
	gettimeofday(&end_time,NULL);
	info_msg(std::cout
			 << "Time elapsed: "
			 << time_diff(start_time,end_time)
			 << "\n"
			 ,1);
	return 0;
  } else if (arrayBDD[globalsidx] == bddtrue && arrayBDD[fidx] == bddfalse) {
	// Formula is True |= FALSE
	if (args.satcheck)
	  std::cout << "Formula is not satisfiable.\n";
	if (args.validcheck)
	  std::cout << "Formula is not valid.\n";

	struct timeval end_time;
	gettimeofday(&end_time,NULL);
	info_msg(std::cout
			 << "Time elapsed: "
			 << time_diff(start_time,end_time)
			 << "\n"
			 ,1);
	return 0;
  } else if (lpos[PLTLFormula::NEXT] > hpos[PLTLFormula::NEXT]) {
	// The formula is essentially classical!
	info_msg(std::cout
			 << "Input is essentially classical!\n"
			 ,1);
	if (args.satcheck) {
	  std::cout << "Formula is ";
	  if (arrayBDD[fidx] == bddfalse)
		std::cout << "not ";
	  std::cout << "satisfiable.\n";
	}

	if (args.validcheck) {
	  int var_array[nBDDvars];
	  for(int i = 0; i < nBDDvars; ++i){ var_array[i] = i;}
	  bdd vall = bdd_makeset(var_array,nBDDvars);

	  std::cout << "Formula is ";
	  if (bdd_appex(arrayBDD[globalsidx],negf,bddop_and,vall) != bddfalse)
	  //if ((arrayBDD[globalsidx] & negf) != bddfalse)
		std::cout << "not ";
	  std::cout << "valid.\n";
	}

	struct timeval end_time;
	gettimeofday(&end_time,NULL);
	info_msg(std::cout
			 << "Time elapsed: "
			 << time_diff(start_time,end_time)
			 << "\n"
			 ,1);
	return 0;
  }

  // Prepare for modal aspects

  info_msg(std::cout << "Number of BDD variables: " << nBDDvars << "\n", 1);

  bddPair * pairmap = bdd_newpair();

  bdd vars, vdash, vall;
  {
	int var_array1[nBDDvars/2];
	int var_array2[nBDDvars/2];

	for(int i = 0; i < nBDDvars; i+=2) {
	  var_array1[i/2] = i;
	  var_array2[i/2] = i+1;
	}

	vdash = bdd_makeset(var_array1,nBDDvars/2);
	vars = bdd_makeset(var_array2,nBDDvars/2);
	vall = vdash & vars;
	// pairmap takes v' to v
	assert(bdd_setpairs(pairmap,var_array2,var_array1,nBDDvars/2) == 0);
  }


  // Now to construct the relation

  struct timeval pre_relation_time;
  gettimeofday(&pre_relation_time,NULL);

  info_msg(std::cout << "Creating relation BDDs...\n", 1);


  bdd bddR;
  {
	std::vector<bdd> v;
	v.reserve(hpos[PLTLFormula::NEXT] - lpos[PLTLFormula::NEXT] + 
			  1);
	for(int i = lpos[PLTLFormula::NEXT]; i <= hpos[PLTLFormula::NEXT]; ++i) {
	  // <AX p> => <p'>
	  v.emplace_back(bdd_biimp(arrayBDD[i], arrayBDDdash[arrayDest1[i]]));
	}
	bddR = bigAnd(v,(args.reorder > 1 ? 1 : 0));
  }

  if (args.reorderInit) {
	bdd_reorder(BDD_REORDER_SIFTITE);
  }

  struct timeval post_relation_time;
  gettimeofday(&post_relation_time,NULL);

  info_msg(std::cout
		   << "Created relations in "
		   << time_diff(pre_relation_time,post_relation_time)
		   << " seconds" << std::endl, 1);

  info_msg(std::cout << "Size of relation: " << bdd_nodecount(bddR) << std::endl, 6);

  // Now begins the real work

  // initialise state
  bdd state = arrayBDD[globalsidx];

  if (args.reorder >= 1) {
	info_msg(std::cout << "Reordering...\n",1);
	bdd_reorder(BDD_REORDER_SIFT);
	info_msg(std::cout << "Reordered\n",1);
  }

  if (args.reorder < 0) {
	bdd_disable_reorder();
  }

  bdd oldstate;
  int iter = 0;
  do {
	// Note: Using appex rather than just and here means it can go faster and use less space
	if (args.satStop && bdd_appex(state,arrayBDD[fidx],bddop_and,vall) == bddfalse) {
	  // S & f is empty, thus the formula is not satisfiable.
	  info_msg(std::cout << "Early termination: Unsatisfiable!\n",2);
	  break;
	} /*else if (args.validStop && bdd_appex(state,negf,bddop_and,vall) == bddfalse) {
	  // S & ~f is empty, thus ~f is unsatisfiable, thus f is valid
	  info_msg(std::cout << "Early termination: Valid!\n",2);
	  // TODO: Is this legit? I think it only works if we don't care about satisfiability
	  state = arrayBDD[fidx];
	  break;
	  }*/

	oldstate = state;
	++iter;

	info_msg(std::cout << "Starting fixpoint iteration " << iter << "\n",2);

	// update state

	// SUCC
	{
	  bdd sdash = bdd_replace(state,pairmap);
	  state = state & bdd_appex(sdash,bddR,bddop_and,vdash);
	}

	// no need for NEXT; any successor for the above suffices 

	// UN
	{

	  info_msg(std::cout
			   << "Computing UN successors\n"
			   ,3);

	  std::vector<bdd> v;
	  v.reserve(hpos[PLTLFormula::UN] - lpos[PLTLFormula::UN] +
				1 + 1);
	  v.push_back(state);

	  for(int i = lpos[PLTLFormula::UN]; i <= hpos[PLTLFormula::UN]; ++i) {
		int exeu = arrayDest2[arrayDest2[i]]; // (f U g) = g | (f & EX E(f U g))
		bdd f = arrayBDD[arrayDest1[arrayDest2[i]]];
		bdd frag = fragun(bddR, vdash, pairmap, state,i);
		bdd b = bdd_imp(arrayBDD[exeu] & f, frag);
		if (b != bddtrue) {
		  v.push_back(b);
		}
	  }

	  state = bigAnd(v,(args.reorder > 1 ? 1 : 0));
	}


  } while(state != oldstate);

  info_msg(std::cout << "Converged in " << iter << " iterations\n",1);
  // Now inspect state to see what the answer is

  if (args.satcheck) {
	std::cout << "Formula is ";
	if (bdd_appex(state,arrayBDD[fidx],bddop_and, vall) == bddfalse) {
	  std::cout << "not ";
	}
	std::cout << "satisfiable.\n";
  }

  if (args.validcheck) {
	std::cout << "Formula is ";
	if (state != bddfalse &&
		(
		 (bdd_appex(state,arrayBDD[fidx],bddop_and, vall) == bddfalse) ||
		 (bdd_appex(state,negf,bddop_and,vall) != bddfalse)
		)
	   ) {
	  std::cout << "not ";
	}
	std::cout << "valid.\n";
  }

  struct timeval end_time;
  gettimeofday(&end_time,NULL);

  info_msg(std::cout
		   << "Time elapsed: "
		   << time_diff(start_time,end_time)
		   << "\n"
		   ,1);

  bdd_freepair(pairmap);
  bdd_done();
  return 0;
}
