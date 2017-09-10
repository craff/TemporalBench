#include "PLTLFormula.h"
#include <assert.h>
#include <ctype.h>
#include <string.h>
#include <algorithm>

#include <iostream>
#include <cstdio>

static std::shared_ptr<PLTLFormula> PLTLtrue(new PLTLFormula(true));
static std::shared_ptr<PLTLFormula> PLTLfalse(new PLTLFormula(false));
PLTLFormula PLTLXtrue(PLTLFormula::NEXT,PLTLtrue,NULL);

const char* PLTLFormula::PLTLFormulaTypeNames[] = 
{"TRUE", "FALSE",
 "AP", "NOT",
 "NEXT",
 "UN", "BF",
 "IMP", "EQU", "AND", "OR"
};


PLTLFormula::PLTLFormula()
  :op(TRUE)
  ,left()
  ,right()
  ,prop("")
{
}

PLTLFormula::PLTLFormula(const std::string& s)
  :op(AP)
  ,left()
  ,right()
  ,prop(s)
{
}

PLTLFormula::PLTLFormula(bool b)
  :op(b ? TRUE : FALSE)
  ,left()
  ,right()
  ,prop("")
{
}

PLTLFormula::PLTLFormula(PLTLFormulaType _op, const PLTLFormula * _left, const PLTLFormula * _right)
  :op(_op)
  ,left(_left)
  ,right(_right)
  ,prop("")
{
}

PLTLFormula::PLTLFormula(PLTLFormulaType _op, const PLTLFormula* _left, std::shared_ptr<const PLTLFormula> const & _right)
  :op(_op)
  ,left(_left)
  ,right(_right)
  ,prop("")
{
}

PLTLFormula::PLTLFormula(PLTLFormulaType _op, std::shared_ptr<const PLTLFormula> const & _left, const PLTLFormula* _right)
  :op(_op)
  ,left(_left)
  ,right(_right)
  ,prop("")
{
}

PLTLFormula::PLTLFormula(PLTLFormulaType _op, std::shared_ptr<const PLTLFormula> const & _left, std::shared_ptr<const PLTLFormula> const & _right)
  :op(_op)
  ,left(_left)
  ,right(_right)
  ,prop("")
{
}


PLTLFormula::PLTLFormula(const PLTLFormula & other)
  :op(other.op)
  ,left(other.left)
  ,right(other.right)
  ,prop(other.prop)
{  
}


PLTLFormula::~PLTLFormula() {
}

PLTLFormula& PLTLFormula::operator=(const PLTLFormula& other) {
  if (this != &other) {
	op = other.op;
	left = other.left;
	right = other.right;
	prop = other.prop;
  }
  return *this;
}

bool PLTLFormula::operator==(const PLTLFormula& other) const {
  return 
	op == other.op &&
	(op <= FALSE ? true :
	 op == AP    ? prop == other.prop :
	 op <= NEXT   ? *left == *(other.left) :
	 *left == *(other.left) && *right == *(other.right)
	 );
}






int PLTLFormula::compare(const PLTLFormula & other) const {
  if (op != other.op) {
	return static_cast<int>(op - other.op);
  }

  switch(op) {
  case TRUE:
  case FALSE:
	return 0;
  case AP:
	return prop.compare(other.prop);
  case NOT:
  case NEXT:
	return left->compare(*other.left);
  case OR:
  case AND:
  case EQU:
  case IMP:
  case UN:
  case BF:
	int c1 = left->compare(*other.left);
	if (c1 != 0) return c1;
	else return right->compare(*other.right);
  }
  assert(false && "Fell out of complete switch!");
}


size_t PLTLFormula::size() const {
  switch(op) {
  case TRUE:
  case FALSE:
  case AP: return 1;
  case NOT: 
  case NEXT: return 1 + left->size();
  case UN:
  case BF:
  case IMP:
  case EQU: 
  case AND:
  case OR: return 1 + left->size() + right->size();
  default:
	// Error!
	assert(false);
	return 0;
  }
}



std::string* PLTLFormula::toString() const {
  std::string *ret = new std::string;
  toString(*ret,-1);
  return ret;
}

static int prionr(PLTLFormula::PLTLFormulaType op) {
  switch(op) {
  case PLTLFormula::EQU: return 0;
  case PLTLFormula::IMP: return 1;
  case PLTLFormula::OR: return 2;
  case PLTLFormula::AND: return 3;
  default: return 4;
  }
}

void PLTLFormula::toString(std::string& s, int precedence) const {
  assert(sane());
  bool needsBrackets = prionr(op) < precedence;
  if (needsBrackets)
	s += '(';
  switch(op){
  case TRUE: s+="True "; break;
  case FALSE: s+="False "; break;
  case AP: s+= prop; break;
  case NOT:
	s += "~";
	left->toString(s,4);
	break;
  case NEXT:
	s += "X ";
	left->toString(s,4);
	break;
  case EQU:
	left->toString(s,0);
	s += " <=> ";
	right->toString(s,0);
	break;
  case IMP:
	left->toString(s,2);
	s += " => ";
	right->toString(s,2);
	break;
  case OR:
	left->toString(s,3);
	s += " | ";
	right->toString(s,3);
	break;
  case AND:
	left->toString(s,4);
	s += " & ";
	right->toString(s,4);
	break;
  case UN:
	s += "(";
	left->toString(s,-1);
	s += " U ";
	right->toString(s,-1);
	s += ")";
	break;
  case BF:
	s += "(";
	left->toString(s,-1);
	s += " B ";
	right->toString(s,-1);
	s += ")";
	break;
  default:
	std::cerr << "Error in tostring; formula is bad!\nOp is " << op << "\n";
	assert(false);
	// Shouldn't get here!
  }

  if (needsBrackets)
	s += ')';

  return;
}

std::ostream& operator<<( std::ostream& stream, const PLTLFormula& f ){
  std::unique_ptr<std::string> s(f.toString());
  return stream << *s;
}

PLTLFormula*  PLTLFormula::parseEQU(const char*& str) {
  PLTLFormula* left = parseIMP(str);
  
  while(isspace(*str)) ++str;
  
  if(strncmp(str,"<=>",3) == 0) {
	// This is an equivalence
	str += 3;
	PLTLFormula* right = parseEQU(str);
	return new PLTLFormula(PLTLFormula::EQU,left,right);
  } else {
	return left;
	// This is not an equivalence
  }
}

PLTLFormula* PLTLFormula::parseIMP(const char*& str) {
  PLTLFormula* left = parseOR(str);
  
  while(isspace(*str)) ++str;
  
  if(strncmp(str,"=>",2) == 0) {
	// This is an implication
	str += 2;
	PLTLFormula* right = parseIMP(str);
	return new PLTLFormula(PLTLFormula::IMP,left,right);
  } else {
	return left;
	// This is not an implication
  }
}

PLTLFormula* PLTLFormula::parseOR(const char*& str) {
  PLTLFormula* left = parseAND(str);
  
  while(isspace(*str)) ++str;
  
  if(*str == '|'){
	// This is a disjunction
	++str;
	PLTLFormula* right = parseOR(str);
	return new PLTLFormula(PLTLFormula::OR,left,right);
  } else {
	return left;
	// This is not a disjunction
  }
}

PLTLFormula* PLTLFormula::parseAND(const char*& str) {
  PLTLFormula* left = parseUNBF(str);
  
  while(isspace(*str)) ++str;
  
  if(*str == '&'){
	// This is a conjunction
	++str;
	PLTLFormula* right = parseAND(str);
	return new PLTLFormula(PLTLFormula::AND,left,right);
  } else {
	return left;
	// This is not a conjunction
  }
}

PLTLFormula* PLTLFormula::parseUNBF(const char*& str) {
  PLTLFormula* left = parseRest(str);
  
  while(isspace(*str)) ++str;

  if(*str == 'U') {
	++str;
	PLTLFormula* right = parseUNBF(str);
	return new PLTLFormula(PLTLFormula::UN,left,right);
  } else if (*str == 'B') {
	++str;
	PLTLFormula* right = parseUNBF(str);
	return new PLTLFormula(PLTLFormula::BF,left,right);
  }
  return left;
}

PLTLFormula* PLTLFormula::parseRest(const char*& str) {
  while(isspace(*str)) ++str;


  PLTLFormula *left;

  if(*str == '('){
	++str;
	left = parseEQU(str);
	while(isspace(*str)) ++str;
	assert(*str == ')');
	++str;
	return left;
  } else if (*str == '~') {
	++str;
	left = parseRest(str);
	left = new PLTLFormula(PLTLFormula::NOT,left,NULL);
	return left;
  } else if (strncmp(str,"X",1) == 0) {
	++str;
	left = parseRest(str);
	left = new PLTLFormula(PLTLFormula::NEXT,left,NULL);
	return left;
  } else if (strncmp(str,"F",1) == 0) {
	++str;
	left = parseRest(str);
	return new PLTLFormula(PLTLFormula::UN,PLTLtrue,left);
  } else if (strncmp(str,"G",1) == 0) {
	++str;
	left = parseRest(str);
	return new PLTLFormula(PLTLFormula::BF,PLTLfalse,new PLTLFormula(PLTLFormula::NOT,left,NULL));
  } else if (strncmp(str,"True",4)==0) {
	str += 4;
	return new PLTLFormula(true);
  } else if (strncmp(str,"False",5)==0) {
	str += 5;
	return new PLTLFormula(false);
  } else if (isalpha(*str) || *str == '_') {
	size_t n = 1;
	while(isalnum(*(str+n)) || *(str+n) == '_') ++n;
	left = new PLTLFormula(std::string(str,n));
	str += n;
	return left;
  }

  assert(false && "Could not parse input");
  // Must not reach here

}

PLTLFormula* PLTLFormula::parsePLTLFormula(const char* str) {
  if (!str || !*str) return NULL;

  PLTLFormula* ret = parseEQU(str);

  while(isspace(*str)) ++str;

  assert(! *str);

  return ret;
}


PLTLFormula* PLTLFormula::nnf() const {
  assert(sane());
  switch(op) {
  case TRUE:
  case FALSE:
  case AP:
	return new PLTLFormula(*this);
  case NOT:
	if (left->op == AP) {
	  return new PLTLFormula(*this);
	} else {
	  return left->nnfNeg();
	}
  case NEXT:
	return new PLTLFormula(op,left->nnf(),NULL);
  case EQU:
	return
	  new PLTLFormula(AND,
					 new PLTLFormula(OR,left->nnfNeg(),right->nnf()),
					 new PLTLFormula(OR,right->nnfNeg(),left->nnf())
					 );
  case IMP:
	return
	  new PLTLFormula(OR,left->nnfNeg(),right->nnf());
  case AND:
  case OR:
  case UN:
  case BF:
	return new PLTLFormula(op,left->nnf(),right->nnf());
  default:
	assert(false);
  }
}

/*
	TRUE, FALSE, 
	AP, NOT,
	NEXT,
	UN, BF,
	IMP, EQU, AND, OR
*/
static PLTLFormula::PLTLFormulaType duals[] = 
  {PLTLFormula::FALSE,
   PLTLFormula::TRUE,
   PLTLFormula::FALSE, // not to be used
   PLTLFormula::FALSE, // not to be used
   PLTLFormula::NEXT,
   PLTLFormula::BF,
   PLTLFormula::UN,
   PLTLFormula::FALSE, // not to be used
   PLTLFormula::FALSE, // not to be used
   PLTLFormula::OR,
   PLTLFormula::AND
  };

PLTLFormula::PLTLFormulaType PLTLFormula::dual(PLTLFormulaType t) {
  assert(t != AP && 
		 t != NOT &&
		 t != IMP &&
		 t != EQU);
  return duals[t];
}

PLTLFormula* PLTLFormula::nnfNeg() const {
  assert(sane());
  switch(op) {
  case TRUE: return new PLTLFormula(false);
  case FALSE: return new PLTLFormula(true);
  case AP:	return new PLTLFormula(NOT,new PLTLFormula(*this),NULL);
  case NOT:
	return left->nnf();
  case NEXT: return new PLTLFormula(dual(op),left->nnfNeg(),NULL);
  case EQU:
	return
	  new PLTLFormula(OR,
					 new PLTLFormula(AND,left->nnf(),right->nnfNeg()),
					 new PLTLFormula(AND,right->nnf(),left->nnfNeg())
					 );
  case IMP:
	return
	  new PLTLFormula(AND,left->nnf(),right->nnfNeg());
  case AND:
  case OR: return new PLTLFormula(dual(op),left->nnfNeg(),right->nnfNeg());
  case UN:
  case BF: return new PLTLFormula(dual(op),left->nnfNeg(),right->nnf());
  default:
	std::cerr << "Formula not in negation normal form!\n" << *this << "\n";
	assert(false);
  }
}


void PLTLFormula::collectOp(PLTLFormulaType op, std::vector<std::shared_ptr<PLTLFormula> >& v,const PLTLFormula* f, PLTLFormula*(func)(const PLTLFormula*)){
  assert(op == AND || op == OR);
  if (f->op != op) {
	PLTLFormula *nf = func(f);
	if (nf->op == op) {
	  std::unique_ptr<PLTLFormula> p(nf);
	  collectOp(op,v,nf,func);
	} else {
	  v.emplace_back(nf);
	}
  } else {
	collectOp(op,v,f->left.get(),func);
	collectOp(op,v,f->right.get(),func);
  }
}
  
static bool greaterfml(const std::shared_ptr<PLTLFormula>& a, const std::shared_ptr<PLTLFormula>& b) {
  return a->compare(*b) > 0;
}

PLTLFormula* PLTLFormula::normalise(const PLTLFormula* f) {
  assert(f->sane());
  PLTLFormula *nfl, *nfr;
  switch(f->op) {
  case TRUE:
  case FALSE:
  case AP:
	return new PLTLFormula(*f);
  case NOT:
	assert(f->left->op == AP);
	return new PLTLFormula(*f);
  case NEXT:
	nfl = normalise(f->left.get());
	if (nfl->op <= FALSE) {
	  return nfl; // X True = True, X False = False
	} else {
	  return new PLTLFormula(NEXT,nfl,NULL);
	}
  case AND:
	{
	  std::vector<std::shared_ptr<PLTLFormula> > v;
	  collectOp(AND,v,f,normalise);
	  // v is a vector of normalised and-related formulae
	  for (std::vector<std::shared_ptr<PLTLFormula> >::const_iterator i = v.cbegin(); i != v.cend(); ++i) {
		if ((*i)->op == FALSE) {
		  // Conjunction is false; break out and freak out
		  // cleanup handled by shared_ptr in the vector
		  return new PLTLFormula(false);
		}
	  }

	  sort(v.begin(),v.end(),greaterfml);

	  // Now construct a new formula
	  std::vector<std::shared_ptr<PLTLFormula> >::iterator i = v.begin();
	  std::shared_ptr<PLTLFormula>& prev = *i;
	  bool started = false;
	  PLTLFormula * nf = NULL;

	  for(;i != v.end(); ++i) {
		if ((*i)->op == BF && (*i)->left->op == FALSE) {
		  if (nf == NULL) {
			nf = new PLTLFormula(*((*i)->right));
			assert(nf != NULL);
		  } else {
			nf = new PLTLFormula(OR,nf,(*i)->right); // (False B ~p) & (False B ~q) = G p & G q = G (p & q) = (False B ~(p & q)) = (False B ~p | ~q)
			assert(nf != NULL);
		  }
		} else if (!started){
		  prev = *i;
		  started = true;
		}
	  }
	  if (nf != NULL) {
		nf = new PLTLFormula(BF, PLTLfalse, nf);
		if (started) {
		  nf = new PLTLFormula(AND,nf, prev);
		} 
	  } else {
		assert(nf == NULL);
		assert(started);
		nf = new PLTLFormula(*prev);
	  }



	  for(i = v.begin();i != v.end(); ++i) {
		if (*prev == **i || (*i)->op == TRUE
			|| ((*i)->op == BF && (*i)->left->op == FALSE)) {
		  // skip it
		} else {
		  prev = *i;
		  // conjoin this to the rest
		  nf = new PLTLFormula(AND,nf,prev);
		}
	  }
	  return nf;
	}
  case OR:
	{
	  std::vector<std::shared_ptr<PLTLFormula> > v;
	  collectOp(OR,v,f,normalise);
	  // v is a vector of normalised or-related formulae
	  for (std::vector<std::shared_ptr<PLTLFormula> >::const_iterator i = v.cbegin(); i != v.cend(); ++i) {
		if ((*i)->op == TRUE) {
		  // Disjunction is true; break out and freak out
		  // cleanup handled by shared_ptr in the vector
		  return new PLTLFormula(true);
		}
	  }
	  sort(v.begin(),v.end(),greaterfml);

	  // Now construct a new formula
	  std::vector<std::shared_ptr<PLTLFormula> >::iterator i = v.begin();
	  std::shared_ptr<PLTLFormula>& prev = *i;
	  PLTLFormula * nf = new PLTLFormula(*prev);

	  for(;i != v.end(); ++i) {
		if (*prev == **i || (*i)->op == FALSE) {
		  // skip it
		} else {
		  prev = *i;
		  // disjoin this to the rest
		  nf = new PLTLFormula(OR,nf,prev);
		}
	  }
	  return nf;
	}
  case UN:
	nfr = normalise(f->right.get());
	if (nfr->op == TRUE || nfr->op == FALSE){
	  return nfr;
	}
	
	nfl = normalise(f->left.get());
	if (nfl->op == FALSE) {
	  delete nfl;
	  return nfr;
	} else if (*nfl == *nfr) {
	  delete nfl;
	  return nfr;
	}
	return new PLTLFormula(f->op,nfl,nfr);
  case BF:
	nfr = normalise(f->right.get());
	if (nfr->op == TRUE){
	  delete nfr;
	  return new PLTLFormula(false);
	} else if (nfr->op == FALSE) {
	  delete nfr;
	  return new PLTLFormula(true);
	}
	
	nfl = normalise(f->left.get());
	if (nfl->op == TRUE) {
	  delete nfl;
	  nfl = nfr->nnfNeg();
	  delete nfr;
	  return nfl;
	} else if (nfl->op == FALSE) {
	  std::unique_ptr<PLTLFormula> p(nfr->nnfNeg());
	  delete nfr;
	  std::unique_ptr<PLTLFormula> q(normaliseG(p.get()));
	  return new PLTLFormula(f->op,nfl,q->nnfNeg());
	} else {
	  return new PLTLFormula(f->op,nfl,nfr);
	}	
  default:
	assert(false && "Not in NNF");
  }
  assert(false && "Fell out of full switch statement!");
}

PLTLFormula* PLTLFormula::normaliseG(const PLTLFormula* f) {
  switch(f->op) {
  case AND:
	// recurse
	{
	  std::vector<std::shared_ptr<PLTLFormula> > v;
	  collectOp(AND,v,f,normaliseG);
	  // v is a vector of normalised and-related formulae
	  for (std::vector<std::shared_ptr<PLTLFormula> >::const_iterator i = v.cbegin(); i != v.cend(); ++i) {
		if ((*i)->op == FALSE) {
		  // Conjunction is false; break out and freak out
		  // cleanup handled by shared_ptr in the vector
		  return new PLTLFormula(false);
		}
	  }

	  sort(v.begin(),v.end(),greaterfml);

	  // Now construct a new formula
	  std::vector<std::shared_ptr<PLTLFormula> >::iterator i = v.begin();
	  std::shared_ptr<PLTLFormula>& prev = *i;
	  PLTLFormula * nf = new PLTLFormula(*prev);

	  for(;i != v.end(); ++i) {
		if (*prev == **i || (*i)->op == TRUE) {
		  // skip it
		} else {
		  prev = *i;
		  // conjoin this to the rest
		  nf = new PLTLFormula(AND,nf,prev);
		}
	  }
	  return nf;
	}
  case BF:
	{
	  std::unique_ptr<PLTLFormula> tmp(f->right->nnfNeg());
	  return normalise(tmp.get());
	}
  default:
	return normalise(f);
  }
}




PLTLFormula::PLTLFormulaSet* PLTLFormula::detClosure(const PLTLFormula& f){
  PLTLFormula::PLTLFormulaSet* s = new PLTLFormula::PLTLFormulaSet();
  // NOTE: TRUE and FALSE may not be in the set, because I don't need it.
  detClosure(*s,f);
  return s;
}
void PLTLFormula::detClosure(PLTLFormula::PLTLFormulaSet& s, const PLTLFormula& f){
  if (s.find(f) != s.end()) return;

  s.insert(f);

  switch(f.op) {
  case AND:
  case OR:
	detClosure(s,*(f.right));
  case NEXT:
  case NOT:
	detClosure(s,*(f.left));
  case TRUE:
  case FALSE:
  case AP:
	break;
  case UN:
	{
	  detClosure(s,*(f.right));
	  std::unique_ptr<PLTLFormula> 
		p(new PLTLFormula(AND,
						 f.left,
						 new PLTLFormula(NEXT,
										new PLTLFormula(f),NULL)
						 ));
	  detClosure(s,*p);
	  break;
	}
  case BF:
	{
	  std::unique_ptr<PLTLFormula> nnfr(f.right->nnfNeg());
	  detClosure(s,*nnfr);
	  std::unique_ptr<PLTLFormula> 
		p(new PLTLFormula(OR,
						 f.left,
						 new PLTLFormula(NEXT,
										new PLTLFormula(f),NULL)
						 ));
	  detClosure(s,*p);
	  break;
	}
  default:
	assert(false);
  }

  // Make sure that everything has its negation in there
  std::unique_ptr<PLTLFormula> neg(f.nnfNeg());
  detClosure(s,*neg);
}



bool PLTLFormula::sane() const {
#ifdef DEBUG
  if (op < TRUE || op > OR) return false;
  if (op == TRUE || op == FALSE) return left.get() == NULL && right.get() == NULL;
  if (op == AP) return prop != "" && left.get() == NULL && right.get() == NULL;
  if (op == NOT || op == NEXT) return right.get() == NULL && left->sane();
  return left->sane() && right->sane();
#else
  return true;
#endif
}




