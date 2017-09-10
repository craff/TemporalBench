#include "PLTLMisc.h"

#include <map>
#include <assert.h>

#include <iostream>

std::vector<PLTLFormula> arrayFormula;
std::vector<PLTLFormula::PLTLFormulaType> arrayType;
std::vector<int> arrayDest1;
std::vector<int> arrayDest2;
std::vector<int> arrayNeg;

int lpos[PLTLFormula::TYPE_COUNT];
int hpos[PLTLFormula::TYPE_COUNT];

int pltlxidx = -1;

typedef std::map<PLTLFormula,unsigned int,PLTLFormula::greater_than> PLTLFormulaMap;


void ppFormula(const PLTLFormula& f, const PLTLFormula& globals, int& fidx, int& globalsidx){
  std::unique_ptr<PLTLFormula::PLTLFormulaSet> s(PLTLFormula::detClosure(f));
  PLTLFormula::detClosure(*s, globals);
  // s now contains everything in the closure


  int counts[PLTLFormula::TYPE_COUNT] = {0};
  for(PLTLFormula::PLTLFormulaSet::const_iterator i = s->cbegin(); i != s->cend(); ++i) {
	counts[i->getop()]++;
  }

  int idxs[PLTLFormula::TYPE_COUNT];
  idxs[0] = 0;
  int prevh = -1;
  for(unsigned int i = 0; i < PLTLFormula::TYPE_COUNT; ++i) {
	lpos[i] = prevh+1;
	hpos[i] = lpos[i]+counts[i]-1;
	idxs[i] = lpos[i];
	prevh = hpos[i];
  }

  PLTLFormulaMap m;
  
  for(PLTLFormula::PLTLFormulaSet::const_iterator i = s->cbegin(); i != s->cend(); ++i) {
	if (m.find(*i) != m.end()) {
	  assert(false);
	}
	m[*i] = idxs[i->getop()]++;
  }

  arrayFormula.resize(m.size(),PLTLFormula(true));
  arrayType.resize(m.size(),PLTLFormula::TRUE);
  arrayDest1.resize(m.size(),0);
  arrayDest2.resize(m.size(),0);
  arrayNeg.resize(m.size(),-1);

  for(PLTLFormulaMap::const_iterator i = m.begin(); i != m.end(); ++i) {
	assert(i->second < arrayFormula.size());
	arrayFormula[i->second] = i->first;
	{
	  PLTLFormula* neg = i->first.nnfNeg();
	  if (s->find(*neg) != s->end()) {
	  	arrayNeg[i->second] = m[*neg];
	  }
	  delete neg;
	}
	arrayType[i->second] = i->first.getop();
	switch(i->first.getop()) {
	case PLTLFormula::AND:
	case PLTLFormula::OR:
	  arrayDest2[i->second] = m[i->first.getright()];
	case PLTLFormula::NEXT:
	  arrayDest1[i->second] = m[i->first.getleft()];
	case PLTLFormula::TRUE:
	case PLTLFormula::FALSE:
	case PLTLFormula::AP:
	  // Do nothing
	  break;
	case PLTLFormula::NOT:
	  assert(i->first.getleft().getop() == PLTLFormula::AP);
	  break;
	case PLTLFormula::UN:
	  {
		arrayDest1[i->second] = m[i->first.getright()];
		std::unique_ptr<PLTLFormula> 
		  nf(new PLTLFormula(PLTLFormula::AND,
							new PLTLFormula(i->first.getleft()),
							new PLTLFormula(PLTLFormula::NEXT,
										   new PLTLFormula(i->first),
										   NULL)
							)
			 );
		arrayDest2[i->second] = m[*nf];
		break;
	  }
	case PLTLFormula::BF:
	  {
		std::unique_ptr<PLTLFormula> negr(i->first.getright().nnfNeg());
		arrayDest1[i->second] = m[*negr];
		std::unique_ptr<PLTLFormula> 
		  nf(new PLTLFormula(PLTLFormula::OR,
							new PLTLFormula(i->first.getleft()),
							new PLTLFormula(PLTLFormula::NEXT,
										   new PLTLFormula(i->first),
										   NULL)
							)
			 );
		arrayDest2[i->second] = m[*nf];
		break;
	  }  
	case PLTLFormula::EQU:
	case PLTLFormula::IMP:
	  assert(false && "Not in negation normal form?");
	  
	}
	
  }

  fidx = m[f];
  globalsidx = m[globals];
}
