#ifndef _PLTLMISC_H_
#define _PLTLMISC_H_

#include "PLTLFormula.h"

extern std::vector<PLTLFormula> arrayFormula;
extern std::vector<PLTLFormula::PLTLFormulaType> arrayType;
extern std::vector<int> arrayDest1;
extern std::vector<int> arrayDest2;
extern std::vector<int> arrayNeg;

extern int lpos[PLTLFormula::TYPE_COUNT];
extern int hpos[PLTLFormula::TYPE_COUNT];

extern int ctlexidx;

void ppFormula(const PLTLFormula& f, const PLTLFormula& globals, int& fidx, int& globalsidx); 

#endif
