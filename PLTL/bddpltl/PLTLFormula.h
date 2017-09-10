#ifndef _PLTLFORMULA_H_
#define _PLTLFORMULA_H_

#include <set>
#include <string>
#include <memory>
#include <vector>

#include <ostream>

class PLTLFormula {
public:

  enum PLTLFormulaType {
	TRUE, FALSE, 
	AP, NOT,
	NEXT,
	UN, BF,
	IMP, EQU, AND, OR
  };
  static const unsigned int TYPE_COUNT = OR+1;

  static const char* PLTLFormulaTypeNames[TYPE_COUNT];

  PLTLFormula(PLTLFormulaType, const PLTLFormula* , const PLTLFormula*);
  PLTLFormula(PLTLFormulaType, const PLTLFormula* , std::shared_ptr<const PLTLFormula> const &);
  PLTLFormula(PLTLFormulaType, std::shared_ptr<const PLTLFormula> const &, const PLTLFormula*);
  PLTLFormula(PLTLFormulaType, std::shared_ptr<const PLTLFormula> const &, std::shared_ptr<const PLTLFormula> const &);
  PLTLFormula(const std::string&);
  explicit PLTLFormula(bool);

  PLTLFormula(const PLTLFormula & other);

  ~PLTLFormula();

  PLTLFormula& operator=(const PLTLFormula&);
  bool operator==(const PLTLFormula&) const;

  size_t size() const;


  std::string* toString() const ;

  int compare(const PLTLFormula&) const;

  PLTLFormulaType getop() const {return op;};
  const PLTLFormula& getleft() const {return *left;};
  const PLTLFormula& getright() const {return *right;};

  PLTLFormula* nnf() const;
  PLTLFormula* nnfNeg() const;

  static PLTLFormula* parsePLTLFormula(const char*);
  static PLTLFormula* normalise(const PLTLFormula*);

  struct equal_to {bool operator()(const PLTLFormula& a, const PLTLFormula& b) {return a == b;}};
  struct less_than {bool operator()(const PLTLFormula& a, const PLTLFormula& b) {return a.compare(b) > 0;}};
  struct greater_than {bool operator()(const PLTLFormula& a, const PLTLFormula& b) {return a.compare(b) < 0;}};
  


  typedef std::set<PLTLFormula,greater_than> PLTLFormulaSet ;

  static PLTLFormulaSet* detClosure(const PLTLFormula&);
  static void detClosure(PLTLFormulaSet&, const PLTLFormula&);


  friend std::ostream& operator<<(std::ostream& ,const PLTLFormula& );

  static PLTLFormulaType dual(PLTLFormulaType);


  static void collectOp(PLTLFormulaType, std::vector<std::shared_ptr<PLTLFormula>>&,const PLTLFormula*,
						PLTLFormula*(func)(const PLTLFormula*));

private:
  PLTLFormula();


  
  void toString(std::string& buf, int precedence) const;

  static PLTLFormula* parseEQU(const char*& str);
  static PLTLFormula* parseIMP(const char*& str);
  static PLTLFormula* parseAND(const char*& str);
  static PLTLFormula* parseOR(const char*& str);
  static PLTLFormula* parseUNBF(const char*& str);
  static PLTLFormula* parseRest(const char*& str);

  static PLTLFormula* normaliseG(const PLTLFormula* f);

  PLTLFormulaType op;
  std::shared_ptr<const PLTLFormula> left, right;
  std::string prop;

  bool sane() const;

};

extern PLTLFormula PLTLXtrue;


#endif
