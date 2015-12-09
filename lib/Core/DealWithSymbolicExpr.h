/*
 * SymbolicListener.h
 *
 *  Created on: 2015年7月21日
 *      Author: zhy
 */

#ifndef LIB_CORE_DEALWITHSYMBOLIC_H_
#define LIB_CORE_DEALWITHSYMBOLIC_H_

#include "klee/Expr.h"
#include "Trace.h"
#include <string>

#include "Event.h"

namespace klee {

class DealWithSymbolicExpr {

private:
	std::set<std::string> allRelatedSymbolicExpr;
	void resolveSymbolicExpr(ref<Expr> value, std::set<std::string>* relatedSymbolicExpr);


public:
	void fillterTrace(Trace* trace, std::set<std::string> allRelatedSymbolicExpr);
	void filterUseless(Trace* trace);
	bool filterUselessWithSet(Trace* trace, std::set<std::string>* relatedSymbolicExpr);
	void addExprToSet(std::set<std::string>* Expr, std::set<std::string>* relatedSymbolicExpr);
	bool isRelated(std::string varName);
	std::string getVarName(ref<Expr> value);
	std::string getFullName(ref<Expr> value);

};

}

#endif /* LIB_CORE_DEALWITHSYMBOLIC_H_ */
