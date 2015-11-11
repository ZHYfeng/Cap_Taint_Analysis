/*
 * SymbolicSystemRuntime.h
 *
 *  Created on: Jun 8, 2014
 *      Author: ylc
 */

#ifndef SYMBOLICSYSTEMRUNTIME_H_
#define SYMBOLICSYSTEMRUNTIME_H_

#include "SymbolicStackFrame.h"
#include <vector>
#include <stack>
#include <map>

namespace klee {

class SymbolicSystemRuntime {
public:
	std::vector<std::stack<SymbolicStackFrame*>* > operandStackVector;
	std::map<std::string, ref<Expr> > heap;
	//std::vector<std::stack<Cell*>* > constants;
	SymbolicSystemRuntime();
	virtual ~SymbolicSystemRuntime();
	void pushStackFrame(llvm::Function* f, unsigned localLength, unsigned threadId);
	void popStackFrame(unsigned threadId);
	void printRunTime();
};

} /* namespace klee */

#endif /* SYMBOLICSYSTEMRUNTIME_H_ */
