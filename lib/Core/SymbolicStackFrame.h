/*
 * SymbolicStackFrame.h
 *
 *  Created on: Jun 8, 2014
 *      Author: ylc
 */

#ifndef SYMBOLICSTACKFRAME_H_
#define SYMBOLICSTACKFRAME_H_

#include "klee/Internal/Module/Cell.h"
#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
#include "llvm/IR/Function.h"
#else
#include "llvm/Function.h"
#endif
#include "string"

namespace llvm {
	class Function;
}

namespace klee {

class SymbolicStackFrame {
public:
	Cell* locals;
	llvm::Function* function;
	unsigned localLength;

	SymbolicStackFrame();
	SymbolicStackFrame(llvm::Function* function, unsigned localLength);
	virtual ~SymbolicStackFrame();
	void printStackFrame();
};

} /* namespace klee */

#endif /* SYMBOLICSTACKFRAME_H_ */
