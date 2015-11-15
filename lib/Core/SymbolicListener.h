/*
 * SymbolicListener.h
 *
 *  Created on: 2015年11月13日
 *      Author: zhy
 */

#ifndef LIB_CORE_SYMBOLICLISTENER_H_
#define LIB_CORE_SYMBOLICLISTENER_H_

#include "AddressSpace.h"
#include "Executor.h"
#include "Memory.h"
#include "BarrierInfo.h"
#include "RuntimeDataManager.h"
#include "BitcodeListener.h"
#include "klee/Internal/Module/KInstruction.h"
#include "klee/ExecutionState.h"

#include <sstream>
#include <iostream>
#include <fstream>
#include <string>
#include <map>

#include "llvm/Support/CallSite.h"
#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/DerivedTypes.h"
#else
#include "llvm/Instructions.h"
#include "llvm/Type.h"
#include "llvm/DerivedTypes.h"
#endif

namespace llvm	{
class Type;
class Constant;
}

namespace klee {

class SymbolicListener : public BitcodeListener {
public:
	SymbolicListener(Executor* executor);
	~SymbolicListener();

	void beforeRunMethodAsMain(ExecutionState &initialState);
	void afterPreparation();
	void executeInstruction(ExecutionState &state, KInstruction *ki);
	void instructionExecuted(ExecutionState &state, KInstruction *ki);
	void afterRunMethodAsMain();
//	void createMutex(ExecutionState &state, Mutex* mutex);
//	void createCondition(ExecutionState &state, Condition* condition);
	void createThread(ExecutionState &state, Thread* thread);
	void executionFailed(ExecutionState &state, KInstruction *ki);

private:
	Executor* executor;
	DealWithSymbolicExpr filter;
	RuntimeDataManager* rdManager;

	//statics
	struct timeval start, finish;


private:

	//add by hy
	ref<Expr> manualMakeSymbolic(ExecutionState& state,
			std::string name, unsigned size, bool isFloat);
	void storeZeroToExpr(ExecutionState& state, ref<Expr> address, Expr::Width type);
	ref<Expr> readExpr(ExecutionState &state, ref<Expr> address, Expr::Width size);
	void getNewPrefix();

	bool isGlobalMO(const MemoryObject* mo) {
		bool result;
		if (mo->isGlobal) {
			result = true;
		} else {
			if (mo->isLocal) {
				result = false;
			} else {
				result = true;
			}
		}
		return result;
	}
};

}

#endif /* LIB_CORE_SYMBOLICLISTENER_H_ */
