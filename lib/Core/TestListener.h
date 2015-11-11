/*
 * TestListener.h
 *
 *  Created on: Jun 5, 2014
 *      Author: ylc
 */

#ifndef TESTLISTENER_H_
#define TESTLISTENER_H_

#include "BitcodeListener.h"
#include "klee/Internal/Module/KInstruction.h"
#include "klee/ExecutionState.h"
#include "Executor.h"
#include <iostream>
#include <fstream>
#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
#include "llvm/IR/Metadata.h"
#include "llvm/IR/Module.h"
#include "llvm/DebugInfo.h"
#else
#include "llvm/Metadata.h"
#include "llvm/Module.h"
#include "llvm/Analysis/DebugInfo.h"
#endif
#include "llvm/ADT/StringRef.h"


using namespace std;
using namespace llvm;

namespace klee {

class TestListener: public klee::BitcodeListener {
public:
	TestListener(Executor* executor);
	virtual ~TestListener();
	virtual void executeInstruction(ExecutionState &state, KInstruction *ki);
	virtual void instructionExecuted(ExecutionState &state, KInstruction *ki);
	virtual void beforeRunMethodAsMain(ExecutionState &initialState);
	virtual void afterRunMethodAsMain();
	virtual void afterPreparation();
//	virtual void createMutex(ExecutionState &state, Mutex* mutex);
//	virtual void createCondition(ExecutionState &state, Condition* condition);
	virtual void createThread(ExecutionState &state, Thread* thread);
	virtual void executionFailed(ExecutionState &state, KInstruction *ki);

private:
	Executor* executor;
	std::string cwd;
	std::string prefixDir;
	std::string uniqueTraceDir;
	std::string redundantTraceDir;
	std::string failedTraceDir;
	std::string prepareShellPos;
	std::string moveShellPos;
};


}

#endif /* TESTLISTENER_H_ */
