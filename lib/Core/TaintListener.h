/*
 * TaintListener.h
 *
 *  Created on: 2016年2月17日
 *      Author: 11297
 */

#ifndef LIB_CORE_TAINTLISTENER_H_
#define LIB_CORE_TAINTLISTENER_H_

#include "Executor.h"
#include "RuntimeDataManager.h"
#include "BitcodeListener.h"
#include "klee/Internal/Module/KInstruction.h"
#include "klee/ExecutionState.h"
#include "DealWithSymbolicExpr.h"

namespace llvm {
class Type;
class Constant;
}

namespace klee {

class TaintListener: public BitcodeListener {
public:
	TaintListener(Executor* executor, RuntimeDataManager* rdManager);
	~TaintListener();

	void beforeRunMethodAsMain(ExecutionState &initialState);
	void executeInstruction(ExecutionState &state, KInstruction *ki);
	void instructionExecuted(ExecutionState &state, KInstruction *ki);
	void afterRunMethodAsMain();
//	void createMutex(ExecutionState &state, Mutex* mutex);
//	void createCondition(ExecutionState &state, Condition* condition);
	void createThread(ExecutionState &state, Thread* thread);
	void executionFailed(ExecutionState &state, KInstruction *ki);

private:
	Executor* executor;
	RuntimeDataManager* rdManager;
	std::vector<Event*>::iterator currentEvent, endEvent;

private:

	//add by hy
	ref<Expr> manualMakeTaint(ExecutionState& state, std::string name,
			unsigned size, bool isFloat);
	ref<Expr> readExpr(ExecutionState &state, ref<Expr> address,
			Expr::Width size);

};

}



#endif /* LIB_CORE_TAINTLISTENER_H_ */
