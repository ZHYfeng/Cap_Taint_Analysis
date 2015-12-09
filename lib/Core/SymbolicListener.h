/*
 * SymbolicListener.h
 *
 *  Created on: 2015年11月13日
 *      Author: zhy
 */

#ifndef LIB_CORE_SYMBOLICLISTENER_H_
#define LIB_CORE_SYMBOLICLISTENER_H_

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

class SymbolicListener: public BitcodeListener {
public:
	SymbolicListener(Executor* executor, RuntimeDataManager* rdManager);
	~SymbolicListener();

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
	DealWithSymbolicExpr filter;
	std::vector<Event*>::iterator currentEvent, endEvent;
	//此Map更新有两处，Load、某些函数。
	std::map<ref<Expr>, ref<Expr> > addressSymbolicMap;
	std::map<std::string, std::vector<unsigned> > assertMap;
	std::map<std::string, ref<Expr> > symbolicMap;
	bool kleeBr;

private:

	//add by hy
	ref<Expr> manualMakeSymbolic(ExecutionState& state, std::string name,
			unsigned size, bool isFloat);
	void storeZeroToExpr(ExecutionState& state, ref<Expr> address,
			Expr::Width type);
	ref<Expr> readExpr(ExecutionState &state, ref<Expr> address,
			Expr::Width size);

};

}

#endif /* LIB_CORE_SYMBOLICLISTENER_H_ */
