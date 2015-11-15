/*
 * BitcodeListener.h
 *
 *  Created on: May 16, 2014
 *      Author: ylc
 */

#ifndef BITCODELISTENER_H_
#define BITCODELISTENER_H_

#include "klee/Internal/Module/KInstruction.h"
#include "klee/ExecutionState.h"
#include "../Core/Mutex.h"
#include "../Core/Condition.h"
#include "../Core/Thread.h"

namespace klee {

class BitcodeListener {
public:
	virtual ~BitcodeListener();
	virtual void beforeRunMethodAsMain(ExecutionState &initialState) = 0;
	virtual void afterPreparation() = 0;
	virtual void executeInstruction(ExecutionState &state, KInstruction *ki) = 0;
	virtual void instructionExecuted(ExecutionState &state, KInstruction *ki) = 0;
	virtual void afterRunMethodAsMain() = 0;
//	virtual void createMutex(ExecutionState &state, Mutex* mutex) = 0;
//	virtual void createCondition(ExecutionState &state, Condition* condition) = 0;
	virtual void createThread(ExecutionState &state, Thread* thread) = 0;
	virtual void executionFailed(ExecutionState &state, KInstruction *ki) = 0;

private:

};

}

#endif /* BITCODELISTENER_H_ */
