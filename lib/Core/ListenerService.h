/*
 * ListenerService.h
 *
 *  Created on: 2015年11月13日
 *      Author: zhy
 */

#ifndef LIB_CORE_LISTENERSERVICE_H_
#define LIB_CORE_LISTENERSERVICE_H_

#include "BitcodeListener.h"
#include "RuntimeDataManager.h"
#include "AddressSpace.h"
#include "Executor.h"
#include "Memory.h"
#include "BarrierInfo.h"
#include "klee/Internal/Module/KInstruction.h"
#include "klee/ExecutionState.h"


namespace klee {

class ListenerService {

private:
	std::vector<BitcodeListener*> bitcodeListeners;
	RuntimeDataManager rdManager;

public:
	void addListener(BitcodeListener* bitcodeListener);
	void removeListener(BitcodeListener* bitcodeListener);

	RuntimeDataManager* getRuntimeDataManager();
	bool getMemoryObject(ObjectPair& op, ExecutionState& state, ref<Expr> address);

	void beforeRunMethodAsMain(ExecutionState &initialState);
	void afterPreparation();
	void executeInstruction(ExecutionState &state, KInstruction *ki);
	void instructionExecuted(ExecutionState &state, KInstruction *ki);
	void afterRunMethodAsMain();
	void executionFailed(ExecutionState &state, KInstruction *ki);

//	void createMutex(ExecutionState &state, Mutex* mutex);
//	void createCondition(ExecutionState &state, Condition* condition);
	void createThread(ExecutionState &state, Thread* thread);


};

}



#endif /* LIB_CORE_LISTENERSERVICE_H_ */
