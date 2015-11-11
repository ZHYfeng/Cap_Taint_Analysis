/*
 * PSOListener.h
 *
 *  Created on: May 16, 2014
 *      Author: ylc
 */

#ifndef PSOLISTENER_H_
#define PSOLISTENER_H_

#include "DealWithSymbolicExpr.h"
#include "BitcodeListener.h"
#include "klee/Internal/Module/KInstruction.h"
#include "klee/ExecutionState.h"
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
#include "AddressSpace.h"
#include "Executor.h"
#include "Memory.h"
#include "SymbolicSystemRuntime.h"
#include "RuntimeDataManager.h"
#include <sstream>
#include <iostream>
#include <fstream>
#include <string>

#include <map>

namespace llvm	{
class Type;
class Constant;
}

namespace klee {

class BarrierInfo {
public:

	unsigned count;
	unsigned current;
	unsigned releasedCount;
	BarrierInfo() {
		this->count = 0x7fffffff;
		this->current = 0;
		this->releasedCount = 0;
	};
	virtual ~BarrierInfo() {

	};

	bool addWaitItem() {
		this->current++;
		if (this->current == this->count) {
			return true;
		} else {
			return false;
		}
	}

	void addReleaseItem() {
		this->current = 0;
		this->releasedCount++;
	}

};

class PSOListener : public BitcodeListener {
public:
	PSOListener(Executor* executor);
	virtual ~PSOListener();
	virtual void executeInstruction(ExecutionState &state, KInstruction *ki);
	virtual void instructionExecuted(ExecutionState &state, KInstruction *ki);
	virtual void beforeSymbolicRun(ExecutionState &state, KInstruction *ki);
	virtual void afterSymbolicRun(ExecutionState &state, KInstruction *ki);
	virtual void prepareSymbolicRun(ExecutionState &initialState);
	virtual void afterprepareSymbolicRun(ExecutionState &initialState);
	virtual void beforeRunMethodAsMain(ExecutionState &initialState);
	virtual void afterRunMethodAsMain();
	virtual void afterPreparation();
//	virtual void createMutex(ExecutionState &state, Mutex* mutex);
//	virtual void createCondition(ExecutionState &state, Condition* condition);
	virtual void createThread(ExecutionState &state, Thread* thread);
	virtual void executionFailed(ExecutionState &state, KInstruction *ki);

	virtual void testForKquery2Z3();
	virtual void getGlobalSymbolic();

private:
	Executor* executor;
	DealWithSymbolicExpr filter;
	//SymbolicSystemRuntime runtime;
	RuntimeDataManager rdManager;
	std::stringstream ss;
	std::map<uint64_t, unsigned> loadRecord;
	std::map<uint64_t, unsigned> storeRecord;
	std::map<uint64_t, llvm::Type*> usedGlobalVariableRecord;
	std::map<uint64_t, BarrierInfo*> barrierRecord;
	std::map<llvm::Instruction*, VectorInfo*> getElementPtrRecord; // 记录getElementPtr解析的数组信息
	unsigned temporalVariableID;

	std::string cwd;
	std::string prefixDir;
	std::string uniqueTraceDir;
	std::string redundantTraceDir;
	std::string failedTraceDir;
	std::string prepareShellPos;
	std::string moveShellPos;

	//statics
	struct timeval start, finish;


private:
	//std::vector<string> monitoredFunction;

	bool getMemoryObject(ObjectPair& op, ExecutionState& state, ref<Expr> address);
	void handleInitializer(llvm::Constant* initializer, MemoryObject* mo, uint64_t& startAddress);
	void handleConstantExpr(llvm::ConstantExpr* expr);
	void insertGlobalVariable(ref<Expr> address, llvm::Type* type);
	ref<Expr> getExprFromMemory(ref<Expr> address, ObjectPair& op, llvm::Type* type);
	llvm::Constant* handleFunctionReturnValue(ExecutionState& state, KInstruction *ki);
	void handleExternalFunction(ExecutionState& state, KInstruction *ki);
	void analyzeInputValue(uint64_t& address, ObjectPair& op, llvm::Type* type);
	unsigned getLoadTime(uint64_t address);
	unsigned getStoreTime(uint64_t address);
	llvm::Function* getPointeredFunction(ExecutionState& state, KInstruction* ki);
	void printPrefix();
	void printInstrcution(ExecutionState& state, KInstruction* ki);

	//add by hy
	ref<Expr> manualMakeSymbolic(ExecutionState& state,
			std::string name, unsigned size, bool isFloat);
	void storeZeroToExpr(ExecutionState& state, ref<Expr> address, Expr::Width type);
	ref<Expr> readExpr(ExecutionState &state, ref<Expr> address, Expr::Width size);
	void getNewPrefix();

	std::string createVarName(unsigned memoryId, ref<Expr> address, bool isGlobal) {
		char signal;
		ss.str("");
		if (isGlobal) {
			signal = 'G';
		} else {
			signal = 'L';
		}
		ss << signal;
		ss << memoryId;
		ss << '_';
		ss << address;
		return ss.str();
	}
	std::string createVarName(unsigned memoryId, uint64_t address, bool isGlobal) {
			char signal;
			ss.str("");
			if (isGlobal) {
				signal = 'G';
			} else {
				signal = 'L';
			}
			ss << signal;
			ss << memoryId;
			ss << '_';
			ss << address;
			return ss.str();
	}

	std::string createGlobalVarFullName (std::string varName, unsigned time, bool isStore) {
		char signal;
		ss.str("");
		ss << varName;
		if (isStore) {
			signal = 'S';
		} else {
			signal = 'L';
		}
		ss << signal;
		ss << time;
		return ss.str();
	}

	std::string createTemporalName() {
		ss.str("");
		ss << "temporal";
		ss << temporalVariableID;
		temporalVariableID++;
		return ss.str();
	}

	std::string createBarrierName(uint64_t address, unsigned releasedCount) {
		ss.str("");
		ss << address;
		ss << "#";
		ss << releasedCount;
		return ss.str();
	}

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

#endif /* PSOLISTENER_H_ */
