/*
 * Event.cpp
 *
 *  Created on: May 29, 2014
 *      Author: ylc
 */

#include "Event.h"
#include "klee/Internal/Module/KInstruction.h"
#include "klee/Internal/Module/InstructionInfoTable.h"
#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
#include "llvm/IR/Instructions.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/TypeBuilder.h"
#else
#include "llvm/Instruction.h"
#include "llvm/IR/BasicBlock.h"
#endif
#include <sstream>

using namespace std;
using namespace llvm;

namespace klee {

Event::Event(unsigned threadId, unsigned eventId, string eventName, KInstruction* inst,
		string varName, string globalVarFullName, EventType eventType)
	:threadId(threadId),
	 eventId(eventId),
	 eventName(eventName),
	 inst(inst),
	 varName(varName),
	 globalVarFullName(globalVarFullName),
	 eventType(eventType),
	 latestWrite(NULL),
	 isGlobal(false),
	 isLocal(false),
	 isConditionIns(false),
	 condition(false),
	 isFunctionWithSourceCode(true),
	 vectorInfo(NULL),
	 calledFunction(NULL),
	 isIgnore(false) {
	// TODO Auto-generated constructor stub
}

Event::~Event() {
	// TODO Auto-generated destructor stub
	if (inst->inst->getOpcode() == Instruction::GetElementPtr && vectorInfo != NULL) {
		delete vectorInfo;
	}
}

//modified by xdzhang
string Event::toString() {
	stringstream ss;
	ss << eventName << ": #Tid = " << threadId << "\n";
	ss << "#Eid = " << eventId << "\n";
	string instStr;
	raw_string_ostream str(instStr);
	inst->inst->print(str);
	ss << " #Inst:" << instStr << "\n";
	if (isGlobal)
		ss << " #GlobalVarName = " << varName << " #GlobalVarFullName = "
				<< globalVarFullName << "\n";
	if (isLocal)
		ss << " #LocalVarName = " << varName << "\n";
	if (isConditionIns) {
		ss << " #CondChoose = " << condition << "\n";
	}
	if (isFunctionWithSourceCode) {
		ss << " #FunctionWithSourceCode = YES" << "\n";
	}
	ss << " #Function = " << inst->inst->getParent()->getParent()->getName().str() << "\n";
	ss << " #Path = " << inst->info->file << "@" << inst->info->line << "\n";
	ss << " #EventType = ";
	if(eventType == Event::IGNORE)
		ss << "IGNORE\n";
	else if(eventType == Event::NORMAL)
		ss << "NORMAL\n";
	else
		ss << "VIRTURL\n";

	return ss.str();
}

} /* namespace klee */
