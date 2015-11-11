/*
 * Event.h
 *
 *  Created on: May 29, 2014
 *      Author: ylc
 */

#ifndef EVENT_H_
#define EVENT_H_

#include "klee/Internal/Module/KInstruction.h"
#include <string>
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Constant.h"
#include "klee/Expr.h"
#include <z3++.h>
#include <map>

using namespace z3;
//using namespace std;
namespace klee {

class VectorInfo {
public:
	uint64_t base;
	uint64_t elementBitWidth;
	uint64_t size;
	uint64_t selectedIndex;
	uint64_t selectedAddress;

	VectorInfo(uint64_t base, uint64_t elementBitWidth, uint64_t size,
			uint64_t selectedIndex) {
		this->base = base;
		this->elementBitWidth = elementBitWidth;
		this->size = size;
		this->selectedIndex = selectedIndex;
		this->selectedAddress = base + selectedIndex * elementBitWidth / 8;
	}

	std::vector<uint64_t> getAllPossibleAddress() {
		std::vector<uint64_t> addresses(size - 1);
		unsigned index = 0;
		for (unsigned i = 0; i < size; i++) {
			uint64_t address = base + i * elementBitWidth / 8;
			if (address != selectedAddress) {
				addresses[index++] = address;
			}
		}
		return addresses;
	}
};

class Event {
public:
	enum EventType {
		NORMAL, //normal event, which participates in the encode and has associated inst
		IGNORE, //ignore event, which does not participate in the encode
		VIRTUAL //virtual event, which has no associated inst
	};
public:
	unsigned threadId; //threadID
	unsigned eventId; //eventID
	std::string eventName; //eventName
	KInstruction* inst; //associated kinst
	std::string varName; //name of global variable
	std::string globalVarFullName; //globalVarName + the read / write sequence
	EventType eventType;
	Event * latestWrite; //the latest write event in the same thread
	bool isGlobal; // is global variable  load, store, call strcpy in these three instruction this attribute will be assigned
	bool isLocal; // is local variable load, store, call strcpy in these three instruction this attribute will be assigned
	bool isConditionIns; // is this event associated with a Br which has two targets
	bool condition; // Br's condition
	bool isFunctionWithSourceCode; // only use by call, whether the called function is defined by user
	llvm::Function* calledFunction; //set for called function. all callinst use it.@14.12.02
	VectorInfo* vectorInfo; // element address of accessed array
	std::vector<std::string> implicitGlobalVar; // function's input variable
	std::string mutexName; // access mutex
	std::string condName; //access condition;
	bool isIgnore; //whether ignore this event when detecting


	//2015.7.8 hy
//	bool isArg;
	std::vector<ref<klee::Expr> > value; // arg of call / index and offset of getelemenptr / cond of switch
	std::map<std::string, llvm::Constant*> scrVariables; // function's input variable



	Event();
	Event(unsigned threadId, unsigned eventId, std::string eventName,
			KInstruction* inst, std::string globalVarName,
			std::string globalVarFullName, EventType eventType);
	virtual ~Event();
	std::string toString();
	llvm::Constant* getAttribute(unsigned index);
	void setAttribute(unsigned index, llvm::Constant* value);
	void addAttribute(llvm::Constant* value);

};

} /* namespace klee */

#endif /* EVENT_H_ */
