/*
 * SymbolicSystemRuntime.cpp
 *
 *  Created on: Jun 8, 2014
 *      Author: ylc
 */

#include "SymbolicSystemRuntime.h"
#include <iostream>

using namespace::std;
using namespace::llvm;

namespace klee {

SymbolicSystemRuntime::SymbolicSystemRuntime() : operandStackVector(20){
	// TODO Auto-generated constructor stub
	for (int i = 0; i < 20; i++) {
		operandStackVector[i] = NULL;
	}
}

SymbolicSystemRuntime::~SymbolicSystemRuntime() {
	// TODO Auto-generated destructor stub
	for (vector<stack<SymbolicStackFrame*>* > :: iterator vi= operandStackVector.begin(), ve = operandStackVector.end(); vi != ve; vi++) {
		if (*vi != NULL) {
			delete *vi;
		}
	}
}

void SymbolicSystemRuntime::pushStackFrame(Function* f, unsigned localLength, unsigned threadId) {
	if (threadId >= operandStackVector.size()) {
		operandStackVector.resize(operandStackVector.size() * 2, NULL);
	}

	stack<SymbolicStackFrame*>* operandStack = operandStackVector[threadId];

	if (!operandStack) {
		operandStack = new stack<SymbolicStackFrame*>();
		operandStackVector[threadId] = operandStack;
	}

	SymbolicStackFrame* newStackFrame = new SymbolicStackFrame(f, localLength);
	operandStack->push(newStackFrame);
}

void SymbolicSystemRuntime::popStackFrame(unsigned threadId) {
	if (threadId < operandStackVector.size()) {
		stack<SymbolicStackFrame*>* operandStack = operandStackVector[threadId];
		delete operandStack->top();
		operandStack->pop();
	} else {
		assert(0 && "thread not exist");
	}
}

void SymbolicSystemRuntime::printRunTime() {
	int threadId = 0;
	for (vector<stack<SymbolicStackFrame*>* >::iterator vi = operandStackVector.begin(), ve = operandStackVector.end(); vi != ve; vi++) {
		if (*vi) {
			cerr << "threadId = " << threadId << endl;
			stack<SymbolicStackFrame*>* operandStack = *vi;
			if (operandStack->size() > 0) {
				operandStack->top()->printStackFrame();
			}
		}
		threadId++;
	}
}

} /* namespace klee */
