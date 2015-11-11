/*
 * TestListener.cpp
 *
 *  Created on: Jun 5, 2014
 *      Author: ylc
 */

#include "llvm/Support/raw_ostream.h"
#include <unistd.h>
#include "TestListener.h"
#include "klee/Expr.h"
#include "PTree.h"

using namespace::std;
using namespace::llvm;

#define PREFIX_DEBUG 1

namespace klee {



TestListener::TestListener(Executor* executor) : executor(executor) {
	// TODO Auto-generated constructor stub
}

TestListener::~TestListener() {
	// TODO Auto-generated destructor stub
}

void TestListener::executeInstruction(ExecutionState &state, KInstruction *ki) {

}

void TestListener::instructionExecuted(ExecutionState &state, KInstruction *ki) {

//	for (set<ExecutionState*>::iterator alli = executor->allThread.begin(), alle = executor->allThread.end(); alli != alle; alli++) {
//		cerr << (*alli)->threadId << endl;
//	}
//	for (set<ExecutionState*>::iterator alli = executor->allThread.begin(), alle = executor->allThread.end(); alli != alle; alli++) {
//					 cerr << *alli << " " << (*alli)->ptreeNode->left << " " << (*alli)->ptreeNode->right << endl;
//	}
}

void TestListener::beforeRunMethodAsMain(ExecutionState &initialState) {
	//gather global variables' initializer
//	Module* m = executor->kmodule->module;
//	for (Module::global_iterator i = m->global_begin(), e = m->global_end(); i != e; ++i) {
//		if (i->hasInitializer() && i->getName().str().at(0) != '.') {
//		    Constant* initializer = i->getInitializer();
//		    cerr << i->getName().str() << " " <<initializer->getType()->getTypeID();
//		    if (initializer->getType()->isStructTy()) {
//		    	cerr << initializer->getType()->getStructName().str();
//		    }
//		    cerr << endl;
//		}
//	}


}

void TestListener::afterRunMethodAsMain() {

}

void TestListener::afterPreparation() {

}

void TestListener::createThread(ExecutionState &state, Thread* thread) {

}

void TestListener::executionFailed(ExecutionState &state, KInstruction *ki) {

}

}
