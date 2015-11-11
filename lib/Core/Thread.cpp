/*
 * Thread.cpp
 *
 *  Created on: 2015年1月5日
 *      Author: berserker
 */

#include "Thread.h"

#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
#include "llvm/IR/Function.h"
#else
#include "llvm/Function.h"
#endif

#include <iostream>
#include <iomanip>

using namespace::llvm;
using namespace::std;

namespace klee {

StackFrame::StackFrame(KInstIterator _caller, KFunction *_kf)
  : caller(_caller), kf(_kf), callPathNode(0),
    minDistToUncoveredOnReturn(0), varargs(0) {
  locals = new Cell[kf->numRegisters];
}

StackFrame::StackFrame(const StackFrame &s)
  : caller(s.caller),
    kf(s.kf),
    callPathNode(s.callPathNode),
    allocas(s.allocas),
    minDistToUncoveredOnReturn(s.minDistToUncoveredOnReturn),
    varargs(s.varargs) {
  locals = new Cell[s.kf->numRegisters];
  for (unsigned i=0; i<s.kf->numRegisters; i++)
    locals[i] = s.locals[i];
}

StackFrame::~StackFrame() {
  delete[] locals;
}

unsigned Thread::nextThreadId = 1;

Thread::Thread() {
	// TODO Auto-generated constructor stub

}

Thread::Thread(unsigned threadId, Thread* parentThread, AddressSpace* addressSpace, KFunction* kf)
	: pc(kf->instructions),
	  prevPC(pc),
	  incomingBBIndex(0),
	  threadId(threadId),
	  parentThread(parentThread),
	  addressSpace(addressSpace),
	  threadState(Thread::RUNNABLE) {

	stack.reserve(10);
	pushFrame(0, kf);
}

Thread::Thread(Thread& anotherThread, AddressSpace* addressSpace)
	: pc(anotherThread.pc),
	  prevPC(anotherThread.prevPC),
	  incomingBBIndex(anotherThread.incomingBBIndex),
	  threadId(anotherThread.threadId),
	  parentThread(anotherThread.parentThread),
	  addressSpace(addressSpace),
	  threadState(anotherThread.threadState),
	  stack(anotherThread.stack) {

}

Thread::~Thread() {
	// TODO Auto-generated destructor stub
	while (!stack.empty()) {
		popFrame();
	}
}

void Thread::pushFrame(KInstIterator caller, KFunction *kf) {
  stack.push_back(StackFrame(caller,kf));
}

void Thread::popFrame() {
  StackFrame &sf = stack.back();
  for (std::vector<const MemoryObject*>::iterator it = sf.allocas.begin(),
         ie = sf.allocas.end(); it != ie; ++it)
    addressSpace->unbindObject(*it);
  stack.pop_back();
}

void Thread::dumpStack(ostream &out) const {
  unsigned idx = 0;
  const KInstruction *target = prevPC;
  out << "thread " << threadId << endl;
  for (Thread::stack_ty::const_reverse_iterator
         it = stack.rbegin(), ie = stack.rend();
       it != ie; ++it) {
    const StackFrame &sf = *it;
    Function *f = sf.kf->function;
    const InstructionInfo &ii = *target->info;
    out << "\t#" << idx++
        << " " << setw(8) << setfill('0') << ii.assemblyLine
        << " in " << f->getName().str() << " (";
    // Yawn, we could go up and print varargs if we wanted to.
    unsigned index = 0;
    for (Function::arg_iterator ai = f->arg_begin(), ae = f->arg_end();
         ai != ae; ++ai) {
      if (ai!=f->arg_begin()) out << ", ";

      out << ai->getName().str();
      // XXX should go through function
      ref<Expr> value = sf.locals[sf.kf->getArgRegister(index++)].value;
      if (isa<ConstantExpr>(value))
        out << "=" << value;
    }
    out << ")";
    if (ii.file != "")
      out << " at " << ii.file << ":" << ii.line;
    out << "\n";
    target = sf.caller;
  }
}


} /* namespace klee */
