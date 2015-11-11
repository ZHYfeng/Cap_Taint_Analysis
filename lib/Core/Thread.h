/*
 * Thread.h
 *
 *  Created on: 2015年1月5日
 *      Author: berserker
 */

#ifndef LIB_CORE_THREAD_H_
#define LIB_CORE_THREAD_H_

#include "../../lib/Core/AddressSpace.h"
#include "klee/Internal/Module/KInstIterator.h"
#include "klee/Internal/Module/Cell.h"
#include "klee/Internal/Module/InstructionInfoTable.h"
#include "klee/Internal/Module/KInstruction.h"
#include "klee/Internal/Module/KModule.h"

namespace klee {

class Array;
class CallPathNode;
struct Cell;
struct KFunction;
struct KInstruction;
class MemoryObject;
struct InstructionInfo;

struct StackFrame {
  KInstIterator caller;
  KFunction *kf;
  CallPathNode *callPathNode;

  std::vector<const MemoryObject*> allocas;
  Cell *locals;

  /// Minimum distance to an uncovered instruction once the function
  /// returns. This is not a good place for this but is used to
  /// quickly compute the context sensitive minimum distance to an
  /// uncovered instruction. This value is updated by the StatsTracker
  /// periodically.
  unsigned minDistToUncoveredOnReturn;

  // For vararg functions: arguments not passed via parameter are
  // stored (packed tightly) in a local (alloca) memory object. This
  // is setup to match the way the front-end generates vaarg code (it
  // does not pass vaarg through as expected). VACopy is lowered inside
  // of intrinsic lowering.
  MemoryObject *varargs;

  StackFrame(KInstIterator caller, KFunction *kf);
  StackFrame(const StackFrame &s);
  ~StackFrame();
};

class Thread {
public:
  typedef std::vector<StackFrame> stack_ty;
  enum ThreadState {
	  RUNNABLE,
	  MUTEX_BLOCKED,
	  COND_BLOCKED,
	  BARRIER_BLOCKED,
	  JOIN_BLOCKED,
	  TERMINATED
  };
  KInstIterator pc, prevPC;
  stack_ty stack;
  unsigned threadId;
  unsigned incomingBBIndex;
  Thread* parentThread;
  ThreadState threadState;
  AddressSpace* addressSpace;
  static unsigned nextThreadId;
public:
	Thread();
	Thread(unsigned threadId, Thread* parentThread, AddressSpace* addressSpace, KFunction* kf);
	Thread(Thread& anotherThread, AddressSpace* addressSpace);
	virtual ~Thread();
	void pushFrame(KInstIterator caller, KFunction *kf);
	void popFrame();
	void dumpStack(std::ostream &out) const;

	bool isRunnable() {
		return threadState == RUNNABLE;
	}

	bool isMutexBlocked() {
		return threadState == MUTEX_BLOCKED;
	}

	bool isCondBlocked() {
		return threadState == COND_BLOCKED;
	}

	bool isBarrierBlocked() {
		return threadState == BARRIER_BLOCKED;
	}

	bool isJoinBlocked() {
		return threadState == JOIN_BLOCKED;
	}

	bool isTerminated() {
		return threadState == TERMINATED;
	}

	bool isSchedulable() {
		return isRunnable() || isMutexBlocked();
	}

	static unsigned getNextThreadId() {
		unsigned threadId = nextThreadId++;
		return threadId;
	}
};

} /* namespace klee */

#endif /* LIB_CORE_THREAD_H_ */
