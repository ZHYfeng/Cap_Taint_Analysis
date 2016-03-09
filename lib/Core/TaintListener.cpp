/*
 * TaintListener.cpp
 *
 *  Created on: 2016年2月17日
 *      Author: 11297
 */

#include "TaintListener.h"
#include "klee/Expr.h"
#include "PTree.h"
#include "Trace.h"
#include "Transfer.h"
#include "AddressSpace.h"
#include "Memory.h"

#include <unistd.h>
#include <map>
#include <sstream>
#include <iostream>
#include <string>

#include "llvm/ADT/StringRef.h"
#include "llvm/Support/raw_ostream.h"
#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
#include "llvm/IR/Metadata.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/DebugInfo.h"
#else
#include "llvm/Metadata.h"
#include "llvm/Module.h"
#include "llvm/IntrinsicInst.h"
#include "llvm/Analysis/DebugInfo.h"
#endif

using namespace std;
using namespace llvm;

#define PTR 0

namespace klee {

TaintListener::TaintListener(Executor* executor, RuntimeDataManager* rdManager) :
		BitcodeListener(), executor(executor), rdManager(rdManager) {
	Kind = TaintListenerKind;
}

TaintListener::~TaintListener() {
	// TODO Auto-generated destructor stub

}

//消息响应函数，在被测程序解释执行之前调用
void TaintListener::beforeRunMethodAsMain(ExecutionState &initialState) {

	Trace* trace = rdManager->getCurrentTrace();
	currentEvent = trace->path.begin();
	endEvent = trace->path.end();
}

void TaintListener::executeInstruction(ExecutionState &state,
		KInstruction *ki) {
	Trace* trace = rdManager->getCurrentTrace();
	Instruction* inst = ki->inst;
	Thread* thread = state.currentThread;
//	std::cerr << "thread id : " << thread->threadId << " ";
//	inst->dump();
	if ((*currentEvent)) {
		switch (inst->getOpcode()) {
		case Instruction::Br: {
			BranchInst *bi = dyn_cast<BranchInst>(inst);
			if (!bi->isUnconditional()) {
				ref<Expr> value1 = executor->eval(ki, 0, thread).value;
				if (value1->getKind() != Expr::Constant) {
					Expr::Width width = value1->getWidth();
					ref<Expr> value2;
					if ((*currentEvent)->condition == true) {
						value2 = ConstantExpr::create(true, width);
					} else {
						value2 = ConstantExpr::create(false, width);
					}
					executor->evalAgainst(ki, 0, thread, value2);
				}
			}
			break;
		}
		case Instruction::Switch: {
//			SwitchInst *si = cast<SwitchInst>(inst);
			ref<Expr> cond1 = executor->eval(ki, 0, thread).value;
			if (cond1->getKind() != Expr::Constant) {
				ref<Expr> cond2 = (*currentEvent)->value.back();
				executor->evalAgainst(ki, 0, thread, cond2);
			}
			break;
		}
		case Instruction::Call: {
			CallSite cs(inst);
			Function *f = (*currentEvent)->calledFunction;
			ref<Expr> function = executor->eval(ki, 0, thread).value;
			if (function->getKind() == Expr::Concat) {
				ref<Expr> value = symbolicMap[filter.getFullName(function)];
				if (value->getKind() != Expr::Constant) {
					assert(0 && "call function is symbolic");
				}
				if(function->isTaint) {
					value->isTaint = true;
				}
				executor->evalAgainst(ki, 0, thread, value);
			}
			if (!(*currentEvent)->isFunctionWithSourceCode) {
				unsigned numArgs = cs.arg_size();
				for (unsigned j = numArgs; j > 0; j--) {
					ref<Expr> value = executor->eval(ki, j, thread).value;
					Type::TypeID id =
							cs.getArgument(j - 1)->getType()->getTypeID();
					bool isFloat = 0;
					if ((id >= Type::HalfTyID) && (id <= Type::DoubleTyID)) {
						isFloat = 1;
					}
					if (isFloat || id == Type::IntegerTyID
							|| id == Type::PointerTyID) {
						if (value->getKind() == Expr::Constant) {

						} else if (value->getKind() == Expr::Concat
								|| value->getKind() == Expr::Read) {
							ref<Expr> svalue = symbolicMap[filter.getFullName(
									value)];
							if (svalue->getKind() != Expr::Constant) {
								assert(0 && "store value is symbolic");
							} else if (id == Type::PointerTyID
									&& value->getKind() == Expr::Read) {
								assert(0 && "pointer is expr::read");
							}
							if(value->isTaint) {
								svalue->isTaint = true;
							}
							executor->evalAgainst(ki, j, thread, svalue);
						} else {
							ref<Expr> svalue = (*currentEvent)->value[j - 1];
							if (svalue->getKind() != Expr::Constant) {
								assert(0 && "store value is symbolic");
							} else if (id == Type::PointerTyID) {
								if (f->getName().str() == "pthread_create") {

								} else {
									assert (0 && "pointer is other symbolic");
								}
							}
							bool isTaint = value->isTaint;
							std::vector<ref<klee::Expr> > relatedSymbolicExpr;
							filter.resolveTaintExpr(value, &relatedSymbolicExpr, &isTaint);
							if(isTaint) {
								svalue->isTaint = true;
							}
							executor->evalAgainst(ki, j, thread, svalue);
						}
					} else {
						if (value->getKind() != Expr::Constant) {
							assert(
									0
											&& "store value is symbolic and type is other");
						}
					}
				}
			}
			break;
		}

		case Instruction::Load: {

			ref<Expr> address = executor->eval(ki, 0, thread).value;
			if (address->getKind() == Expr::Concat) {
				ref<Expr> value = symbolicMap[filter.getFullName(address)];
				if (value->getKind() != Expr::Constant) {
					assert(0 && "load symbolic print");
				}
				executor->evalAgainst(ki, 0, thread, value);
			}
			break;
		}

		case Instruction::Store: {
			ref<Expr> address = executor->eval(ki, 1, thread).value;
			if (address->getKind() == Expr::Concat) {
				ref<Expr> value = symbolicMap[filter.getFullName(address)];
				if (value->getKind() != Expr::Constant) {
					assert(0 && "store address is symbolic");
				}
				executor->evalAgainst(ki, 1, thread, value);
			}

			ref<Expr> value = executor->eval(ki, 0, thread).value;
//			cerr << "value : " << value << "\n";
			bool isTaint = value->isTaint;
			std::vector<ref<klee::Expr> >* relatedSymbolicExpr = &((*currentEvent)->relatedSymbolicExpr);
			filter.resolveTaintExpr(value, relatedSymbolicExpr, &isTaint);
//			cerr << "relatedSymbolicExpr" << "\n";
//			for (std::vector<ref<klee::Expr> >::iterator it = relatedSymbolicExpr->begin();
//					it != relatedSymbolicExpr->end(); it++) {
//				cerr << "name : " << *it << " isTaint : " << (*it)->isTaint << "\n";
//			}
			ObjectPair op;
			executor->getMemoryObject(op, state, address);
			const MemoryObject *mo = op.first;
			const ObjectState *os = op.second;
			ObjectState *wos = state.addressSpace.getWriteable(mo, os);
			if (isTaint) {
				wos->insertTaint(address);
			} else {
				wos->eraseTaint(address);
			}
			Type::TypeID id = ki->inst->getOperand(0)->getType()->getTypeID();
			bool isFloat = 0;
			if ((id >= Type::HalfTyID) && (id <= Type::DoubleTyID)) {
				isFloat = 1;
			}
			if ((*currentEvent)->isGlobal) {
#if PTR
				if (isFloat || id == Type::IntegerTyID
						|| id == Type::PointerTyID) {
#else
				if (isFloat || id == Type::IntegerTyID) {
#endif
					Expr::Width size = executor->getWidthForLLVMType(
							ki->inst->getOperand(0)->getType());
					ref<Expr> symbolic = manualMakeTaintSymbolic(state,
							(*currentEvent)->globalVarFullName, size);

					//收集TS和PTS
					std::string varName = (*currentEvent)->varName;
					if (isTaint) {
						trace->DTAMSerial.insert((*currentEvent)->globalVarFullName);
						manualMakeTaint(symbolic, true);
						trace->taintSymbolicExpr.insert(varName);
						if (trace->unTaintSymbolicExpr.find(varName) != trace->unTaintSymbolicExpr.end()) {
							trace->unTaintSymbolicExpr.erase(varName);
						}
					} else {
						if (trace->taintSymbolicExpr.find(varName) == trace->taintSymbolicExpr.end()) {
							trace->unTaintSymbolicExpr.insert(varName);
						}
					}

					//编码tp
					ref<Expr> temp = ConstantExpr::create(0, size);
					for (std::vector<ref<klee::Expr> >::iterator it = relatedSymbolicExpr->begin();
							it != relatedSymbolicExpr->end(); it++) {
						string varFullName = filter.getFullName(*it);
						ref<Expr> orExpr = manualMakeTaintSymbolic(state, varFullName, size);
						temp = OrExpr::create(temp, orExpr);
					}
					ref<Expr> constraint = EqExpr::create(temp, symbolic);
					trace->taintExpr.push_back(constraint);
//					cerr << constraint << "isTaint : " << isTaint << "\n" ;

					if (value->getKind() == Expr::Constant) {

					} else if (value->getKind() == Expr::Concat
							|| value->getKind() == Expr::Read) {
						ref<Expr> svalue =
								symbolicMap[filter.getFullName(value)];
						if (svalue->getKind() != Expr::Constant) {
							assert(0 && "store value is symbolic");
						} else if (id == Type::PointerTyID
								&& value->getKind() == Expr::Read) {
							assert(0 && "pointer is Expr::read");
						}
						if(value->isTaint) {
							svalue->isTaint = true;
						}
						executor->evalAgainst(ki, 0, thread, svalue);
					} else {
						ref<Expr> svalue = (*currentEvent)->value.back();
						if (svalue->getKind() != Expr::Constant) {
							assert(0 && "store value is symbolic");
						} else if (id == Type::PointerTyID) {
							assert(0 && "pointer is other symbolic");
						}
						if(isTaint) {
							svalue->isTaint = true;
						}
						executor->evalAgainst(ki, 0, thread, svalue);
					}
				} else {
					if (value->getKind() != Expr::Constant) {
						assert(
								0
										&& "store value is symbolic and type is other");
					}
				}
			} else {
				//会丢失指针的一些关系约束，但是不影响。
				if (id == Type::PointerTyID && PTR) {
					if (value->getKind() == Expr::Concat) {
						ref<Expr> svalue =
								symbolicMap[filter.getFullName(value)];
						if (svalue->getKind() != Expr::Constant) {
							assert(0 && "store pointer is symbolic");
						}
						executor->evalAgainst(ki, 0, thread, svalue);
						ref<Expr> address = executor->eval(ki, 1, thread).value;
						addressSymbolicMap[address] = value;
					} else if (value->getKind() == Expr::Read) {
						assert(0 && "pointer is expr::read");
					} else {
						ref<Expr> address = executor->eval(ki, 1, thread).value;
						addressSymbolicMap[address] = value;
					}
				} else if (isFloat || id == Type::IntegerTyID) {
					//局部非指针变量内存中可能存储符号值。
				} else {
					if (value->getKind() != Expr::Constant) {
						assert(
								0
										&& "store value is symbolic and type is other");
					}
				}
			}
			break;
		}

		case Instruction::GetElementPtr: {
			KGEPInstruction *kgepi = static_cast<KGEPInstruction*>(ki);
			ref<Expr> base = executor->eval(ki, 0, thread).value;
			if (base->getKind() == Expr::Concat) {
				ref<Expr> value = symbolicMap[filter.getFullName(base)];
				if (value->getKind() != Expr::Constant) {
					assert(0 && "GetElementPtr symbolic print");
				}
				executor->evalAgainst(ki, 0, thread, value);
			} else if (base->getKind() == Expr::Read) {
				assert(0 && "pointer is expr::read");
			}
			std::vector<ref<klee::Expr> >::iterator first =
					(*currentEvent)->value.begin();
			for (std::vector<std::pair<unsigned, uint64_t> >::iterator it =
					kgepi->indices.begin(), ie = kgepi->indices.end(); it != ie;
					++it) {
				ref<Expr> index = executor->eval(ki, it->first, thread).value;
				if (index->getKind() != Expr::Constant) {
					executor->evalAgainst(ki, it->first, thread, *first);
				} else {
					if (index != *first) {
						assert(0 && "index != first");
					}
				}
				++first;
			}
			if (kgepi->offset) {

			}
			break;
		}
		case Instruction::PtrToInt: {
			ref<Expr> arg = executor->eval(ki, 0, thread).value;
			if (arg->getKind() == Expr::Concat) {
				ref<Expr> value = symbolicMap[filter.getFullName(arg)];
				if (value->getKind() != Expr::Constant) {
					assert(0 && "GetElementPtr symbolic print");
				}
				executor->evalAgainst(ki, 0, thread, value);
			} else if (arg->getKind() == Expr::Read) {
				assert(0 && "pointer is expr::read");
			}
			break;
		}
		default: {
			break;
		}
		}
	}
}

//TODO： Algorithm 2 AnalyseTaint
void TaintListener::instructionExecuted(ExecutionState &state,
		KInstruction *ki) {
	Trace* trace = rdManager->getCurrentTrace();
	if ((*currentEvent)) {
		Instruction* inst = ki->inst;
		Thread* thread = state.currentThread;
		switch (inst->getOpcode()) {
		case Instruction::Load: {
			bool isFloat = 0;
			Type::TypeID id = ki->inst->getType()->getTypeID();
			if ((id >= Type::HalfTyID) && (id <= Type::DoubleTyID)) {
				isFloat = 1;
			}
			if ((*currentEvent)->isGlobal) {

				for (unsigned i = 0; i < thread->vectorClock.size(); i++) {
					(*currentEvent)->vectorClock.push_back(thread->vectorClock[i]);
//					cerr << "vectorClock " << i << " : " << (*currentEvent)->vectorClock[i] << "\n";
				}

				//指针！！！
#if PTR
				if (isFloat || id == Type::IntegerTyID || id == Type::PointerTyID) {
#else
				if (isFloat || id == Type::IntegerTyID) {
#endif
					Expr::Width size = executor->getWidthForLLVMType(
							ki->inst->getType());
					ref<Expr> value = executor->getDestCell(thread, ki).value;
					ref<Expr> symbolic = manualMakeTaintSymbolic(state,
							(*currentEvent)->globalVarFullName, size);
					executor->setDestCell(thread, ki, symbolic);
					symbolicMap[(*currentEvent)->globalVarFullName] = value;
//					std::cerr << "globalVarFullName : " << (*currentEvent)->globalVarFullName << "\n";
				}
			} else {
				//会丢失指针的一些关系约束，但是不影响。
				if (id == Type::PointerTyID && PTR) {
					ref<Expr> address = executor->eval(ki, 0, thread).value;
					for (std::map<ref<Expr>, ref<Expr> >::iterator it =
							addressSymbolicMap.begin(), ie =
							addressSymbolicMap.end(); it != ie; ++it) {
						if (it->first == address) {
							executor->setDestCell(state.currentThread, ki,
									it->second);
							break;
						}
					}
				} else {

				}
			}
			ref<Expr> address = executor->eval(ki, 0, thread).value;
			ref<Expr> value = executor->getDestCell(thread, ki).value;
			ObjectPair op;
			executor->getMemoryObject(op, state, address);
			const ObjectState *os = op.second;
			bool isTaint = false;
			if (os->isTaint.find(address) != os->isTaint.end()) {
				isTaint = true;
			}
			if (isTaint) {
				manualMakeTaint(value, true);
				if (!inst->getType()->isPointerTy() && (*currentEvent)->isGlobal) {
					trace->DTAMSerial.insert((*currentEvent)->globalVarFullName);

//					inst->dump();
				}

			} else {
				manualMakeTaint(value, false);
			}
			executor->setDestCell(thread, ki, value);
//			cerr << value << " taint : " << isTaint << "\n";
			break;
		}
		case Instruction::Store: {
			if ((*currentEvent)->isGlobal) {
				for (unsigned i = 0; i < thread->vectorClock.size(); i++) {
					(*currentEvent)->vectorClock.push_back(thread->vectorClock[i]);
//					cerr << "vectorClock " << i << " : " << (*currentEvent)->vectorClock[i] << "\n";
				}
			}
			break;
		}
		case Instruction::Call: {
			CallSite cs(inst);
			Function *f = (*currentEvent)->calledFunction;
			if (!(*currentEvent)->isFunctionWithSourceCode) {
				unsigned numArgs = cs.arg_size();
				bool isTaint = 0;
				for (unsigned j = numArgs; j > 0; j--) {
					ref<Expr> value = executor->eval(ki, j, thread).value;
					if(value->isTaint){
						isTaint = true;
					}
				}
				ref<Expr> returnValue = executor->getDestCell(
						state.currentThread, ki).value;
				if (isTaint) {
					returnValue.get()->isTaint = true;
				}
				executor->setDestCell(state.currentThread, ki, returnValue);
			}
			if (f->getName() == "make_taint") {
				ref<Expr> address =
						executor->eval(ki, 1, state.currentThread).value;
				ObjectPair op;
				executor->getMemoryObject(op, state, address);
				const MemoryObject *mo = op.first;
				const ObjectState* os = op.second;
				ObjectState *wos = state.addressSpace.getWriteable(mo, os);
				wos->insertTaint(address);

				trace->initTaintSymbolicExpr.insert((*currentEvent)->globalVarFullName);

			} else if (f->getName() == "pthread_create") {

				ref<Expr> pthreadAddress = executor->eval(ki, 1,
						state.currentThread).value;
				ObjectPair pthreadop;
				executor->getMemoryObject(pthreadop, state, pthreadAddress);
				const ObjectState* pthreados = pthreadop.second;
				const MemoryObject* pthreadmo = pthreadop.first;
				Expr::Width size = BIT_WIDTH;
				ref<Expr> value = pthreados->read(0, size);
				if (executor->isGlobalMO(pthreadmo)) {
					string globalVarFullName =
							(*currentEvent)->globalVarFullName;
					symbolicMap[globalVarFullName] = value;
				}

				thread->vectorClock[thread->threadId]++;
			} else if (f->getName().str() == "pthread_join") {
				thread->vectorClock[thread->threadId]++;
			} else if (f->getName().str() == "pthread_cond_wait") {
				thread->vectorClock[thread->threadId]++;
			} else if (f->getName().str() == "pthread_cond_signal") {
				thread->vectorClock[thread->threadId]++;
			} else if (f->getName().str() == "pthread_cond_broadcast") {
				thread->vectorClock[thread->threadId]++;
			} else if (f->getName().str() == "pthread_mutex_lock") {
//				thread->vectorClock[thread->threadId]++;
			} else if (f->getName().str() == "pthread_mutex_unlock") {
//				thread->vectorClock[thread->threadId]++;
			} else if (f->getName().str() == "pthread_barrier_wait") {
				assert(0 && "目前没做");
			}
			break;
		}
		case Instruction::GetElementPtr: {
			break;
		}
		default: {

			break;
		}
		}
	}
	if (currentEvent != endEvent)
		currentEvent++;
}

//消息响应函数，在被测程序解释执行之后调用
void TaintListener::afterRunMethodAsMain() {
	cerr << "######################taint analysis####################\n";

}

//消息相应函数，在创建了新线程之后调用
void TaintListener::createThread(ExecutionState &state, Thread* thread) {

}

//消息相应函数，在前缀执行出错之后程序推出之前调用
void TaintListener::executionFailed(ExecutionState &state, KInstruction *ki) {
	rdManager->getCurrentTrace()->traceType = Trace::FAILED;
}

ref<Expr> TaintListener::manualMakeTaintSymbolic(ExecutionState& state,
		std::string name, unsigned size) {

	//添加新的污染符号变量
	//name maybe need add a "Tag"
	const Array *array = new Array(name, size);
	ObjectState *os = new ObjectState(size, array);
	ref<Expr> offset = ConstantExpr::create(0, BIT_WIDTH);
	ref<Expr> result = os->read(offset, size);
#if DEBUGSYMBOLIC
	cerr << "Event name : " << (*currentEvent)->eventName << "\n";
	cerr << "make symboic:" << name << std::endl;
	cerr << "isTaint:" << isTaint << std::endl;
	std::cerr << "result : ";
	result->dump();
#endif
	return result;

}

void TaintListener::manualMakeTaint(ref<Expr> value, bool isTaint) {
	value->isTaint = isTaint;
}

ref<Expr> TaintListener::readExpr(ExecutionState &state, ref<Expr> address,
		Expr::Width size) {
	ObjectPair op;
	executor->getMemoryObject(op, state, address);
	const MemoryObject *mo = op.first;
	ref<Expr> offset = mo->getOffsetExpr(address);
	const ObjectState *os = op.second;
	ref<Expr> result = os->read(offset, size);
	return result;
}

}

