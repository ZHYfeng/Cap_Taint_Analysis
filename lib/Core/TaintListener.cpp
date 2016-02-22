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
	if ((*currentEvent)) {
		Instruction* inst = ki->inst;
		Thread* thread = state.currentThread;
//		cerr << "event name : " << (*currentEvent)->eventName << " ";
//		cerr << "thread id : " << thread->threadId;
//		inst->dump();
//		cerr << "thread id : " << (*currentEvent)->threadId ;
//		(*currentEvent)->inst->inst->dump();
		switch (inst->getOpcode()) {

		}
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
			ref<Expr> function = executor->eval(ki, 0, thread).value;
			if (function->getKind() == Expr::Concat) {
				ref<Expr> value = symbolicMap[filter.getFullName(function)];
				if (value->getKind() != Expr::Constant) {
					assert(0 && "call function is symbolic");
				}
				executor->evalAgainst(ki, 0, thread, value);
			}
			if (!(*currentEvent)->isFunctionWithSourceCode) {
				unsigned numArgs = cs.arg_size();
				for (unsigned j = numArgs; j > 0; j--) {
					ref<Expr> value = executor->eval(ki, j, thread).value;
					Type::TypeID id = cs.getArgument(j - 1)->getType()->getTypeID();
					bool isFloat = 0;
					if ((id >= Type::HalfTyID) && (id <= Type::DoubleTyID)) {
						isFloat = 1;
					}
					if (isFloat || id == Type::IntegerTyID || id == Type::PointerTyID) {
						if (value->getKind() == Expr::Constant) {

						} else if (value->getKind() == Expr::Concat || value->getKind() == Expr::Read) {
							ref<Expr> svalue = symbolicMap[filter.getFullName(value)];
							if (svalue->getKind() != Expr::Constant) {
								assert(0 && "store value is symbolic");
							} else if (id == Type::PointerTyID && value->getKind() == Expr::Read) {
								assert(0 && "pointer is expr::read");
							}
							executor->evalAgainst(ki, j, thread, svalue);
						} else {
							ref<Expr> svalue = (*currentEvent)->value[j-1];
							if (svalue->getKind() != Expr::Constant) {
								assert(0 && "store value is symbolic");
							} else if (id == Type::PointerTyID) {
								assert(0 && "pointer is other symbolic");
							}
							executor->evalAgainst(ki, j, thread, svalue);
						}
					} else {
						if (value->getKind() != Expr::Constant) {
							assert(0 && "store value is symbolic and type is other");
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
			ref<Expr> base = executor->eval(ki, 1, thread).value;
			Type::TypeID id = ki->inst->getOperand(0)->getType()->getTypeID();
			//			cerr << "store value : " << value << std::endl;
			//			cerr << "store base : " << base << std::endl;
			//			cerr << "value->getKind() : " << value->getKind() << std::endl;
			//			cerr << "TypeID id : " << id << std::endl;
			bool isFloat = 0;
			if ((id >= Type::HalfTyID) && (id <= Type::DoubleTyID)) {
				isFloat = 1;
			}
			if ((*currentEvent)->isGlobal) {
				if (isFloat || id == Type::IntegerTyID
						|| id == Type::PointerTyID) {
					Expr::Width size = executor->getWidthForLLVMType(
							ki->inst->getOperand(0)->getType());
					ref<Expr> address = executor->eval(ki, 1, thread).value;
					ref<Expr> symbolic = manualMakeTaintSymbolic(state,
							(*currentEvent)->globalVarFullName, size, isFloat);
					ref<Expr> constraint = EqExpr::create(value, symbolic);
					trace->storeSymbolicExpr.push_back(constraint);
					//					cerr << "event name : " << (*currentEvent)->eventName << "\n";
					//					cerr << "store constraint : " << constraint << "\n";
					if (value->getKind() == Expr::Constant) {

					} else if (value->getKind() == Expr::Concat || value->getKind() == Expr::Read) {
						ref<Expr> svalue = symbolicMap[filter.getFullName(value)];
						if (svalue->getKind() != Expr::Constant) {
							assert(0 && "store value is symbolic");
						} else if (id == Type::PointerTyID && value->getKind() == Expr::Read) {
							assert(0 && "pointer is Expr::read");
						}
						executor->evalAgainst(ki, 0, thread, svalue);
					} else {
						ref<Expr> svalue = (*currentEvent)->value.back();
						if (svalue->getKind() != Expr::Constant) {
							assert(0 && "store value is symbolic");
						} else if (id == Type::PointerTyID) {
							assert(0 && "pointer is other symbolic");
						}
						executor->evalAgainst(ki, 0, thread, svalue);
					}
				} else {
					if (value->getKind() != Expr::Constant) {
						assert(0 && "store value is symbolic and type is other");
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
						//						cerr << "address : " << address << " value : " << value << "\n";
					} else if (value->getKind() == Expr::Read) {
						assert(0 && "pointer is expr::read");
					} else {
						ref<Expr> address = executor->eval(ki, 1, thread).value;
						addressSymbolicMap[address] = value;
						//						cerr << "address : " << address << " value : " << value << "\n";
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
			std::vector<ref<klee::Expr> >::iterator first = (*currentEvent)->value.begin();
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
		default: {
			break;
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

				//指针！！！
#if PTR
				if (isFloat || id == Type::IntegerTyID || id == Type::PointerTyID) {
#else
				if (isFloat || id == Type::IntegerTyID) {
#endif
					Expr::Width size = executor->getWidthForLLVMType(
							ki->inst->getType());
					ref<Expr> address = executor->eval(ki, 0, thread).value;
					ObjectPair op;
					executor->getMemoryObject(op, state, address);
					const ObjectState *os = op.second;
					ref<Expr> value = executor->getDestCell(thread, ki).value;
					ref<Expr> symbolic = manualMakeTaintSymbolic(state,
							(*currentEvent)->globalVarFullName, size, os->isTaint);
					executor->setDestCell(thread, ki, symbolic);
					symbolicMap[(*currentEvent)->globalVarFullName] = value;
				}
			} else {
				//会丢失指针的一些关系约束，但是不影响。
				if (id == Type::PointerTyID && PTR) {
					ref<Expr> address = executor->eval(ki, 0, thread).value;
					for (std::map<ref<Expr>, ref<Expr> >::iterator it =
							addressSymbolicMap.begin(), ie =
							addressSymbolicMap.end(); it != ie; ++it) {
						if (it->first == address) {
//							cerr << "it->first : " << it->first << " it->second : " << it->second << "\n";
							executor->setDestCell(state.currentThread, ki, it->second);
							break;
						}
					}
				} else {

				}
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
			ref<Expr> base = executor->eval(ki, 1, thread).value;
			Type::TypeID id = ki->inst->getOperand(0)->getType()->getTypeID();
			//			cerr << "store value : " << value << std::endl;
			//			cerr << "store base : " << base << std::endl;
			//			cerr << "value->getKind() : " << value->getKind() << std::endl;
			//			cerr << "TypeID id : " << id << std::endl;
			bool isFloat = 0;
			if ((id >= Type::HalfTyID) && (id <= Type::DoubleTyID)) {
				isFloat = 1;
			}
			if ((*currentEvent)->isGlobal) {
				if (isFloat || id == Type::IntegerTyID
						|| id == Type::PointerTyID) {
					Expr::Width size = executor->getWidthForLLVMType(
							ki->inst->getOperand(0)->getType());
					ref<Expr> address = executor->eval(ki, 1, thread).value;
					ref<Expr> symbolic = manualMakeTaintSymbolic(state,
							(*currentEvent)->globalVarFullName, size, isFloat);
					ref<Expr> constraint = EqExpr::create(value, symbolic);
					trace->storeSymbolicExpr.push_back(constraint);
					//					cerr << "event name : " << (*currentEvent)->eventName << "\n";
					//					cerr << "store constraint : " << constraint << "\n";
					if (value->getKind() == Expr::Constant) {

					} else if (value->getKind() == Expr::Concat || value->getKind() == Expr::Read) {
						ref<Expr> svalue = symbolicMap[filter.getFullName(value)];
						if (svalue->getKind() != Expr::Constant) {
							assert(0 && "store value is symbolic");
						} else if (id == Type::PointerTyID && value->getKind() == Expr::Read) {
							assert(0 && "pointer is Expr::read");
						}
						executor->evalAgainst(ki, 0, thread, svalue);
					} else {
						ref<Expr> svalue = (*currentEvent)->value.back();
						if (svalue->getKind() != Expr::Constant) {
							assert(0 && "store value is symbolic");
						} else if (id == Type::PointerTyID) {
							assert(0 && "pointer is other symbolic");
						}
						executor->evalAgainst(ki, 0, thread, svalue);
					}
				} else {
					if (value->getKind() != Expr::Constant) {
						assert(0 && "store value is symbolic and type is other");
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
						//						cerr << "address : " << address << " value : " << value << "\n";
					} else if (value->getKind() == Expr::Read) {
						assert(0 && "pointer is expr::read");
					} else {
						ref<Expr> address = executor->eval(ki, 1, thread).value;
						addressSymbolicMap[address] = value;
						//						cerr << "address : " << address << " value : " << value << "\n";
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
		case Instruction::Call: {
			CallSite cs(inst);
			Function *f = (*currentEvent)->calledFunction;
			if (!(*currentEvent)->isFunctionWithSourceCode) {
				//TODO: taint
				ref<Expr> returnValue = executor->getDestCell(state.currentThread, ki).value;
				bool isFloat = 0;
				Type::TypeID id = inst->getType()->getTypeID();
				if ((id >= Type::HalfTyID) && (id <= Type::DoubleTyID)) {
					isFloat = 1;
				}
				if (isFloat) {
					returnValue.get()->isFloat = true;
				}
				executor->setDestCell(state.currentThread, ki, returnValue);
			}
			if (f->getName() == "strcpy") {
				//地址可能还有问题
				ref<Expr> destAddress = executor->eval(ki, 1,
						state.currentThread).value;
				//				ref<Expr> scrAddress = executor->eval(ki, 0,
				//						state.currentThread).value;
				//				ObjectPair scrop;
				ObjectPair destop;
				//				getMemoryObject(scrop, state, scrAddress);
				executor->getMemoryObject(destop, state, destAddress);
				const ObjectState* destos = destop.second;
				const MemoryObject* destmo = destop.first;
				//				std::cerr<<destAddress<<std::endl;
				//				std::cerr<<destmo->address<<std::endl;
				//				std::cerr<<"destmo->size : "<<destmo->size<<std::endl;
				Expr::Width size = 8;
				for (unsigned i = 0; i < (*currentEvent)->implicitGlobalVar.size(); i++) {
					//					std::cerr<<"dest"<<std::endl;
					ref<Expr> address = AddExpr::create(destAddress,
							ConstantExpr::create(i, BIT_WIDTH));
					ref<Expr> value = destos->read(
							destmo->getOffsetExpr(address), size);
					//					std::cerr<<"value : "<<value<<std::endl;
					//					std::cerr<<"value : "<<value<<std::endl;
					if (executor->isGlobalMO(destmo)) {
						ref<Expr> value2 = manualMakeTaintSymbolic(state,
								(*currentEvent)->implicitGlobalVar[i], size,
								false);
						ref<Expr> value1 = value;
						ref<Expr> constraint = EqExpr::create(value1, value2);
						trace->storeSymbolicExpr.push_back(constraint);
						//						cerr << "constraint : " << constraint << "\n";
						//						cerr << "Store Map varName : " << (*currentEvent)->varName << "\n";
						//						cerr << "Store Map value : " << value << "\n";
					}
					if (value->isZero()) {
						break;
					}
				}
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
			} else if (f->getName() == "klee_make_taint") {
				//TODO: deal with make taint

			}
			break;
		}
		case Instruction::PHI: {
			//TODO: maybe need add taint tag
			break;
		}
		case Instruction::Select: {
			SelectInst *SI = cast<SelectInst>(ki->inst);
			assert(
					SI->getCondition() == SI->getOperand(0)
							&& "Wrong operand index!");
			ref<Expr> cond = eval(ki, 0, thread).value;
			ref<Expr> tExpr = eval(ki, 1, thread).value;
			ref<Expr> fExpr = eval(ki, 2, thread).value;
			ref<Expr> result = SelectExpr::create(cond, tExpr, fExpr);
			bindLocal(ki, thread, result);
			break;
		}
		case Instruction::Add: {
			ref<Expr> left = eval(ki, 0, thread).value;
			ref<Expr> right = eval(ki, 1, thread).value;
			bindLocal(ki, thread, AddExpr::create(left, right));
			break;
		}

		case Instruction::Sub: {
			ref<Expr> left = eval(ki, 0, thread).value;
			ref<Expr> right = eval(ki, 1, thread).value;
			bindLocal(ki, thread, SubExpr::create(left, right));
			break;
		}

		case Instruction::Mul: {
			ref<Expr> left = eval(ki, 0, thread).value;
			ref<Expr> right = eval(ki, 1, thread).value;
			bindLocal(ki, thread, MulExpr::create(left, right));
			break;
		}

		case Instruction::UDiv: {
			ref<Expr> left = eval(ki, 0, thread).value;
			ref<Expr> right = eval(ki, 1, thread).value;
			ref<Expr> result = UDivExpr::create(left, right);
			bindLocal(ki, thread, result);
			break;
		}

		case Instruction::SDiv: {
			ref<Expr> left = eval(ki, 0, thread).value;
			ref<Expr> right = eval(ki, 1, thread).value;
			ref<Expr> result = SDivExpr::create(left, right);
			bindLocal(ki, thread, result);
			break;
		}

		case Instruction::URem: {
			ref<Expr> left = eval(ki, 0, thread).value;
			ref<Expr> right = eval(ki, 1, thread).value;
			ref<Expr> result = URemExpr::create(left, right);
			bindLocal(ki, thread, result);
			break;
		}

		case Instruction::SRem: {
			ref<Expr> left = eval(ki, 0, thread).value;
			ref<Expr> right = eval(ki, 1, thread).value;
			ref<Expr> result = SRemExpr::create(left, right);
			bindLocal(ki, thread, result);
			break;
		}

		case Instruction::And: {
			ref<Expr> left = eval(ki, 0, thread).value;
			ref<Expr> right = eval(ki, 1, thread).value;
			ref<Expr> result = AndExpr::create(left, right);
			bindLocal(ki, thread, result);
			break;
		}

		case Instruction::Or: {
			ref<Expr> left = eval(ki, 0, thread).value;
			ref<Expr> right = eval(ki, 1, thread).value;
			ref<Expr> result = OrExpr::create(left, right);
			bindLocal(ki, thread, result);
			break;
		}

		case Instruction::Xor: {
			ref<Expr> left = eval(ki, 0, thread).value;
			ref<Expr> right = eval(ki, 1, thread).value;
			ref<Expr> result = XorExpr::create(left, right);
			bindLocal(ki, thread, result);
			break;
		}

		case Instruction::Shl: {
			ref<Expr> left = eval(ki, 0, thread).value;
			ref<Expr> right = eval(ki, 1, thread).value;
			ref<Expr> result = ShlExpr::create(left, right);
			bindLocal(ki, thread, result);
			break;
		}

		case Instruction::LShr: {
			ref<Expr> left = eval(ki, 0, thread).value;
			ref<Expr> right = eval(ki, 1, thread).value;
			ref<Expr> result = LShrExpr::create(left, right);
			bindLocal(ki, thread, result);
			break;
		}

		case Instruction::AShr: {
			ref<Expr> left = eval(ki, 0, thread).value;
			ref<Expr> right = eval(ki, 1, thread).value;
			ref<Expr> result = AShrExpr::create(left, right);
			bindLocal(ki, thread, result);
			break;
		}
		case Instruction::ICmp: {
			CmpInst *ci = cast<CmpInst>(i);
			ICmpInst *ii = cast<ICmpInst>(ci);

			switch (ii->getPredicate()) {
			case ICmpInst::ICMP_EQ: {
				ref<Expr> left = eval(ki, 0, thread).value;
				ref<Expr> right = eval(ki, 1, thread).value;
				ref<Expr> result = EqExpr::create(left, right);
				bindLocal(ki, thread, result);
				break;
			}

			case ICmpInst::ICMP_NE: {
				ref<Expr> left = eval(ki, 0, thread).value;
				ref<Expr> right = eval(ki, 1, thread).value;
				ref<Expr> result = NeExpr::create(left, right);
				bindLocal(ki, thread, result);
				break;
			}

			case ICmpInst::ICMP_UGT: {
				ref<Expr> left = eval(ki, 0, thread).value;
				ref<Expr> right = eval(ki, 1, thread).value;
				ref<Expr> result = UgtExpr::create(left, right);
				bindLocal(ki, thread, result);
				break;
			}

			case ICmpInst::ICMP_UGE: {
				ref<Expr> left = eval(ki, 0, thread).value;
				ref<Expr> right = eval(ki, 1, thread).value;
				ref<Expr> result = UgeExpr::create(left, right);
				bindLocal(ki, thread, result);
				break;
			}

			case ICmpInst::ICMP_ULT: {
				ref<Expr> left = eval(ki, 0, thread).value;
				ref<Expr> right = eval(ki, 1, thread).value;
				ref<Expr> result = UltExpr::create(left, right);
				bindLocal(ki, thread, result);
				break;
			}

			case ICmpInst::ICMP_ULE: {
				ref<Expr> left = eval(ki, 0, thread).value;
				ref<Expr> right = eval(ki, 1, thread).value;
				ref<Expr> result = UleExpr::create(left, right);
				bindLocal(ki, thread, result);
				break;
			}

			case ICmpInst::ICMP_SGT: {
				ref<Expr> left = eval(ki, 0, thread).value;
				ref<Expr> right = eval(ki, 1, thread).value;
				ref<Expr> result = SgtExpr::create(left, right);
				bindLocal(ki, thread, result);
				break;
			}

			case ICmpInst::ICMP_SGE: {
				ref<Expr> left = eval(ki, 0, thread).value;
				ref<Expr> right = eval(ki, 1, thread).value;
				ref<Expr> result = SgeExpr::create(left, right);
				bindLocal(ki, thread, result);
				break;
			}

			case ICmpInst::ICMP_SLT: {
				ref<Expr> left = eval(ki, 0, thread).value;
				ref<Expr> right = eval(ki, 1, thread).value;
				ref<Expr> result = SltExpr::create(left, right);
				bindLocal(ki, thread, result);
				break;
			}

			case ICmpInst::ICMP_SLE: {
				ref<Expr> left = eval(ki, 0, thread).value;
				ref<Expr> right = eval(ki, 1, thread).value;
				ref<Expr> result = SleExpr::create(left, right);
				bindLocal(ki, thread, result);
				break;
			}

			default:
				break;
			}
			break;
		}
			// Memory instructions...
		case Instruction::Alloca: {
			AllocaInst *ai = cast<AllocaInst>(inst);
			unsigned elementSize = kmodule->targetData->getTypeStoreSize(
					ai->getAllocatedType());
			ref<Expr> size = Expr::createPointer(elementSize);
			if (ai->isArrayAllocation()) {
				ref<Expr> count = eval(ki, 0, thread).value;
				count = Expr::createZExtToPointerWidth(count);
				size = MulExpr::create(size, count);
			}
			bool isLocal = inst->getOpcode() == Instruction::Alloca;
			executeAlloc(state, size, isLocal, ki);
			//handle local mutex, cond and barrier
			ref<Expr> result = getDestCell(thread, ki).value;
			uint64_t startAddress =
					(dyn_cast<ConstantExpr>(result.get()))->getZExtValue();
			createSpecialElement(state, ai->getAllocatedType(), startAddress,
					false);
			break;
		}
		case Instruction::GetElementPtr: {
//			ref<Expr> value = executor->getDestCell(state.currentThread, ki).value;
//			cerr << "value : " << value << "\n";
			break;
		}
			// Conversion
		case Instruction::Trunc: {
			CastInst *ci = cast<CastInst>(i);
			ref<Expr> result = ExtractExpr::create(eval(ki, 0, thread).value, 0,
					getWidthForLLVMType(ci->getType()));
			bindLocal(ki, thread, result);
			break;
		}
		case Instruction::ZExt: {
			CastInst *ci = cast<CastInst>(i);
			ref<Expr> result = ZExtExpr::create(eval(ki, 0, thread).value,
					getWidthForLLVMType(ci->getType()));
			bindLocal(ki, thread, result);
			break;
		}
		case Instruction::SExt: {
			CastInst *ci = cast<CastInst>(i);
			ref<Expr> result = SExtExpr::create(eval(ki, 0, thread).value,
					getWidthForLLVMType(ci->getType()));
			bindLocal(ki, thread, result);
			break;
		}

		case Instruction::IntToPtr: {
			CastInst *ci = cast<CastInst>(i);
			Expr::Width pType = getWidthForLLVMType(ci->getType());
			ref<Expr> arg = eval(ki, 0, thread).value;
			bindLocal(ki, thread, ZExtExpr::create(arg, pType));
			break;
		}
		case Instruction::PtrToInt: {
			//			CastInst *ci = cast<CastInst>(inst);
			//			Expr::Width iType = executor->getWidthForLLVMType(ci->getType());
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

		case Instruction::BitCast: {
			ref<Expr> result = eval(ki, 0, thread).value;
			bindLocal(ki, thread, result);
			break;
		}

			// Floating point instructions

		case Instruction::FAdd: {

			ref<Expr> originLeft = eval(ki, 0, thread).value;
			ref<Expr> originRight = eval(ki, 1, thread).value;

			ConstantExpr *leftCE = dyn_cast<ConstantExpr>(originLeft);
			ConstantExpr *rightCE = dyn_cast<ConstantExpr>(originRight);
			if (leftCE != NULL && rightCE != NULL) {
				ref<ConstantExpr> left = toConstant(state,
						eval(ki, 0, thread).value, "floating point");
				ref<ConstantExpr> right = toConstant(state,
						eval(ki, 1, thread).value, "floating point");
				if (!fpWidthToSemantics(left->getWidth())
						|| !fpWidthToSemantics(right->getWidth()))
					return terminateStateOnExecError(state,
							"Unsupported FAdd operation");

#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
				llvm::APFloat Res(*fpWidthToSemantics(left->getWidth()),
						left->getAPValue());
				Res.add(
						APFloat(*fpWidthToSemantics(right->getWidth()),
								right->getAPValue()),
						APFloat::rmNearestTiesToEven);
#else
				llvm::APFloat Res(left->getAPValue());
				Res.add(APFloat(right->getAPValue()), APFloat::rmNearestTiesToEven);
#endif
				ref<Expr> result = ConstantExpr::alloc(Res.bitcastToAPInt());
				result.get()->isFloat = true;
				bindLocal(ki, thread, result);
				//    bindLocal(ki, thread, ConstantExpr::alloc(Res.bitcastToAPInt()));
			} else {
				ref<Expr> res = AddExpr::create(originLeft, originRight);
				res.get()->isFloat = true;
				bindLocal(ki, thread, res);
			}
			break;
		}

		case Instruction::FSub: {
			ref<Expr> originLeft = eval(ki, 0, thread).value;
			ref<Expr> originRight = eval(ki, 1, thread).value;

			ConstantExpr *leftCE = dyn_cast<ConstantExpr>(originLeft);
			ConstantExpr *rightCE = dyn_cast<ConstantExpr>(originRight);
			if (leftCE != NULL && rightCE != NULL) {
				ref<ConstantExpr> left = toConstant(state,
						eval(ki, 0, thread).value, "floating point");
				ref<ConstantExpr> right = toConstant(state,
						eval(ki, 1, thread).value, "floating point");
				if (!fpWidthToSemantics(left->getWidth())
						|| !fpWidthToSemantics(right->getWidth()))
					return terminateStateOnExecError(state,
							"Unsupported FSub operation");
#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
				llvm::APFloat Res(*fpWidthToSemantics(left->getWidth()),
						left->getAPValue());
				Res.subtract(
						APFloat(*fpWidthToSemantics(right->getWidth()),
								right->getAPValue()),
						APFloat::rmNearestTiesToEven);
#else
				llvm::APFloat Res(left->getAPValue());
				Res.subtract(APFloat(right->getAPValue()), APFloat::rmNearestTiesToEven);
#endif
				ref<Expr> result = ConstantExpr::alloc(Res.bitcastToAPInt());
				result.get()->isFloat = true;
				bindLocal(ki, thread, result);
			} else {
				originLeft.get()->isFloat = true;
				originRight.get()->isFloat = true;
				ref<Expr> res = SubExpr::create(originLeft, originRight);
				res.get()->isFloat = true;
				bindLocal(ki, thread, res);
			}
			break;
		}

		case Instruction::FMul: {
			ref<Expr> originLeft = eval(ki, 0, thread).value;
			ref<Expr> originRight = eval(ki, 1, thread).value;

			ConstantExpr *leftCE = dyn_cast<ConstantExpr>(originLeft);
			ConstantExpr *rightCE = dyn_cast<ConstantExpr>(originRight);
			if (leftCE != NULL && rightCE != NULL) {
				ref<ConstantExpr> left = toConstant(state,
						eval(ki, 0, thread).value, "floating point");
				ref<ConstantExpr> right = toConstant(state,
						eval(ki, 1, thread).value, "floating point");
				if (!fpWidthToSemantics(left->getWidth())
						|| !fpWidthToSemantics(right->getWidth()))
					return terminateStateOnExecError(state,
							"Unsupported FMul operation");

#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
				llvm::APFloat Res(*fpWidthToSemantics(left->getWidth()),
						left->getAPValue());
				Res.multiply(
						APFloat(*fpWidthToSemantics(right->getWidth()),
								right->getAPValue()),
						APFloat::rmNearestTiesToEven);
#else
				llvm::APFloat Res(left->getAPValue());
				Res.multiply(APFloat(right->getAPValue()), APFloat::rmNearestTiesToEven);
#endif
				ref<Expr> result = ConstantExpr::alloc(Res.bitcastToAPInt());
				result.get()->isFloat = true;
				bindLocal(ki, thread, result);
				//    bindLocal(ki, thread, ConstantExpr::alloc(Res.bitcastToAPInt()));
			} else {
				originLeft.get()->isFloat = true;
				originRight.get()->isFloat = true;
				//			cerr << "MulExpr : "<< originLeft << " * "<< originRight << "\n";
				ref<Expr> res = MulExpr::create(originLeft, originRight);
				//			cerr << "MulExpr : "<< res << "\n";
				res.get()->isFloat = true;
				bindLocal(ki, thread, res);
			}
			break;
		}

		case Instruction::FDiv: {
			ref<Expr> originLeft = eval(ki, 0, thread).value;
			ref<Expr> originRight = eval(ki, 1, thread).value;

			ConstantExpr *leftCE = dyn_cast<ConstantExpr>(originLeft);
			ConstantExpr *rightCE = dyn_cast<ConstantExpr>(originRight);
			if (leftCE != NULL && rightCE != NULL) {
				ref<ConstantExpr> left = toConstant(state,
						eval(ki, 0, thread).value, "floating point");
				ref<ConstantExpr> right = toConstant(state,
						eval(ki, 1, thread).value, "floating point");
				if (!fpWidthToSemantics(left->getWidth())
						|| !fpWidthToSemantics(right->getWidth()))
					return terminateStateOnExecError(state,
							"Unsupported FDiv operation");

#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
				llvm::APFloat Res(*fpWidthToSemantics(left->getWidth()),
						left->getAPValue());
				Res.divide(
						APFloat(*fpWidthToSemantics(right->getWidth()),
								right->getAPValue()),
						APFloat::rmNearestTiesToEven);
#else
				llvm::APFloat Res(left->getAPValue());
				Res.divide(APFloat(right->getAPValue()), APFloat::rmNearestTiesToEven);
#endif
				ref<Expr> result = ConstantExpr::alloc(Res.bitcastToAPInt());
				result.get()->isFloat = true;
				bindLocal(ki, thread, result);
				//    bindLocal(ki, thread, ConstantExpr::alloc(Res.bitcastToAPInt()));
			} else {
				originLeft.get()->isFloat = true;
				originRight.get()->isFloat = true;
				ref<Expr> result = SDivExpr::create(originLeft, originRight);
				result.get()->isFloat = true;
				bindLocal(ki, thread, result);
			}
			break;
		}

		case Instruction::FRem: {
			ref<Expr> originLeft = eval(ki, 0, thread).value;
			ref<Expr> originRight = eval(ki, 1, thread).value;

			ConstantExpr *leftCE = dyn_cast<ConstantExpr>(originLeft);
			ConstantExpr *rightCE = dyn_cast<ConstantExpr>(originRight);
			if (leftCE != NULL && rightCE != NULL) {
				ref<ConstantExpr> left = toConstant(state,
						eval(ki, 0, thread).value, "floating point");
				ref<ConstantExpr> right = toConstant(state,
						eval(ki, 1, thread).value, "floating point");
				if (!fpWidthToSemantics(left->getWidth())
						|| !fpWidthToSemantics(right->getWidth()))
					return terminateStateOnExecError(state,
							"Unsupported FRem operation");
#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
				llvm::APFloat Res(*fpWidthToSemantics(left->getWidth()),
						left->getAPValue());
				Res.remainder(
						APFloat(*fpWidthToSemantics(right->getWidth()),
								right->getAPValue()));
#else
				llvm::APFloat Res(left->getAPValue());
				Res.mod(APFloat(right->getAPValue()), APFloat::rmNearestTiesToEven);
#endif
				ref<Expr> result = ConstantExpr::alloc(Res.bitcastToAPInt());
				result.get()->isFloat = true;
				bindLocal(ki, thread, result);
				//    bindLocal(ki, thread, ConstantExpr::alloc(Res.bitcastToAPInt()));
			} else {
				ref<Expr> result = SRemExpr::create(originLeft, originRight);
				result.get()->isFloat = true;
				bindLocal(ki, thread, result);
			}
			break;
		}

		case Instruction::FPTrunc: {

			FPTruncInst *fi = cast<FPTruncInst>(i);
			ref<Expr> srcExpr = eval(ki, 0, thread).value;
			ConstantExpr *srcCons = dyn_cast<ConstantExpr>(srcExpr);
			if (srcCons != NULL) {
				//	  FPTruncInst *fi = cast<FPTruncInst>(i);
				Expr::Width resultType = getWidthForLLVMType(fi->getType());
				ref<ConstantExpr> arg = toConstant(state,
						eval(ki, 0, thread).value, "floating point");
				if (!fpWidthToSemantics(arg->getWidth())
						|| resultType > arg->getWidth())
					return terminateStateOnExecError(state,
							"Unsupported FPTrunc operation");

#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
				llvm::APFloat Res(*fpWidthToSemantics(arg->getWidth()),
						arg->getAPValue());
#else
				llvm::APFloat Res(arg->getAPValue());
#endif
				bool losesInfo = false;
				Res.convert(*fpWidthToSemantics(resultType),
						llvm::APFloat::rmNearestTiesToEven, &losesInfo);
				ref<Expr> result = ConstantExpr::alloc(Res);
				result.get()->isFloat = true;
				bindLocal(ki, thread, result);
				//    bindLocal(ki, thread, ConstantExpr::alloc(Res));
			} else {
				ref<Expr> result = ExtractExpr::create(
						eval(ki, 0, thread).value, 0,
						getWidthForLLVMType(fi->getType()));
				result.get()->isFloat = true;
				bindLocal(ki, thread, result);
			}
			break;
		}

		case Instruction::FPExt: {
			FPExtInst *fi = cast<FPExtInst>(i);
			ref<Expr> srcExpr = eval(ki, 0, thread).value;
			ConstantExpr *srcCons = dyn_cast<ConstantExpr>(srcExpr);
			if (srcCons != NULL) {
				//    FPExtInst *fi = cast<FPExtInst>(i);
				Expr::Width resultType = getWidthForLLVMType(fi->getType());
				ref<ConstantExpr> arg = toConstant(state,
						eval(ki, 0, thread).value, "floating point");
				if (!fpWidthToSemantics(arg->getWidth())
						|| arg->getWidth() > resultType)
					return terminateStateOnExecError(state,
							"Unsupported FPExt operation");
#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
				llvm::APFloat Res(*fpWidthToSemantics(arg->getWidth()),
						arg->getAPValue());
#else
				llvm::APFloat Res(arg->getAPValue());
#endif
				bool losesInfo = false;
				Res.convert(*fpWidthToSemantics(resultType),
						llvm::APFloat::rmNearestTiesToEven, &losesInfo);
				ref<Expr> result = ConstantExpr::alloc(Res);
				result.get()->isFloat = true;
				bindLocal(ki, thread, result);
			} else {
				ref<Expr> result = SExtExpr::create(eval(ki, 0, thread).value,
						getWidthForLLVMType(fi->getType()));
				result.get()->isFloat = true;
				bindLocal(ki, thread, result);
			}
			break;
		}

		case Instruction::FPToUI: {
			FPToUIInst *fi = cast<FPToUIInst>(i);
			ref<Expr> srcExpr = eval(ki, 0, thread).value;
			ConstantExpr *srcCons = dyn_cast<ConstantExpr>(srcExpr);
			if (srcCons != NULL) {
				//    FPToUIInst *fi = cast<FPToUIInst>(i);
				Expr::Width resultType = getWidthForLLVMType(fi->getType());
				ref<ConstantExpr> arg = toConstant(state,
						eval(ki, 0, thread).value, "floating point");
				if (!fpWidthToSemantics(arg->getWidth()) || resultType > 64)
					return terminateStateOnExecError(state,
							"Unsupported FPToUI operation");

#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
				llvm::APFloat Arg(*fpWidthToSemantics(arg->getWidth()),
						arg->getAPValue());
#else
				llvm::APFloat Arg(arg->getAPValue());
#endif
				uint64_t value = 0;
				bool isExact = true;
				Arg.convertToInteger(&value, resultType, false,
						llvm::APFloat::rmTowardZero, &isExact);
				bindLocal(ki, thread, ConstantExpr::alloc(value, resultType));
			} else {
				ref<Expr> result = ExtractExpr::alloc(eval(ki, 0, thread).value,
						0, getWidthForLLVMType(fi->getType()));
				result.get()->isFloat = false;
				bindLocal(ki, thread, result);
			}
			break;
		}

		case Instruction::FPToSI: {

			FPToSIInst *fi = cast<FPToSIInst>(i);
			ref<Expr> srcExpr = eval(ki, 0, thread).value;
			ConstantExpr *srcCons = dyn_cast<ConstantExpr>(srcExpr);
			if (srcCons != NULL) {
				//	  FPToSIInst *fi = cast<FPToSIInst>(i);
				Expr::Width resultType = getWidthForLLVMType(fi->getType());
				ref<ConstantExpr> arg = toConstant(state,
						eval(ki, 0, thread).value, "floating point");
				if (!fpWidthToSemantics(arg->getWidth()) || resultType > 64)
					return terminateStateOnExecError(state,
							"Unsupported FPToSI operation");
#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
				llvm::APFloat Arg(*fpWidthToSemantics(arg->getWidth()),
						arg->getAPValue());
#else
				llvm::APFloat Arg(arg->getAPValue());

#endif
				uint64_t value = 0;
				bool isExact = true;
				Arg.convertToInteger(&value, resultType, true,
						llvm::APFloat::rmTowardZero, &isExact);
				bindLocal(ki, thread, ConstantExpr::alloc(value, resultType));
			} else {
				ref<Expr> result = ExtractExpr::alloc(eval(ki, 0, thread).value,
						0, getWidthForLLVMType(fi->getType()));
				result.get()->isFloat = false;
				//			std::cerr << "fptosi in exe ";
				//			std::cerr << result.get()->getKind() << "\n";
				//			result.get()->dump();
				bindLocal(ki, thread, result);
			}
			break;
		}

		case Instruction::UIToFP: {
			UIToFPInst *fi = cast<UIToFPInst>(i);
			ref<Expr> srcExpr = eval(ki, 0, thread).value;
			ConstantExpr *srcCons = dyn_cast<ConstantExpr>(srcExpr);
			if (srcCons != NULL) {
				//    UIToFPInst *fi = cast<UIToFPInst>(i);
				Expr::Width resultType = getWidthForLLVMType(fi->getType());
				ref<ConstantExpr> arg = toConstant(state,
						eval(ki, 0, thread).value, "floating point");
				const llvm::fltSemantics *semantics = fpWidthToSemantics(
						resultType);
				if (!semantics)
					return terminateStateOnExecError(state,
							"Unsupported UIToFP operation");
				llvm::APFloat f(*semantics, 0);
				f.convertFromAPInt(arg->getAPValue(), false,
						llvm::APFloat::rmNearestTiesToEven);

				ref<Expr> result = ConstantExpr::alloc(f);
				result.get()->isFloat = true;
				bindLocal(ki, thread, result);
			} else {
				ref<Expr> result = SExtExpr::alloc(eval(ki, 0, thread).value,
						getWidthForLLVMType(fi->getType()));
				result.get()->isFloat = true;
				bindLocal(ki, thread, result);
			}
			break;
		}

		case Instruction::SIToFP: {
			SIToFPInst *fi = cast<SIToFPInst>(i);

			ref<Expr> srcExpr = eval(ki, 0, thread).value;
			ConstantExpr *srcCons = dyn_cast<ConstantExpr>(srcExpr);
			if (srcCons != NULL) {
				//	  SIToFPInst *fi = cast<SIToFPInst>(i);
				Expr::Width resultType = getWidthForLLVMType(fi->getType());
				ref<ConstantExpr> arg = toConstant(state,
						eval(ki, 0, thread).value, "floating point");
				const llvm::fltSemantics *semantics = fpWidthToSemantics(
						resultType);
				if (!semantics)
					return terminateStateOnExecError(state,
							"Unsupported SIToFP operation");
				llvm::APFloat f(*semantics, 0);
				f.convertFromAPInt(arg->getAPValue(), true,
						llvm::APFloat::rmNearestTiesToEven);

				ref<Expr> result = ConstantExpr::alloc(f);
				result.get()->isFloat = true;
				bindLocal(ki, thread, result);
			} else {
				ref<Expr> result = SExtExpr::alloc(eval(ki, 0, thread).value,
						getWidthForLLVMType(fi->getType()));
				result.get()->isFloat = true;
				bindLocal(ki, thread, result);
			}
			break;
		}

		case Instruction::FCmp: {
			FCmpInst *fi = cast<FCmpInst>(i);
			ref<Expr> originLeft = eval(ki, 0, thread).value;
			ref<Expr> originRight = eval(ki, 1, thread).value;
			ConstantExpr *leftCE = dyn_cast<ConstantExpr>(originLeft);
			ConstantExpr *rightCE = dyn_cast<ConstantExpr>(originRight);
			if (leftCE != NULL && rightCE != NULL) {
				//    FCmpInst *fi = cast<FCmpInst>(i);
				ref<ConstantExpr> left = toConstant(state,
						eval(ki, 0, thread).value, "floating point");
				ref<ConstantExpr> right = toConstant(state,
						eval(ki, 1, thread).value, "floating point");
				if (!fpWidthToSemantics(left->getWidth())
						|| !fpWidthToSemantics(right->getWidth()))
					return terminateStateOnExecError(state,
							"Unsupported FCmp operation");

#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
				APFloat LHS(*fpWidthToSemantics(left->getWidth()),
						left->getAPValue());
				APFloat RHS(*fpWidthToSemantics(right->getWidth()),
						right->getAPValue());
#else
				APFloat LHS(left->getAPValue());
				APFloat RHS(right->getAPValue());
#endif
				APFloat::cmpResult CmpRes = LHS.compare(RHS);

				bool Result = false;
				switch (fi->getPredicate()) {
				// Predicates which only care about whether or not the operands are NaNs.
				case FCmpInst::FCMP_ORD:
					Result = CmpRes != APFloat::cmpUnordered;
					break;

				case FCmpInst::FCMP_UNO:
					Result = CmpRes == APFloat::cmpUnordered;
					break;

					// Ordered comparisons return false if either operand is NaN.  Unordered
					// comparisons return true if either operand is NaN.
				case FCmpInst::FCMP_UEQ:
					if (CmpRes == APFloat::cmpUnordered) {
						Result = true;
						break;
					}
				case FCmpInst::FCMP_OEQ:
					Result = CmpRes == APFloat::cmpEqual;
					break;

				case FCmpInst::FCMP_UGT:
					if (CmpRes == APFloat::cmpUnordered) {
						Result = true;
						break;
					}
				case FCmpInst::FCMP_OGT:
					Result = CmpRes == APFloat::cmpGreaterThan;
					break;

				case FCmpInst::FCMP_UGE:
					if (CmpRes == APFloat::cmpUnordered) {
						Result = true;
						break;
					}
				case FCmpInst::FCMP_OGE:
					Result = CmpRes == APFloat::cmpGreaterThan
							|| CmpRes == APFloat::cmpEqual;
					break;

				case FCmpInst::FCMP_ULT:
					if (CmpRes == APFloat::cmpUnordered) {
						Result = true;
						break;
					}
				case FCmpInst::FCMP_OLT:
					Result = CmpRes == APFloat::cmpLessThan;
					break;

				case FCmpInst::FCMP_ULE:
					if (CmpRes == APFloat::cmpUnordered) {
						Result = true;
						break;
					}
				case FCmpInst::FCMP_OLE:
					Result = CmpRes == APFloat::cmpLessThan
							|| CmpRes == APFloat::cmpEqual;
					break;

				case FCmpInst::FCMP_UNE:
					Result = CmpRes == APFloat::cmpUnordered
							|| CmpRes != APFloat::cmpEqual;
					break;
				case FCmpInst::FCMP_ONE:
					Result = CmpRes != APFloat::cmpUnordered
							&& CmpRes != APFloat::cmpEqual;
					break;

				default:
					assert(0 && "Invalid FCMP predicate!");
				case FCmpInst::FCMP_FALSE:
					Result = false;
					break;
				case FCmpInst::FCMP_TRUE:
					Result = true;
					break;
				}
				bindLocal(ki, thread, ConstantExpr::alloc(Result, Expr::Bool));
			} else {
				switch (fi->getPredicate()) {
				case FCmpInst::FCMP_ORD:
					break;
				case FCmpInst::FCMP_UNO:
					break;
				case FCmpInst::FCMP_UEQ:
					bindLocal(ki, thread,
							EqExpr::alloc(originLeft, originRight));
					break;
				case FCmpInst::FCMP_OEQ:
					bindLocal(ki, thread,
							EqExpr::alloc(originLeft, originRight));
					break;
				case FCmpInst::FCMP_UGT:
					bindLocal(ki, thread,
							SltExpr::alloc(originRight, originLeft));
					break;
				case FCmpInst::FCMP_OGT:
					bindLocal(ki, thread,
							SltExpr::alloc(originRight, originLeft));
					break;
				case FCmpInst::FCMP_UGE:
					bindLocal(ki, thread,
							SleExpr::alloc(originRight, originLeft));
					break;
				case FCmpInst::FCMP_OGE:
					bindLocal(ki, thread,
							SleExpr::alloc(originRight, originLeft));
					break;
				case FCmpInst::FCMP_ULT:
					bindLocal(ki, thread,
							SltExpr::alloc(originLeft, originRight));
					break;
				case FCmpInst::FCMP_OLT:
					bindLocal(ki, thread,
							SltExpr::alloc(originLeft, originRight));
					break;
				case FCmpInst::FCMP_ULE:
					bindLocal(ki, thread,
							SleExpr::alloc(originLeft, originRight));
					break;
				case FCmpInst::FCMP_OLE:
					bindLocal(ki, thread,
							SleExpr::alloc(originLeft, originRight));
					break;
				case FCmpInst::FCMP_UNE:
					bindLocal(ki, thread,
							NeExpr::alloc(originLeft, originRight));
					break;
				case FCmpInst::FCMP_ONE:
					bindLocal(ki, thread,
							NeExpr::alloc(originLeft, originRight));
					break;
				case FCmpInst::FCMP_FALSE:
					bindLocal(ki, thread, ConstantExpr::alloc(0, 1));
				case FCmpInst::FCMP_TRUE:
					bindLocal(ki, thread, ConstantExpr::alloc(1, 1));
					break;
				default:
					assert(0 && "Invalid FCMP predicate!");
					break;
				}
			}
			break;
		}
		case Instruction::InsertValue: {
			KGEPInstruction *kgepi = static_cast<KGEPInstruction*>(ki);

			ref<Expr> agg = eval(ki, 0, thread).value;
			ref<Expr> val = eval(ki, 1, thread).value;

			ref<Expr> l = NULL, r = NULL;
			unsigned lOffset = kgepi->offset * 8, rOffset = kgepi->offset * 8
					+ val->getWidth();

			if (lOffset > 0)
				l = ExtractExpr::create(agg, 0, lOffset);
			if (rOffset < agg->getWidth())
				r = ExtractExpr::create(agg, rOffset,
						agg->getWidth() - rOffset);

			ref<Expr> result;
			if (!l.isNull() && !r.isNull())
				result = ConcatExpr::create(r, ConcatExpr::create(val, l));
			else if (!l.isNull())
				result = ConcatExpr::create(val, l);
			else if (!r.isNull())
				result = ConcatExpr::create(r, val);
			else
				result = val;

			bindLocal(ki, thread, result);
			break;
		}
		case Instruction::ExtractValue: {
			KGEPInstruction *kgepi = static_cast<KGEPInstruction*>(ki);

			ref<Expr> agg = eval(ki, 0, thread).value;

			ref<Expr> result = ExtractExpr::create(agg, kgepi->offset * 8,
					getWidthForLLVMType(i->getType()));

			bindLocal(ki, thread, result);
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
		std::string name, unsigned size, bool isTaint) {

	//添加新的污染符号变量
	//name maybe need add a "Tag"
	const Array *array = new Array(name, size);
	ObjectState *os = new ObjectState(size, array);
	ref<Expr> offset = ConstantExpr::create(0, BIT_WIDTH);
	ref<Expr> result = os->read(offset, size);
	if (isTaint) {
		result.get()->isTaint = true;
	}
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

