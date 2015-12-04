/*
 * SymbolicListener.h
 *
 *  Created on: 2015年7月21日
 *      Author: zhy
 */

#ifndef LIB_CORE_DEALWITHSYMBOLIC_C_
#define LIB_CORE_DEALWITHSYMBOLIC_C_

#include "DealWithSymbolicExpr.h"
#include "llvm/IR/Instruction.h"
#include <sstream>
#include <ostream>
#include <set>
#include <vector>
#include <map>

namespace klee {

std::string DealWithSymbolicExpr::getVarName(ref<klee::Expr> value) {
//	std::cerr << "getVarName : " << value << "\n";
	std::stringstream varName;
	varName.str("");
	ReadExpr *revalue;
	if (value->getKind() == Expr::Concat) {
		ConcatExpr *ccvalue = cast<ConcatExpr>(value);
		revalue = cast<ReadExpr>(ccvalue->getKid(0));
	} else if (value->getKind() == Expr::Read) {
		revalue = cast<ReadExpr>(value);
	} else {
		return varName.str();
	}
	std::string globalVarFullName = revalue->updates.root->name;
	unsigned int i = 0;
	while ((globalVarFullName.at(i) != 'S') && (globalVarFullName.at(i) != 'L')) {
		varName << globalVarFullName.at(i);
		i++;
	}
	return varName.str();
}

std::string DealWithSymbolicExpr::getFullName(ref<klee::Expr> value) {

	ReadExpr *revalue;
	if (value->getKind() == Expr::Concat) {
		ConcatExpr *ccvalue = cast<ConcatExpr>(value);
		revalue = cast<ReadExpr>(ccvalue->getKid(0));
	} else if (value->getKind() == Expr::Read) {
		revalue = cast<ReadExpr>(value);
	} else {
		assert( 0 && "getFullName");
	}
	std::string globalVarFullName = revalue->updates.root->name;
	return globalVarFullName;
}

void DealWithSymbolicExpr::resolveSymbolicExpr(ref<klee::Expr> value,
		std::set<std::string> relatedSymbolicExpr) {
	if (value->getKind() == Expr::Read) {
		std::string varName = getVarName(value);
		if (relatedSymbolicExpr.find(varName) == relatedSymbolicExpr.end()) {
			relatedSymbolicExpr.insert(varName);
		}
		return;
	} else {
		unsigned kidsNum = value->getNumKids();
		if (kidsNum == 2 && value->getKid(0) == value->getKid(1)) {
			resolveSymbolicExpr(value->getKid(0), relatedSymbolicExpr);
		} else {
			for (unsigned int i = 0; i < kidsNum; i++) {
				resolveSymbolicExpr(value->getKid(i), relatedSymbolicExpr);
			}
		}
	}
}

void DealWithSymbolicExpr::addExprToSet(std::set<std::string>* Expr,
		std::set<std::string> relatedSymbolicExpr) {

	for (std::set<std::string>::iterator it =
			Expr->begin(), ie = Expr->end(); it != ie; ++it) {
		std::string varName =*it;
		if (relatedSymbolicExpr.find(varName) != relatedSymbolicExpr.end()) {
			relatedSymbolicExpr.insert(varName);
		}
	}
}

bool DealWithSymbolicExpr::isRelated(std::string varName) {
	if (allRelatedSymbolicExpr.find(varName) != allRelatedSymbolicExpr.end()) {
		return true;
	} else {
		return false;
	}
}

void DealWithSymbolicExpr::fillterTrace(Trace* trace, std::set<std::string> RelatedSymbolicExpr) {
	std::string varName;

	std::map<std::string, std::vector<Event *> > &usefulReadSet = trace->usefulReadSet;
	std::map<std::string, std::vector<Event *> > &readSet = trace->readSet;
	usefulReadSet.clear();
	for (std::map<std::string, std::vector<Event *> >::iterator nit =
			readSet.begin(), nie = readSet.end(); nit != nie; ++nit) {
		varName = nit->first;
		if (RelatedSymbolicExpr.find(varName) != RelatedSymbolicExpr.end()) {
			usefulReadSet.insert(*nit);
		}
	}

	std::map<std::string, std::vector<Event *> > &usefulWriteSet = trace->usefulWriteSet;
	std::map<std::string, std::vector<Event *> > &writeSet = trace->writeSet;
	usefulWriteSet.clear();
	for (std::map<std::string, std::vector<Event *> >::iterator nit =
			writeSet.begin(), nie = writeSet.end(); nit != nie; ++nit) {
		varName = nit->first;
		if (RelatedSymbolicExpr.find(varName) != RelatedSymbolicExpr.end()) {
			usefulWriteSet.insert(*nit);
		}
	}

	std::map<std::string, llvm::Constant*> &useful_global_variable_initializer = trace->useful_global_variable_initializer;
	std::map<std::string, llvm::Constant*> &global_variable_initializer = trace->global_variable_initializer;
	useful_global_variable_initializer.clear();
	for (std::map<std::string, llvm::Constant*>::iterator nit =
			global_variable_initializer.begin(), nie = global_variable_initializer.end(); nit != nie; ++nit) {
		varName = nit->first;
		if (RelatedSymbolicExpr.find(varName) != RelatedSymbolicExpr.end()) {
			useful_global_variable_initializer.insert(*nit);
		}
	}


	//	TODO isglobal
	for (std::vector<Event*>::iterator currentEvent = trace->path.begin(), endEvent = trace->path.end();
			currentEvent != endEvent; currentEvent++) {
		if ((*currentEvent)->isGlobal == true) {
			if ((*currentEvent)->inst->inst->getOpcode() == llvm::Instruction::Load
					|| (*currentEvent)->inst->inst->getOpcode() == llvm::Instruction::Store) {
				if (RelatedSymbolicExpr.find((*currentEvent)->varName) == RelatedSymbolicExpr.end()) {
					(*currentEvent)->condition = false;
				} else {
					(*currentEvent)->condition = true;
				}
			}
		}
	}
}

void DealWithSymbolicExpr::filterUseless(Trace* trace) {

	std::string varName;
	std::vector<std::string> remainingExprVarName;
	std::vector<ref<klee::Expr> > remainingExpr;
	allRelatedSymbolicExpr.clear();
	remainingExprVarName.clear();
	remainingExpr.clear();
	std::vector<ref<klee::Expr> > &storeSymbolicExpr = trace->storeSymbolicExpr;
	for (std::vector<ref<Expr> >::iterator it = storeSymbolicExpr.begin(), ie =
			storeSymbolicExpr.end(); it != ie; ++it) {
		varName = getVarName(it->get()->getKid(1));
		remainingExprVarName.push_back(varName);
		remainingExpr.push_back(it->get());
	}

	//br
	std::vector<ref<klee::Expr> > &brSymbolicExpr = trace->brSymbolicExpr;
	std::vector<std::set<std::string>*> &brRelatedSymbolicExpr = trace->brRelatedSymbolicExpr;
	for (std::vector<ref<Expr> >::iterator it = brSymbolicExpr.begin(), ie =
			brSymbolicExpr.end(); it != ie; ++it) {
		std::set<std::string>* tempSymbolicExpr = new std::set<std::string>();
		resolveSymbolicExpr(it->get(), *tempSymbolicExpr);
		brRelatedSymbolicExpr.push_back(tempSymbolicExpr);
		addExprToSet(tempSymbolicExpr, allRelatedSymbolicExpr);
	}

	//assert
	std::vector<ref<klee::Expr> > &assertSymbolicExpr = trace->assertSymbolicExpr;
	std::vector<std::set<std::string>*> &assertRelatedSymbolicExpr = trace->assertRelatedSymbolicExpr;
	for (std::vector<ref<Expr> >::iterator it = assertSymbolicExpr.begin(), ie =
			assertSymbolicExpr.end(); it != ie; ++it) {
		std::set<std::string>* tempSymbolicExpr = new std::set<std::string>();
		resolveSymbolicExpr(it->get(), *tempSymbolicExpr);
		assertRelatedSymbolicExpr.push_back(tempSymbolicExpr);
		addExprToSet(tempSymbolicExpr, allRelatedSymbolicExpr);
	}

	std::vector<ref<klee::Expr> > &kQueryExpr = trace->kQueryExpr;
	std::vector<std::string> &kQueryExprVarName = trace->kQueryExprVarName;
	std::map<std::string, std::set<std::string>* > &varRelatedSymbolicExpr = trace->varRelatedSymbolicExpr;
	for (std::set<std::string>::iterator nit = allRelatedSymbolicExpr.begin();
			nit != allRelatedSymbolicExpr.end(); ++nit) {
		varName = *nit;
		std::vector<ref<Expr> >::iterator itt = remainingExpr.begin();
		for (std::vector<std::string>::iterator it =
				remainingExprVarName.begin(), ie = remainingExprVarName.end();
				it != ie;) {
			if (varName == *it) {
				remainingExprVarName.erase(it);
				--ie;
				kQueryExpr.push_back(*itt);
				kQueryExprVarName.push_back(varName);

				std::set<std::string>* tempSymbolicExpr = new std::set<std::string>();
				resolveSymbolicExpr(itt->get(), *tempSymbolicExpr);
				if (varRelatedSymbolicExpr.find(varName) != varRelatedSymbolicExpr.end()) {
					addExprToSet(tempSymbolicExpr, *(varRelatedSymbolicExpr[varName]));
				} else {
					varRelatedSymbolicExpr[varName] = tempSymbolicExpr;
				}
				addExprToSet(tempSymbolicExpr, allRelatedSymbolicExpr);

				remainingExpr.erase(itt);
			} else {
				++it;
				++itt;
			}
		}
	}

	std::map<std::string, std::vector<Event *> > usefulReadSet;
	std::map<std::string, std::vector<Event *> > &readSet = trace->readSet;
	usefulReadSet.clear();
	for (std::map<std::string, std::vector<Event *> >::iterator nit =
			readSet.begin(), nie = readSet.end(); nit != nie; ++nit) {
		varName = nit->first;
		if (allRelatedSymbolicExpr.find(varName) != allRelatedSymbolicExpr.end()) {
			usefulReadSet.insert(*nit);
		}
	}
	readSet.clear();
	for (std::map<std::string, std::vector<Event *> >::iterator nit =
			usefulReadSet.begin(), nie = usefulReadSet.end(); nit != nie;
			++nit) {
		readSet.insert(*nit);
	}

	std::map<std::string, std::vector<Event *> > usefulWriteSet;
	std::map<std::string, std::vector<Event *> > &writeSet = trace->writeSet;
	usefulWriteSet.clear();
	for (std::map<std::string, std::vector<Event *> >::iterator nit =
			writeSet.begin(), nie = writeSet.end(); nit != nie; ++nit) {
		varName = nit->first;
		if (allRelatedSymbolicExpr.find(varName) != allRelatedSymbolicExpr.end()) {
			usefulWriteSet.insert(*nit);
		}
	}
	writeSet.clear();
	for (std::map<std::string, std::vector<Event *> >::iterator nit =
			usefulWriteSet.begin(), nie = usefulWriteSet.end(); nit != nie;
			++nit) {
		writeSet.insert(*nit);
	}

	std::map<std::string, llvm::Constant*> usefulGlobal_variable_initializer;
	std::map<std::string, llvm::Constant*> &global_variable_initializer = trace->global_variable_initializer;
	usefulGlobal_variable_initializer.clear();
	for (std::map<std::string, llvm::Constant*>::iterator nit =
			global_variable_initializer.begin(), nie = global_variable_initializer.end(); nit != nie; ++nit) {
		varName = nit->first;
		if (allRelatedSymbolicExpr.find(varName) != allRelatedSymbolicExpr.end()) {
			usefulGlobal_variable_initializer.insert(*nit);
		}
	}
	global_variable_initializer.clear();
	for (std::map<std::string, llvm::Constant*>::iterator nit =
			usefulGlobal_variable_initializer.begin(), nie = usefulGlobal_variable_initializer.end(); nit != nie;
			++nit) {
		global_variable_initializer.insert(*nit);
	}

//	std::vector<std::vector<Event*>*> eventList = trace->eventList;
	for (std::vector<Event*>::iterator currentEvent = trace->path.begin(), endEvent = trace->path.end();
			currentEvent != endEvent; currentEvent++) {
		if ((*currentEvent)->isGlobal == true) {
			if ((*currentEvent)->inst->inst->getOpcode() == llvm::Instruction::Load
					|| (*currentEvent)->inst->inst->getOpcode() == llvm::Instruction::Store) {
				if (allRelatedSymbolicExpr.find((*currentEvent)->varName) == allRelatedSymbolicExpr.end()) {
					(*currentEvent)->isGlobal = false;
				}
			}
		}
	}

	fillterTrace(trace, allRelatedSymbolicExpr);

}

void DealWithSymbolicExpr::filterUselessWithSet(Trace* trace, std::set<std::string>* relatedSymbolicExpr){
	std::set<std::string> &RelatedSymbolicExpr = trace->RelatedSymbolicExpr;
	RelatedSymbolicExpr.clear();
	addExprToSet(relatedSymbolicExpr, RelatedSymbolicExpr);
	std::string varName;
	std::vector<ref<klee::Expr> > &kQueryExpr = trace->kQueryExpr;
	std::vector<std::string> &kQueryExprVarName = trace->kQueryExprVarName;
	std::map<std::string, std::set<std::string>* > &varRelatedSymbolicExpr = trace->varRelatedSymbolicExpr;
	for (std::set<std::string>::iterator nit = RelatedSymbolicExpr.begin();
			nit != RelatedSymbolicExpr.end(); ++nit) {
		varName = *nit;
		addExprToSet(varRelatedSymbolicExpr[varName], RelatedSymbolicExpr);
	}
	fillterTrace(trace, RelatedSymbolicExpr);
}

}

#endif /* LIB_CORE_DEALWITHSYMBOLIC_C_ */
