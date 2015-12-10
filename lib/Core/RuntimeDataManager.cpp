/*
 * RuntimeDataManager.cpp
 *
 *  Created on: Jun 10, 2014
 *      Author: ylc
 */

#include "RuntimeDataManager.h"

#include "Transfer.h"
#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
#include "llvm/IR/Constants.h"
#include "llvm/Support/raw_ostream.h"
#else
#include "llvm/Constants.h"
#endif
#include <iostream>

using namespace std;
using namespace llvm;

namespace klee {

RuntimeDataManager::RuntimeDataManager() :
		currentTrace(NULL) {
	// TODO Auto-generated constructor stub
	traceList.reserve(20);
	allFormulaNum = 0;
	allGlobal = 0;
	brGlobal = 0;
	solvingTimes = 0;
	satBranch = 0;
	unSatBranch = 0;
	uunSatBranch = 0;
	solvingCost = 0.0;
	runningCost = 0.0;
	satCost = 0.0;
	unSatCost = 0.0;
	runState = 0;
}

RuntimeDataManager::~RuntimeDataManager() {
	// TODO Auto-generated destructor stub
	for (vector<Trace*>::iterator ti = traceList.begin(), te = traceList.end();
			ti != te; ti++) {
		delete *ti;
	}
	string ErrorInfo;
	raw_fd_ostream out_to_file("./output_info/statics.txt", ErrorInfo, 0x0202);
	stringstream ss;
	ss << "AllFormulaNum:" << allFormulaNum << "\n";
	ss << "SovingTimes:" << solvingTimes << "\n";
	ss << "TotalNewPath:" << testedTraceList.size() << "\n";
	ss << "TotalOldPath:" << traceList.size() - testedTraceList.size() << "\n";
	ss << "TotalPath:" << traceList.size() << "\n";
	if (testedTraceList.size()) {
		ss << "allGlobal:" << allGlobal * 1.0 / testedTraceList.size() << "\n";
		ss << "brGlobal:" << brGlobal * 1.0 / testedTraceList.size() << "\n";
	} else {
		ss << "allGlobal:0" << "\n";
		ss << "brGlobal:0" << "\n";
	}
	if (testedTraceList.size()) {
		ss << "AllBranch:" << ( satBranch + unSatBranch ) * 1.0 / testedTraceList.size() << "\n";
		ss << "satBranch:" << satBranch * 1.0 / testedTraceList.size() << "\n";
	} else {
		ss << "AllBranch:0" << "\n";
		ss << "satBranch:0" << "\n";
	}
	if (satBranch) {
		ss << "satCost:" << satCost / satBranch << "\n";
	} else {
		ss << "satCost:0" << "\n";
	}
	if (testedTraceList.size()) {
		ss << "unSatBranch:" << unSatBranch * 1.0 / testedTraceList.size()  << "\n";
	} else {
		ss << "unSatBranch:0" << "\n";
	}
	if (unSatBranch) {
		ss << "unSatCost:" << unSatCost / unSatBranch << "\n";
	} else {
		ss << "unSatCost:0" << "\n";
	}
	if (testedTraceList.size()) {
		ss << "uunSatBranch:" << uunSatBranch * 1.0 / testedTraceList.size()  << "\n";
	} else {
		ss << "uunSatBranch:0" << "\n";
	}
	ss << "SolvingCost:" << solvingCost << "\n";
	ss << "RunningCost:" << runningCost << "\n";
	out_to_file << ss.str();
	out_to_file.close();
}

Trace* RuntimeDataManager::createNewTrace(unsigned traceId) {
	currentTrace = new Trace();
	currentTrace->Id = traceId;
	traceList.push_back(currentTrace);
	return currentTrace;
}

Trace* RuntimeDataManager::getCurrentTrace() {
	return currentTrace;
}

void RuntimeDataManager::addScheduleSet(Prefix* prefix) {
	scheduleSet.push_back(prefix);
}

void RuntimeDataManager::printCurrentTrace(bool file) {
	currentTrace->print(file);
}

Prefix* RuntimeDataManager::getNextPrefix() {
	//cerr << "prefix num = " << scheduleSet.size() << endl;
	if (scheduleSet.empty()) {
		return NULL;
	} else {
		Prefix* prefix = scheduleSet.front();
		scheduleSet.pop_front();
		return prefix;
	}
}

void RuntimeDataManager::clearAllPrefix() {
	scheduleSet.clear();
}

bool RuntimeDataManager::isCurrentTraceUntested() {
	bool result = true;
	for (set<Trace*>::iterator ti = testedTraceList.begin(), te =
			testedTraceList.end(); ti != te; ti++) {
		if (currentTrace->isEqual(*ti)) {
			result = false;
			break;
		}
	}
	currentTrace->isUntested = result;
	if (result) {
		testedTraceList.insert(currentTrace);
	}
	return result;
}

void RuntimeDataManager::printAllPrefix(ostream &out) {
	out << "num of prefix: " << scheduleSet.size() << endl;
	unsigned num = 1;
	for (list<Prefix*>::iterator pi = scheduleSet.begin(), pe =
			scheduleSet.end(); pi != pe; pi++) {
		out << "Prefix " << num << endl;
		(*pi)->print(out);
		num++;
	}
}

void RuntimeDataManager::printAllTrace(ostream &out) {
	out << "\nTrace Info:\n";
	out << "num of trace: " << traceList.size() << endl << endl;
	unsigned num = 1;
	for (vector<Trace*>::iterator ti = traceList.begin(), te = traceList.end();
			ti != te; ti++) {
		Trace* trace = *ti;
		if (trace->isUntested) {
			out << "Trace " << num << endl;
			if (trace->abstract.empty()) {
				trace->createAbstract();
			}
			for (vector<string>::iterator ai = trace->abstract.begin(), ae =
					trace->abstract.end(); ai != ae; ai++) {
				out << *ai << endl;
			}
			out << endl;
			num++;
		}
	}
}

}
