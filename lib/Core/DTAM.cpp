/*
 * VectorClock.cpp
 *
 *  Created on: Feb 24, 2016
 *      Author: zhy
 */

#include "DTAM.h"

namespace klee {

DTAM::DTAM(RuntimeDataManager* data) :
		runtimeData(data) {
	trace = runtimeData->getCurrentTrace();
	cost = 0;
}

DTAM::~DTAM() {

}

void DTAM::DTAMParallel() {

	for (std::map<std::string, std::vector<Event *> >::iterator it =
			trace->allReadSet.begin(), ie = trace->allReadSet.end(); it != ie; it++) {

		std::vector<Event *> var = (*it).second;
		for (std::vector<Event *>::iterator itt = var.begin(), iee = var.end();
				itt != iee; itt++) {
			std::string globalVarFullName = (*itt)->globalVarFullName;
//			std::cerr << "allReadSet globalVarFullName name : " << globalVarFullName << "\n";
			DTAMPoint *point = new DTAMPoint(globalVarFullName, (*itt)->vectorClock);
			allRead[globalVarFullName] = point;
		}
	}

	for (std::map<std::string, std::vector<Event *> >::iterator it =
			trace->allWriteSet.begin(), ie = trace->allWriteSet.end(); it != ie;
			it++) {
		std::vector<Event *> var = (*it).second;
		for (std::vector<Event *>::iterator itt = var.begin(), iee = var.end();
				itt != iee; itt++) {
			std::string globalVarFullName = (*itt)->globalVarFullName;
//			std::cerr << "allWriteSet globalVarFullName name : " << globalVarFullName << "\n";
			DTAMPoint *point = new DTAMPoint(globalVarFullName,
					(*itt)->vectorClock);
//			std::cerr << "affectedVariable : \n";
			for (std::vector<ref<klee::Expr> >::iterator ittt =
					(*itt)->relatedSymbolicExpr.begin(), ieee =
					(*itt)->relatedSymbolicExpr.end(); ittt != ieee; ittt++) {
				std::string value = DealWithSymbolicExpr::getFullName(*ittt);
//				std::cerr << "name : " << value << "\n";
				point->affectedVariable.push_back(allRead[value]);
				allRead[value]->affectingVariable.push_back(point);
			}
//			std::cerr << "affectingVariable : \n";
			std::string varName = (*itt)->varName;
			for (std::vector<Event *>::iterator ittt =
					trace->allReadSet[varName].begin(), ieee =
					trace->allReadSet[varName].end(); ittt != ieee; ittt++) {
				std::string value = (*ittt)->globalVarFullName;
//				std::cerr << "name : " << value << "\n";
				point->affectingVariable.push_back(allRead[value]);
				allRead[value]->affectedVariable.push_back(point);
			}
			allWrite[globalVarFullName] = point;
		}
	}

}

void DTAM::DTAMhybrid() {

	for (std::map<std::string, DTAMPoint*>::iterator it = allWrite.begin(), ie =
			allWrite.end(); it != ie; it++) {
		DTAMPoint *point = (*it).second;
		std::string name = point->name;
//		std::cerr << "name : " << name << "\n";
//		for (unsigned i = 0; i < point->vectorClock.size(); i++) {
//			std::cerr << point->vectorClock[i] << " ";
//		}
//		std::cerr << "\n";
		for (std::vector<DTAMPoint*>::iterator itt =
				point->affectingVariable.begin();
				itt < point->affectingVariable.end();) {
//			std::cerr << "affectingVariable name : " << (*itt)->name << " ";
//			for (unsigned i = 0; i < (*itt)->vectorClock.size(); i++) {
//				std::cerr << (*itt)->vectorClock[i] << " ";
//			}
//			std::cerr << "\n";
			if (point->isBefore(*itt)) {
				itt++;
			} else {
//				std::cerr << "erase\n";
				for (std::vector<DTAMPoint*>::iterator ittt =
						(*itt)->affectingVariable.begin();
						ittt < (*itt)->affectingVariable.end(); ittt++) {
					if (*ittt == point) {
						(*itt)->affectedVariable.erase(ittt);
					}
				}
				point->affectingVariable.erase(itt);
			}
		}
	}
}

void DTAM::initTaint() {

	std::vector<DTAMPoint*> remainPoint;

	for (std::map<std::string, DTAMPoint*>::iterator it = allWrite.begin(), ie =
			allWrite.end(); it != ie; it++) {
		DTAMPoint *point = (*it).second;
		std::string name = point->name;
		if (trace->DTAMSerial.find(name) != trace->DTAMSerial.end()) {
			point->isTaint = true;
			remainPoint.push_back(point);
		} else {
			point->isTaint = false;
		}
	}

	for (std::map<std::string, DTAMPoint*>::iterator it = allRead.begin(), ie =
			allRead.end(); it != ie; it++) {
		DTAMPoint *point = (*it).second;
		std::string name = point->name;
		if (trace->DTAMSerial.find(name) != trace->DTAMSerial.end()) {
			point->isTaint = true;
			remainPoint.push_back(point);
		} else {
			point->isTaint = false;
		}
	}

	//深度优先
	std::vector<DTAMPoint*>::iterator it;
	for (; !remainPoint.empty();) {
		it = remainPoint.end();
		it--;
		DTAMPoint *point = (*it);
		remainPoint.pop_back();
		for (std::vector<DTAMPoint*>::iterator itt =
				point->affectingVariable.begin(), iee =
				point->affectingVariable.end(); itt < iee; itt++) {
			if (!(*itt)->isTaint) {
				(*itt)->isTaint = true;
				remainPoint.push_back((*itt));
			}
		}
	}
}

void DTAM::getTaint(std::set<std::string> &taint) {

	for (std::map<std::string, DTAMPoint*>::iterator it = allWrite.begin(), ie =
			allWrite.end(); it != ie; it++) {
		DTAMPoint *point = (*it).second;
		if (point->isTaint == true) {
			std::string name = point->name;
//			std::cerr << "name : " << name << "\n";
//			std::cerr << "vector clock :";
//			for (unsigned i = 0; i < point->vectorClock.size(); i++) {
//				std::cerr << " " << point->vectorClock[i];
//			}
//			std::cerr << "\n";
			taint.insert(name);
		}
	}

	for (std::map<std::string, DTAMPoint*>::iterator it = allRead.begin(), ie =
			allRead.end(); it != ie; it++) {
		DTAMPoint *point = (*it).second;
		if (point->isTaint == true) {
			std::string name = point->name;
//			std::cerr << "name : " << name << "\n";
//			std::cerr << "vector clock :";
//			for (unsigned i = 0; i < point->vectorClock.size(); i++) {
//				std::cerr << " " << point->vectorClock[i];
//			}
//			std::cerr << "\n";
			taint.insert(name);
		}
	}
//	std::cerr << "size : " << taint.size() << "\n";
}

void DTAM::dtam() {

	std::cerr << "\n DTAMSerial : \n";
	std::cerr << "size : " << trace->DTAMSerial.size() << "\n";
	for (std::set<std::string>::iterator it = trace->DTAMSerial.begin(), ie =
			trace->DTAMSerial.end(); it != ie; it++) {
		std::string name = (*it);
		runtimeData->DTAMSerialMap.insert(trace->getAssemblyLine(name));
		trace->DTAMSerialMap.insert(trace->getAssemblyLine(name));
//		std::cerr << "name : " << name << "\n";
	}
	runtimeData->allDTAMSerialMap.push_back(trace->DTAMSerialMap.size());
	runtimeData->DTAMSerial += trace->DTAMSerial.size();
	runtimeData->allDTAMSerial.push_back(trace->DTAMSerial.size());

	gettimeofday(&start, NULL);
	std::cerr << "\n DTAMParallel : \n";
	DTAMParallel();
	std::cerr << "\n DTAMParallel : \n";
	initTaint();
	getTaint(trace->DTAMParallel);
	std::set<std::string> &potentialTaintSymbolicExpr = trace->potentialTaintSymbolicExpr;
	for (std::set<std::string>::iterator it = trace->DTAMParallel.begin(), ie =
			trace->DTAMParallel.end(); it != ie; it++) {
		std::string name = (*it);
		runtimeData->DTAMParallelMap.insert(trace->getAssemblyLine(name));
		trace->DTAMParallelMap.insert(trace->getAssemblyLine(name));
		potentialTaintSymbolicExpr.insert(filter.getVarName(name));
//		std::cerr << "name : " << name << "\n";
	}
	runtimeData->allDTAMParallelMap.push_back(trace->DTAMParallelMap.size());
	runtimeData->DTAMParallel += trace->DTAMParallel.size();
	runtimeData->allDTAMParallel.push_back(trace->DTAMParallel.size());
	gettimeofday(&finish, NULL);
	cost = (double) (finish.tv_sec * 1000000UL + finish.tv_usec
			- start.tv_sec * 1000000UL - start.tv_usec) / 1000000UL;
	runtimeData->DTAMParallelCost += cost;
	runtimeData->allDTAMParallelCost.push_back(cost);

	gettimeofday(&start, NULL);
	std::cerr << "\n DTAMhybrid : \n";
	DTAMhybrid();
	std::cerr << "\n DTAMhybrid : \n";
	initTaint();
	getTaint(trace->DTAMhybrid);
	for (std::set<std::string>::iterator it = trace->DTAMhybrid.begin(), ie =
			trace->DTAMhybrid.end(); it != ie; it++) {
		std::string name = (*it);
		runtimeData->DTAMhybridMap.insert(trace->getAssemblyLine(name));
		trace->DTAMhybridMap.insert(trace->getAssemblyLine(name));
//		std::cerr << "name : " << name << "\n";
	}
	runtimeData->allDTAMhybridMap.push_back(trace->DTAMhybridMap.size());
	std::cerr << "\n";
	runtimeData->DTAMhybrid += trace->DTAMhybrid.size();
	runtimeData->allDTAMhybrid.push_back(trace->DTAMhybrid.size());
	gettimeofday(&finish, NULL);
	cost = (double) (finish.tv_sec * 1000000UL + finish.tv_usec
			- start.tv_sec * 1000000UL - start.tv_usec) / 1000000UL;
	runtimeData->DTAMhybridCost += cost;
	runtimeData->allDTAMhybridCost.push_back(cost);
}

}
