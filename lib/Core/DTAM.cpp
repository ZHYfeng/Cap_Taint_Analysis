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
	trace = data->getCurrentTrace();

}

void DTAM::DTAMSerialAndParallel() {

	for (std::map<std::string, std::vector<Event *> >::iterator it =
			trace->readSet.begin(), ie = trace->readSet.end(); it != ie; it++) {
		std::vector<Event *> var = (*it).second;
		for (std::vector<Event *>::iterator itt = var.begin(), iee = var.end();
				itt != iee; itt++) {
			std::string varName = (*itt)->globalVarFullName;
			DTAMPoint *point = new DTAMPoint(varName, (*itt)->vectorClock);
			allRead[varName] = point;
		}
	}

	for (std::map<std::string, std::vector<Event *> >::iterator it =
			trace->writeSet.begin(), ie = trace->writeSet.end(); it != ie;
			it++) {
		std::vector<Event *> var = (*it).second;
		for (std::vector<Event *>::iterator itt = var.begin(), iee = var.end();
				itt != iee; itt++) {
			std::string globalVarFullName = (*itt)->globalVarFullName;
			DTAMPoint *point = new DTAMPoint(globalVarFullName,
					(*itt)->vectorClock);
			for (std::vector<ref<klee::Expr> >::iterator ittt =
					(*itt)->value.begin(), ieee = (*itt)->value.end();
					ittt != ieee; ittt++) {
				std::string value = DealWithSymbolicExpr::getFullName(*ittt);
				point->affectedVariable.push_back(allRead[value]);
				allRead[value]->affectingVariable.push_back(point);
			}
			std::string varName = (*itt)->varName;
			for (std::vector<Event *>::iterator ittt =
					trace->readSet[varName].begin(), ieee =
					trace->readSet[varName].end(); ittt != ieee; ittt++) {
				std::string value = (*ittt)->globalVarFullName;
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
		for (std::vector<DTAMPoint*>::iterator itt =
				point->affectingVariable.begin();
				itt < point->affectingVariable.end();) {
			if (point->isBefore(*itt)) {
				itt++;
			} else {
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
		if (trace->taint.find(name) != trace->taint.end()) {
			point->isTaint = true;
		} else {
			point->isTaint = false;
		}
		remainPoint.push_back(point);
	}

	for (std::map<std::string, DTAMPoint*>::iterator it = allRead.begin(), ie =
			allRead.end(); it != ie; it++) {
		DTAMPoint *point = (*it).second;
		point->isTaint = false;
	}

	//深度优先
	for (std::vector<DTAMPoint*>::iterator it = remainPoint.end();
			it != remainPoint.begin(); ) {
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

void DTAM::getTaint() {
	for (std::map<std::string, DTAMPoint*>::iterator it = allWrite.begin(), ie =
			allWrite.end(); it != ie; it++) {
		DTAMPoint *point = (*it).second;
		if (point->isTaint == true) {
			std::string name = point->name;
		}
	}

	for (std::map<std::string, DTAMPoint*>::iterator it = allRead.begin(), ie =
			allRead.end(); it != ie; it++) {
		DTAMPoint *point = (*it).second;
		if (point->isTaint == true) {
			std::string name = point->name;
		}
	}
}

}
