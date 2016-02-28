/*
 * HybridPoint.cpp
 *
 *  Created on: Feb 24, 2016
 *      Author: zhy
 */

#include "DTAMPoint.h"

DTAMPoint::DTAMPoint(std::string _name, std::vector<unsigned> _vectorClock) :
		name(_name), isTaint(false) {
	for (unsigned i = 0; i < _vectorClock.size(); i++) {
		vectorClock.push_back(_vectorClock[i]);
	}
}

DTAMPoint::~DTAMPoint() {

}

bool DTAMPoint::isBefore(DTAMPoint *point) {
	for (unsigned i = 0; i < vectorClock.size(); i++) {
		if(vectorClock[i] > point->vectorClock[i]){
			return false;
		}
	}
	return true;
}

