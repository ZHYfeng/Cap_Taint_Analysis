/*
 * VectorClock.h
 *
 *  Created on: Feb 24, 2016
 *      Author: zhy
 */

#ifndef LIB_CORE_VECTORCLOCK_H_
#define LIB_CORE_VECTORCLOCK_H_

#include "Trace.h"
#include "Event.h"
#include "RuntimeDataManager.h"
#include "HybridPoint.h"

namespace klee {


class VectorClock {
private:
	RuntimeDataManager* runtimeData;
	Trace* trace;
	std::map<std::string, HybridPoint*> allWrite;
	std::map<std::string, HybridPoint*> allRead;

public:
	VectorClock(RuntimeDataManager* data) : runtimeData(data){
		trace = data->getCurrentTrace();
	}
	virtual ~VectorClock();
};

}
#endif /* LIB_CORE_VECTORCLOCK_H_ */

