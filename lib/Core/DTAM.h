/*
 * VectorClock.h
 *
 *  Created on: Feb 24, 2016
 *      Author: zhy
 */

#ifndef LIB_CORE_DTAM_
#define LIB_CORE_DTAM_

#include "DTAMPoint.h"
#include "Trace.h"
#include "Event.h"
#include "RuntimeDataManager.h"
#include "DealWithSymbolicExpr.h"

namespace klee {


class DTAM {
private:
	RuntimeDataManager* runtimeData;
	Trace* trace;
	std::map<std::string, DTAMPoint*> allWrite;
	std::map<std::string, DTAMPoint*> allRead;

public:
	DTAM(RuntimeDataManager* data);
	~DTAM();
	void DTAMParallel();
	void DTAMhybrid();
	void initTaint();
	void getTaint(std::set<std::string> &taint);
	void dtam();


};

}
#endif /* LIB_CORE_DTAM_ */

