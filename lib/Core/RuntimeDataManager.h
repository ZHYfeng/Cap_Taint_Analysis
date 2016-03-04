/*
 * RuntimeDataManager.h
 *
 *  Created on: Jun 10, 2014
 *      Author: ylc
 */

#ifndef RUNTIMEDATAMANAGER_H_
#define RUNTIMEDATAMANAGER_H_

#include "Trace.h"
#include "Prefix.h"
#include <set>
namespace klee {

class RuntimeDataManager {

private:
	std::vector<Trace*> traceList; // store all traces;
	Trace* currentTrace; // trace associated with current execution
	std::set<Trace*> testedTraceList; // traces which have been examined
	std::list<Prefix*> scheduleSet; // prefixes which have not been examined

public:
	//newly added stastic info
	unsigned allFormulaNum;
	unsigned allGlobal;
	unsigned brGlobal;
	unsigned solvingTimes;
	unsigned satBranch;
	unsigned unSatBranch;
	unsigned uunSatBranch;
	double runningCost;
	double solvingCost;
	double satCost;
	double unSatCost;

	unsigned runState;

	double taintCost;
	double PTSCost;
	double DTAMCost;
	double DTAMParallelCost;
	double DTAMhybridCost;

	unsigned DTAMSerial;
	unsigned DTAMParallel;
	unsigned DTAMhybrid;

	unsigned taint;
	unsigned taintPTS;
	unsigned noTaintPTS;

	std::vector<double> allTaintCost;
	std::vector<double> allPTSCost;
	std::vector<double> allDTAMCost;
	std::vector<double> allDTAMParallelCost;
	std::vector<double> allDTAMhybridCost;

	std::vector<unsigned> allDTAMSerial;
	std::vector<unsigned> allDTAMParallel;
	std::vector<unsigned> allDTAMhybrid;

	std::vector<unsigned> allTaint;
	std::vector<unsigned> allTaintPTS;
	std::vector<unsigned> allNoTaintPTS;

	std::vector<unsigned> allDTAMSerialMap;
	std::vector<unsigned> allDTAMParallelMap;
	std::vector<unsigned> allDTAMhybridMap;
	std::vector<unsigned> allTaintMap;



	RuntimeDataManager();
	virtual ~RuntimeDataManager();

	Trace* createNewTrace(unsigned traceId);
	Trace* getCurrentTrace();
	void addScheduleSet(Prefix* prefix);
	void printCurrentTrace(bool file);
	Prefix* getNextPrefix();
	void clearAllPrefix();
	bool isCurrentTraceUntested();
	void printAllPrefix(std::ostream &out);
	void printAllTrace(std::ostream &out);

	std::set<std::string> taintMap;
	std::set<std::string> DTAMSerialMap;
	std::set<std::string> DTAMParallelMap;
	std::set<std::string> DTAMhybridMap;
};

}
#endif /* RUNTIMEDATAMANAGER_H_ */
