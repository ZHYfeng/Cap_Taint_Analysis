/*
 * HybridPoint.h
 *
 *  Created on: Feb 24, 2016
 *      Author: zhy
 */

#ifndef LIB_CORE_DTAMPOINT_H_
#define LIB_CORE_DTAMPOINT_H_

#include <vector>
#include <map>
#include <string>

class DTAMPoint {
public:
	std::string name;
	bool isTaint;
	std::vector<DTAMPoint*> affectingVariable;
	std::vector<DTAMPoint*> affectedVariable;
	std::vector<unsigned> vectorClock;

public:
	DTAMPoint(std::string _name, std::vector<unsigned> _vectorClock);
	virtual ~DTAMPoint();
	bool isBefore(DTAMPoint *point);
};

#endif /* LIB_CORE_DTAMPOINT_H_ */
