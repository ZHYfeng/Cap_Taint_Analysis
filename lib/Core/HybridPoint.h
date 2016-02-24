/*
 * HybridPoint.h
 *
 *  Created on: Feb 24, 2016
 *      Author: zhy
 */

#ifndef LIB_CORE_HYBRIDPOINT_H_
#define LIB_CORE_HYBRIDPOINT_H_

#include <vector>
#include <map>
#include <string>

class HybridPoint {
public:
	std::string name;
	bool isTaint;
	std::vector<HybridPoint*> affectingVariable;
	std::vector<HybridPoint*> affectedVariable;

public:
	HybridPoint(std::string _name);
	virtual ~HybridPoint();
};

#endif /* LIB_CORE_HYBRIDPOINT_H_ */
