/*
 * Prefix.h
 *
 *  Created on: 2015年2月3日
 *      Author: berserker
 */

#ifndef LIB_CORE_PREFIX_H_
#define LIB_CORE_PREFIX_H_

#include "llvm/Support/raw_ostream.h"
#include <iostream>
#include <vector>
#include <map>
#include <string>

#include "Event.h"

namespace klee {

class Prefix {
public:
	typedef std::vector<Event*>::iterator EventIterator;

private:
	std::vector<Event*> eventList;
	std::map<Event*, uint64_t> threadIdMap;
	EventIterator pos;
	std::string name;

public:
	Prefix(std::vector<Event*>& eventList, std::map<Event*, uint64_t>& threadIdMap, std::string name);
	virtual ~Prefix();
	std::vector<Event*>* getEventList();
	void increase();
	void reuse();
	bool isFinished();
	EventIterator begin();
	EventIterator end();
	EventIterator current();
	uint64_t getNextThreadId();
	unsigned getCurrentEventThreadId();
	void print(std::ostream &out);
	void print(llvm::raw_ostream &out);
	KInstruction* getCurrentInst();
	std::string getName();
};

} /* namespace klee */

#endif /* LIB_CORE_PREFIX_H_ */
