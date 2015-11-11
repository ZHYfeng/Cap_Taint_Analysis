/*
 * Prefix.cpp
 *
 *  Created on: 2015年2月3日
 *      Author: berserker
 */

#include "Prefix.h"

#include "klee/Internal/Module/InstructionInfoTable.h"

#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
#include "llvm/IR/Instructions.h"
#else
#include "llvm/Instructions.h"
#endif

using namespace::std;
using namespace::llvm;

namespace klee {

Prefix::Prefix(vector<Event*>& eventList, std::map<Event*, uint64_t>& threadIdMap, std::string name)
	: eventList(eventList),
	  threadIdMap(threadIdMap),
	  name(name){
	// TODO Auto-generated constructor stub
	pos = this->eventList.begin();
}

void Prefix::reuse(){
	pos = this->eventList.begin();
}

Prefix::~Prefix() {
	// TODO Auto-generated destructor stub
}

vector<Event*>* Prefix::getEventList() {
	return &eventList;
}

void Prefix::increase() {
	if (!isFinished()) {
		pos++;
	}
}



bool Prefix::isFinished() {
	return pos == eventList.end();
}

Prefix::EventIterator Prefix::begin() {
	return eventList.begin();
}

Prefix::EventIterator Prefix::end() {
	return eventList.end();
}

Prefix::EventIterator Prefix::current() {
	return Prefix::EventIterator(pos);
}

uint64_t Prefix::getNextThreadId() {
	assert(!isFinished());
	Event* event = *pos;
	map<Event*, uint64_t>::iterator ti = threadIdMap.find(event);
	return ti->second;
}

unsigned Prefix::getCurrentEventThreadId() {
	assert(!isFinished());
	Event* event = *pos;
	return event->threadId;
}

void Prefix::print(ostream &out) {
	for (vector<Event*>::iterator ei = eventList.begin(), ee = eventList.end(); ei != ee; ei++) {
		Event* event = *ei;
		out << "thread" << event->threadId << " " << event->inst->info->file << " " << event->inst->info->line << ": " << event->inst->inst->getOpcodeName();
		map<Event*, uint64_t>::iterator ti = threadIdMap.find(event);
		if (ti != threadIdMap.end()) {
			out << "\n child threadId = " << ti->second;
		}
		out << endl;
	}
	out << "prefix print finished\n";
}

void Prefix::print(raw_ostream &out) {
	for (vector<Event*>::iterator ei = eventList.begin(), ee = eventList.end(); ei != ee; ei++) {
		Event* event = *ei;
		out << "thread" << event->threadId << " " << event->inst->info->file << " " << event->inst->info->line << ": ";
		event->inst->inst->print(out);
		map<Event*, uint64_t>::iterator ti = threadIdMap.find(event);
		if (ti != threadIdMap.end()) {
			out << "\n child threadId = " << ti->second;
		}
		out << '\n';
	}
	out << "prefix print finished\n";
}

KInstruction* Prefix::getCurrentInst() {
	assert(!isFinished());
	Event* event = *pos;
	return event->inst;
}
std::string Prefix::getName(){
	return name;
}

} /* namespace klee */
