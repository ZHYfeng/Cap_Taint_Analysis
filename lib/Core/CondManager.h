/*
 * CondManager.h
 *
 *  Created on: Jul 24, 2014
 *      Author: ylc
 */

#ifndef CONDMANAGER_H_
#define CONDMANAGER_H_

#include <map>
#include <string>
#include "Condition.h"
#include "MutexManager.h"
#include "Scheduler.h"
#include "WaitParam.h"
#include "Prefix.h"

namespace klee {


class CondManager {
private:
	std::map<std::string, Condition*> condPool;
	MutexManager* mutexManager;
	unsigned nextConditionId;
	Executor* executor;

public:
	CondManager();
	CondManager(MutexManager* mutexManaget);
	virtual ~CondManager();
	bool wait(std::string condName, std::string mutexName, unsigned threadId, std::string& errorMsg);
	bool signal(std::string condName, unsigned& releasedThreadId, std::string& errorMsg);
	bool broadcast(std::string condName, std::vector<unsigned>& threads, std::string& errorMsg);
	bool addCondition(std::string condName, std::string& errorMsg);
	bool addCondition(std::string condName, std::string& errorMsg, Prefix* prefix);
	Condition* getCondition(std::string condName);
	void setMutexManager(MutexManager* mutexManager) {this->mutexManager = mutexManager;}
	void setExecutor(Executor* executor) {this->executor = executor;}
	void clear();
	void print(std::ostream &out);
	unsigned getNextConditionId();
};

}
#endif /* CONDMANAGER_H_ */
