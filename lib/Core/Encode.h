/*
 * Encode.h
 *
 *  Created on: Jun 10, 2014
 *      Author: xdzhang
 */

#ifndef ENCODE_H_
#define ENCODE_H_

#include "Event.h"
#include "RuntimeDataManager.h"
#include "Trace.h"
#include <z3++.h>
#include <stack>
#include <utility>
enum InstType {
	NormalOp, GlobalVarOp, ThreadOp
};
using namespace llvm;
using namespace z3;
using namespace std;
namespace klee {

class Encode {
private:
	RuntimeDataManager& runtimeData;
	Trace* trace; //all data about encoding
	context& z3_ctx;
	solver& z3_solver;
	double solvingCost;
	unsigned formulaNum;
	unsigned solvingTimes;

public:
	Encode(RuntimeDataManager& data, context& c, solver& s) :
			runtimeData(data), z3_ctx(c), z3_solver(s) {
		trace = data.getCurrentTrace();
		solvingCost = 0.0;
		formulaNum = 0;
		solvingTimes = 0;
	}
	~Encode() {
		runtimeData.allFormulaNum += formulaNum;
		runtimeData.solvingTimes += solvingTimes;
	}
	void buildAllFormula();
	void showInitTrace();
	void check_output();
	void check_if();
	bool verify();

private:

	////////////////////////////////modify this sagment at the end/////////////////////////
	vector<pair<expr, expr> > globalOutputFormula;
	//first--equality, second--constrait which equality must satisfy.

	vector<pair<Event*, expr> > ifFormula;
	vector<pair<Event*, expr> > assertFormula;

	void buildInitValueFormula();
	void buildPathCondition();
	void buildMemoryModelFormula();
	void buildPartialOrderFormula();
	void buildReadWriteFormula();
	void buildSynchronizeFormula();
	void buildOutputFormula();

	expr buildExprForConstantValue(Value *V, bool isLeft, string prefix);

private:
	void markLatestWriteForGlobalVar();

	map<string, Event*> latestWriteOneThread;
	map<int, map<string, Event*> > allThreadLastWrite;
	map<string, expr> eventNameInZ3; //int:eventid.add data in function buildMemoryModelFormula
	z3::sort llvmTy_to_z3Ty(const Type *typ);

	//key--local var, value--index..like ssa
	expr makeExprsAnd(vector<expr> exprs);
	expr makeExprsOr(vector<expr> exprs);
	expr makeExprsSum(vector<expr> exprs);
	expr enumerateOrder(Event *read, Event *write, Event *anotherWrite);
	expr readFromWriteFormula(Event *read, Event *write, string var);
	bool readFromInitFormula(Event * read, expr& ret);

	void computePrefix(vector<Event*>& vecEvent, Event* ifEvent);
	void showPrefixInfo(Prefix* prefix, Event* ifEvent);

	void printSourceLine(string path, vector<struct Pair *>& eventIndexPair);
	void printSourceLine(string path, vector<Event *>& trace);
	string readLine(string filename, unsigned line);
	bool isAssert(string filename, unsigned line);
	string stringTrim(char * source);
	InstType getInstOpType(Event *event);
	void logStatisticInfo();

	void controlGranularity(int level);

};

}

#endif /* ENCODE_H_ */
