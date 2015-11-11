/*
 * SymbolicStackFrame.cpp
 *
 *  Created on: Jun 8, 2014
 *      Author: ylc
 */

#include "SymbolicStackFrame.h"
#include <iostream>

using namespace std;
using namespace llvm;

namespace klee {


SymbolicStackFrame::SymbolicStackFrame() {
	// TODO Auto-generated constructor stub

}

SymbolicStackFrame::SymbolicStackFrame(Function* function, unsigned localLength) :
		function(function), localLength(localLength){
	this->locals = new Cell[localLength];
}

SymbolicStackFrame::~SymbolicStackFrame() {
	// TODO Auto-generated destructor stub
	if (locals) {
		delete[] locals;
	}
}

void SymbolicStackFrame::printStackFrame() {
	cerr << function->getName().str() << " : " << localLength << endl;
}

} /* namespace klee */
