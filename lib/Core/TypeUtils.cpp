/*
 * TypeUtils.cpp
 *
 *  Created on: 2014年9月27日
 *      Author: berserker
 */

#include <TypeUtils.h>
using namespace::llvm;

TypeUtils::TypeUtils() {
	// TODO Auto-generated constructor stub

}

TypeUtils::~TypeUtils() {
	// TODO Auto-generated destructor stub
}

unsigned TypeUtils::getPrimitiveTypeWidth(const Type* type) {
	if (type->isVoidTy()) {
		return 0;
	} else if (type->isFloatTy()) {
		return 32 / 8;
	} else if (type->isDoubleTy()) {
		return 64 / 8;
	} else if (type->isX86_FP80Ty()) {
		return 80 / 8;
	} else if (type->isFP128Ty()) {
		return 128 / 8;
	} else if (type->isPPC_FP128Ty()) {
		return 128 / 8;
	} else if (type->isX86_MMXTy()) {
		return 64 / 8;
	} else if (type->isIntegerTy()) {
		IntegerType* integerTy = (IntegerType*) type;
		return integerTy->getBitWidth() / 8;
	} else {
		assert(0 && "must be a primitive type");
		return -1;
	}
}

