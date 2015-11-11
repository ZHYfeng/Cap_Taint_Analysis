/*
 * TypeUtils.h
 *
 *  Created on: 2014年9月27日
 *      Author: berserker
 */

#ifndef TYPEUTILS_H_
#define TYPEUTILS_H_

#include "klee/Config/Version.h"
#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/DerivedTypes.h"
#else
#include "llvm/Instruction.h"
#include "llvm/Type.h"
#include "llvm/DerivedTypes.h"
#endif

class TypeUtils {
public:
	TypeUtils();
	virtual ~TypeUtils();
	static unsigned getPrimitiveTypeWidth(const llvm::Type* type);

};

#endif /* TYPEUTILS_H_ */
