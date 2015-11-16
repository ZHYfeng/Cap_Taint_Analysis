//by hy 2015.7.21

#include "klee/Expr.h"
#include "Trace.h"
#include <string>

#include "Event.h"

namespace klee {

class DealWithSymbolicExpr {

private:

	void resolveSymbolicExpr(ref<Expr> value);


public:
	void filterUseless(Trace* trace);
	std::string getVarName(ref<Expr> value);
	std::string getFullName(ref<Expr> value);

};

}
