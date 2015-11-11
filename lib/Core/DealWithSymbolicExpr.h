//by hy 2015.7.21

#include "klee/Expr.h"
#include "Event.h"
#include "Trace.h"
#include <vector>
#include <map>
#include <string>

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
