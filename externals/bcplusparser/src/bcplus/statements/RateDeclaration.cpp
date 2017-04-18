
#include <boost/foreach.hpp>

#include "babb/utils/memory.h"
#include "memwrappers.h"

#include "bcplus/Location.h"
#include "bcplus/symbols/ConstantSymbol.h"
#include "bcplus/elements/terms.h"
#include "bcplus/statements/Statement.h"
#include "bcplus/statements/RateDeclaration.h"


namespace bcplus {
namespace statements {


RateDeclaration::RateDeclaration(elements::Constant const* sym, elements::Term const* term, ReferencedString const* mode, Location const& begin, Location const& end)
	: Statement(Statement::Type::RATE, begin, end), _sym(sym), _term(term), _mode(mode) {
	/* Intentionally left blank */
}

RateDeclaration::~RateDeclaration() {
	/* Intentionally left blank */
}

Statement* RateDeclaration::copy() const {
	// copy the formula list
	return new RateDeclaration(constant(), term(), mode(), beginLoc(), endLoc());
}


}}
