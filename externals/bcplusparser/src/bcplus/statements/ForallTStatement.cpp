
#include <boost/foreach.hpp>

#include "babb/utils/memory.h"
#include "memwrappers.h"

#include "bcplus/Location.h"
#include "bcplus/elements/formulas.h"
#include "bcplus/elements/terms.h"
#include "bcplus/statements/Statement.h"
#include "bcplus/statements/ForallTStatement.h"


namespace bcplus {
namespace statements {


ForallTStatement::ForallTStatement(elements::Formula const* formula, ReferencedString const* mode, Location const& begin, Location const& end)
	: Statement(Statement::Type::FORALLT, begin, end), _formula(formula), _mode(mode) {
	/* Intentionally left blank */
}

ForallTStatement::~ForallTStatement() {
	/* Intentionally left blank */
}

Statement* ForallTStatement::copy() const {
	// copy the formula list
	return new ForallTStatement(formula(), mode(), beginLoc(), endLoc());
}


}}
