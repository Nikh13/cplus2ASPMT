#pragma once

#include "bcplus/Location.h"
#include "bcplus/statements/Statement.h"
#include "bcplus/statements/detail/RateDeclaration.h"

namespace bcplus {
namespace statements {
namespace detail {


RateDeclaration::RateDeclaration(symbols::ConstantSymbol const* sym, elements::Term const* term, int mode,
	Location const& begin, Location const& end)
	: Statement(t, begin, end), _sym(sym), _term(term), _mode(mode) {
	/* Intentionally left blank */
}

RateDeclaration::~RateDeclaration() {
	/* Intentionally left blank */
}

Statement* RateDeclaration::copy() const {
	return new RateDeclaration(constant(), term(), mode(), beginLoc(), endLoc());
}

}}}
