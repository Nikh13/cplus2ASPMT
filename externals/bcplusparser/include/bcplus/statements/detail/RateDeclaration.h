#pragma once

#include "babb/utils/memory.h"
#include "memwrappers.h"

#include "bcplus/Location.h"
#include "bcplus/symbols/ConstantSymbol.h"
#include "bcplus/elements/formulas.h"
#include "bcplus/statements/Statement.h"

namespace bcplus {
namespace statements {
namespace detail {

/// Rate Declaration form for rate of continuousFluent constants
class RateDeclaration : public Statement {
private:

	/**************************************************************************************/
	/* Private Members */
	/**************************************************************************************/

	/// Constant element
	babb::utils::ref_ptr<const symbols::ConstantSymbol> _sym;

	/// 'term' clause
	babb::utils::ref_ptr<const elements::Term> _term;

	int _mode;

public:
	/**************************************************************************************/
	/* Constructors / Destructors */
	/**************************************************************************************/
	RateDeclaration(symbols::ConstantSymbol const* constant, elements::Term const* term, int mode,
		Location const& begin = Location(NULL, 0, 0), Location
		const& end = Location(NULL, 0, 0));

	virtual ~RateDeclaration();

	/**************************************************************************************/
	/* Public Methods */
	/**************************************************************************************/

	/// Get the constant element
	inline symbols::ConstantSymbol const* constant() const 							{ return _sym; }

	/// Get the rate 'term' clause
	inline elements::Term const* term() const							{ return _term; }

	inline int mode() const							{ return _mode; }

	// inherited
	virtual Statement* copy() const;


};

#include "bcplus/statements/detail/RateDeclaration.impl.h"

}}}
