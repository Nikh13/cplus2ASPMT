#pragma once

#include "babb/utils/memory.h"
#include "memwrappers.h"

#include "bcplus/Location.h"
#include "bcplus/elements/formulas.h"
#include "bcplus/statements/Statement.h"

namespace bcplus {
namespace statements {

/// Rate Declaration form for rate of continuousFluent constants
class ForallTStatement : public Statement {
private:

	/**************************************************************************************/
	/* Private Members */
	/**************************************************************************************/

	/// Constant element
	babb::utils::ref_ptr<const elements::Formula> _formula;

	ReferencedString const* _mode;

public:
	/**************************************************************************************/
	/* Constructors / Destructors */
	/**************************************************************************************/
	ForallTStatement(elements::Formula const* formula, ReferencedString const* mode,
		Location const& begin = Location(NULL, 0, 0), Location
		const& end = Location(NULL, 0, 0));

	virtual ~ForallTStatement();

	/**************************************************************************************/
	/* Public Methods */
	/**************************************************************************************/

	/// Get the constant element
	inline elements::Formula const* formula() const 							{ return _formula; }

	inline ReferencedString const* mode() const							{ return _mode; }

	// inherited
	virtual Statement* copy() const;


};


}}
