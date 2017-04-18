
#include "bcplus/symbols/ConstantSymbol.h"

#include "ConstantData.h"



namespace cplusode {
namespace cplusode_bin {

namespace sy = bcplus::symbols;

ConstantData::ConstantData(sy::ConstantSymbol const* constant)
	: _constant(constant), _translated(false) {
	/* Intentionally left blank */
}

ConstantData::~ConstantData() {
	/* Intentionally left blank */
}


}}
