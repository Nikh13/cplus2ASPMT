
#include "bcplus/symbols/SortSymbol.h"
#include "bcplus/symbols/NumberRangeSymbol.h"

#include "RangeData.h"



namespace cplusode {
namespace cplusode_bin {

namespace sy = bcplus::symbols;

RangeData::RangeData(sy::NumberRangeSymbol const* range)
	: _range(range), _translated(false) {
	/* Intentionally left blank */
}

RangeData::~RangeData() {
	/* Intentionally left blank */
}



}}
