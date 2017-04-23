
#include "bcplus/symbols/SortSymbol.h"
#include "bcplus/symbols/ObjectSymbol.h"

#include "ObjectData.h"



namespace cplusode {
namespace cplusode_bin {

namespace sy = bcplus::symbols;

ObjectData::ObjectData(sy::ObjectSymbol const* obj)
	: _obj(obj), _translated(false) {
	/* Intentionally left blank */
}

ObjectData::~ObjectData() {
	/* Intentionally left blank */
}



}}
