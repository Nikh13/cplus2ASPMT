/* Driver template for the LEMON parser generator.
** The author disclaims copyright to this source code.
*/
/* First off, code is included that follows the "include" declaration
** in the input grammar file. */
#include <stdio.h>
#line 1 "bcplus/parser/detail/lemon_parser.y"

			#include <cassert>
			#include <cstring>

			#include <boost/foreach.hpp>

			#include "babb/utils/memory.h"

			#include "bcplus/Location.h"
			#include "bcplus/parser/BCParser.h"
			#include "bcplus/parser/Token.h"
			#include "bcplus/parser/detail/lemon_parser.h"
			#include "bcplus/parser/Number.h"
			#include "bcplus/parser/detail/NumberRange.h"
			#include "bcplus/parser/detail/NumberRangeEval.h"
			#include "bcplus/statements/Statement.h"
			#include "bcplus/statements/declarations.h"
			#include "bcplus/statements/QueryStatement.h"
			#include "bcplus/statements/RateDeclaration.h"
			#include "bcplus/statements/ForallTStatement.h"
			#include "bcplus/statements/blocks.h"
			#include "bcplus/statements/laws.h"
			#include "bcplus/elements/Element.h"
			#include "bcplus/elements/terms.h"
			#include "bcplus/elements/formulas.h"
			#include "bcplus/symbols/Symbol.h"
			#include "bcplus/symbols/MacroSymbol.h"
			#include "bcplus/symbols/ConstantSymbol.h"
			#include "bcplus/symbols/AttributeSymbol.h"
			#include "bcplus/symbols/NumberRangeSymbol.h"

			#define UNUSED void*

			using namespace bcplus;
			using namespace babb::utils;
			using namespace bcplus::parser;
			using namespace bcplus::statements;
			using namespace bcplus::elements;
			using namespace bcplus::languages;
			using namespace bcplus::symbols;
			using namespace bcplus::parser::detail;

			bool implicit=true;

			/// A list of terms
			typedef ReferencedVector<ref_ptr<const Term> >::type TermList;

			/// A list of sorts
			typedef ReferencedVector<ref_ptr<const SortSymbol> >::type SortList;


			typedef ReferencedVector<ref_ptr<const Token> >::type TokenList;

			/// Helper for deallocating things
			#define DEALLOC(x)	{ if (x) delete x; x = NULL; }

			/// A list of name sortlist pairs for declaring identifiers
			typedef std::pair<ref_ptr<const Token>, ref_ptr<SortList> > IdentifierDecl;
			typedef ReferencedVector<IdentifierDecl>::type IdentifierDeclList;

		
#line 343 "bcplus/parser/detail/lemon_parser.y"

	#define BASE_ELEM_DEF(elem, id, lparen, args, rparen, symtype, class, symclass)											\
		BASE_ELEM_DEF9(elem, id, lparen, args, rparen, symtype, class, symclass, false)

	#define BASE_ELEM_DEF9(elem, id, lparen, args, rparen, symtype, class, symclass, dynamic)								\
		elem = NULL;																										\
		ref_ptr<const Token> id_ptr = id;																					\
		ref_ptr<const Token> lparen_ptr = lparen;																			\
		ref_ptr<TermList> args_ptr = args;																					\
		ref_ptr<const Token> rparen_ptr = rparen;																			\
		size_t arity = (args_ptr ? args_ptr->size() : 0);																	\
																															\
		/* Check to see if we have constants in any of the terms */															\
		bool good = true;																									\
		if (!parser->lang()->support(Language::Feature::FORMULA_CONSTANT_ARGS) && arity) {									\
			int cargs = 0;																									\
			/*BOOST_FOREACH(Element const* elem, *args_ptr) { */															\
			for (TermList::const_iterator it = args_ptr->begin(); it != args_ptr->end(); it++) {							\
				cargs |=(*it)->cmask();																						\
			}																												\
			if (cargs) {																									\
				parser->_feature_error(Language::Feature::FORMULA_CONSTANT_ARGS, &id->beginLoc());							\
				good = false;																								\
			}																												\
		}																													\
																															\
		if (good) {																											\
			Symbol const* sym = parser->symtab()->resolve(symtype, *id_ptr->str(), arity);									\
																															\
			if (!sym && dynamic) {																							\
				/* Dynamic declarations are allowed. Attempt to create a new symbol */										\
				ref_ptr<ConstantSymbol::SortList> sorts = new ConstantSymbol::SortList();									\
				int argnum = 0;																								\
				if (args) {																									\
					BOOST_FOREACH(Term const* t, *args_ptr) {																\
							argnum++;																						\
						switch (t->subType()) {																				\
						case Term::Type::VARIABLE:																			\
							sorts->push_back(((Variable const*)t)->symbol()->sort());										\
							break;																							\
						case Term::Type::CONSTANT:																			\
							sorts->push_back(((Constant const*)t)->symbol()->sort());										\
							break;																							\
						case Term::Type::ANON_VAR:																			\
						case Term::Type::NULLARY:																			\
						case Term::Type::LUA:																				\
						case Term::Type::PYTHON:																			\
						case Term::Type::OBJECT:																			\
						case Term::Type::BINARY:																			\
						case Term::Type::UNARY:																				\
						case Term::Type::BINDING:																			\
							parser->_parse_error("Unable to dynamically declare abAction \"" + Symbol::genName(*id_ptr->str(), (args_ptr ? args_ptr->size() : 0))\
							+ "\". Could not deduce the sort of argument #" + boost::lexical_cast<std::string>(argnum)		\
							+ " as it isn't a constant or variable. This problem can be fixed by explicitly declaring the abAction" \
							" prior to this rule.", &id_ptr->beginLoc());													\
							good = false;																					\
							break;																							\
						}																									\
					}																										\
				}																											\
				if  (good) {																								\
					ref_ptr<ConstantSymbol> cs = new ConstantSymbol(ConstantSymbol::Type::ABACTION, id_ptr->str(), parser->symtab()->bsort(SymbolTable::BuiltinSort::BOOLEAN), sorts);\
					/* add the sort to the symbol table */																	\
					if (!parser->symtab()->create(cs)) {																	\
						/* It seems there was a problem. */																	\
						parser->_parse_error("An error occurred while declaring \"" + Symbol::genName(*id_ptr->str(), (args_ptr ? args_ptr->size() : 0)) + "\".");\
						good = false;																						\
						break;																								\
					} else sym = cs;																						\
				}																											\
			}																												\
																															\
			if (!good) {																									\
				YYERROR;																									\
			} else if (!sym || sym->type() != symtype) {																	\
				/* The preprocessor indicated this was a constant and it's not... oops. */									\
				parser->_parse_error(std::string("INTERNAL ERROR: Could not locate symbol table entry for ")				\
					+ Symbol::Type::cstr(symtype) + " \"" + Symbol::genName(*id_ptr->str(), arity)		 					\
					+ "\".", &id_ptr->beginLoc());																			\
				YYERROR;																									\
			} else {																										\
				elem = new class((symclass*)sym, args, id_ptr->beginLoc(), (arity ? rparen_ptr->endLoc() : id_ptr->endLoc()));	\
			} 																												\
		}																													\

	#define BASE_ELEM_BARE_DEF(elem, id, symtype, class, symclass)															\
		elem = NULL;																										\
		ref_ptr<const Token> id_ptr = id;																					\
																															\
		Symbol const* sym = parser->symtab()->resolve(symtype, *id_ptr->str());												\
		if (sym && sym->type() == symtype) {																				\
			elem = new class((symclass*)sym, id_ptr->beginLoc(), id_ptr->endLoc());											\
		} else {																											\
			/* The preprocessor indicated this was a constant and it's not... oops. */										\
			parser->_parse_error(std::string("INTERNAL ERROR: Could not locate symbol table entry for ")					\
				+ Symbol::Type::cstr(symtype) + " \"" + Symbol::genName(*id_ptr->str(), 0)			 						\
				+ "\".", &id_ptr->beginLoc());																				\
			YYERROR;																										\
		}

	#define BASE_LUA_ELEM(elem, id, lparen, args, rparen)																	\
		ref_ptr<const Token> id_ptr = id;																					\
		ref_ptr<const Token> lparen_ptr = lparen;																			\
		ref_ptr<TermList> args_ptr = args;																					\
		ref_ptr<const Token> rparen_ptr = rparen;																			\
		elem = new LuaTerm(id_ptr->str(), args, id_ptr->beginLoc(), (args ? rparen_ptr->endLoc() : id_ptr->endLoc()));

	#define BASE_PYTHON_ELEM(elem, id, lparen, args, rparen)																	\
		ref_ptr<const Token> id_ptr = id;																					\
		ref_ptr<const Token> lparen_ptr = lparen;																			\
		ref_ptr<TermList> args_ptr = args;																					\
		ref_ptr<const Token> rparen_ptr = rparen;																			\
		elem = new PyTerm(id_ptr->str(), args, id_ptr->beginLoc(), (args ? rparen_ptr->endLoc() : id_ptr->endLoc()));

	#define UNDECLARED(elem, id, args)																						\
		elem = NULL;																										\
		ref_ptr<const Token> id_ptr = id;																					\
		ref_ptr<TermList> args_ptr = args;																					\
		parser->_parse_error("Encountered undeclared identifier \"" 														\
			+ Symbol::genName(*id->str(), (args_ptr ? args_ptr->size() : 0)) + "\".", &id_ptr->beginLoc());					\
		YYERROR;

#line 544 "bcplus/parser/detail/lemon_parser.y"

	#define BASIC_TERM(term, id)																							\
		term = NULL;																										\
		ref_ptr<const Token> id_ptr = id;																					\
		ObjectSymbol const* sym = parser->symtab()->resolveOrCreate(new ObjectSymbol(id->str()));							\
		if (!sym) {																											\
			parser->_parse_error("An error occurred creating symbol \"" + *(id->str()) + "/0\".", &id->beginLoc());			\
			YYERROR;																										\
		} else term = new Object(sym, NULL, id->beginLoc(), id->endLoc());

	#define TERM_PARENS(term, lparen, sub, rparen)																			\
		ref_ptr<const Token> lparen_ptr = lparen;																			\
		ref_ptr<const Token> rparen_ptr = rparen;																			\
		term = sub;																											\
		term->parens(true);																									\
		term->beginLoc(lparen->beginLoc());																					\
		term->endLoc(rparen->endLoc());


	#define UNARY_ARITH(term, op, sub, operator)																			\
		term = NULL;																										\
		ref_ptr<const Token> op_ptr = op;																					\
		ref_ptr<Term> sub_ptr = sub;																						\
	 	term = new UnaryTerm(operator, sub, sub->beginLoc(), sub->endLoc());

	#define BINARY_ARITH(term, lhs, op, rhs, operator)																		\
		term = NULL;																										\
		ref_ptr<Term> lhs_ptr = lhs;																						\
		ref_ptr<Term> rhs_ptr = rhs;																						\
		ref_ptr<const Token> op_ptr = op;																					\
																															\
		bool good = true;																									\
		if (good) term = new BinaryTerm(operator, lhs, rhs, lhs->beginLoc(), rhs->endLoc());

	#define NULLARY_TERM(term, op, feature, operator)																		\
		term = NULL;																										\
		ref_ptr<const Token> op_ptr = op;																					\
																															\
		if (!parser->lang()->support(feature)) {																			\
			parser->_feature_error(feature, &op->beginLoc());																\
		} else {																											\
			term = new NullaryTerm(operator, op->beginLoc(), op->endLoc());													\
		}

#line 809 "bcplus/parser/detail/lemon_parser.y"

	#define NUM_UOP(t_new, t, val) \
		ref_ptr<const Referenced> t_ptr = t; \
		t_new = new Number(val, t->beginLoc(), t->endLoc());


	#define NUM_BOP(t_new, l, r, val) \
		ref_ptr<const Referenced> l_ptr = l, r_ptr = r; \
		t_new = new Number(val, l->beginLoc(), r->endLoc());

#line 855 "bcplus/parser/detail/lemon_parser.y"

	#define NESTED_BOP(new_f, lhs, op, rhs, operator)															\
		new_f = NULL;																							\
		ref_ptr<Formula> lhs_ptr = lhs;																			\
		ref_ptr<const Token> op_ptr = op;																		\
		ref_ptr<Formula> rhs_ptr = rhs;																			\
																												\
		if (!parser->lang()->support(Language::Feature::FORMULA_NESTED)) {										\
			parser->_feature_error(Language::Feature::FORMULA_NESTED, &op->beginLoc());							\
			YYERROR;																							\
		}																										\
		new_f = new BinaryFormula(operator, lhs, rhs, lhs->beginLoc(), rhs->endLoc());  						\

	#define NESTED_UOP(new_f, op, rhs, operator, feature)														\
		new_f = NULL;																							\
		ref_ptr<const Token> op_ptr = op;																		\
		ref_ptr<Formula> rhs_ptr = rhs;																			\
																												\
		/* Check to ensure that the operator is supported */													\
		if (!parser->lang()->support(feature)) {																\
			parser->_feature_error(feature);																	\
			YYERROR;																							\
		} else if (!parser->lang()->support(Language::Feature::FORMULA_NESTED)) {								\
			/* Check to ensure that this isn't nested */														\
			if (rhs->subType() == Formula::Type::BINARY || rhs->subType() == Formula::Type::UNARY) {			\
				parser->_feature_error(Language::Feature::FORMULA_NESTED, &rhs->beginLoc());					\
				YYERROR;																						\
			}																									\
		}																										\
		else new_f = new UnaryFormula (UnaryFormula:: Operator::NOT, rhs, op->beginLoc(), rhs->endLoc());

#line 936 "bcplus/parser/detail/lemon_parser.y"


	#define ATOMIC_FORMULA(af, constant, value) 														\
		af = NULL;																						\
		ref_ptr<Constant> c_ptr = constant;																\
																										\
																										\
		ref_ptr<const ObjectSymbol> t =																	\
			(value ? parser->symtab()->bobj(SymbolTable::BuiltinObject::TRUE) 							\
				: parser->symtab()->bobj(SymbolTable::BuiltinObject::FALSE));							\
																										\
																										\
		/* If this is a boolean constant we can interpret it as a shortcut for c=true */				\
		if (!constant->symbol()->sort()->contains(t)) {													\
			parser->_parse_error("\"" + *constant->symbol()->name() 									\
				+ "\" is not a boolean valued constant and therefore "									\
				"cannot be used in a bare atomic formula.", &constant->beginLoc());						\
			YYERROR;																					\
		} else {																						\
			af = new AtomicFormula(constant,															\
					new Object(t, NULL, constant->beginLoc(), constant->endLoc()), 						\
					constant->beginLoc(), constant->endLoc());											\
		}



#line 1072 "bcplus/parser/detail/lemon_parser.y"

	#define CARD_FORMULA(card, min, lbrack, vars, af, rbrack, max)																	\
		card = NULL;																												\
		ref_ptr<const Referenced> vars_ptr = vars, af_ptr = af;																	\
		ref_ptr<const Term> min_ptr = min, max_ptr = max;																		\
		ref_ptr<const Token> lbrack_ptr = lbrack, rbrack_ptr = rbrack;															\
																																	\
		bool good = true;																										\
		if (min && min_ptr->domainType() != DomainType::INTEGRAL && min_ptr->domainType() != DomainType::UNKNOWN) {				\
			parser->_parse_error("Invalid lower cardinality bound. Expected an integral expression.", &min_ptr->beginLoc());		\
			good = false;																										\
			YYERROR;																											\
		}																														\
																																	\
		if (max && max_ptr->domainType() != DomainType::INTEGRAL && max_ptr->domainType() != DomainType::UNKNOWN) {				\
			parser->_parse_error("Invalid upper cardinality bound. Expected an integral expression.", &max_ptr->beginLoc());		\
			good = false;																										\
			YYERROR;																											\
		}																														\
																																\
		if (good) {																												\
			/* hopefully good to go. */																							\
			card = new CardinalityFormula(vars, af, min, max, 																	\
				(min ? min_ptr->beginLoc() : lbrack_ptr->beginLoc()), 															\
				(max ? max_ptr->endLoc() : rbrack_ptr->endLoc()));																\
		}																														\



#line 1141 "bcplus/parser/detail/lemon_parser.y"

	#define BINDING(new_f, lhs, op, rhs, class)																	\
		new_f = NULL;																							\
		ref_ptr<const Element> lhs_ptr = lhs, rhs_ptr;															\
		ref_ptr<const Token> op_ptr = op;																		\
																												\
		if (!parser->lang()->support(Language::Feature::QUERY_BIND_STEP)) {										\
			parser->_feature_error(Language::Feature::QUERY_BIND_STEP, &op->beginLoc());						\
			YYERROR;																							\
		} else {																								\
			new_f = new class(lhs, rhs, lhs->beginLoc(), rhs->endLoc());										\
		}

#line 1558 "bcplus/parser/detail/lemon_parser.y"


	#define DYNAMIC_SORT_PLUS(new_s, s, op, feature, o)																												\
		new_s = NULL;																																				\
		ref_ptr<const Referenced> s_ptr = s, op_ptr = op;																											\
																																									\
																																									\
		if (!parser->lang()->support(feature)) {																													\
			parser->_feature_error(feature, &op->beginLoc());																										\
			YYERROR;																																				\
		} else {																																					\
			new_s = parser->symtab()->plus(s, o);																													\
		}
#line 1686 "bcplus/parser/detail/lemon_parser.y"

	#define CONSTANT_DECL(c, loc)																							\
		if (!parser->symtab()->create(c)) {																					\
			/* Check if it's a duplicate */																					\
			ConstantSymbol* c2 = (ConstantSymbol*)parser->symtab()->resolve(Symbol::Type::CONSTANT, *c->base(), c->arity());\
			if (!c2 || c2 != c) {																							\
				parser->_parse_error("Detected conflicting definition of symbol \"" + *c->name() + "\".", &loc);			\
			} else {																										\
				parser->_parse_error("Detected a duplicate definition of symbol \"" + *c->name() + "\".", &loc);			\
			}																												\
		}
#line 2711 "bcplus/parser/detail/lemon_parser.y"

	#define NC_STATEMENT(stmt, kw, period, feature, class)											\
		stmt = NULL;																				\
		ref_ptr<const Token> kw_ptr = kw, p_ptr = period;											\
																									\
		if (!parser->lang()->support(feature)) {													\
			parser->_feature_error(feature, &kw->beginLoc());										\
			YYERROR;																				\
		} else {																					\
			stmt = new class(kw->beginLoc(), period->endLoc());										\
		}

#line 2734 "bcplus/parser/detail/lemon_parser.y"

	#define VALUE_DECL(stmt, cd, kw, val_obj, p, feature, class)									\
		stmt = NULL;																				\
		ref_ptr<const Referenced> cd_ptr = cd, kw_ptr = kw, val_ptr = val_obj, p_ptr = p;			\
																									\
		if (!parser->lang()->support(feature)) {													\
			parser->_feature_error(feature, &kw->beginLoc());										\
			YYERROR;																				\
		} else { 																					\
			int value = val_obj->val();																\
			if (value < 0) {																		\
				parser->_parse_error("ERROR: Expected a positive integer.", &val_obj->beginLoc());	\
			} else {																				\
				stmt = new class(value, cd->beginLoc(), p->endLoc());								\
			}																						\
		}
#line 2763 "bcplus/parser/detail/lemon_parser.y"

	struct QueryData {
		QueryStatement::FormulaList* l;
		NumberRangeEval* maxstep;
		Token const* label;
	};

#line 2870 "bcplus/parser/detail/lemon_parser.y"

	#define QUERY_DECL(decl, kw, val, feature)																\
		decl = NULL;																						\
		ref_ptr<const Token> kw_ptr = kw, val_ptr = val;													\
																											\
		if (!parser->lang()->support(feature)) {															\
			parser->_feature_error(feature, &kw->beginLoc());												\
			YYERROR;																						\
		} else {																							\
			decl = val_ptr.release();																		\
		}

#line 2942 "bcplus/parser/detail/lemon_parser.y"

	#define CLAUSE(elem, kw, f, feature) 														\
		ref_ptr<const Token> kw_ptr = kw;														\
		elem = f;																				\
		if (!parser->lang()->support(feature)) {												\
			parser->_feature_error(feature, &kw->beginLoc());									\
			YYERROR;																			\
		}
#line 3053 "bcplus/parser/detail/lemon_parser.y"

	#define LAW_BASIC_FORM(law, kw, head, ifbody, ifcons, after, unless, where, p, static, dynamic, class)											\
		law = NULL;																																	\
		ref_ptr<Element> head_ptr = head, if_ptr = ifbody, ifcons_ptr = ifcons, after_ptr = after, unless_ptr = unless, where_ptr = where;		\
		ref_ptr<const Token> kw_ptr = kw, p_ptr = p;																								\
		Language::Feature::type feature = ((after) ? (dynamic) : (static));																			\
																																					\
		if (!parser->lang()->support(feature)) {																									\
			parser->_feature_error(feature, ((kw) ? &(kw_ptr)->beginLoc() : &(head_ptr)->beginLoc()));												\
			YYERROR;																																\
		} else {																																	\
			law = new class(head, ifbody, ifcons, after, unless, where, ((kw) ? (kw_ptr)->beginLoc() : (head_ptr)->beginLoc()), (p_ptr)->endLoc());	\
		}

	#define LAW_IMPL_FORM(law, head, kw, body, where, p, feature, class)																			\
		law = NULL;																																	\
		ref_ptr<Element> body_ptr = body, where_ptr = where;																						\
		ref_ptr<Formula> head_ptr = head;																											\
		ref_ptr<const Token> kw_ptr = kw, p_ptr = p;																								\
																																					\
		if (!head) head_ptr = new NullaryFormula(NullaryFormula::Operator::FALSE, kw->beginLoc(), kw->beginLoc());									\
		if (!parser->lang()->support(feature)) {																									\
			parser->_feature_error(feature, &kw->beginLoc());																						\
			YYERROR;																																\
		} else {																																	\
			law = new class(head_ptr, body, where, head_ptr->beginLoc(), p->endLoc());																\
		}


	#define LAW_DYNAMIC_FORM(law, body, kw, head, ifbody, unless, where, p, feature, class)															\
		law = NULL;																																	\
		ref_ptr<Element> body_ptr = body, head_ptr = head, if_ptr = ifbody, unless_ptr = unless, where_ptr = where;								\
		ref_ptr<const Token> kw_ptr = kw, p_ptr = p;																								\
																																					\
		if (!parser->lang()->support(feature)) {																									\
			parser->_feature_error(feature, &kw->beginLoc());																						\
			YYERROR;																																\
		} else {																																	\
			law = new class(body, head, ifbody, unless, where, body->beginLoc(), p->endLoc());														\
		}

	#define LAW_INCREMENTAL_FORM(law, body, kw, head, by, ifbody, unless, where, p, feature, class)													\
		law = NULL;																																	\
		ref_ptr<Element> body_ptr = body, head_ptr = head, if_ptr = ifbody, unless_ptr = unless, where_ptr = where;								\
		ref_ptr<Element> by_ptr = by;																											\
		ref_ptr<const Token> kw_ptr = kw, p_ptr = p;																								\
																																					\
		if (!parser->lang()->support(feature)) {																									\
			parser->_feature_error(feature, &kw->beginLoc());																						\
			YYERROR;																																\
		} else {																																	\
			law = new class(body, head, by, ifbody, unless, where, body->beginLoc(), p->endLoc());													\
		}


	#define LAW_CONSTRAINT_FORM(law, kw, body, after, unless, where, p, static, dynamic, class)														\
		law = NULL;																																	\
		ref_ptr<Element> body_ptr = body, after_ptr = after, unless_ptr = unless, where_ptr = where;												\
		ref_ptr<const Token> kw_ptr = kw, p_ptr = p;																								\
																																					\
		Language::Feature::type feature = (after ? dynamic : static);																				\
																																					\
		if (!parser->lang()->support(feature)) {																									\
			parser->_feature_error(feature, (kw ? &kw_ptr->beginLoc() : &body_ptr->beginLoc()));													\
			YYERROR;																																\
		} else {																																	\
			law = new class(body, after, unless, where, (kw ? kw_ptr->beginLoc() : body_ptr->beginLoc()), p_ptr->endLoc());							\
		}

	#define LAW_DYNAMIC_CONSTRAINT_FORM(law, kw, body, ifbody, unless, where, p, feature, class)													\
		law = NULL;																																	\
		ref_ptr<Element> body_ptr = body, if_ptr = ifbody, unless_ptr = unless, where_ptr = where;													\
		ref_ptr<const Token> kw_ptr = kw, p_ptr = p;																								\
																																					\
		if (!parser->lang()->support(feature)) {																									\
			parser->_feature_error(feature, (kw ? &kw_ptr->beginLoc() : &body_ptr->beginLoc()));													\
			YYERROR;																																\
		} else {																																	\
			law = new class(body, ifbody, unless, where, (kw ? kw_ptr->beginLoc() : body_ptr->beginLoc()), p_ptr->endLoc());						\
		}

	#define LAW_SIMPLE_FORM(law, kw, head, where, p, feature, class)																				\
		law = NULL;																																	\
		ref_ptr<Element> head_ptr = head;																		\
		ref_ptr<const Referenced> where_ptr = where;															\
		ref_ptr<const Token> kw_ptr = kw, p_ptr = p;															\
																												\
		if (!parser->lang()->support(feature)) {																\
			parser->_feature_error(feature, (kw ? &kw_ptr->beginLoc() : &head_ptr->beginLoc()));				\
			YYERROR;																							\
		} else {																								\
			law = new class(head, where, (kw ? kw_ptr->beginLoc() : head_ptr->beginLoc()), p_ptr->endLoc());	\
		}


#line 3246 "bcplus/parser/detail/lemon_parser.y"

	#define CODE_BLK(stmt, code, feature, type) 												\
		ref_ptr<const Token> code_ptr = code;													\
		if (!parser->lang()->support(feature)) {												\
			stmt = NULL;																		\
			parser->_feature_error(feature, &code->beginLoc());									\
			YYERROR;																			\
		} else {																				\
			stmt = new type(code, code->beginLoc(), code->endLoc());							\
		}
#line 545 "bcplus/parser/detail/lemon_parser.c"
/* Next is all token values, in a form suitable for use by makeheaders.
** This section will be null unless lemon is run with the -m switch.
*/
/* 
** These constants (all generated automatically by the parser generator)
** specify the various kinds of tokens (terminals) that the parser
** understands. 
**
** Each symbol here is a terminal symbol in the grammar.
*/
/* Make sure the INTERFACE macro is defined.
*/
#ifndef INTERFACE
# define INTERFACE 1
#endif
/* The next thing included is series of defines which control
** various aspects of the generated parser.
**    YYCODETYPE         is the data type used for storing terminal
**                       and nonterminal numbers.  "unsigned char" is
**                       used if there are fewer than 250 terminals
**                       and nonterminals.  "int" is used otherwise.
**    YYNOCODE           is a number of type YYCODETYPE which corresponds
**                       to no legal terminal or nonterminal number.  This
**                       number is used to fill in empty slots of the hash 
**                       table.
**    YYFALLBACK         If defined, this indicates that one or more tokens
**                       have fall-back values which should be used if the
**                       original value of the token will not parse.
**    YYACTIONTYPE       is the data type used for storing terminal
**                       and nonterminal numbers.  "unsigned char" is
**                       used if there are fewer than 250 rules and
**                       states combined.  "int" is used otherwise.
**    lemon_parserTOKENTYPE     is the data type used for minor tokens given 
**                       directly to the parser from the tokenizer.
**    YYMINORTYPE        is the data type used for all minor tokens.
**                       This is typically a union of many types, one of
**                       which is lemon_parserTOKENTYPE.  The entry in the union
**                       for base tokens is called "yy0".
**    YYSTACKDEPTH       is the maximum depth of the parser's stack.  If
**                       zero the stack is dynamically sized using realloc()
**    lemon_parserARG_SDECL     A static variable declaration for the %extra_argument
**    lemon_parserARG_PDECL     A parameter declaration for the %extra_argument
**    lemon_parserARG_STORE     Code to store %extra_argument into yypParser
**    lemon_parserARG_FETCH     Code to extract %extra_argument from yypParser
**    YYNSTATE           the combined number of states.
**    YYNRULE            the number of rules in the grammar
**    YYERRORSYMBOL      is the code number of the error symbol.  If not
**                       defined, then do no error processing.
*/
#define YYCODETYPE unsigned short int
#define YYNOCODE 270
#define YYACTIONTYPE unsigned short int
#define lemon_parserTOKENTYPE  Token const* 								
typedef union {
  int yyinit;
  lemon_parserTOKENTYPE yy0;
  NumberRangeEval* yy1;
  MacroDeclaration::ElementList* yy5;
  VariableDeclaration* yy19;
  ObjectDeclaration* yy24;
  SortSymbol const* yy32;
  Term* yy39;
  ConstantDeclaration* yy55;
  Number* yy68;
  SortSymbol* yy69;
  Statement* yy76;
  NumberRange* yy107;
  CardinalityFormula::VariableList* yy117;
  QueryStatement* yy136;
  RateDeclaration* yy175;
  Formula* yy179;
  Constant* yy189;
  Token const* yy193;
  Variable* yy195;
  MacroSymbol::ArgumentList* yy214;
  LuaTerm* yy237;
  MacroDeclaration* yy243;
  AtomicFormula* yy274;
  TokenList* yy280;
  QueryData yy305;
  ObjectDeclaration::Element::ObjectList* yy323;
  QuantifierFormula::Operator::type yy325;
  ShowStatement::ElementList* yy331;
  ObjectDeclaration::Element* yy332;
  SortDeclaration* yy333;
  IdentifierDeclList* yy368;
  NCStatement* yy379;
  QuantifierFormula* yy387;
  CardinalityFormula* yy393;
  UNUSED yy409;
  ForallTStatement* yy416;
  Object* yy418;
  ObjectDeclaration::ElementList* yy419;
  ConstantSymbol::SortList* yy423;
  VariableDeclaration::ElementList* yy424;
  MacroSymbol* yy437;
  QuantifierFormula::QuantifierList* yy445;
  ConstantSymbol::Type::type yy449;
  ConstantDeclaration::ElementList* yy451;
  TermList* yy457;
  StrongNCStatement* yy494;
  SortDeclaration::ElementList* yy523;
  int yy539;
} YYMINORTYPE;
#ifndef YYSTACKDEPTH
#define YYSTACKDEPTH 100
#endif
#define lemon_parserARG_SDECL  BCParser* parser						;
#define lemon_parserARG_PDECL , BCParser* parser						
#define lemon_parserARG_FETCH  BCParser* parser						 = yypParser->parser						
#define lemon_parserARG_STORE yypParser->parser						 = parser						
#define YYNSTATE 940
#define YYNRULE 482
#define YYERRORSYMBOL 147
#define YYERRSYMDT yy539
#define YYFALLBACK 1
#define YY_NO_ACTION      (YYNSTATE+YYNRULE+2)
#define YY_ACCEPT_ACTION  (YYNSTATE+YYNRULE+1)
#define YY_ERROR_ACTION   (YYNSTATE+YYNRULE)

/* The yyzerominor constant is used to initialize instances of
** YYMINORTYPE objects to zero. */
static const YYMINORTYPE yyzerominor = { 0 };

/* Define the yytestcase() macro to be a no-op if is not already defined
** otherwise.
**
** Applications can choose to define yytestcase() in the %include section
** to a macro that can assist in verifying code coverage.  For production
** code the yytestcase() macro should be turned off.  But it is useful
** for testing.
*/
#ifndef yytestcase
# define yytestcase(X)
#endif


/* Next are the tables used to determine what action to take based on the
** current state and lookahead token.  These tables are used to implement
** functions that take a state number and lookahead value and return an
** action integer.  
**
** Suppose the action integer is N.  Then the action is determined as
** follows
**
**   0 <= N < YYNSTATE                  Shift N.  That is, push the lookahead
**                                      token onto the stack and goto state N.
**
**   YYNSTATE <= N < YYNSTATE+YYNRULE   Reduce by rule N-YYNSTATE.
**
**   N == YYNSTATE+YYNRULE              A syntax error has occurred.
**
**   N == YYNSTATE+YYNRULE+1            The parser accepts its input.
**
**   N == YYNSTATE+YYNRULE+2            No such action.  Denotes unused
**                                      slots in the yy_action[] table.
**
** The action table is constructed as a single large table named yy_action[].
** Given state S and lookahead X, the action is computed as
**
**      yy_action[ yy_shift_ofst[S] + X ]
**
** If the index value yy_shift_ofst[S]+X is out of range or if the value
** yy_lookahead[yy_shift_ofst[S]+X] is not equal to X or if yy_shift_ofst[S]
** is equal to YY_SHIFT_USE_DFLT, it means that the action is not in the table
** and that yy_default[S] should be used instead.  
**
** The formula above is for computing the action when the lookahead is
** a terminal symbol.  If the lookahead is a non-terminal (as occurs after
** a reduce action) then the yy_reduce_ofst[] array is used in place of
** the yy_shift_ofst[] array and YY_REDUCE_USE_DFLT is used in place of
** YY_SHIFT_USE_DFLT.
**
** The following are the tables generated in this section:
**
**  yy_action[]        A single table containing all actions.
**  yy_lookahead[]     A table containing the lookahead for each entry in
**                     yy_action.  Used to detect hash collisions.
**  yy_shift_ofst[]    For each state, the offset into yy_action for
**                     shifting terminals.
**  yy_reduce_ofst[]   For each state, the offset into yy_action for
**                     shifting non-terminals after a reduce.
**  yy_default[]       Default action for each state.
*/
#define YY_ACTTAB_COUNT (3781)
static const YYACTIONTYPE yy_action[] = {
 /*     0 */   939,  214,  215,  938,  937,  936,  935,  934,  933,  932,
 /*    10 */   931,  928,  927,  926,  925,  924,  923,  922,  930,  929,
 /*    20 */   754,  889,  336,  921,  913,  920,  919,  912,  128,  126,
 /*    30 */   124,  122,  120,  916,  332,  337,  889,  336,  921,  913,
 /*    40 */   501,  919,  912,  843,  443,  124,  122,  120,  914,  331,
 /*    50 */   337,  756,  826,  378,  258,  940,  351,  835,  832,  831,
 /*    60 */   830,  829,  756,  129,  378,  260,  842,  841,   64,   19,
 /*    70 */   503,  889,  336,  921,  913,  920,  919,  912,  129,   24,
 /*    80 */    23,   22,   26,   25,  331,  337,   27,  553,  494,  757,
 /*    90 */   758,  383,  835,  832,  831,  830,  829,  492,  554,  494,
 /*   100 */   757,  758,   63,  643,  642,  641,  640,  639,  638,  637,
 /*   110 */   636,  635,  634,  633,  632,  631,  630,  629,  628,  627,
 /*   120 */   626,  625,  888,  887,  597,  820,   60,  598,  886,  609,
 /*   130 */   608,  605,  604,  603,  602,  607,  606,  907,  917,  918,
 /*   140 */   921,  913,  920,  919,  912,  508,  442,   24,   23,   22,
 /*   150 */    26,   25,   12,   14,   27,  824,  823,   33,  837,   10,
 /*   160 */    11,   62,  200,   21,  263, 1252,  532,  121,  915,  910,
 /*   170 */   217,  262,  727,  592,  378,  859,  858,  860,    9,  534,
 /*   180 */   533,    8, 1252,   32, 1252,  581,  261,   36,  776,  756,
 /*   190 */   755,  378,  839,  840,  713,  567,  580,  338,  193,  129,
 /*   200 */    37,  177,  175,  174,  273, 1252, 1252,  817,   13,  592,
 /*   210 */   816,  119,  749,  748,  747,  746, 1252, 1252,  732,  486,
 /*   220 */   726,  552,  651, 1252,  650,  566,  494,  757,  758,  745,
 /*   230 */   713,  743,  565,  557,  132,  453,  710,  787,  742,  103,
 /*   240 */   118,  771,  770,  772,   31, 1252,  133,  601,  824,  823,
 /*   250 */   559,  561,  741,  739,  740,  744,   40,  309,  773,  774,
 /*   260 */   600,  911,  599,  589,  588,  587,  232,  199,  888,  887,
 /*   270 */   597,  452,  710,  598,  886,  716,  696,  581,  921,  913,
 /*   280 */   501,  919,  912,   26,   25,   16,  915,   27,  696,  581,
 /*   290 */   921,  913,  920,  919,  912,   23,   22,   26,   25,  663,
 /*   300 */   230,   27,   54,   53,  764,  228,   55,   36,  763,   38,
 /*   310 */   503,  663,  327,  908,  915,  343,  667,  664,  662,  661,
 /*   320 */   717,  859,  858,  860,  327,  738,  173,  359,  667,  664,
 /*   330 */   662,  661,  325,   35,  687,  759,  270,  760,  827,  828,
 /*   340 */   778,  218,   66,  129,    2,  271,   30,  214,  215,   34,
 /*   350 */   273,  213,  889,  336,  921,  913,  920,  919,  912,  258,
 /*   360 */   222,  474,  649,  648,  733,  328,  337,  157,  155,  153,
 /*   370 */   152,  151,  349,  835,  832,  831,  830,  829,  600,   28,
 /*   380 */    29,  888,  887,  597,  192,  103,  598,  886,  593,  911,
 /*   390 */   696,  581,  921,  913,  501,  919,  912,   24,   23,   22,
 /*   400 */    26,   25,  724,  655,   27,  360,  600,  911,  599,  589,
 /*   410 */   588,  587,  205,  663,  223,  187,    4,  197,  203,  204,
 /*   420 */   105,  707,  221,   39,  503,  475,  327,  915,  224,  345,
 /*   430 */   667,  664,  662,  661,  859,  858,  860,  696,  581,  921,
 /*   440 */   913,  920,  919,  912,  231,  229,  227,  226,  225,  476,
 /*   450 */   477,  839,  840,   27,  227,  226,  225,  193,  134,   37,
 /*   460 */   663,  782,  783,  273,   52,   51,   50,   54,   53,  194,
 /*   470 */   102,   55,  885,  327,  881,  762,  358,  667,  664,  662,
 /*   480 */   661,  112,  111,  110,  548,  109,  108,  107,  106,   66,
 /*   490 */   250,  249,  248,  132,  104,  695,  694,  597,  103,  255,
 /*   500 */   598,  693,  101,  255,  182,  117,  116,  115,  114,  113,
 /*   510 */   715,  653,  652,  592,  157,  155,  153,  152,  151,  600,
 /*   520 */   911,  599,  589,  588,  587,  581,  906,  905,  597,  819,
 /*   530 */   201,  598,  904,  253,  713,  100,   73,  253,  251,  202,
 /*   540 */   196,  915,  251,  153,  152,  151,  535,  838,  671,  670,
 /*   550 */   536,  696,  581,  921,  913,  920,  919,  912,   72,  129,
 /*   560 */    24,   23,   22,   26,   25,  659,  660,   27,  212,  291,
 /*   570 */    75,    6,  915,   49,  663,   61,  714,  273,  719,  899,
 /*   580 */   898,  900,   24,   23,   22,   26,   25,  326,  325,   27,
 /*   590 */   341,  667,  664,  662,  661, 1359,  901,  902,  216,  181,
 /*   600 */   179,  177,  175,  174,  127,  909,   47,   48,  695,  694,
 /*   610 */   597,  861,  139,  598,  693, 1359,  592,  907,  917,  918,
 /*   620 */   921,  913,  920,  919,  912,  507,  442,   74,   94,   93,
 /*   630 */    92,   91,   90,  600,  911,  599,   76,  590,  125,  244,
 /*   640 */   220,  503,  845,  123,  593,  906,  905,  597,   45,   44,
 /*   650 */   598,  904,   46,  818,  915,  254,  252,  250,  249,  248,
 /*   660 */    69,  671,  670,  672,  600,  911,  599,  596,  595,  594,
 /*   670 */   696,  581,  921,  913,  920,  919,  912,  569,  659,  660,
 /*   680 */   582,  212,   31,  727,    6,  378,   49,  482,  478,  542,
 /*   690 */   273,  915,  861,  663,  496,  734,  495,  592,  899,  898,
 /*   700 */   900,   99,   98,   97,   96,   95,  669,  268,   55,  657,
 /*   710 */   667,  664,  662,  661,  709,  901,  902,   68,  585,   47,
 /*   720 */    48,  219,  503,  127,  915,  139,  863,  888,  887,  597,
 /*   730 */   324,  730,  598,  886,  201,  696,  581,  921,  913,  920,
 /*   740 */   919,  912,  592,  202,  793,   36,  600,  911,  599,  880,
 /*   750 */   870,  921,  913,  920,  919,  912,  247,  125,  663,  504,
 /*   760 */   432,  256,  123,  591,  814,  813,  597,  903, 1174,  598,
 /*   770 */   812,  327, 1174,  915,  666,  667,  664,  662,  661,  654,
 /*   780 */   859,  858,  860,  600,  911,  599,  596,  595,  594,  907,
 /*   790 */   917,  918,  921,  913,  920,  919,  912,  505,  442,    5,
 /*   800 */   128,  126,  124,  122,  120,  131,  792,  879,  878,  597,
 /*   810 */   915,    7,  598,  877,  692,  581,  600,  806,  805,  807,
 /*   820 */  1319,  895,   15,  146,  145,  144,  791,  143,  142,  141,
 /*   830 */   140,  484,  720,  483,  796,  797,  790,  838,  245,  130,
 /*   840 */   789,  750,   58,  246,  103,   67, 1319,  159,  150,  149,
 /*   850 */   148,  147,   17,  915,  128,  126,  124,  122,  120,  509,
 /*   860 */   872,  871,  873,  788,  894,  600,  911,  599,  589,  588,
 /*   870 */   587,  191,  499,  779,  592,   56,   57,  874,  875,  308,
 /*   880 */   190,  160,  568,  777,  495,  180,  785,  690,  689,  597,
 /*   890 */    71,  780,  598,  688,  258,  713,  243,  128,  126,  124,
 /*   900 */   122,  120,  600,  911,  599,  198,  543,  815,  804,  921,
 /*   910 */   913,  920,  919,  912,   24,   23,   22,   26,   25,  178,
 /*   920 */   189,   27,  334,  592,  176,   24,   23,   22,   26,   25,
 /*   930 */   736,  209,   27,  915,  380,  801,  798,  712,  735,  562,
 /*   940 */   683,  682,  684,  893,  586,  600,  911,  599,  753,  889,
 /*   950 */   336,  921,  913,  501,  919,  912,  208,  685,  686,  756,
 /*   960 */   191,  378,  331,  337,  529,  158,  723,  483,  191,  353,
 /*   970 */   835,  832,  831,  830,  829,  752,  128,  126,  124,  122,
 /*   980 */   120,  751,   20,  503,  729,  259,  322,  889,  335,  921,
 /*   990 */   913,  920,  919,  912,  490,  554,  494,  757,  758,  156,
 /*  1000 */   836,  337,  497,  781,  154,  824,  823,  821,  835,  832,
 /*  1010 */   831,  830,  829,  563,  191,  378,  889,  336,  921,  913,
 /*  1020 */   920,  919,  912, 1423,    1,  600,  911,  599,   70,  331,
 /*  1030 */   337,  128,  126,  124,  122,  120,  834,  835,  832,  831,
 /*  1040 */   830,  829,  481,  542,  889,  336,  921,  913,  920,  919,
 /*  1050 */   912,  207,   24,   23,   22,   26,   25,  331,  337,   27,
 /*  1060 */   556,  480,  542,  555,  833,  835,  832,  831,  830,  829,
 /*  1070 */   186,  889,  336,  921,  913,  920,  919,  912,  231,  229,
 /*  1080 */   227,  226,  225,  525,  331,  337,  479,  542,  794,  454,
 /*  1090 */   542,  584,  835,  832,  831,  830,  829,   31,  257,  322,
 /*  1100 */   188,  206,  889,  336,  921,  913,  920,  919,  912,  549,
 /*  1110 */    52,   51,   50,   54,   53,  331,  337,   55,  737,  560,
 /*  1120 */   547,  378,  583,  835,  832,  831,  830,  829,  727,  185,
 /*  1130 */   378,  889,  336,  921,  913,  920,  919,  912,  184,   24,
 /*  1140 */    23,   22,   26,   25,  331,  337,   27,  183,  558,  541,
 /*  1150 */   378,  410,  835,  832,  831,  830,  829,  889,  336,  921,
 /*  1160 */   913,  920,  919,  912,  128,  126,  124,  122,  120,  722,
 /*  1170 */   331,  337,  540,  487,  725,  486,  726,  462,  835,  832,
 /*  1180 */   831,  830,  829,  718,   46,  889,  336,  921,  913,  920,
 /*  1190 */   919,  912,  711,  756,  550,  378,  378,  708,  331,  337,
 /*  1200 */   267,  647,  210,  473,  646,  461,  835,  832,  831,  830,
 /*  1210 */   829,  530,  528,  889,  336,  921,  913,  920,  919,  912,
 /*  1220 */   756,  658,  378,   65,  527,  325,  331,  337,  489,  554,
 /*  1230 */   494,  757,  758,  354,  835,  832,  831,  830,  829,  526,
 /*  1240 */   889,  336,  921,  913,  920,  919,  912,  524,   43,   42,
 /*  1250 */    41,   45,   44,  331,  337,   46,  544,  494,  757,  758,
 /*  1260 */   352,  835,  832,  831,  830,  829,  254,  252,  250,  249,
 /*  1270 */   248,  889,  336,  921,  913,  920,  919,  912,  645,  523,
 /*  1280 */   756,  593,  378,  522,  331,  337,  656,  864,  644,  624,
 /*  1290 */   623,  350,  835,  832,  831,  830,  829,  915,  622,  539,
 /*  1300 */   889,  336,  921,  913,  920,  919,  912,  621,   43,   42,
 /*  1310 */    41,   45,   44,  331,  337,   46,  493,  494,  757,  758,
 /*  1320 */   382,  835,  832,  831,  830,  829,  889,  336,  921,  913,
 /*  1330 */   920,  919,  912,  273,  620,  618,  876,  593,  617,  331,
 /*  1340 */   337,  615,  614,  613,  612,  611,  381,  835,  832,  831,
 /*  1350 */   830,  829,  325,  242,  889,  336,  921,  913,  920,  919,
 /*  1360 */   912,  862,  756,  264,  378,  911,  825,  331,  337,  181,
 /*  1370 */   179,  177,  175,  174,  239,  835,  832,  831,  830,  829,
 /*  1380 */   320,   18,  889,  336,  921,  913,  920,  919,  912,  600,
 /*  1390 */   822,  319,   17,  138,  195,  333,  337,  485,  554,  494,
 /*  1400 */   757,  758,  372,  835,  832,  831,  830,  829,  593,  889,
 /*  1410 */   336,  921,  913,  920,  919,  912,  318,   43,   42,   41,
 /*  1420 */    45,   44,  331,  337,   46,  577,   59,  316,  786,  340,
 /*  1430 */   835,  832,  831,  830,  829,  498,  575,  573,  731,  314,
 /*  1440 */   889,  336,  921,  913,  920,  919,  912,  312,  755,  306,
 /*  1450 */   571,  885,  310,  331,  337,   31,  379,  305,  290,  570,
 /*  1460 */   238,  835,  832,  831,  830,  829,  301,  304,  302,  889,
 /*  1470 */   336,  921,  913,  920,  919,  912,  521,  855,  582,  300,
 /*  1480 */   289,  520,  331,  337,  117,  116,  115,  114,  113,  237,
 /*  1490 */   835,  832,  831,  830,  829,  889,  336,  921,  913,  920,
 /*  1500 */   919,  912,  323,  298,  285,  854,  845,  518,  331,  337,
 /*  1510 */   128,  126,  124,  122,  120,  233,  835,  832,  831,  830,
 /*  1520 */   829,  296,  915,  889,  336,  921,  913,  920,  919,  912,
 /*  1530 */   517,  756,  294,  378,  516,  292,  331,  337,  128,  126,
 /*  1540 */   124,  122,  120,  236,  835,  832,  831,  830,  829,  515,
 /*  1550 */   288,  889,  336,  921,  913,  920,  919,  912,  211,  287,
 /*  1560 */   284,  514,  283,  513,  331,  337,  282,  491,  494,  757,
 /*  1570 */   758,  235,  835,  832,  831,  830,  829,  280,  889,  336,
 /*  1580 */   921,  913,  920,  919,  912,  279,  278,  277,  317,  574,
 /*  1590 */   512,  331,  337,    3,  275,  572,  885,  511,  234,  835,
 /*  1600 */   832,  831,  830,  829,    7,  112,  111,  110,  510,  109,
 /*  1610 */   108,  107,  106,  311,  600,   15,  146,  145,  144,  784,
 /*  1620 */   143,  142,  141,  140,  531,  307,  303,  616,  286,  117,
 /*  1630 */   116,  115,  114,  113,  281,  274,  321,  376,  761,  377,
 /*  1640 */   159,  150,  149,  148,  147,  315,  546,  450,  705,  451,
 /*  1650 */   704,  696,  581,  921,  913,  920,  919,  912,  703,  696,
 /*  1660 */   581,  921,  913,  920,  919,  912,  889,  339,  921,  913,
 /*  1670 */   920,  919,  912,  702,  663,   51,   50,   54,   53,  857,
 /*  1680 */   428,   55,  663,   42,   41,   45,   44,  327,  701,   46,
 /*  1690 */   665,  667,  664,  662,  661,  327,  375,  374,  538,  667,
 /*  1700 */   664,  662,  661,  576,  373,  696,  581,  921,  913,  920,
 /*  1710 */   919,  912,  393,  696,  581,  921,  913,  920,  919,  912,
 /*  1720 */   889,  427,  921,  913,  920,  919,  912,  356,  663,  355,
 /*  1730 */   313,  519,  276,  387,  428,  299,  663,  455,  295,  293,
 /*  1740 */   297,  327,  769,  456,  537,  667,  664,  662,  661,  327,
 /*  1750 */   768,  767,  394,  667,  664,  662,  661,  766,  721,  765,
 /*  1760 */   696,  581,  921,  913,  920,  919,  912,  396,  696,  581,
 /*  1770 */   921,  913,  920,  919,  912,  889,  852,  921,  913,  920,
 /*  1780 */   919,  912, 1424,  663, 1424, 1424, 1424, 1424,  857,  428,
 /*  1790 */  1424,  663, 1424, 1424, 1424, 1424,  327, 1424, 1424,  445,
 /*  1800 */   667,  664,  662,  661,  327,   59,   17,  444,  667,  664,
 /*  1810 */   662,  661,  696,  581,  921,  913,  920,  919,  912, 1424,
 /*  1820 */   696,  581,  921,  913,  920,  919,  912,  907,  917,  918,
 /*  1830 */   921,  913,  920,  919,  912,  663,  441,   24,   23,   22,
 /*  1840 */    26,   25, 1424,  663,   27, 1424, 1424, 1424,  327, 1424,
 /*  1850 */  1424,  346,  667,  664,  662,  661,  327, 1424, 1424,  344,
 /*  1860 */   667,  664,  662,  661,  696,  581,  921,  913,  920,  919,
 /*  1870 */   912,  889,  336,  921,  913,  920,  919,  912,  700,   24,
 /*  1880 */    23,   22,   26,   25,  329,  337,   27,  663, 1424, 1424,
 /*  1890 */  1424, 1424,  853,  843,  838, 1424, 1424, 1424, 1424, 1424,
 /*  1900 */   327, 1424, 1424,  342,  667,  664,  662,  661, 1424, 1424,
 /*  1910 */   254,  252,  250,  249,  248,  502,  842,  841,  889,  336,
 /*  1920 */   921,  913,  920,  919,  912,  128,  126,  124,  122,  120,
 /*  1930 */  1424,  332,  337,  889,  336,  921,  913,  920,  919,  912,
 /*  1940 */   843,  838, 1424, 1424, 1424, 1424,  332,  337,  880,  870,
 /*  1950 */   921,  913,  920,  919,  912,  843,  838, 1424, 1424,  433,
 /*  1960 */  1424, 1424,  844,  842,  841, 1424, 1424, 1424,  889,  336,
 /*  1970 */   921,  913,  920,  919,  912, 1424, 1424,  272,  842,  841,
 /*  1980 */  1424,  332,  337,  889,  336,  921,  913,  920,  919,  912,
 /*  1990 */   843,  838, 1424, 1424, 1424, 1424,  332,  337,  880,  870,
 /*  2000 */   921,  913,  920,  919,  912,  843,  838, 1424, 1424,  467,
 /*  2010 */  1424, 1424,  269,  842,  841, 1424, 1424,  889,  336,  921,
 /*  2020 */   913,  920,  919,  912, 1424, 1424, 1424,  266,  842,  841,
 /*  2030 */   332,  337,  699,  194, 1424, 1424, 1424, 1424, 1424,  843,
 /*  2040 */   838,    3, 1424, 1424, 1424,  112,  111,  110, 1424,  109,
 /*  2050 */   108,  107,  106,  112,  111,  110, 1424,  109,  108,  107,
 /*  2060 */   106,  265,  842,  841,  254,  252,  250,  249,  248,  117,
 /*  2070 */   116,  115,  114,  113, 1424, 1424, 1424,  117,  116,  115,
 /*  2080 */   114,  113, 1424, 1424, 1424, 1424,  811,   89,   88,   87,
 /*  2090 */  1424,   86,   85,   84,   83,  167,  166,  165, 1424,  164,
 /*  2100 */   163,  162,  161,   76,   82,   81, 1424,   80,   79,   78,
 /*  2110 */    77,   94,   93,   92,   91,   90, 1424, 1424, 1424,  172,
 /*  2120 */   171,  170,  169,  168, 1424, 1424, 1424,   99,   98,   97,
 /*  2130 */    96,   95,  488,  728,  545, 1019, 1019, 1019, 1424, 1019,
 /*  2140 */  1019, 1019, 1019,  167,  166,  165, 1424,  164,  163,  162,
 /*  2150 */   161,  112,  111,  110, 1424,  109,  108,  107,  106, 1019,
 /*  2160 */  1019, 1019, 1019, 1019,  776, 1424,  755,  172,  171,  170,
 /*  2170 */   169,  168, 1424, 1424, 1424,  117,  116,  115,  114,  113,
 /*  2180 */  1424, 1424, 1424, 1424, 1424,  771,  770,  772,  907,  917,
 /*  2190 */   918,  921,  913,  920,  919,  912,  500,  442, 1424, 1424,
 /*  2200 */  1424, 1424,  773,  774,  776, 1424,  755, 1424, 1424, 1424,
 /*  2210 */   232, 1424, 1424, 1424, 1424, 1424, 1424,  771,  770,  772,
 /*  2220 */  1424, 1424, 1424, 1424, 1424, 1424,  564,  880,  870,  921,
 /*  2230 */   913,  920,  919,  912,  773,  774,  137,  698,  388, 1424,
 /*  2240 */  1424, 1424,  232,   31,  230, 1424, 1424, 1424, 1424,  228,
 /*  2250 */   815,  804,  921,  913,  920,  919,  912,  771,  770,  772,
 /*  2260 */    43,   42,   41,   45,   44,  330,  551,   46, 1424,  254,
 /*  2270 */   252,  250,  249,  248,  773,  774,  230,  348,  801,  798,
 /*  2280 */  1424,  228,  232,  815,  804,  921,  913,  920,  919,  912,
 /*  2290 */   815,  804,  921,  913,  920,  919,  912, 1424,  803,   24,
 /*  2300 */    23,   22,   26,   25, 1424,  334,   27, 1424, 1424, 1424,
 /*  2310 */   795,  801,  798, 1424,  136, 1424,  230,  800,  801,  798,
 /*  2320 */  1424,  228,  815,  804,  921,  913,  920,  919,  912,  815,
 /*  2330 */   804,  921,  913,  920,  919,  912, 1424,  334,   43,   42,
 /*  2340 */    41,   45,   44, 1424,  334,   46, 1424, 1424, 1424,  799,
 /*  2350 */   801,  798, 1424, 1424, 1424, 1424,  579,  801,  798,  907,
 /*  2360 */   917,  918,  921,  913,  920,  919,  912,  506,  442, 1424,
 /*  2370 */  1424, 1424,  815,  804,  921,  913,  920,  919,  912,  815,
 /*  2380 */   804,  921,  913,  920,  919,  912, 1424,  334, 1424,  776,
 /*  2390 */  1424,  755, 1424, 1424,  334, 1424, 1424, 1424, 1424,  578,
 /*  2400 */   801,  798,  776,  135, 1424, 1424,  397,  801,  798, 1424,
 /*  2410 */  1424,  815,  804,  921,  913,  920,  919,  912,  815,  804,
 /*  2420 */   921,  913,  920,  919,  912, 1424,  334,   43,   42,   41,
 /*  2430 */    45,   44, 1424,  334,   46, 1424, 1424, 1424,  458,  801,
 /*  2440 */   798,  775,  771,  770,  772,  457,  801,  798,  691,  681,
 /*  2450 */   921,  913,  920,  919,  912,  771,  770,  772, 1424,  773,
 /*  2460 */   774,   43,   42,   41,   45,   44, 1424,  232,   46, 1424,
 /*  2470 */  1424, 1424,  773,  774,  231,  229,  227,  226,  225, 1424,
 /*  2480 */   232, 1424, 1424,  447,  907,  917,  918,  921,  913,  920,
 /*  2490 */   919,  912, 1424,  471,  880,  870,  921,  913,  920,  919,
 /*  2500 */   912,  230, 1424, 1424, 1424,  468,  228, 1424, 1424, 1424,
 /*  2510 */  1424, 1424, 1424, 1424,  230, 1424, 1424, 1424, 1424,  228,
 /*  2520 */  1424, 1424, 1424, 1424,  907,  917,  918,  921,  913,  920,
 /*  2530 */   919,  912, 1424,  392,  907,  917,  918,  921,  913,  920,
 /*  2540 */   919,  912, 1424,  472,  907,  917,  918,  921,  913,  920,
 /*  2550 */   919,  912, 1424,  897, 1424, 1424, 1424,  907,  917,  918,
 /*  2560 */   921,  913,  920,  919,  912, 1424,  890,  907,  917,  918,
 /*  2570 */   921,  913,  920,  919,  912, 1424,  896, 1424, 1424,  907,
 /*  2580 */   917,  918,  921,  913,  920,  919,  912, 1424,  891,  907,
 /*  2590 */   917,  918,  921,  913,  920,  919,  912, 1424,  391, 1424,
 /*  2600 */  1424,  907,  917,  918,  921,  913,  920,  919,  912, 1424,
 /*  2610 */   892,  907,  917,  918,  921,  913,  920,  919,  912, 1424,
 /*  2620 */   390, 1424, 1424,  907,  917,  918,  921,  913,  920,  919,
 /*  2630 */   912, 1424,  389, 1424, 1424,  907,  917,  918,  921,  913,
 /*  2640 */   920,  919,  912, 1424,  470, 1424, 1424, 1424,  907,  917,
 /*  2650 */   918,  921,  913,  920,  919,  912, 1424,  469,  907,  917,
 /*  2660 */   918,  921,  913,  920,  919,  912, 1424,  884, 1424,  907,
 /*  2670 */   917,  918,  921,  913,  920,  919,  912, 1424,  883, 1424,
 /*  2680 */  1424, 1424,  907,  917,  918,  921,  913,  920,  919,  912,
 /*  2690 */  1424,  882,  907,  917,  918,  921,  913,  920,  919,  912,
 /*  2700 */  1424,  440,  907,  917,  918,  921,  913,  920,  919,  912,
 /*  2710 */  1424,  439,  907,  917,  918,  921,  913,  920,  919,  912,
 /*  2720 */  1424,  438, 1424, 1424, 1424,  907,  917,  918,  921,  913,
 /*  2730 */   920,  919,  912, 1424,  437,  907,  917,  918,  921,  913,
 /*  2740 */   920,  919,  912, 1424,  436, 1424, 1424,  907,  917,  918,
 /*  2750 */   921,  913,  920,  919,  912, 1424,  435,  907,  917,  918,
 /*  2760 */   921,  913,  920,  919,  912, 1424,  434, 1424, 1424,  907,
 /*  2770 */   917,  918,  921,  913,  920,  919,  912, 1424,  430,  907,
 /*  2780 */   917,  918,  921,  913,  920,  919,  912, 1424,  429, 1424,
 /*  2790 */  1424,  907,  917,  918,  921,  913,  920,  919,  912, 1424,
 /*  2800 */   856, 1424, 1424,  907,  917,  918,  921,  913,  920,  919,
 /*  2810 */   912, 1424,  386, 1424, 1424, 1424,  907,  917,  918,  921,
 /*  2820 */   913,  920,  919,  912, 1424,  385,  907,  917,  918,  921,
 /*  2830 */   913,  920,  919,  912, 1424,  384, 1424,  907,  917,  918,
 /*  2840 */   921,  913,  920,  919,  912, 1424,  466, 1424, 1424, 1424,
 /*  2850 */   907,  917,  918,  921,  913,  920,  919,  912, 1424,  465,
 /*  2860 */   907,  917,  918,  921,  913,  920,  919,  912, 1424,  851,
 /*  2870 */   907,  917,  918,  921,  913,  920,  919,  912, 1424,  850,
 /*  2880 */   907,  917,  918,  921,  913,  920,  919,  912, 1424,  849,
 /*  2890 */  1424, 1424, 1424,  907,  917,  918,  921,  913,  920,  919,
 /*  2900 */   912, 1424,  464,  907,  917,  918,  921,  913,  920,  919,
 /*  2910 */   912, 1424,  463, 1424, 1424,  907,  917,  918,  921,  913,
 /*  2920 */   920,  919,  912, 1424,  848,  907,  917,  918,  921,  913,
 /*  2930 */   920,  919,  912, 1424,  847, 1424, 1424,  907,  917,  918,
 /*  2940 */   921,  913,  920,  919,  912, 1424,  846,  907,  917,  918,
 /*  2950 */   921,  913,  920,  919,  912, 1424,  426, 1424, 1424,  907,
 /*  2960 */   917,  918,  921,  913,  920,  919,  912, 1424,  425, 1424,
 /*  2970 */  1424,  907,  917,  918,  921,  913,  920,  919,  912, 1424,
 /*  2980 */   424, 1424, 1424, 1424,  907,  917,  918,  921,  913,  920,
 /*  2990 */   919,  912, 1424,  423,  907,  917,  918,  921,  913,  920,
 /*  3000 */   919,  912, 1424,  422, 1424,  907,  917,  918,  921,  913,
 /*  3010 */   920,  919,  912, 1424,  421, 1424, 1424, 1424,  907,  917,
 /*  3020 */   918,  921,  913,  920,  919,  912, 1424,  420,  907,  917,
 /*  3030 */   918,  921,  913,  920,  919,  912, 1424,  419,  907,  917,
 /*  3040 */   918,  921,  913,  920,  919,  912, 1424,  418,  907,  917,
 /*  3050 */   918,  921,  913,  920,  919,  912, 1424,  417, 1424, 1424,
 /*  3060 */  1424,  907,  917,  918,  921,  913,  920,  919,  912, 1424,
 /*  3070 */   416,  907,  917,  918,  921,  913,  920,  919,  912, 1424,
 /*  3080 */   415, 1424, 1424,  907,  917,  918,  921,  913,  920,  919,
 /*  3090 */   912, 1424,  414,  907,  917,  918,  921,  913,  920,  919,
 /*  3100 */   912, 1424,  413, 1424, 1424,  907,  917,  918,  921,  913,
 /*  3110 */   920,  919,  912, 1424,  412,  907,  917,  918,  921,  913,
 /*  3120 */   920,  919,  912, 1424,  411, 1424, 1424,  907,  917,  918,
 /*  3130 */   921,  913,  920,  919,  912, 1424,  409, 1424, 1424,  907,
 /*  3140 */   917,  918,  921,  913,  920,  919,  912, 1424,  408, 1424,
 /*  3150 */  1424, 1424,  907,  917,  918,  921,  913,  920,  919,  912,
 /*  3160 */  1424,  407,  907,  917,  918,  921,  913,  920,  919,  912,
 /*  3170 */  1424,  406, 1424,  907,  917,  918,  921,  913,  920,  919,
 /*  3180 */   912, 1424,  405, 1424, 1424, 1424,  907,  917,  918,  921,
 /*  3190 */   913,  920,  919,  912, 1424,  241,  907,  917,  918,  921,
 /*  3200 */   913,  920,  919,  912, 1424,  240,  907,  917,  918,  921,
 /*  3210 */   913,  920,  919,  912, 1424,  395,  907,  917,  918,  921,
 /*  3220 */   913,  920,  919,  912, 1424,  357,  880,  870,  921,  913,
 /*  3230 */   920,  919,  912, 1424, 1424, 1424, 1424,  869, 1424,  880,
 /*  3240 */   870,  921,  913,  920,  919,  912, 1424, 1424, 1424, 1424,
 /*  3250 */   865, 1424,  880,  870,  921,  913,  920,  919,  912, 1424,
 /*  3260 */  1424, 1424, 1424,  868,  880,  870,  921,  913,  920,  919,
 /*  3270 */   912, 1424, 1424, 1424, 1424,  867,  880,  870,  921,  913,
 /*  3280 */   920,  919,  912, 1424, 1424, 1424, 1424,  866,  880,  870,
 /*  3290 */   921,  913,  920,  919,  912, 1424, 1424, 1424, 1424,  431,
 /*  3300 */   880,  870,  921,  913,  920,  919,  912, 1424, 1424, 1424,
 /*  3310 */  1424,  460,  880,  870,  921,  913,  920,  919,  912, 1424,
 /*  3320 */  1424, 1424, 1424,  459,  880,  870,  921,  913,  920,  919,
 /*  3330 */   912, 1424, 1424, 1424, 1424,  810,  880,  870,  921,  913,
 /*  3340 */   920,  919,  912, 1424, 1424, 1424, 1424,  809,  880,  870,
 /*  3350 */   921,  913,  920,  919,  912, 1424, 1424, 1424, 1424,  808,
 /*  3360 */   880,  870,  921,  913,  920,  919,  912, 1424, 1424, 1424,
 /*  3370 */  1424,  404,  880,  870,  921,  913,  920,  919,  912, 1424,
 /*  3380 */  1424, 1424, 1424,  403,  880,  870,  921,  913,  920,  919,
 /*  3390 */   912, 1424, 1424, 1424, 1424,  402,  880,  870,  921,  913,
 /*  3400 */   920,  919,  912, 1424, 1424, 1424, 1424,  401,  880,  870,
 /*  3410 */   921,  913,  920,  919,  912, 1424, 1424, 1424, 1424,  400,
 /*  3420 */  1424,  880,  870,  921,  913,  920,  919,  912, 1424, 1424,
 /*  3430 */  1424, 1424,  399,  880,  870,  921,  913,  920,  919,  912,
 /*  3440 */  1424, 1424, 1424, 1424,  398,  880,  870,  921,  913,  920,
 /*  3450 */   919,  912, 1424, 1424, 1424, 1424,  802,  691,  681,  921,
 /*  3460 */   913,  920,  919,  912, 1424, 1424, 1424, 1424,  691,  681,
 /*  3470 */   921,  913,  920,  919,  912,  691,  681,  921,  913,  920,
 /*  3480 */   919,  912,  691,  681,  921,  913,  920,  919,  912, 1424,
 /*  3490 */  1424, 1424,  347,  691,  681,  921,  913,  920,  919,  912,
 /*  3500 */  1424, 1424, 1424,  448, 1424, 1424, 1424, 1424, 1424, 1424,
 /*  3510 */   680, 1424, 1424, 1424,  706, 1424, 1424,  449,  691,  681,
 /*  3520 */   921,  913,  920,  919,  912, 1424, 1424, 1424,  679,  691,
 /*  3530 */   681,  921,  913,  920,  919,  912, 1424, 1424, 1424, 1424,
 /*  3540 */   691,  681,  921,  913,  920,  919,  912,  254,  252,  250,
 /*  3550 */   249,  248,  697,  678,  691,  681,  921,  913,  920,  919,
 /*  3560 */   912, 1424, 1424, 1424,  677,  691,  681,  921,  913,  920,
 /*  3570 */   919,  912, 1424, 1424, 1424,  676,  691,  681,  921,  913,
 /*  3580 */   920,  919,  912, 1424,  254,  252,  250,  249,  248,  446,
 /*  3590 */   691,  681,  921,  913,  920,  919,  912, 1424, 1424, 1424,
 /*  3600 */   675,  691,  681,  921,  913,  920,  919,  912, 1424, 1424,
 /*  3610 */  1424,  674, 1424,  691,  681,  921,  913,  920,  919,  912,
 /*  3620 */  1424, 1424, 1424, 1424,  619,  673,  691,  681,  921,  913,
 /*  3630 */   920,  919,  912, 1424, 1424, 1424,  371,  691,  681,  921,
 /*  3640 */   913,  920,  919,  912, 1424, 1424,  610, 1424,  370,  691,
 /*  3650 */   681,  921,  913,  920,  919,  912,  254,  252,  250,  249,
 /*  3660 */   248,  369,  691,  681,  921,  913,  920,  919,  912, 1424,
 /*  3670 */  1424, 1424,  368, 1424, 1424, 1424, 1424, 1424,  254,  252,
 /*  3680 */   250,  249,  248, 1424,  367, 1424,  691,  681,  921,  913,
 /*  3690 */   920,  919,  912, 1424, 1424, 1424, 1424,  366,  691,  681,
 /*  3700 */   921,  913,  920,  919,  912, 1424, 1424, 1424, 1424,  691,
 /*  3710 */   681,  921,  913,  920,  919,  912, 1424, 1424, 1424, 1424,
 /*  3720 */  1424,  365,  691,  681,  921,  913,  920,  919,  912, 1424,
 /*  3730 */  1424, 1424, 1424,  668,  691,  681,  921,  913,  920,  919,
 /*  3740 */   912, 1424, 1424, 1424,  364,  691,  681,  921,  913,  920,
 /*  3750 */   919,  912, 1424, 1424, 1424, 1424, 1424,  363, 1424, 1424,
 /*  3760 */  1424, 1424, 1424, 1424, 1424, 1424, 1424, 1424, 1424,  362,
 /*  3770 */  1424, 1424, 1424, 1424, 1424, 1424, 1424, 1424, 1424, 1424,
 /*  3780 */   361,
};
static const YYCODETYPE yy_lookahead[] = {
 /*     0 */   147,  107,  108,  150,  151,  152,  153,  154,  155,  156,
 /*    10 */   157,  158,  159,  160,  161,  162,  163,  164,  165,  166,
 /*    20 */    80,  168,  169,  170,  171,  172,  173,  174,  113,  114,
 /*    30 */   115,  116,  117,   80,  181,  182,  168,  169,  170,  171,
 /*    40 */   172,  173,  174,  190,  191,  115,  116,  117,   80,  181,
 /*    50 */   182,  184,   75,  186,  114,    0,  188,  189,  190,  191,
 /*    60 */   192,  193,  184,  110,  186,  212,  213,  214,   79,  201,
 /*    70 */   202,  168,  169,  170,  171,  172,  173,  174,  110,  102,
 /*    80 */   103,  104,  105,  106,  181,  182,  109,  220,  221,  222,
 /*    90 */   223,  188,  189,  190,  191,  192,  193,  219,  220,  221,
 /*   100 */   222,  223,   79,  250,  251,  252,  253,  254,  255,  256,
 /*   110 */   257,  258,  259,  260,  261,  262,  263,  264,  265,  266,
 /*   120 */   267,  268,    1,    2,    3,   80,   79,    6,    7,    8,
 /*   130 */     9,   10,   11,   12,   13,   14,   15,  167,  168,  169,
 /*   140 */   170,  171,  172,  173,  174,  175,  176,  102,  103,  104,
 /*   150 */   105,  106,   31,   32,  109,   98,   99,   36,   80,   38,
 /*   160 */    39,   79,   41,  106,   43,   29,   45,   79,   47,   80,
 /*   170 */    79,   50,  184,  177,  186,   54,   55,   56,   57,   58,
 /*   180 */    59,   60,   46,   62,   48,  169,   65,  109,    1,  184,
 /*   190 */     3,  186,   71,   72,  198,  104,  180,   76,   77,  110,
 /*   200 */    79,  115,  116,  117,   83,   69,   70,  191,   87,  177,
 /*   210 */   194,   79,   25,   26,   27,   28,   80,   81,  230,  231,
 /*   220 */   232,   34,    1,   87,    3,  220,  221,  222,  223,   42,
 /*   230 */   198,   44,  227,  228,  113,  239,  240,   81,   51,  118,
 /*   240 */    79,   54,   55,   56,   46,  109,   79,  126,   98,   99,
 /*   250 */    63,   64,   65,   66,   67,   68,  106,  101,   71,   72,
 /*   260 */   139,  140,  141,  142,  143,  144,   79,  146,    1,    2,
 /*   270 */     3,  239,  240,    6,    7,    3,  168,  169,  170,  171,
 /*   280 */   172,  173,  174,  105,  106,   87,   47,  109,  168,  169,
 /*   290 */   170,  171,  172,  173,  174,  103,  104,  105,  106,  191,
 /*   300 */   113,  109,  105,  106,  115,  118,  109,  109,  119,  201,
 /*   310 */   202,  191,  204,   80,   47,  207,  208,  209,  210,  211,
 /*   320 */    80,   54,   55,   56,  204,   80,   89,  207,  208,  209,
 /*   330 */   210,  211,   83,   37,   80,    1,   40,    3,   71,   72,
 /*   340 */    81,   74,   88,  110,   77,   49,   79,  107,  108,   53,
 /*   350 */    83,   79,  168,  169,  170,  171,  172,  173,  174,  114,
 /*   360 */   101,  241,  242,  243,   81,  181,  182,  113,  114,  115,
 /*   370 */   116,  117,  188,  189,  190,  191,  192,  193,  139,  112,
 /*   380 */   113,    1,    2,    3,  101,  118,    6,    7,  139,  140,
 /*   390 */   168,  169,  170,  171,  172,  173,  174,  102,  103,  104,
 /*   400 */   105,  106,   81,  185,  109,  187,  139,  140,  141,  142,
 /*   410 */   143,  144,   17,  191,   19,   20,   21,   22,   23,   24,
 /*   420 */    78,    1,  101,  201,  202,    1,  204,   47,   97,  207,
 /*   430 */   208,  209,  210,  211,   54,   55,   56,  168,  169,  170,
 /*   440 */   171,  172,  173,  174,  113,  114,  115,  116,  117,   54,
 /*   450 */    55,   71,   72,  109,  115,  116,  117,   77,   84,   79,
 /*   460 */   191,    4,    5,   83,  102,  103,  104,  105,  106,   77,
 /*   470 */    79,  109,   80,  204,   80,  141,  207,  208,  209,  210,
 /*   480 */   211,   89,   90,   91,  110,   93,   94,   95,   96,   88,
 /*   490 */   115,  116,  117,  113,   78,    1,    2,    3,  118,   79,
 /*   500 */     6,    7,   79,   79,  110,  113,  114,  115,  116,  117,
 /*   510 */    81,  242,  243,  177,  113,  114,  115,  116,  117,  139,
 /*   520 */   140,  141,  142,  143,  144,  169,    1,    2,    3,   80,
 /*   530 */   101,    6,    7,  113,  198,   79,   78,  113,  118,  110,
 /*   540 */   145,   47,  118,  115,  116,  117,   52,  191,   54,   55,
 /*   550 */    56,  168,  169,  170,  171,  172,  173,  174,   78,  110,
 /*   560 */   102,  103,  104,  105,  106,   71,   72,  109,   74,  213,
 /*   570 */    78,   77,   47,   79,  191,   79,  240,   83,   81,   54,
 /*   580 */    55,   56,  102,  103,  104,  105,  106,  204,   83,  109,
 /*   590 */   207,  208,  209,  210,  211,   81,   71,   72,  101,  113,
 /*   600 */   114,  115,  116,  117,   79,   80,  112,  113,    1,    2,
 /*   610 */     3,  172,  118,    6,    7,  101,  177,  167,  168,  169,
 /*   620 */   170,  171,  172,  173,  174,  175,  176,   78,  113,  114,
 /*   630 */   115,  116,  117,  139,  140,  141,   89,  198,  113,   97,
 /*   640 */   201,  202,  169,  118,  139,    1,    2,    3,  105,  106,
 /*   650 */     6,    7,  109,  180,   47,  113,  114,  115,  116,  117,
 /*   660 */    89,   54,   55,   56,  139,  140,  141,  142,  143,  144,
 /*   670 */   168,  169,  170,  171,  172,  173,  174,   80,   71,   72,
 /*   680 */     3,   74,   46,  184,   77,  186,   79,  236,  237,  238,
 /*   690 */    83,   47,  172,  191,  224,  225,  226,  177,   54,   55,
 /*   700 */    56,  113,  114,  115,  116,  117,  204,  110,  109,  207,
 /*   710 */   208,  209,  210,  211,   81,   71,   72,   35,  198,  112,
 /*   720 */   113,  201,  202,   79,   47,  118,  106,    1,    2,    3,
 /*   730 */   110,  232,    6,    7,  101,  168,  169,  170,  171,  172,
 /*   740 */   173,  174,  177,  110,   81,  109,  139,  140,  141,  168,
 /*   750 */   169,  170,  171,  172,  173,  174,   84,  113,  191,  178,
 /*   760 */   179,   89,  118,  198,    1,    2,    3,   80,  106,    6,
 /*   770 */     7,  204,  110,   47,  207,  208,  209,  210,  211,   81,
 /*   780 */    54,   55,   56,  139,  140,  141,  142,  143,  144,  167,
 /*   790 */   168,  169,  170,  171,  172,  173,  174,  175,  176,  101,
 /*   800 */   113,  114,  115,  116,  117,   79,   81,    1,    2,    3,
 /*   810 */    47,   77,    6,    7,   80,  169,  139,   54,   55,   56,
 /*   820 */    84,   80,   88,   89,   90,   91,   81,   93,   94,   95,
 /*   830 */    96,  233,  234,  235,   71,   72,   81,  191,   84,  113,
 /*   840 */    81,   80,   79,   89,  118,   35,  110,  113,  114,  115,
 /*   850 */   116,  117,   29,   47,  113,  114,  115,  116,  117,  213,
 /*   860 */    54,   55,   56,   81,   80,  139,  140,  141,  142,  143,
 /*   870 */   144,  110,  215,  216,  177,  112,  113,   71,   72,   84,
 /*   880 */    84,  118,  104,  225,  226,   79,   82,    1,    2,    3,
 /*   890 */    78,   82,    6,    7,  114,  198,   73,  113,  114,  115,
 /*   900 */   116,  117,  139,  140,  141,  110,  110,  168,  169,  170,
 /*   910 */   171,  172,  173,  174,  102,  103,  104,  105,  106,  113,
 /*   920 */    79,  109,  183,  177,  118,  102,  103,  104,  105,  106,
 /*   930 */    80,   74,  109,   47,  195,  196,  197,  240,   80,   75,
 /*   940 */    54,   55,   56,   80,  198,  139,  140,  141,   80,  168,
 /*   950 */   169,  170,  171,  172,  173,  174,   79,   71,   72,  184,
 /*   960 */   110,  186,  181,  182,   46,   79,  234,  235,  110,  188,
 /*   970 */   189,  190,  191,  192,  193,   80,  113,  114,  115,  116,
 /*   980 */   117,   75,  201,  202,   80,  199,  200,  168,  169,  170,
 /*   990 */   171,  172,  173,  174,  219,  220,  221,  222,  223,  113,
 /*  1000 */   181,  182,  217,  218,  118,   98,   99,  188,  189,  190,
 /*  1010 */   191,  192,  193,  184,  110,  186,  168,  169,  170,  171,
 /*  1020 */   172,  173,  174,  148,  149,  139,  140,  141,   78,  181,
 /*  1030 */   182,  113,  114,  115,  116,  117,  188,  189,  190,  191,
 /*  1040 */   192,  193,  237,  238,  168,  169,  170,  171,  172,  173,
 /*  1050 */   174,   74,  102,  103,  104,  105,  106,  181,  182,  109,
 /*  1060 */    61,  237,  238,    3,  188,  189,  190,  191,  192,  193,
 /*  1070 */    79,  168,  169,  170,  171,  172,  173,  174,  113,  114,
 /*  1080 */   115,  116,  117,   46,  181,  182,  237,  238,   80,  237,
 /*  1090 */   238,  188,  189,  190,  191,  192,  193,   46,  199,  200,
 /*  1100 */    79,   74,  168,  169,  170,  171,  172,  173,  174,   75,
 /*  1110 */   102,  103,  104,  105,  106,  181,  182,  109,   80,  184,
 /*  1120 */     3,  186,  188,  189,  190,  191,  192,  193,  184,   79,
 /*  1130 */   186,  168,  169,  170,  171,  172,  173,  174,   79,  102,
 /*  1140 */   103,  104,  105,  106,  181,  182,  109,   79,  184,  110,
 /*  1150 */   186,  188,  189,  190,  191,  192,  193,  168,  169,  170,
 /*  1160 */   171,  172,  173,  174,  113,  114,  115,  116,  117,    3,
 /*  1170 */   181,  182,   30,  229,  230,  231,  232,  188,  189,  190,
 /*  1180 */   191,  192,  193,    3,  109,  168,  169,  170,  171,  172,
 /*  1190 */   173,  174,   81,  184,  184,  186,  186,   81,  181,  182,
 /*  1200 */    74,   81,   84,   84,   81,  188,  189,  190,  191,  192,
 /*  1210 */   193,   75,   47,  168,  169,  170,  171,  172,  173,  174,
 /*  1220 */   184,   75,  186,   89,   89,   83,  181,  182,  219,  220,
 /*  1230 */   221,  222,  223,  188,  189,  190,  191,  192,  193,    1,
 /*  1240 */   168,  169,  170,  171,  172,  173,  174,   47,  102,  103,
 /*  1250 */   104,  105,  106,  181,  182,  109,  220,  221,  222,  223,
 /*  1260 */   188,  189,  190,  191,  192,  193,  113,  114,  115,  116,
 /*  1270 */   117,  168,  169,  170,  171,  172,  173,  174,   81,   89,
 /*  1280 */   184,  139,  186,    1,  181,  182,   80,  177,   81,   81,
 /*  1290 */    81,  188,  189,  190,  191,  192,  193,   47,   81,   30,
 /*  1300 */   168,  169,  170,  171,  172,  173,  174,   81,  102,  103,
 /*  1310 */   104,  105,  106,  181,  182,  109,  220,  221,  222,  223,
 /*  1320 */   188,  189,  190,  191,  192,  193,  168,  169,  170,  171,
 /*  1330 */   172,  173,  174,   83,   81,   81,   80,  139,   81,  181,
 /*  1340 */   182,   81,   81,   81,   81,   81,  188,  189,  190,  191,
 /*  1350 */   192,  193,   83,   73,  168,  169,  170,  171,  172,  173,
 /*  1360 */   174,  172,  184,  113,  186,  140,  172,  181,  182,  113,
 /*  1370 */   114,  115,  116,  117,  188,  189,  190,  191,  192,  193,
 /*  1380 */   247,   48,  168,  169,  170,  171,  172,  173,  174,  139,
 /*  1390 */   172,  246,   29,   78,   69,  181,  182,  219,  220,  221,
 /*  1400 */   222,  223,  188,  189,  190,  191,  192,  193,  139,  168,
 /*  1410 */   169,  170,  171,  172,  173,  174,  248,  102,  103,  104,
 /*  1420 */   105,  106,  181,  182,  109,  249,   70,  248,  216,  188,
 /*  1430 */   189,  190,  191,  192,  193,    3,  249,  249,  223,  248,
 /*  1440 */   168,  169,  170,  171,  172,  173,  174,  248,    3,  247,
 /*  1450 */   249,   80,  248,  181,  182,   46,  186,  246,  245,  249,
 /*  1460 */   188,  189,  190,  191,  192,  193,  246,  248,  247,  168,
 /*  1470 */   169,  170,  171,  172,  173,  174,  249,   80,    3,  248,
 /*  1480 */   247,  249,  181,  182,  113,  114,  115,  116,  117,  188,
 /*  1490 */   189,  190,  191,  192,  193,  168,  169,  170,  171,  172,
 /*  1500 */   173,  174,  200,  248,  245,   80,  169,  249,  181,  182,
 /*  1510 */   113,  114,  115,  116,  117,  188,  189,  190,  191,  192,
 /*  1520 */   193,  248,   47,  168,  169,  170,  171,  172,  173,  174,
 /*  1530 */   249,  184,  248,  186,  249,  248,  181,  182,  113,  114,
 /*  1540 */   115,  116,  117,  188,  189,  190,  191,  192,  193,  249,
 /*  1550 */   246,  168,  169,  170,  171,  172,  173,  174,   83,  248,
 /*  1560 */   247,  249,  246,  249,  181,  182,  248,  220,  221,  222,
 /*  1570 */   223,  188,  189,  190,  191,  192,  193,  245,  168,  169,
 /*  1580 */   170,  171,  172,  173,  174,  247,  246,  248,  245,  169,
 /*  1590 */   249,  181,  182,   77,  248,  169,   80,  249,  188,  189,
 /*  1600 */   190,  191,  192,  193,   77,   89,   90,   91,  249,   93,
 /*  1610 */    94,   95,   96,  245,  139,   88,   89,   90,   91,  218,
 /*  1620 */    93,   94,   95,   96,  169,  245,  245,  169,  169,  113,
 /*  1630 */   114,  115,  116,  117,  169,  169,  245,  187,  171,  187,
 /*  1640 */   113,  114,  115,  116,  117,  245,    3,  187,  187,  187,
 /*  1650 */   187,  168,  169,  170,  171,  172,  173,  174,  187,  168,
 /*  1660 */   169,  170,  171,  172,  173,  174,  168,  169,  170,  171,
 /*  1670 */   172,  173,  174,  187,  191,  103,  104,  105,  106,  181,
 /*  1680 */   182,  109,  191,  103,  104,  105,  106,  204,  187,  109,
 /*  1690 */   207,  208,  209,  210,  211,  204,  187,  187,  207,  208,
 /*  1700 */   209,  210,  211,  249,  187,  168,  169,  170,  171,  172,
 /*  1710 */   173,  174,  187,  168,  169,  170,  171,  172,  173,  174,
 /*  1720 */   168,  169,  170,  171,  172,  173,  174,  187,  191,  187,
 /*  1730 */   245,  249,  245,  181,  182,  246,  191,  186,  246,  246,
 /*  1740 */   246,  204,  186,  186,  207,  208,  209,  210,  211,  204,
 /*  1750 */   186,  186,  207,  208,  209,  210,  211,  186,    3,  186,
 /*  1760 */   168,  169,  170,  171,  172,  173,  174,  186,  168,  169,
 /*  1770 */   170,  171,  172,  173,  174,  168,  169,  170,  171,  172,
 /*  1780 */   173,  174,  269,  191,  269,  269,  269,  269,  181,  182,
 /*  1790 */   269,  191,  269,  269,  269,  269,  204,  269,  269,  207,
 /*  1800 */   208,  209,  210,  211,  204,   70,   29,  207,  208,  209,
 /*  1810 */   210,  211,  168,  169,  170,  171,  172,  173,  174,  269,
 /*  1820 */   168,  169,  170,  171,  172,  173,  174,  167,  168,  169,
 /*  1830 */   170,  171,  172,  173,  174,  191,  176,  102,  103,  104,
 /*  1840 */   105,  106,  269,  191,  109,  269,  269,  269,  204,  269,
 /*  1850 */   269,  207,  208,  209,  210,  211,  204,  269,  269,  207,
 /*  1860 */   208,  209,  210,  211,  168,  169,  170,  171,  172,  173,
 /*  1870 */   174,  168,  169,  170,  171,  172,  173,  174,   81,  102,
 /*  1880 */   103,  104,  105,  106,  181,  182,  109,  191,  269,  269,
 /*  1890 */   269,  269,   80,  190,  191,  269,  269,  269,  269,  269,
 /*  1900 */   204,  269,  269,  207,  208,  209,  210,  211,  269,  269,
 /*  1910 */   113,  114,  115,  116,  117,  212,  213,  214,  168,  169,
 /*  1920 */   170,  171,  172,  173,  174,  113,  114,  115,  116,  117,
 /*  1930 */   269,  181,  182,  168,  169,  170,  171,  172,  173,  174,
 /*  1940 */   190,  191,  269,  269,  269,  269,  181,  182,  168,  169,
 /*  1950 */   170,  171,  172,  173,  174,  190,  191,  269,  269,  179,
 /*  1960 */   269,  269,  212,  213,  214,  269,  269,  269,  168,  169,
 /*  1970 */   170,  171,  172,  173,  174,  269,  269,  212,  213,  214,
 /*  1980 */   269,  181,  182,  168,  169,  170,  171,  172,  173,  174,
 /*  1990 */   190,  191,  269,  269,  269,  269,  181,  182,  168,  169,
 /*  2000 */   170,  171,  172,  173,  174,  190,  191,  269,  269,  179,
 /*  2010 */   269,  269,  212,  213,  214,  269,  269,  168,  169,  170,
 /*  2020 */   171,  172,  173,  174,  269,  269,  269,  212,  213,  214,
 /*  2030 */   181,  182,   81,   77,  269,  269,  269,  269,  269,  190,
 /*  2040 */   191,   77,  269,  269,  269,   89,   90,   91,  269,   93,
 /*  2050 */    94,   95,   96,   89,   90,   91,  269,   93,   94,   95,
 /*  2060 */    96,  212,  213,  214,  113,  114,  115,  116,  117,  113,
 /*  2070 */   114,  115,  116,  117,  269,  269,  269,  113,  114,  115,
 /*  2080 */   116,  117,  269,  269,  269,  269,   80,   89,   90,   91,
 /*  2090 */   269,   93,   94,   95,   96,   89,   90,   91,  269,   93,
 /*  2100 */    94,   95,   96,   89,   90,   91,  269,   93,   94,   95,
 /*  2110 */    96,  113,  114,  115,  116,  117,  269,  269,  269,  113,
 /*  2120 */   114,  115,  116,  117,  269,  269,  269,  113,  114,  115,
 /*  2130 */   116,  117,    1,    2,    3,   89,   90,   91,  269,   93,
 /*  2140 */    94,   95,   96,   89,   90,   91,  269,   93,   94,   95,
 /*  2150 */    96,   89,   90,   91,  269,   93,   94,   95,   96,  113,
 /*  2160 */   114,  115,  116,  117,    1,  269,    3,  113,  114,  115,
 /*  2170 */   116,  117,  269,  269,  269,  113,  114,  115,  116,  117,
 /*  2180 */   269,  269,  269,  269,  269,   54,   55,   56,  167,  168,
 /*  2190 */   169,  170,  171,  172,  173,  174,  175,  176,  269,  269,
 /*  2200 */   269,  269,   71,   72,    1,  269,    3,  269,  269,  269,
 /*  2210 */    79,  269,  269,  269,  269,  269,  269,   54,   55,   56,
 /*  2220 */   269,  269,  269,  269,  269,  269,   63,  168,  169,  170,
 /*  2230 */   171,  172,  173,  174,   71,   72,   78,   81,  179,  269,
 /*  2240 */   269,  269,   79,   46,  113,  269,  269,  269,  269,  118,
 /*  2250 */   168,  169,  170,  171,  172,  173,  174,   54,   55,   56,
 /*  2260 */   102,  103,  104,  105,  106,  183,   63,  109,  269,  113,
 /*  2270 */   114,  115,  116,  117,   71,   72,  113,  195,  196,  197,
 /*  2280 */   269,  118,   79,  168,  169,  170,  171,  172,  173,  174,
 /*  2290 */   168,  169,  170,  171,  172,  173,  174,  269,  183,  102,
 /*  2300 */   103,  104,  105,  106,  269,  183,  109,  269,  269,  269,
 /*  2310 */   195,  196,  197,  269,   78,  269,  113,  195,  196,  197,
 /*  2320 */   269,  118,  168,  169,  170,  171,  172,  173,  174,  168,
 /*  2330 */   169,  170,  171,  172,  173,  174,  269,  183,  102,  103,
 /*  2340 */   104,  105,  106,  269,  183,  109,  269,  269,  269,  195,
 /*  2350 */   196,  197,  269,  269,  269,  269,  195,  196,  197,  167,
 /*  2360 */   168,  169,  170,  171,  172,  173,  174,  175,  176,  269,
 /*  2370 */   269,  269,  168,  169,  170,  171,  172,  173,  174,  168,
 /*  2380 */   169,  170,  171,  172,  173,  174,  269,  183,  269,    1,
 /*  2390 */   269,    3,  269,  269,  183,  269,  269,  269,  269,  195,
 /*  2400 */   196,  197,    1,   78,  269,  269,  195,  196,  197,  269,
 /*  2410 */   269,  168,  169,  170,  171,  172,  173,  174,  168,  169,
 /*  2420 */   170,  171,  172,  173,  174,  269,  183,  102,  103,  104,
 /*  2430 */   105,  106,  269,  183,  109,  269,  269,  269,  195,  196,
 /*  2440 */   197,   80,   54,   55,   56,  195,  196,  197,  168,  169,
 /*  2450 */   170,  171,  172,  173,  174,   54,   55,   56,  269,   71,
 /*  2460 */    72,  102,  103,  104,  105,  106,  269,   79,  109,  269,
 /*  2470 */   269,  269,   71,   72,  113,  114,  115,  116,  117,  269,
 /*  2480 */    79,  269,  269,  203,  167,  168,  169,  170,  171,  172,
 /*  2490 */   173,  174,  269,  176,  168,  169,  170,  171,  172,  173,
 /*  2500 */   174,  113,  269,  269,  269,  179,  118,  269,  269,  269,
 /*  2510 */   269,  269,  269,  269,  113,  269,  269,  269,  269,  118,
 /*  2520 */   269,  269,  269,  269,  167,  168,  169,  170,  171,  172,
 /*  2530 */   173,  174,  269,  176,  167,  168,  169,  170,  171,  172,
 /*  2540 */   173,  174,  269,  176,  167,  168,  169,  170,  171,  172,
 /*  2550 */   173,  174,  269,  176,  269,  269,  269,  167,  168,  169,
 /*  2560 */   170,  171,  172,  173,  174,  269,  176,  167,  168,  169,
 /*  2570 */   170,  171,  172,  173,  174,  269,  176,  269,  269,  167,
 /*  2580 */   168,  169,  170,  171,  172,  173,  174,  269,  176,  167,
 /*  2590 */   168,  169,  170,  171,  172,  173,  174,  269,  176,  269,
 /*  2600 */   269,  167,  168,  169,  170,  171,  172,  173,  174,  269,
 /*  2610 */   176,  167,  168,  169,  170,  171,  172,  173,  174,  269,
 /*  2620 */   176,  269,  269,  167,  168,  169,  170,  171,  172,  173,
 /*  2630 */   174,  269,  176,  269,  269,  167,  168,  169,  170,  171,
 /*  2640 */   172,  173,  174,  269,  176,  269,  269,  269,  167,  168,
 /*  2650 */   169,  170,  171,  172,  173,  174,  269,  176,  167,  168,
 /*  2660 */   169,  170,  171,  172,  173,  174,  269,  176,  269,  167,
 /*  2670 */   168,  169,  170,  171,  172,  173,  174,  269,  176,  269,
 /*  2680 */   269,  269,  167,  168,  169,  170,  171,  172,  173,  174,
 /*  2690 */   269,  176,  167,  168,  169,  170,  171,  172,  173,  174,
 /*  2700 */   269,  176,  167,  168,  169,  170,  171,  172,  173,  174,
 /*  2710 */   269,  176,  167,  168,  169,  170,  171,  172,  173,  174,
 /*  2720 */   269,  176,  269,  269,  269,  167,  168,  169,  170,  171,
 /*  2730 */   172,  173,  174,  269,  176,  167,  168,  169,  170,  171,
 /*  2740 */   172,  173,  174,  269,  176,  269,  269,  167,  168,  169,
 /*  2750 */   170,  171,  172,  173,  174,  269,  176,  167,  168,  169,
 /*  2760 */   170,  171,  172,  173,  174,  269,  176,  269,  269,  167,
 /*  2770 */   168,  169,  170,  171,  172,  173,  174,  269,  176,  167,
 /*  2780 */   168,  169,  170,  171,  172,  173,  174,  269,  176,  269,
 /*  2790 */   269,  167,  168,  169,  170,  171,  172,  173,  174,  269,
 /*  2800 */   176,  269,  269,  167,  168,  169,  170,  171,  172,  173,
 /*  2810 */   174,  269,  176,  269,  269,  269,  167,  168,  169,  170,
 /*  2820 */   171,  172,  173,  174,  269,  176,  167,  168,  169,  170,
 /*  2830 */   171,  172,  173,  174,  269,  176,  269,  167,  168,  169,
 /*  2840 */   170,  171,  172,  173,  174,  269,  176,  269,  269,  269,
 /*  2850 */   167,  168,  169,  170,  171,  172,  173,  174,  269,  176,
 /*  2860 */   167,  168,  169,  170,  171,  172,  173,  174,  269,  176,
 /*  2870 */   167,  168,  169,  170,  171,  172,  173,  174,  269,  176,
 /*  2880 */   167,  168,  169,  170,  171,  172,  173,  174,  269,  176,
 /*  2890 */   269,  269,  269,  167,  168,  169,  170,  171,  172,  173,
 /*  2900 */   174,  269,  176,  167,  168,  169,  170,  171,  172,  173,
 /*  2910 */   174,  269,  176,  269,  269,  167,  168,  169,  170,  171,
 /*  2920 */   172,  173,  174,  269,  176,  167,  168,  169,  170,  171,
 /*  2930 */   172,  173,  174,  269,  176,  269,  269,  167,  168,  169,
 /*  2940 */   170,  171,  172,  173,  174,  269,  176,  167,  168,  169,
 /*  2950 */   170,  171,  172,  173,  174,  269,  176,  269,  269,  167,
 /*  2960 */   168,  169,  170,  171,  172,  173,  174,  269,  176,  269,
 /*  2970 */   269,  167,  168,  169,  170,  171,  172,  173,  174,  269,
 /*  2980 */   176,  269,  269,  269,  167,  168,  169,  170,  171,  172,
 /*  2990 */   173,  174,  269,  176,  167,  168,  169,  170,  171,  172,
 /*  3000 */   173,  174,  269,  176,  269,  167,  168,  169,  170,  171,
 /*  3010 */   172,  173,  174,  269,  176,  269,  269,  269,  167,  168,
 /*  3020 */   169,  170,  171,  172,  173,  174,  269,  176,  167,  168,
 /*  3030 */   169,  170,  171,  172,  173,  174,  269,  176,  167,  168,
 /*  3040 */   169,  170,  171,  172,  173,  174,  269,  176,  167,  168,
 /*  3050 */   169,  170,  171,  172,  173,  174,  269,  176,  269,  269,
 /*  3060 */   269,  167,  168,  169,  170,  171,  172,  173,  174,  269,
 /*  3070 */   176,  167,  168,  169,  170,  171,  172,  173,  174,  269,
 /*  3080 */   176,  269,  269,  167,  168,  169,  170,  171,  172,  173,
 /*  3090 */   174,  269,  176,  167,  168,  169,  170,  171,  172,  173,
 /*  3100 */   174,  269,  176,  269,  269,  167,  168,  169,  170,  171,
 /*  3110 */   172,  173,  174,  269,  176,  167,  168,  169,  170,  171,
 /*  3120 */   172,  173,  174,  269,  176,  269,  269,  167,  168,  169,
 /*  3130 */   170,  171,  172,  173,  174,  269,  176,  269,  269,  167,
 /*  3140 */   168,  169,  170,  171,  172,  173,  174,  269,  176,  269,
 /*  3150 */   269,  269,  167,  168,  169,  170,  171,  172,  173,  174,
 /*  3160 */   269,  176,  167,  168,  169,  170,  171,  172,  173,  174,
 /*  3170 */   269,  176,  269,  167,  168,  169,  170,  171,  172,  173,
 /*  3180 */   174,  269,  176,  269,  269,  269,  167,  168,  169,  170,
 /*  3190 */   171,  172,  173,  174,  269,  176,  167,  168,  169,  170,
 /*  3200 */   171,  172,  173,  174,  269,  176,  167,  168,  169,  170,
 /*  3210 */   171,  172,  173,  174,  269,  176,  167,  168,  169,  170,
 /*  3220 */   171,  172,  173,  174,  269,  176,  168,  169,  170,  171,
 /*  3230 */   172,  173,  174,  269,  269,  269,  269,  179,  269,  168,
 /*  3240 */   169,  170,  171,  172,  173,  174,  269,  269,  269,  269,
 /*  3250 */   179,  269,  168,  169,  170,  171,  172,  173,  174,  269,
 /*  3260 */   269,  269,  269,  179,  168,  169,  170,  171,  172,  173,
 /*  3270 */   174,  269,  269,  269,  269,  179,  168,  169,  170,  171,
 /*  3280 */   172,  173,  174,  269,  269,  269,  269,  179,  168,  169,
 /*  3290 */   170,  171,  172,  173,  174,  269,  269,  269,  269,  179,
 /*  3300 */   168,  169,  170,  171,  172,  173,  174,  269,  269,  269,
 /*  3310 */   269,  179,  168,  169,  170,  171,  172,  173,  174,  269,
 /*  3320 */   269,  269,  269,  179,  168,  169,  170,  171,  172,  173,
 /*  3330 */   174,  269,  269,  269,  269,  179,  168,  169,  170,  171,
 /*  3340 */   172,  173,  174,  269,  269,  269,  269,  179,  168,  169,
 /*  3350 */   170,  171,  172,  173,  174,  269,  269,  269,  269,  179,
 /*  3360 */   168,  169,  170,  171,  172,  173,  174,  269,  269,  269,
 /*  3370 */   269,  179,  168,  169,  170,  171,  172,  173,  174,  269,
 /*  3380 */   269,  269,  269,  179,  168,  169,  170,  171,  172,  173,
 /*  3390 */   174,  269,  269,  269,  269,  179,  168,  169,  170,  171,
 /*  3400 */   172,  173,  174,  269,  269,  269,  269,  179,  168,  169,
 /*  3410 */   170,  171,  172,  173,  174,  269,  269,  269,  269,  179,
 /*  3420 */   269,  168,  169,  170,  171,  172,  173,  174,  269,  269,
 /*  3430 */   269,  269,  179,  168,  169,  170,  171,  172,  173,  174,
 /*  3440 */   269,  269,  269,  269,  179,  168,  169,  170,  171,  172,
 /*  3450 */   173,  174,  269,  269,  269,  269,  179,  168,  169,  170,
 /*  3460 */   171,  172,  173,  174,  269,  269,  269,  269,  168,  169,
 /*  3470 */   170,  171,  172,  173,  174,  168,  169,  170,  171,  172,
 /*  3480 */   173,  174,  168,  169,  170,  171,  172,  173,  174,  269,
 /*  3490 */   269,  269,  203,  168,  169,  170,  171,  172,  173,  174,
 /*  3500 */   269,  269,  269,  203,  269,  269,  269,  269,  269,  269,
 /*  3510 */   203,  269,  269,  269,   80,  269,  269,  203,  168,  169,
 /*  3520 */   170,  171,  172,  173,  174,  269,  269,  269,  203,  168,
 /*  3530 */   169,  170,  171,  172,  173,  174,  269,  269,  269,  269,
 /*  3540 */   168,  169,  170,  171,  172,  173,  174,  113,  114,  115,
 /*  3550 */   116,  117,   81,  203,  168,  169,  170,  171,  172,  173,
 /*  3560 */   174,  269,  269,  269,  203,  168,  169,  170,  171,  172,
 /*  3570 */   173,  174,  269,  269,  269,  203,  168,  169,  170,  171,
 /*  3580 */   172,  173,  174,  269,  113,  114,  115,  116,  117,  203,
 /*  3590 */   168,  169,  170,  171,  172,  173,  174,  269,  269,  269,
 /*  3600 */   203,  168,  169,  170,  171,  172,  173,  174,  269,  269,
 /*  3610 */   269,  203,  269,  168,  169,  170,  171,  172,  173,  174,
 /*  3620 */   269,  269,  269,  269,   81,  203,  168,  169,  170,  171,
 /*  3630 */   172,  173,  174,  269,  269,  269,  203,  168,  169,  170,
 /*  3640 */   171,  172,  173,  174,  269,  269,   81,  269,  203,  168,
 /*  3650 */   169,  170,  171,  172,  173,  174,  113,  114,  115,  116,
 /*  3660 */   117,  203,  168,  169,  170,  171,  172,  173,  174,  269,
 /*  3670 */   269,  269,  203,  269,  269,  269,  269,  269,  113,  114,
 /*  3680 */   115,  116,  117,  269,  203,  269,  168,  169,  170,  171,
 /*  3690 */   172,  173,  174,  269,  269,  269,  269,  203,  168,  169,
 /*  3700 */   170,  171,  172,  173,  174,  269,  269,  269,  269,  168,
 /*  3710 */   169,  170,  171,  172,  173,  174,  269,  269,  269,  269,
 /*  3720 */   269,  203,  168,  169,  170,  171,  172,  173,  174,  269,
 /*  3730 */   269,  269,  269,  203,  168,  169,  170,  171,  172,  173,
 /*  3740 */   174,  269,  269,  269,  203,  168,  169,  170,  171,  172,
 /*  3750 */   173,  174,  269,  269,  269,  269,  269,  203,  269,  269,
 /*  3760 */   269,  269,  269,  269,  269,  269,  269,  269,  269,  203,
 /*  3770 */   269,  269,  269,  269,  269,  269,  269,  269,  269,  269,
 /*  3780 */   203,
};
#define YY_SHIFT_USE_DFLT (-107)
#define YY_SHIFT_COUNT (601)
#define YY_SHIFT_MIN   (-106)
#define YY_SHIFT_MAX   (3565)
static const short yy_shift_ofst[] = {
 /*     0 */  -107,  121,  267,  267,  494,  494,  607,  607,  267,  267,
 /*    10 */   267,  267,  267,  267,  267,  267,  267,  267,  267,  267,
 /*    20 */   267,  267,  267,  267,  267,  267,  267,  267,  267,  267,
 /*    30 */   267,  267,  380,  380,  380,  380,  380,  380,  607,  607,
 /*    40 */   607,  607,  607,  607,  607,  607,  607,  607,  607,  607,
 /*    50 */   763,  763,  763,  763,  763,  763,  763,  763,  763,  763,
 /*    60 */   525,  644,  644,  644,  644,  644,  644,  644,  644,  644,
 /*    70 */   644,  644,  644,  644,  644,  644,  644,  644,  644,  644,
 /*    80 */   644,  644,  644,  644,  644,  644,  644,  644,  644,  644,
 /*    90 */   644,  644,  644,  644,  644,  644,  644,  644,  644,  644,
 /*   100 */   644,  644,  644,  644,  644,  644,  644,  644,  644,  644,
 /*   110 */   644,  644,  644,  644,  644,  644,  644,  644,  644,  644,
 /*   120 */   644,  644,  644,  644,  644,  644,  644,  644,  644,  644,
 /*   130 */   726,  726,  726,  806,  187,  886,  886,  886,  886,  886,
 /*   140 */   886,  886,  886,  886,  886,  886,  886,  886,  886,  886,
 /*   150 */   886,  886,  886,  886,  886,  886,  886,  886,  886,  886,
 /*   160 */   806,  806,  806,  806,  806,  806,  806,  806,  806,  806,
 /*   170 */   806,  806,  806,  806,  806,  806,  806,  806,  806,  806,
 /*   180 */   806,  806,  806, 2388, 2388, 2388, 2388, 2131, 2203, 2163,
 /*   190 */  2388, 2388, 2131,  249,  249, 1475, 1269, 1142, 2131, 1250,
 /*   200 */  1250,  505,  505,  272, 1755, 1643, 2401, 2401, 2401, 2401,
 /*   210 */   424,  677,  907,  272,  272,  272,  272,  457,  907,  505,
 /*   220 */   505, 1755, 1643, 1432, 2401, 2401, 2401, 2401, 2401, 2401,
 /*   230 */  2401, 2401, 2401,  823, 2197, 1777, 1777, 1777, 1735, 1735,
 /*   240 */  1051, 1051,  420,  420,  420,  420,  420,  420,  420,  420,
 /*   250 */   420,  420,  420,  420,  420,  420,  420,  150,  334,   57,
 /*   260 */   198,  239,  239,  239,  239,  636,  636,  239,  457,  636,
 /*   270 */   239,  239,  636,  239, 1356, 1356, 1325, 1356, 1325, 1363,
 /*   280 */  1333, 1409, 1356, 1325, 1363, 1333, 1409, 1356, 1325, 1363,
 /*   290 */  1333, 1409, 1356, 1325, 1356, 1325, 1356, 1325, 1356, 1325,
 /*   300 */  1356, 1325, 1363, 1333, 1356, 1325, 1363, 1333, 1445, 1432,
 /*   310 */  1356, 1325, 1356, 1325, 1356, 1325, 1356, 1325, 1356, 1325,
 /*   320 */  1363, 1333, 1225, 1225, 1225, 1198,  734, 1527, 1516,  392,
 /*   330 */  2006, 1964, 1956, 2062, 2054, 2046, 2014, 1998,  395,  136,
 /*   340 */  1037, 1206, 2325, 2236, 2158, 1315, 1146,  254, 1008,   45,
 /*   350 */   950,  812,  480,  458,  -23, 3565, 3543,  918, 2359, 2359,
 /*   360 */   542,  401,  401,  401,  401,  401,  401,  401,  401,  401,
 /*   370 */   401,  401,  295, 3471, 2156, 1951, 1797, 3434,  331, 2361,
 /*   380 */   362,  295,  295,  295, 1812, 1425, 1397, 1371, 1256,  863,
 /*   390 */   784,  741,  687, 1153, 1580,  -85,  965, 1572,  486,  486,
 /*   400 */   486,  486,  486,  486,  486,  -85,  -85,  -85,  -85,  -85,
 /*   410 */   192,  -85,  -85,  -85,  -85,  -85,  -85,  -85,  -85,  -85,
 /*   420 */   -85,  -85,  -85,  -85,  -85,  -85,  -85,  588,  515,  -85,
 /*   430 */   -85,  486,  486,  486,  -85,  -85,  -85,  -85,  -85,  -85,
 /*   440 */   -85,  -85,  -85,  296,  543,  543,  428,  428,  428,  428,
 /*   450 */   375,  375,  633,  429,  240,  339,  339,  197,  197,   86,
 /*   460 */    86,  178,  178,  -70,  -70,  -70,  -70,   86,   86,  -70,
 /*   470 */   -70,  -70,  -70,  221,  698,  514,  754,  672, -106, -106,
 /*   480 */  -106, -106,  497,  796,  321,  904,  795,  283,  736,  858,
 /*   490 */   850,  245,  761,  -60,  189,  374,  259,  597,   91,  156,
 /*   500 */   449,  662,   78,  620,  394,  233,   89,  -32,  -47, 1280,
 /*   510 */  1264, 1263, 1262, 1261, 1260, 1257, 1254, 1253, 1226, 1217,
 /*   520 */  1209, 1208, 1207, 1282, 1190, 1200, 1197, 1238, 1135, 1165,
 /*   530 */  1134, 1136, 1126, 1123, 1120, 1119, 1118, 1075, 1075, 1116,
 /*   540 */  1111, 1180, 1039, 1166,  780, 1068, 1059, 1050, 1117, 1038,
 /*   550 */  1034, 1027, 1021,  780,  780,  991, 1060,  999,  906,  977,
 /*   560 */   895,  877,  868,  864,  857,  841,  780,  809,  804,  778,
 /*   570 */   782,  759,  810,  755,  682,  745,  725,  663,  599,  599,
 /*   580 */   571,  547,  496,  344,  344,  549,  492,  456,  423,  391,
 /*   590 */   416,  342,  237,  167,  161,  132,   88,   82,   47,   23,
 /*   600 */   -11,   55,
};
#define YY_REDUCE_USE_DFLT (-148)
#define YY_REDUCE_COUNT (325)
#define YY_REDUCE_MIN   (-147)
#define YY_REDUCE_MAX   (3577)
static const short yy_reduce_ofst[] = {
 /*     0 */   875, -147,  781, -132,  120,  269,  222,  108, 1410, 1383,
 /*    10 */  1355, 1327, 1301, 1272, 1241, 1214, 1186, 1158, 1132, 1103,
 /*    20 */  1072, 1045, 1017,  989,  963,  934,  903,  876,  848,  819,
 /*    30 */   184,  -97, 1849, 1815, 1800, 1765, 1750, 1703, 1696, 1652,
 /*    40 */  1644, 1600, 1592, 1545, 1537, 1491, 1483,  567,  502,  383,
 /*    50 */  2250, 2243, 2211, 2204, 2161, 2154, 2122, 2115, 2082,  739,
 /*    60 */  2192, 2021,  622,  450,  -30, 3049, 3039, 3029, 3019, 3006,
 /*    70 */  2995, 2985, 2972, 2960, 2948, 2938, 2926, 2916, 2904, 2894,
 /*    80 */  2881, 2871, 2861, 2851, 2838, 2827, 2817, 2804, 2792, 2780,
 /*    90 */  2770, 2758, 2748, 2736, 2726, 2713, 2703, 2693, 2683, 2670,
 /*   100 */  2659, 2649, 2636, 2624, 2612, 2602, 2590, 2580, 2568, 2558,
 /*   110 */  2545, 2535, 2525, 2515, 2502, 2491, 2481, 2468, 2456, 2444,
 /*   120 */  2434, 2422, 2412, 2400, 2390, 2377, 2367, 2357, 2317, 1660,
 /*   130 */  1607, 1552, 1498,  581,    5, 3577, 3566, 3554, 3541, 3530,
 /*   140 */  3518, 3494, 3481, 3469, 3458, 3445, 3433, 3422, 3408, 3397,
 /*   150 */  3386, 3372, 3361, 3350, 3325, 3314, 3307, 3300, 3289, 2280,
 /*   160 */  3277, 3265, 3253, 3240, 3228, 3216, 3204, 3192, 3180, 3168,
 /*   170 */  3156, 3144, 3132, 3120, 3108, 3096, 3084, 3071, 3058, 2326,
 /*   180 */  2059, 1830, 1780, 1178, 1009,  775, -122,  944, 1347, 1096,
 /*   190 */  1036, -133,  -12,  520,  439,   16,   32,   -4,  499,  646,
 /*   200 */   356,  697,  336,  451,  598,  470, 1010,  964,  935,  829,
 /*   210 */   218,  473,  899,  852,  849,  824,  805,  785,  786,  746,
 /*   220 */   565,  732,  658,  657, 1581, 1573, 1571, 1565, 1564, 1557,
 /*   230 */  1556, 1551, 1270, 1494, 1487, 1493, 1492, 1489, 1482, 1454,
 /*   240 */  1485, 1400, 1542, 1540, 1525, 1517, 1510, 1509, 1501, 1486,
 /*   250 */  1471, 1463, 1462, 1461, 1460, 1452, 1450, 1302, 1467, 1302,
 /*   260 */  1391, 1466, 1465, 1459, 1458, 1381, 1380, 1455, 1401, 1368,
 /*   270 */  1426, 1420, 1343, 1337, 1359, 1348, 1346, 1341, 1339, 1340,
 /*   280 */  1338, 1332, 1314, 1318, 1316, 1313, 1259, 1312, 1311, 1304,
 /*   290 */  1233, 1213, 1300, 1287, 1285, 1284, 1281, 1273, 1258, 1255,
 /*   300 */  1232, 1231, 1220, 1221, 1227, 1219, 1211, 1202, 1215, 1212,
 /*   310 */  1210, 1204, 1201, 1199, 1188, 1191, 1187, 1179, 1176, 1168,
 /*   320 */  1145, 1133, 1218, 1194, 1189, 1110,
};
static const YYACTIONTYPE yy_default[] = {
 /*     0 */   941, 1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422,
 /*    10 */  1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422,
 /*    20 */  1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422,
 /*    30 */  1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422,
 /*    40 */  1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422,
 /*    50 */  1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422,
 /*    60 */  1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422,
 /*    70 */  1166, 1170, 1165, 1169, 1257, 1253, 1422, 1422, 1422, 1422,
 /*    80 */  1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422,
 /*    90 */  1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422,
 /*   100 */  1422, 1422, 1422, 1422, 1258, 1254, 1422, 1422, 1422, 1422,
 /*   110 */  1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422,
 /*   120 */  1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422,
 /*   130 */  1422, 1422, 1422, 1422, 1422, 1237, 1241, 1236, 1240, 1422,
 /*   140 */  1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422,
 /*   150 */  1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422,
 /*   160 */  1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422,
 /*   170 */  1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422,
 /*   180 */  1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422,
 /*   190 */  1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422,
 /*   200 */  1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422,
 /*   210 */  1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422,
 /*   220 */  1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422,
 /*   230 */  1422, 1422, 1422, 1366, 1364, 1366, 1366, 1366, 1372, 1372,
 /*   240 */  1364, 1364, 1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422,
 /*   250 */  1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422,
 /*   260 */  1364, 1422, 1422, 1422, 1422, 1364, 1364, 1422, 1422, 1364,
 /*   270 */  1422, 1422, 1364, 1422, 1372, 1372, 1370, 1372, 1370, 1366,
 /*   280 */  1368, 1364, 1372, 1370, 1366, 1368, 1364, 1372, 1370, 1366,
 /*   290 */  1368, 1364, 1372, 1370, 1372, 1370, 1372, 1370, 1372, 1370,
 /*   300 */  1372, 1370, 1366, 1368, 1372, 1370, 1366, 1368, 1422, 1422,
 /*   310 */  1372, 1370, 1372, 1370, 1372, 1370, 1372, 1370, 1372, 1370,
 /*   320 */  1366, 1368, 1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422,
 /*   330 */  1422, 1422, 1422, 1203, 1422, 1130, 1130, 1422, 1422, 1019,
 /*   340 */  1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422,
 /*   350 */  1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422, 1356, 1353,
 /*   360 */  1422, 1239, 1243, 1238, 1242, 1234, 1233, 1232, 1231, 1230,
 /*   370 */  1229, 1228, 1221, 1422, 1422, 1422, 1422, 1422, 1422, 1422,
 /*   380 */  1371, 1365, 1367, 1363, 1422, 1422, 1422, 1422, 1422, 1422,
 /*   390 */  1422, 1422, 1422, 1084, 1218, 1189, 1083, 1144, 1156, 1155,
 /*   400 */  1154, 1153, 1152, 1151, 1150, 1136, 1168, 1172, 1167, 1171,
 /*   410 */  1101, 1259, 1255, 1132, 1129, 1128, 1127, 1126, 1125, 1124,
 /*   420 */  1123, 1122, 1121, 1120, 1119, 1118, 1117, 1422, 1422, 1260,
 /*   430 */  1256, 1159,  984,  985, 1116, 1115, 1114, 1113, 1112, 1111,
 /*   440 */  1110,  981,  980, 1251, 1220, 1219, 1207, 1206, 1190, 1191,
 /*   450 */  1089, 1090, 1422, 1422, 1422, 1078, 1079, 1146, 1145, 1047,
 /*   460 */  1046, 1103, 1102, 1021, 1020, 1026, 1025, 1064, 1065, 1031,
 /*   470 */  1030, 1001, 1002, 1422, 1422, 1085, 1422, 1422, 1330, 1334,
 /*   480 */  1333, 1331, 1422, 1326, 1422, 1422, 1422, 1422, 1069, 1422,
 /*   490 */  1422, 1422, 1422, 1422, 1272, 1422, 1422, 1422, 1422, 1422,
 /*   500 */  1422,  963, 1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422,
 /*   510 */  1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422,
 /*   520 */  1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422,
 /*   530 */  1422, 1422, 1422, 1422, 1422, 1422, 1200, 1217, 1216, 1422,
 /*   540 */  1422, 1422, 1332, 1422, 1325, 1317, 1293, 1295, 1422, 1422,
 /*   550 */  1422, 1422, 1308, 1271, 1270, 1291, 1422, 1422, 1422, 1422,
 /*   560 */  1422, 1422, 1422, 1422, 1422, 1290, 1288, 1422, 1422, 1422,
 /*   570 */  1422, 1422, 1422, 1422, 1422, 1422, 1422, 1422, 1143, 1142,
 /*   580 */  1134, 1130,  968, 1100, 1099, 1422, 1422, 1422, 1422, 1422,
 /*   590 */  1422, 1422, 1157,  983, 1422, 1422, 1422,  979,  976,  972,
 /*   600 */   966, 1422, 1421, 1420, 1419, 1418, 1417, 1416, 1415, 1414,
 /*   610 */  1412, 1411, 1410, 1409, 1408, 1407, 1252, 1406, 1405, 1413,
 /*   620 */  1404, 1403, 1398, 1396, 1395, 1393, 1392, 1391, 1390, 1389,
 /*   630 */  1388, 1387, 1386, 1385, 1384, 1383, 1382, 1381, 1380, 1379,
 /*   640 */  1378, 1377, 1376, 1375, 1374, 1373, 1347, 1346, 1355, 1354,
 /*   650 */  1362, 1361, 1358, 1357, 1352, 1360, 1212, 1214, 1235, 1227,
 /*   660 */  1226, 1225, 1224, 1223, 1222, 1215, 1213, 1211, 1205, 1204,
 /*   670 */  1202, 1201, 1200, 1210, 1209, 1208, 1194, 1193, 1192, 1188,
 /*   680 */  1187, 1186, 1185, 1184, 1183, 1182, 1181, 1180, 1179, 1178,
 /*   690 */  1177, 1176, 1199, 1198, 1197, 1196, 1195, 1351, 1350, 1349,
 /*   700 */  1348, 1093, 1092, 1091, 1088, 1087, 1086, 1085, 1341, 1340,
 /*   710 */  1342, 1339, 1344, 1345, 1343, 1338, 1336, 1335, 1337, 1329,
 /*   720 */  1323, 1327, 1328, 1324, 1322, 1312, 1315, 1321, 1320, 1318,
 /*   730 */  1316, 1314, 1313, 1311, 1283, 1294, 1296, 1310, 1309, 1307,
 /*   740 */  1306, 1305, 1304, 1303, 1302, 1301, 1300, 1299, 1298, 1297,
 /*   750 */  1292, 1289, 1287, 1286, 1285, 1281, 1280, 1279, 1278, 1277,
 /*   760 */  1276, 1275,  972, 1274, 1273, 1082, 1081, 1080, 1077, 1076,
 /*   770 */  1075, 1074, 1073, 1072, 1071, 1070, 1069, 1284, 1282, 1262,
 /*   780 */  1265, 1266, 1269, 1268, 1267, 1264, 1263, 1261, 1402, 1401,
 /*   790 */  1400, 1399, 1397, 1394, 1138, 1140, 1149, 1148, 1147, 1141,
 /*   800 */  1139, 1137, 1045, 1044, 1043, 1042, 1041, 1040, 1050, 1049,
 /*   810 */  1048, 1039, 1038, 1037, 1036, 1035, 1369, 1133, 1135,  969,
 /*   820 */  1095, 1097, 1161, 1164, 1163, 1162, 1160, 1109, 1108, 1107,
 /*   830 */  1106, 1105, 1104, 1098, 1096, 1094, 1014, 1245, 1251, 1250,
 /*   840 */  1249, 1248, 1247, 1246, 1244, 1131, 1024, 1023, 1022, 1029,
 /*   850 */  1028, 1027, 1019, 1018, 1017, 1016, 1015, 1014, 1013, 1012,
 /*   860 */  1011, 1174, 1175, 1173, 1158, 1066, 1068, 1067, 1063, 1062,
 /*   870 */  1061, 1060, 1059, 1058, 1057, 1056, 1055, 1054, 1053, 1052,
 /*   880 */  1051,  982, 1034, 1033, 1032, 1010, 1009, 1008, 1007, 1006,
 /*   890 */  1003, 1004, 1005, 1000,  999,  998,  997,  996,  995,  994,
 /*   900 */   993,  992,  991,  990,  989,  988,  987,  986,  978,  977,
 /*   910 */   975,  974,  973,  971,  970,  967,  965,  961,  960,  964,
 /*   920 */   963,  962,  959,  958,  957,  956,  955,  954,  953,  952,
 /*   930 */   951,  950,  949,  948,  947,  946,  945,  944,  943,  942,
};

/* The next table maps tokens into fallback tokens.  If a construct
** like the following:
** 
**      %fallback ID X Y Z.
**
** appears in the grammar, then ID becomes a fallback token for X, Y,
** and Z.  Whenever one of the tokens X, Y, or Z is input to the parser
** but it does not parse, the type of the token is changed to ID and
** the parse is retried before an error is thrown.
*/
#ifdef YYFALLBACK
static const YYCODETYPE yyFallback[] = {
    0,  /*          $ => nothing */
    0,  /*    INTEGER => nothing */
    0,  /*      FLOAT => nothing */
    0,  /* IDENTIFIER => nothing */
    0,  /* POUND_IDENTIFIER => nothing */
    0,  /* POUND_INTEGER => nothing */
    0,  /* AT_IDENTIFIER => nothing */
    0,  /* STRING_LITERAL => nothing */
    0,  /*     ASP_GR => nothing */
    0,  /*     ASP_CP => nothing */
    0,  /*     LUA_GR => nothing */
    0,  /*     LUA_CP => nothing */
    0,  /*  PYTHON_GR => nothing */
    0,  /*  PYTHON_CP => nothing */
    0,  /*    F2LP_GR => nothing */
    0,  /*    F2LP_CP => nothing */
    0,  /*    COMMENT => nothing */
    0,  /*  CONSTANTS => nothing */
    0,  /*    INCLUDE => nothing */
    0,  /*     MACROS => nothing */
    0,  /*    OBJECTS => nothing */
    0,  /*      QUERY => nothing */
    0,  /*       SHOW => nothing */
    0,  /*      SORTS => nothing */
    0,  /*  VARIABLES => nothing */
    0,  /*   ABACTION => nothing */
    0,  /*     ACTION => nothing */
    0,  /* ADDITIVEACTION => nothing */
    0,  /* ADDITIVEFLUENT => nothing */
    0,  /*      AFTER => nothing */
    0,  /*        ALL => nothing */
    0,  /*     ALWAYS => nothing */
    0,  /*    ALWAYST => nothing */
    0,  /*   ASSUMING => nothing */
    0,  /*  ATTRIBUTE => nothing */
    0,  /*         BY => nothing */
    0,  /*     CAUSED => nothing */
    0,  /*     CAUSES => nothing */
    0,  /* IMPOSSIBLE => nothing */
    0,  /* CONSTRAINT => nothing */
    0,  /* DECREMENTS => nothing */
    0,  /*    DEFAULT => nothing */
    0,  /* EXTERNALACTION => nothing */
    0,  /*  EXOGENOUS => nothing */
    0,  /* EXOGENOUSACTION => nothing */
    0,  /*        DDT => nothing */
    0,  /*         IF => nothing */
    0,  /*       MODE => nothing */
    0,  /*     IFCONS => nothing */
    0,  /* INCREMENTS => nothing */
    0,  /*   INERTIAL => nothing */
    0,  /* INERTIALFLUENT => nothing */
    0,  /*      LABEL => nothing */
    0,  /*  MAY_CAUSE => nothing */
    0,  /* MAXADDITIVE => nothing */
    0,  /* MAXAFVALUE => nothing */
    0,  /*    MAXSTEP => nothing */
    0,  /*      NEVER => nothing */
    0,  /* NOCONCURRENCY => nothing */
    0,  /* STRONG_NOCONCURRENCY => nothing */
    0,  /* NONEXECUTABLE => nothing */
    0,  /*         OF => nothing */
    0,  /* POSSIBLY_CAUSED => nothing */
    0,  /*       REAL => nothing */
    0,  /* CONTINUOUS => nothing */
    0,  /*      RIGID => nothing */
    0,  /*   SDFLUENT => nothing */
    0,  /* SIMPLEFLUENT => nothing */
    0,  /* EXTERNALFLUENT => nothing */
    0,  /*     UNLESS => nothing */
    0,  /*      WHERE => nothing */
    0,  /*      FALSE => nothing */
    0,  /*       TRUE => nothing */
    0,  /*         AT => nothing */
    0,  /*  BRACKET_L => nothing */
    0,  /*  BRACKET_R => nothing */
    0,  /* COLON_DASH => nothing */
    0,  /* CBRACKET_L => nothing */
    0,  /* CBRACKET_R => nothing */
    0,  /*    PAREN_L => nothing */
    0,  /*    PAREN_R => nothing */
    0,  /*     PERIOD => nothing */
    0,  /* MACRO_STRING => nothing */
    0,  /*      TILDE => nothing */
    0,  /*  DBL_COLON => nothing */
    0,  /*  ARROW_LEQ => nothing */
    0,  /*  ARROW_REQ => nothing */
    0,  /* ARROW_LDASH => nothing */
    0,  /*      COLON => nothing */
    0,  /*         EQ => nothing */
    0,  /*     DBL_EQ => nothing */
    0,  /*        NEQ => nothing */
    0,  /*     NOT_EQ => nothing */
    0,  /*      LTHAN => nothing */
    0,  /*      GTHAN => nothing */
    0,  /*   LTHAN_EQ => nothing */
    0,  /*   GTHAN_EQ => nothing */
    0,  /* DBL_PERIOD => nothing */
    0,  /*   BIG_CONJ => nothing */
    0,  /*   BIG_DISJ => nothing */
    0,  /*      POUND => nothing */
    0,  /*  SEMICOLON => nothing */
    0,  /*      EQUIV => nothing */
    0,  /*       IMPL => nothing */
    0,  /* ARROW_RDASH => nothing */
    0,  /*   DBL_PLUS => nothing */
    0,  /*       PIPE => nothing */
    0,  /*  DBL_GTHAN => nothing */
    0,  /*  DBL_LTHAN => nothing */
    0,  /*        AMP => nothing */
    0,  /*      COMMA => nothing */
    0,  /*    DBL_AMP => nothing */
    0,  /*        NOT => nothing */
    0,  /*       DASH => nothing */
    0,  /*       PLUS => nothing */
    0,  /*       STAR => nothing */
    0,  /*    INT_DIV => nothing */
    0,  /*        MOD => nothing */
    0,  /*        ABS => nothing */
    0,  /*     CARROT => nothing */
    0,  /*     UMINUS => nothing */
    0,  /*     PREC_4 => nothing */
    0,  /*     PREC_3 => nothing */
    0,  /*     PREC_2 => nothing */
    0,  /*     PREC_1 => nothing */
    0,  /*     PREC_0 => nothing */
    0,  /*        EOF => nothing */
    0,  /*     ERR_IO => nothing */
    0,  /* ERR_UNKNOWN_SYMBOL => nothing */
    0,  /* ERR_UNTERMINATED_STRING => nothing */
    0,  /* ERR_UNTERMINATED_ASP => nothing */
    0,  /* ERR_UNTERMINATED_LUA => nothing */
    0,  /* ERR_UNTERMINATED_PYTHON => nothing */
    0,  /* ERR_UNTERMINATED_F2LP => nothing */
    0,  /* ERR_UNTERMINATED_BLK_COMMENT => nothing */
    0,  /* ERR_SYNTAX => nothing */
    0,  /* ERR_PAREN_MISMATCH => nothing */
    0,  /*        ARG => nothing */
    0,  /*       NOOP => nothing */
    3,  /* CONSTANT_ID => IDENTIFIER */
    3,  /* VARIABLE_ID => IDENTIFIER */
    3,  /*  OBJECT_ID => IDENTIFIER */
};
#endif /* YYFALLBACK */

/* The following structure represents a single element of the
** parser's stack.  Information stored includes:
**
**   +  The state number for the parser at this level of the stack.
**
**   +  The value of the token stored at this level of the stack.
**      (In other words, the "major" token.)
**
**   +  The semantic value stored at this level of the stack.  This is
**      the information used by the action routines in the grammar.
**      It is sometimes called the "minor" token.
*/
struct yyStackEntry {
  YYACTIONTYPE stateno;  /* The state-number */
  YYCODETYPE major;      /* The major token value.  This is the code
                         ** number for the token at this stack level */
  YYMINORTYPE minor;     /* The user-supplied minor token value.  This
                         ** is the value of the token  */
};
typedef struct yyStackEntry yyStackEntry;

/* The state of the parser is completely contained in an instance of
** the following structure */
struct yyParser {
  int yyidx;                    /* Index of top element in stack */
#ifdef YYTRACKMAXSTACKDEPTH
  int yyidxMax;                 /* Maximum value of yyidx */
#endif
  int yyerrcnt;                 /* Shifts left before out of the error */
  lemon_parserARG_SDECL                /* A place to hold %extra_argument */
#if YYSTACKDEPTH<=0
  int yystksz;                  /* Current side of the stack */
  yyStackEntry *yystack;        /* The parser's stack */
#else
  yyStackEntry yystack[YYSTACKDEPTH];  /* The parser's stack */
#endif

  int yylookmajor;				/* major token type for the lookahead token */
  YYMINORTYPE yylookminor;		/* minor token type for the lookahead token */
  int yysyntaxerr;				/* a flag used to trigger a syntax error */

};
typedef struct yyParser yyParser;

#ifndef NDEBUG
#include <stdio.h>
static FILE *yyTraceFILE = 0;
static char const*yyTracePrompt = 0;
#endif /* NDEBUG */

#ifndef NDEBUG
/* 
** Turn parser tracing on by giving a stream to which to write the trace
** and a prompt to preface each trace message.  Tracing is turned off
** by making either argument NULL 
**
** Inputs:
** <ul>
** <li> A FILE* to which trace output should be written.
**      If NULL, then tracing is turned off.
** <li> A prefix string written at the beginning of every
**      line of trace output.  If NULL, then tracing is
**      turned off.
** </ul>
**
** Outputs:
** None.
*/
void lemon_parserTrace(FILE *TraceFILE, char const*zTracePrompt){
  yyTraceFILE = TraceFILE;
  yyTracePrompt = zTracePrompt;
  if( yyTraceFILE==0 ) yyTracePrompt = 0;
  else if( yyTracePrompt==0 ) yyTraceFILE = 0;
}
#endif /* NDEBUG */

//#ifndef NDEBUG
/* For tracing shifts, the names of all terminals and nonterminals
** are required.  The following table supplies these names */
static const char *const yyTokenName[] = { 
  "$",             "INTEGER",       "FLOAT",         "IDENTIFIER",  
  "POUND_IDENTIFIER",  "POUND_INTEGER",  "AT_IDENTIFIER",  "STRING_LITERAL",
  "ASP_GR",        "ASP_CP",        "LUA_GR",        "LUA_CP",      
  "PYTHON_GR",     "PYTHON_CP",     "F2LP_GR",       "F2LP_CP",     
  "COMMENT",       "CONSTANTS",     "INCLUDE",       "MACROS",      
  "OBJECTS",       "QUERY",         "SHOW",          "SORTS",       
  "VARIABLES",     "ABACTION",      "ACTION",        "ADDITIVEACTION",
  "ADDITIVEFLUENT",  "AFTER",         "ALL",           "ALWAYS",      
  "ALWAYST",       "ASSUMING",      "ATTRIBUTE",     "BY",          
  "CAUSED",        "CAUSES",        "IMPOSSIBLE",    "CONSTRAINT",  
  "DECREMENTS",    "DEFAULT",       "EXTERNALACTION",  "EXOGENOUS",   
  "EXOGENOUSACTION",  "DDT",           "IF",            "MODE",        
  "IFCONS",        "INCREMENTS",    "INERTIAL",      "INERTIALFLUENT",
  "LABEL",         "MAY_CAUSE",     "MAXADDITIVE",   "MAXAFVALUE",  
  "MAXSTEP",       "NEVER",         "NOCONCURRENCY",  "STRONG_NOCONCURRENCY",
  "NONEXECUTABLE",  "OF",            "POSSIBLY_CAUSED",  "REAL",        
  "CONTINUOUS",    "RIGID",         "SDFLUENT",      "SIMPLEFLUENT",
  "EXTERNALFLUENT",  "UNLESS",        "WHERE",         "FALSE",       
  "TRUE",          "AT",            "BRACKET_L",     "BRACKET_R",   
  "COLON_DASH",    "CBRACKET_L",    "CBRACKET_R",    "PAREN_L",     
  "PAREN_R",       "PERIOD",        "MACRO_STRING",  "TILDE",       
  "DBL_COLON",     "ARROW_LEQ",     "ARROW_REQ",     "ARROW_LDASH", 
  "COLON",         "EQ",            "DBL_EQ",        "NEQ",         
  "NOT_EQ",        "LTHAN",         "GTHAN",         "LTHAN_EQ",    
  "GTHAN_EQ",      "DBL_PERIOD",    "BIG_CONJ",      "BIG_DISJ",    
  "POUND",         "SEMICOLON",     "EQUIV",         "IMPL",        
  "ARROW_RDASH",   "DBL_PLUS",      "PIPE",          "DBL_GTHAN",   
  "DBL_LTHAN",     "AMP",           "COMMA",         "DBL_AMP",     
  "NOT",           "DASH",          "PLUS",          "STAR",        
  "INT_DIV",       "MOD",           "ABS",           "CARROT",      
  "UMINUS",        "PREC_4",        "PREC_3",        "PREC_2",      
  "PREC_1",        "PREC_0",        "EOF",           "ERR_IO",      
  "ERR_UNKNOWN_SYMBOL",  "ERR_UNTERMINATED_STRING",  "ERR_UNTERMINATED_ASP",  "ERR_UNTERMINATED_LUA",
  "ERR_UNTERMINATED_PYTHON",  "ERR_UNTERMINATED_F2LP",  "ERR_UNTERMINATED_BLK_COMMENT",  "ERR_SYNTAX",  
  "ERR_PAREN_MISMATCH",  "ARG",           "NOOP",          "CONSTANT_ID", 
  "VARIABLE_ID",   "OBJECT_ID",     "SIN",           "COS",         
  "TAN",           "HIDE",          "OBSERVED",      "error",       
  "start",         "statement_lst",  "statement",     "stmt_macro_def",
  "stmt_constant_def",  "stmt_object_def",  "stmt_variable_def",  "stmt_sort_def",
  "stmt_code_blk",  "stmt_law",      "stmt_show",     "stmt_hide",   
  "stmt_noconcurrency",  "stmt_strong_noconcurrency",  "stmt_maxafvalue",  "stmt_maxadditive",
  "stmt_query",    "rate_decl",     "alwayst_stmt",  "base_elem",   
  "base_elem_no_const",  "constant",      "object",        "object_nullary",
  "variable",      "lua",           "undeclared",    "term_lst",    
  "term",          "constant_one_const",  "term_no_const_lst",  "term_no_const",
  "const_anon",    "term_strong",   "term_strong_candidate",  "term_no_const_strong",
  "num_range",     "num_range_eval",  "term_integral",  "term_int_eval",
  "formula",       "formula_base",  "comparison",    "atomic_formula",
  "formula_quant",  "formula_card",  "atomic_formula_anon",  "formula_no_const",
  "formula_no_const_base",  "comparison_no_const",  "atomic_formula_one_const",  "quant_lst",   
  "quant_op",      "card_var_lst",  "card_var_lst_inner",  "term_temporal",
  "term_temporal_strong",  "term_temporal_strong_candidate",  "constant_temporal",  "formula_temporal",
  "formula_temporal_base",  "comparison_temporal",  "formula_temporal_quant",  "formula_temporal_card",
  "head_formula",  "atomic_head_formula",  "formula_smpl_card",  "macro_def_lst",
  "macro_bnd",     "macro_args",    "macro_arg",     "sort_lst",    
  "sort",          "sort_id_nr",    "sort_nr",       "sort_id",     
  "constant_bnd_lst",  "constant_bnd",  "constant_dcl_lst",  "constant_dcl_type",
  "attrib_spec",   "object_bnd_lst",  "object_bnd",    "object_lst",  
  "object_spec",   "variable_bnd_lst",  "variable_bnd",  "variable_lst",
  "sort_bnd_lst",  "sort_bnd",      "sort_dcl_lst",  "show_lst",    
  "show_elem",     "query_lst",     "query_maxstep_decl",  "query_label_decl",
  "query_label_Decl",  "clause_if",     "clause_after",  "clause_ifcons",
  "clause_unless",  "clause_where",  "law_basic",     "law_caused",  
  "law_pcaused",   "law_impl",      "law_causes",    "law_increments",
  "law_decrements",  "law_mcause",    "law_always",    "law_constraint",
  "law_impossible",  "law_never",     "law_default",   "law_exogenous",
  "law_inertial",  "law_nonexecutable",  "law_rigid",     "law_observed",
  "law_temporal_constraint",
};
//#endif /* NDEBUG */

#ifndef NDEBUG
/* For tracing reduce actions, the names of all rules are required.
*/
static const char *const yyRuleName[] = {
 /*   0 */ "start ::= statement_lst EOF",
 /*   1 */ "statement_lst ::=",
 /*   2 */ "statement_lst ::= statement_lst error",
 /*   3 */ "statement_lst ::= statement_lst statement",
 /*   4 */ "statement ::= stmt_macro_def",
 /*   5 */ "statement ::= stmt_constant_def",
 /*   6 */ "statement ::= stmt_object_def",
 /*   7 */ "statement ::= stmt_variable_def",
 /*   8 */ "statement ::= stmt_sort_def",
 /*   9 */ "statement ::= stmt_code_blk",
 /*  10 */ "statement ::= stmt_law",
 /*  11 */ "statement ::= rate_decl",
 /*  12 */ "statement ::= alwayst_stmt",
 /*  13 */ "statement ::= stmt_show",
 /*  14 */ "statement ::= stmt_hide",
 /*  15 */ "statement ::= stmt_noconcurrency",
 /*  16 */ "statement ::= stmt_strong_noconcurrency",
 /*  17 */ "statement ::= stmt_maxafvalue",
 /*  18 */ "statement ::= stmt_maxadditive",
 /*  19 */ "statement ::= stmt_query",
 /*  20 */ "base_elem ::= constant",
 /*  21 */ "base_elem ::= base_elem_no_const",
 /*  22 */ "base_elem_no_const ::= object",
 /*  23 */ "base_elem_no_const ::= variable",
 /*  24 */ "base_elem_no_const ::= lua",
 /*  25 */ "constant ::= CONSTANT_ID PAREN_L term_lst PAREN_R",
 /*  26 */ "constant ::= CONSTANT_ID",
 /*  27 */ "constant ::= MODE",
 /*  28 */ "const_anon ::= IDENTIFIER",
 /*  29 */ "const_anon ::= IDENTIFIER PAREN_L term_lst PAREN_R",
 /*  30 */ "object ::= OBJECT_ID PAREN_L term_lst PAREN_R",
 /*  31 */ "object ::= object_nullary",
 /*  32 */ "object_nullary ::= OBJECT_ID",
 /*  33 */ "object ::= undeclared",
 /*  34 */ "variable ::= VARIABLE_ID",
 /*  35 */ "lua ::= AT_IDENTIFIER PAREN_L term_lst PAREN_R",
 /*  36 */ "lua ::= AT_IDENTIFIER",
 /*  37 */ "lua ::= AT_IDENTIFIER PAREN_L PAREN_R",
 /*  38 */ "undeclared ::= IDENTIFIER PAREN_L term_lst PAREN_R",
 /*  39 */ "undeclared ::= IDENTIFIER",
 /*  40 */ "term_lst ::= term",
 /*  41 */ "term_lst ::= term_lst COMMA term",
 /*  42 */ "constant_one_const ::= CONSTANT_ID PAREN_L term_no_const_lst PAREN_R",
 /*  43 */ "constant_one_const ::= CONSTANT_ID",
 /*  44 */ "term_no_const_lst ::= term_no_const",
 /*  45 */ "term_no_const_lst ::= term_no_const_lst COMMA term_no_const",
 /*  46 */ "term ::= base_elem",
 /*  47 */ "term ::= INTEGER",
 /*  48 */ "term ::= FLOAT",
 /*  49 */ "term ::= STRING_LITERAL",
 /*  50 */ "term ::= PAREN_L term PAREN_R",
 /*  51 */ "term ::= TRUE",
 /*  52 */ "term ::= FALSE",
 /*  53 */ "term ::= MAXSTEP",
 /*  54 */ "term ::= MAXADDITIVE",
 /*  55 */ "term ::= MAXAFVALUE",
 /*  56 */ "term ::= DASH term",
 /*  57 */ "term ::= ABS term",
 /*  58 */ "term ::= SIN PAREN_L term PAREN_R",
 /*  59 */ "term ::= COS PAREN_L term PAREN_R",
 /*  60 */ "term ::= TAN PAREN_L term PAREN_R",
 /*  61 */ "term ::= term DASH term",
 /*  62 */ "term ::= term PLUS term",
 /*  63 */ "term ::= term STAR term",
 /*  64 */ "term ::= term INT_DIV term",
 /*  65 */ "term ::= term MOD term",
 /*  66 */ "term_strong ::= base_elem_no_const",
 /*  67 */ "term_strong ::= INTEGER",
 /*  68 */ "term_strong ::= FLOAT",
 /*  69 */ "term_strong ::= STRING_LITERAL",
 /*  70 */ "term_strong ::= PAREN_L term_strong PAREN_R",
 /*  71 */ "term_strong ::= MAXSTEP",
 /*  72 */ "term_strong ::= MAXADDITIVE",
 /*  73 */ "term_strong ::= MAXAFVALUE",
 /*  74 */ "term_strong ::= DASH term_strong",
 /*  75 */ "term_strong ::= ABS term",
 /*  76 */ "term_strong ::= SIN PAREN_L term PAREN_R",
 /*  77 */ "term_strong ::= COS PAREN_L term PAREN_R",
 /*  78 */ "term_strong ::= TAN PAREN_L term PAREN_R",
 /*  79 */ "term_strong_candidate ::= DASH constant",
 /*  80 */ "term_strong ::= term_strong_candidate DASH term",
 /*  81 */ "term_strong ::= term_strong_candidate PLUS term",
 /*  82 */ "term_strong ::= term_strong_candidate STAR term",
 /*  83 */ "term_strong ::= term_strong_candidate INT_DIV term",
 /*  84 */ "term_strong ::= term_strong_candidate MOD term",
 /*  85 */ "term_strong ::= constant DASH term",
 /*  86 */ "term_strong ::= constant PLUS term",
 /*  87 */ "term_strong ::= constant STAR term",
 /*  88 */ "term_strong ::= constant INT_DIV term",
 /*  89 */ "term_strong ::= constant MOD term",
 /*  90 */ "term_strong ::= term_strong DASH term",
 /*  91 */ "term_strong ::= term_strong PLUS term",
 /*  92 */ "term_strong ::= term_strong STAR term",
 /*  93 */ "term_strong ::= term_strong INT_DIV term",
 /*  94 */ "term_strong ::= term_strong MOD term",
 /*  95 */ "term_no_const_strong ::= base_elem_no_const",
 /*  96 */ "term_no_const_strong ::= INTEGER",
 /*  97 */ "term_no_const_strong ::= FLOAT",
 /*  98 */ "term_no_const_strong ::= STRING_LITERAL",
 /*  99 */ "term_no_const_strong ::= PAREN_L term_no_const_strong PAREN_R",
 /* 100 */ "term_no_const_strong ::= MAXSTEP",
 /* 101 */ "term_no_const_strong ::= MAXADDITIVE",
 /* 102 */ "term_no_const_strong ::= MAXAFVALUE",
 /* 103 */ "term_no_const_strong ::= constant",
 /* 104 */ "term_no_const_strong ::= DASH term_no_const_strong",
 /* 105 */ "term_no_const_strong ::= ABS term_no_const",
 /* 106 */ "term_no_const_strong ::= term_no_const_strong DASH term_no_const",
 /* 107 */ "term_no_const_strong ::= term_no_const_strong PLUS term_no_const",
 /* 108 */ "term_no_const_strong ::= term_no_const_strong STAR term_no_const",
 /* 109 */ "term_no_const_strong ::= term_no_const_strong INT_DIV term_no_const",
 /* 110 */ "term_no_const_strong ::= term_no_const_strong MOD term_no_const",
 /* 111 */ "term_no_const ::= base_elem_no_const",
 /* 112 */ "term_no_const ::= INTEGER",
 /* 113 */ "term_no_const ::= FLOAT",
 /* 114 */ "term_no_const ::= STRING_LITERAL",
 /* 115 */ "term_no_const ::= PAREN_L term_no_const PAREN_R",
 /* 116 */ "term_no_const ::= TRUE",
 /* 117 */ "term_no_const ::= FALSE",
 /* 118 */ "term_no_const ::= MAXSTEP",
 /* 119 */ "term_no_const ::= MAXADDITIVE",
 /* 120 */ "term_no_const ::= MAXAFVALUE",
 /* 121 */ "term_no_const ::= constant",
 /* 122 */ "term_no_const ::= DASH term_no_const",
 /* 123 */ "term_no_const ::= ABS term_no_const",
 /* 124 */ "term_no_const ::= term_no_const DASH term_no_const",
 /* 125 */ "term_no_const ::= term_no_const PLUS term_no_const",
 /* 126 */ "term_no_const ::= term_no_const STAR term_no_const",
 /* 127 */ "term_no_const ::= term_no_const INT_DIV term_no_const",
 /* 128 */ "term_no_const ::= term_no_const MOD term_no_const",
 /* 129 */ "term_integral ::= INTEGER",
 /* 130 */ "term_integral ::= PAREN_L term_integral PAREN_R",
 /* 131 */ "term_integral ::= TRUE",
 /* 132 */ "term_integral ::= FALSE",
 /* 133 */ "term_integral ::= MAXSTEP",
 /* 134 */ "term_integral ::= MAXADDITIVE",
 /* 135 */ "term_integral ::= MAXAFVALUE",
 /* 136 */ "term_integral ::= DASH term_integral",
 /* 137 */ "term_integral ::= ABS term_integral",
 /* 138 */ "term_integral ::= term_integral DASH term_integral",
 /* 139 */ "term_integral ::= term_integral PLUS term_integral",
 /* 140 */ "term_integral ::= term_integral STAR term_integral",
 /* 141 */ "term_integral ::= term_integral INT_DIV term_integral",
 /* 142 */ "term_integral ::= term_integral MOD term_integral",
 /* 143 */ "num_range ::= term_integral DBL_PERIOD term_integral",
 /* 144 */ "num_range_eval ::= term_int_eval DBL_PERIOD term_int_eval",
 /* 145 */ "term_int_eval ::= INTEGER",
 /* 146 */ "term_int_eval ::= PAREN_L term_int_eval PAREN_R",
 /* 147 */ "term_int_eval ::= DASH term_int_eval",
 /* 148 */ "term_int_eval ::= ABS term_int_eval",
 /* 149 */ "term_int_eval ::= term_int_eval DASH term_int_eval",
 /* 150 */ "term_int_eval ::= term_int_eval PLUS term_int_eval",
 /* 151 */ "term_int_eval ::= term_int_eval STAR term_int_eval",
 /* 152 */ "term_int_eval ::= term_int_eval INT_DIV term_int_eval",
 /* 153 */ "term_int_eval ::= term_int_eval MOD term_int_eval",
 /* 154 */ "formula ::= formula_base",
 /* 155 */ "formula ::= PAREN_L formula PAREN_R",
 /* 156 */ "formula ::= NOT formula",
 /* 157 */ "formula ::= DASH formula",
 /* 158 */ "formula ::= formula AMP formula",
 /* 159 */ "formula ::= formula DBL_PLUS formula",
 /* 160 */ "formula ::= formula PIPE formula",
 /* 161 */ "formula ::= formula EQUIV formula",
 /* 162 */ "formula ::= formula IMPL formula",
 /* 163 */ "formula ::= formula ARROW_RDASH formula",
 /* 164 */ "formula_base ::= comparison",
 /* 165 */ "formula_base ::= atomic_formula",
 /* 166 */ "formula_base ::= formula_quant",
 /* 167 */ "formula_base ::= formula_card",
 /* 168 */ "formula_base ::= TRUE",
 /* 169 */ "formula_base ::= FALSE",
 /* 170 */ "comparison ::= term_strong EQ term",
 /* 171 */ "comparison ::= term_strong DBL_EQ term",
 /* 172 */ "comparison ::= term_strong NEQ term",
 /* 173 */ "comparison ::= term_strong LTHAN term",
 /* 174 */ "comparison ::= term_strong GTHAN term",
 /* 175 */ "comparison ::= term_strong LTHAN_EQ term",
 /* 176 */ "comparison ::= term_strong GTHAN_EQ term",
 /* 177 */ "comparison ::= term_strong_candidate EQ term",
 /* 178 */ "comparison ::= term_strong_candidate DBL_EQ term",
 /* 179 */ "comparison ::= term_strong_candidate NEQ term",
 /* 180 */ "comparison ::= term_strong_candidate LTHAN term",
 /* 181 */ "comparison ::= term_strong_candidate GTHAN term",
 /* 182 */ "comparison ::= term_strong_candidate LTHAN_EQ term",
 /* 183 */ "comparison ::= term_strong_candidate GTHAN_EQ term",
 /* 184 */ "comparison ::= constant DBL_EQ term",
 /* 185 */ "comparison ::= constant NEQ term",
 /* 186 */ "comparison ::= constant LTHAN term",
 /* 187 */ "comparison ::= constant GTHAN term",
 /* 188 */ "comparison ::= constant LTHAN_EQ term",
 /* 189 */ "comparison ::= constant GTHAN_EQ term",
 /* 190 */ "atomic_formula ::= constant",
 /* 191 */ "atomic_formula ::= TILDE constant",
 /* 192 */ "atomic_formula ::= constant EQ term",
 /* 193 */ "atomic_formula_anon ::= atomic_formula",
 /* 194 */ "atomic_formula_anon ::= const_anon",
 /* 195 */ "atomic_formula_anon ::= TILDE const_anon",
 /* 196 */ "atomic_formula_anon ::= const_anon EQ term",
 /* 197 */ "formula_no_const ::= formula_no_const_base",
 /* 198 */ "formula_no_const ::= PAREN_L formula_no_const PAREN_R",
 /* 199 */ "formula_no_const ::= NOT formula_no_const",
 /* 200 */ "formula_no_const ::= DASH formula_no_const",
 /* 201 */ "formula_no_const ::= formula_no_const AMP formula_no_const",
 /* 202 */ "formula_no_const ::= formula_no_const DBL_PLUS formula_no_const",
 /* 203 */ "formula_no_const ::= formula_no_const PIPE formula_no_const",
 /* 204 */ "formula_no_const ::= formula_no_const EQUIV formula_no_const",
 /* 205 */ "formula_no_const ::= formula_no_const IMPL formula_no_const",
 /* 206 */ "formula_no_const ::= formula_no_const ARROW_RDASH formula_no_const",
 /* 207 */ "formula_no_const_base ::= comparison_no_const",
 /* 208 */ "formula_no_const_base ::= TRUE",
 /* 209 */ "formula_no_const_base ::= FALSE",
 /* 210 */ "comparison_no_const ::= term_no_const_strong EQ term_no_const",
 /* 211 */ "comparison_no_const ::= term_no_const_strong DBL_EQ term_no_const",
 /* 212 */ "comparison_no_const ::= term_no_const_strong NEQ term_no_const",
 /* 213 */ "comparison_no_const ::= term_no_const_strong LTHAN term_no_const",
 /* 214 */ "comparison_no_const ::= term_no_const_strong GTHAN term_no_const",
 /* 215 */ "comparison_no_const ::= term_no_const_strong LTHAN_EQ term_no_const",
 /* 216 */ "comparison_no_const ::= term_no_const_strong GTHAN_EQ term_no_const",
 /* 217 */ "atomic_formula_one_const ::= constant_one_const",
 /* 218 */ "atomic_formula_one_const ::= TILDE constant_one_const",
 /* 219 */ "atomic_formula_one_const ::= constant_one_const EQ term_no_const",
 /* 220 */ "formula_quant ::= BRACKET_L quant_lst PIPE formula BRACKET_R",
 /* 221 */ "quant_lst ::= quant_op variable",
 /* 222 */ "quant_lst ::= quant_lst quant_op variable",
 /* 223 */ "quant_op ::= BIG_CONJ",
 /* 224 */ "quant_op ::= BIG_DISJ",
 /* 225 */ "formula_card ::= CBRACKET_L card_var_lst formula CBRACKET_R",
 /* 226 */ "formula_card ::= term_strong CBRACKET_L card_var_lst formula CBRACKET_R",
 /* 227 */ "formula_card ::= CBRACKET_L card_var_lst formula CBRACKET_R term",
 /* 228 */ "formula_card ::= term_strong CBRACKET_L card_var_lst formula CBRACKET_R term",
 /* 229 */ "formula_card ::= CBRACKET_L formula CBRACKET_R",
 /* 230 */ "formula_card ::= term_strong CBRACKET_L formula CBRACKET_R",
 /* 231 */ "formula_card ::= CBRACKET_L formula CBRACKET_R term",
 /* 232 */ "formula_card ::= term_strong CBRACKET_L formula CBRACKET_R term",
 /* 233 */ "card_var_lst ::= card_var_lst_inner PIPE",
 /* 234 */ "card_var_lst_inner ::= variable",
 /* 235 */ "card_var_lst_inner ::= card_var_lst_inner COMMA variable",
 /* 236 */ "term_temporal ::= base_elem_no_const",
 /* 237 */ "term_temporal ::= INTEGER",
 /* 238 */ "term_temporal ::= FLOAT",
 /* 239 */ "term_temporal ::= STRING_LITERAL",
 /* 240 */ "term_temporal ::= PAREN_L term_temporal PAREN_R",
 /* 241 */ "term_temporal ::= TRUE",
 /* 242 */ "term_temporal ::= FALSE",
 /* 243 */ "term_temporal ::= MAXSTEP",
 /* 244 */ "term_temporal ::= MAXADDITIVE",
 /* 245 */ "term_temporal ::= MAXAFVALUE",
 /* 246 */ "term_temporal ::= constant",
 /* 247 */ "term_temporal ::= DASH term_temporal",
 /* 248 */ "term_temporal ::= ABS term_temporal",
 /* 249 */ "term_temporal ::= term_temporal COLON term",
 /* 250 */ "term_temporal ::= term_temporal DASH term_temporal",
 /* 251 */ "term_temporal ::= term_temporal PLUS term_temporal",
 /* 252 */ "term_temporal ::= term_temporal STAR term_temporal",
 /* 253 */ "term_temporal ::= term_temporal INT_DIV term_temporal",
 /* 254 */ "term_temporal ::= term_temporal MOD term_temporal",
 /* 255 */ "term_temporal_strong ::= base_elem_no_const",
 /* 256 */ "term_temporal_strong ::= INTEGER",
 /* 257 */ "term_temporal_strong ::= FLOAT",
 /* 258 */ "term_temporal_strong ::= STRING_LITERAL",
 /* 259 */ "term_temporal_strong ::= PAREN_L term_temporal_strong PAREN_R",
 /* 260 */ "term_temporal_strong ::= MAXSTEP",
 /* 261 */ "term_temporal_strong ::= MAXADDITIVE",
 /* 262 */ "term_temporal_strong ::= MAXAFVALUE",
 /* 263 */ "term_temporal_strong ::= term_temporal_strong COLON term_strong",
 /* 264 */ "term_temporal_strong ::= DASH term_temporal_strong",
 /* 265 */ "term_temporal_strong ::= ABS term_temporal",
 /* 266 */ "term_temporal_strong ::= term_temporal_strong DASH term_temporal",
 /* 267 */ "term_temporal_strong ::= term_temporal_strong PLUS term_temporal",
 /* 268 */ "term_temporal_strong ::= term_temporal_strong STAR term_temporal",
 /* 269 */ "term_temporal_strong ::= term_temporal_strong INT_DIV term_temporal",
 /* 270 */ "term_temporal_strong ::= term_temporal_strong MOD term_temporal",
 /* 271 */ "formula_temporal ::= formula_temporal_base",
 /* 272 */ "formula_temporal ::= PAREN_L formula_temporal PAREN_R",
 /* 273 */ "formula_temporal ::= NOT formula_temporal",
 /* 274 */ "formula_temporal ::= DASH formula_temporal",
 /* 275 */ "formula_temporal ::= formula_temporal AMP formula_temporal",
 /* 276 */ "formula_temporal ::= formula_temporal DBL_PLUS formula_temporal",
 /* 277 */ "formula_temporal ::= formula_temporal PIPE formula_temporal",
 /* 278 */ "formula_temporal ::= formula_temporal EQUIV formula_temporal",
 /* 279 */ "formula_temporal ::= formula_temporal IMPL formula_temporal",
 /* 280 */ "formula_temporal ::= formula_temporal ARROW_RDASH formula_temporal",
 /* 281 */ "formula_temporal ::= term_temporal_strong COLON formula",
 /* 282 */ "formula_temporal_base ::= comparison_temporal",
 /* 283 */ "formula_temporal_base ::= atomic_formula",
 /* 284 */ "formula_temporal_base ::= formula_temporal_quant",
 /* 285 */ "formula_temporal_base ::= formula_temporal_card",
 /* 286 */ "formula_temporal_base ::= TRUE",
 /* 287 */ "formula_temporal_base ::= FALSE",
 /* 288 */ "comparison_temporal ::= term_temporal_strong EQ term_temporal",
 /* 289 */ "comparison_temporal ::= term_temporal_strong DBL_EQ term_temporal",
 /* 290 */ "comparison_temporal ::= term_temporal_strong NEQ term_temporal",
 /* 291 */ "comparison_temporal ::= term_temporal_strong LTHAN term_temporal",
 /* 292 */ "comparison_temporal ::= term_temporal_strong GTHAN term_temporal",
 /* 293 */ "comparison_temporal ::= term_temporal_strong LTHAN_EQ term_temporal",
 /* 294 */ "comparison_temporal ::= term_temporal_strong GTHAN_EQ term_temporal",
 /* 295 */ "formula_temporal_quant ::= BRACKET_L quant_lst PIPE formula_temporal BRACKET_R",
 /* 296 */ "formula_temporal_card ::= CBRACKET_L card_var_lst formula_temporal CBRACKET_R",
 /* 297 */ "formula_temporal_card ::= term_temporal_strong CBRACKET_L card_var_lst formula_temporal CBRACKET_R",
 /* 298 */ "formula_temporal_card ::= CBRACKET_L card_var_lst formula_temporal CBRACKET_R term_temporal",
 /* 299 */ "formula_temporal_card ::= term_temporal_strong CBRACKET_L card_var_lst formula_temporal CBRACKET_R term_temporal",
 /* 300 */ "formula_temporal_card ::= CBRACKET_L formula_temporal CBRACKET_R",
 /* 301 */ "formula_temporal_card ::= term_temporal_strong CBRACKET_L formula_temporal CBRACKET_R",
 /* 302 */ "formula_temporal_card ::= CBRACKET_L formula_temporal CBRACKET_R term_temporal",
 /* 303 */ "formula_temporal_card ::= term_temporal_strong CBRACKET_L formula_temporal CBRACKET_R term_temporal",
 /* 304 */ "head_formula ::= head_formula AMP head_formula",
 /* 305 */ "head_formula ::= PAREN_L head_formula PAREN_R",
 /* 306 */ "head_formula ::= comparison",
 /* 307 */ "head_formula ::= atomic_head_formula",
 /* 308 */ "head_formula ::= formula_smpl_card",
 /* 309 */ "head_formula ::= TRUE",
 /* 310 */ "head_formula ::= FALSE",
 /* 311 */ "atomic_head_formula ::= atomic_formula",
 /* 312 */ "atomic_head_formula ::= DASH constant",
 /* 313 */ "formula_smpl_card ::= CBRACKET_L card_var_lst atomic_formula_one_const CBRACKET_R",
 /* 314 */ "formula_smpl_card ::= term_strong CBRACKET_L card_var_lst atomic_formula_one_const CBRACKET_R",
 /* 315 */ "formula_smpl_card ::= CBRACKET_L card_var_lst atomic_formula_one_const CBRACKET_R term",
 /* 316 */ "formula_smpl_card ::= term_strong CBRACKET_L card_var_lst atomic_formula_one_const CBRACKET_R term",
 /* 317 */ "formula_smpl_card ::= CBRACKET_L atomic_formula_one_const CBRACKET_R",
 /* 318 */ "formula_smpl_card ::= term_strong CBRACKET_L atomic_formula_one_const CBRACKET_R",
 /* 319 */ "formula_smpl_card ::= CBRACKET_L atomic_formula_one_const CBRACKET_R term",
 /* 320 */ "formula_smpl_card ::= term_strong CBRACKET_L atomic_formula_one_const CBRACKET_R term",
 /* 321 */ "stmt_macro_def ::= COLON_DASH MACROS macro_def_lst PERIOD",
 /* 322 */ "macro_def_lst ::= macro_bnd",
 /* 323 */ "macro_def_lst ::= macro_def_lst SEMICOLON macro_bnd",
 /* 324 */ "macro_bnd ::= IDENTIFIER PAREN_L macro_args PAREN_R ARROW_RDASH MACRO_STRING",
 /* 325 */ "macro_bnd ::= IDENTIFIER ARROW_RDASH MACRO_STRING",
 /* 326 */ "macro_args ::= macro_arg",
 /* 327 */ "macro_args ::= macro_args COMMA macro_arg",
 /* 328 */ "macro_arg ::= POUND_INTEGER",
 /* 329 */ "macro_arg ::= POUND_IDENTIFIER",
 /* 330 */ "sort_lst ::= sort",
 /* 331 */ "sort_lst ::= sort_lst COMMA sort",
 /* 332 */ "sort ::= sort_id_nr",
 /* 333 */ "sort ::= sort_id_nr STAR",
 /* 334 */ "sort ::= sort_id_nr CARROT",
 /* 335 */ "sort ::= sort PLUS object_nullary",
 /* 336 */ "sort ::= sort PLUS IDENTIFIER",
 /* 337 */ "sort ::= sort PLUS INTEGER",
 /* 338 */ "sort_id_nr ::= sort_id",
 /* 339 */ "sort_id_nr ::= sort_nr",
 /* 340 */ "sort_nr ::= num_range",
 /* 341 */ "sort_id ::= IDENTIFIER",
 /* 342 */ "stmt_constant_def ::= COLON_DASH CONSTANTS constant_bnd_lst PERIOD",
 /* 343 */ "constant_bnd_lst ::= constant_bnd",
 /* 344 */ "constant_bnd_lst ::= constant_bnd_lst SEMICOLON constant_bnd",
 /* 345 */ "constant_bnd ::= constant_dcl_lst DBL_COLON constant_dcl_type PAREN_L sort PAREN_R",
 /* 346 */ "constant_bnd ::= constant_dcl_lst DBL_COLON constant_dcl_type PAREN_L REAL BRACKET_L num_range BRACKET_R PAREN_R",
 /* 347 */ "constant_bnd ::= constant_dcl_lst DBL_COLON CONTINUOUS PAREN_L num_range PAREN_R",
 /* 348 */ "constant_bnd ::= constant_dcl_lst DBL_COLON sort",
 /* 349 */ "constant_bnd ::= constant_dcl_lst DBL_COLON REAL BRACKET_L num_range BRACKET_R",
 /* 350 */ "constant_bnd ::= constant_dcl_lst DBL_COLON constant_dcl_type",
 /* 351 */ "constant_bnd ::= constant_dcl_lst DBL_COLON attrib_spec OF IDENTIFIER",
 /* 352 */ "constant_bnd ::= constant_dcl_lst DBL_COLON attrib_spec OF IDENTIFIER PAREN_L sort_lst PAREN_R",
 /* 353 */ "constant_dcl_lst ::= IDENTIFIER",
 /* 354 */ "constant_dcl_lst ::= IDENTIFIER PAREN_L sort_lst PAREN_R",
 /* 355 */ "constant_dcl_lst ::= constant_dcl_lst COMMA IDENTIFIER",
 /* 356 */ "constant_dcl_lst ::= constant_dcl_lst COMMA IDENTIFIER PAREN_L sort_lst PAREN_R",
 /* 357 */ "constant_dcl_type ::= ABACTION",
 /* 358 */ "constant_dcl_type ::= ACTION",
 /* 359 */ "constant_dcl_type ::= ADDITIVEACTION",
 /* 360 */ "constant_dcl_type ::= ADDITIVEFLUENT",
 /* 361 */ "constant_dcl_type ::= EXTERNALACTION",
 /* 362 */ "constant_dcl_type ::= EXTERNALFLUENT",
 /* 363 */ "constant_dcl_type ::= EXOGENOUSACTION",
 /* 364 */ "constant_dcl_type ::= INERTIALFLUENT",
 /* 365 */ "constant_dcl_type ::= RIGID",
 /* 366 */ "constant_dcl_type ::= SIMPLEFLUENT",
 /* 367 */ "constant_dcl_type ::= SDFLUENT",
 /* 368 */ "attrib_spec ::= ATTRIBUTE",
 /* 369 */ "attrib_spec ::= ATTRIBUTE PAREN_L sort PAREN_R",
 /* 370 */ "attrib_spec ::= ATTRIBUTE PAREN_L REAL BRACKET_L num_range BRACKET_R PAREN_R",
 /* 371 */ "stmt_object_def ::= COLON_DASH OBJECTS object_bnd_lst PERIOD",
 /* 372 */ "object_bnd_lst ::= object_bnd",
 /* 373 */ "object_bnd_lst ::= object_bnd_lst SEMICOLON object_bnd",
 /* 374 */ "object_bnd ::= object_lst DBL_COLON sort_id",
 /* 375 */ "object_lst ::= object_spec",
 /* 376 */ "object_lst ::= object_lst COMMA object_spec",
 /* 377 */ "object_spec ::= IDENTIFIER",
 /* 378 */ "object_spec ::= IDENTIFIER PAREN_L sort_lst PAREN_R",
 /* 379 */ "object_spec ::= INTEGER",
 /* 380 */ "object_spec ::= FLOAT",
 /* 381 */ "object_spec ::= num_range",
 /* 382 */ "stmt_variable_def ::= COLON_DASH VARIABLES variable_bnd_lst PERIOD",
 /* 383 */ "variable_bnd_lst ::= variable_bnd",
 /* 384 */ "variable_bnd_lst ::= variable_bnd_lst SEMICOLON variable_bnd",
 /* 385 */ "variable_bnd ::= variable_lst DBL_COLON sort",
 /* 386 */ "variable_bnd ::= variable_lst",
 /* 387 */ "variable_lst ::= IDENTIFIER",
 /* 388 */ "variable_lst ::= variable_lst COMMA IDENTIFIER",
 /* 389 */ "stmt_sort_def ::= COLON_DASH SORTS sort_bnd_lst PERIOD",
 /* 390 */ "sort_bnd_lst ::= sort_bnd",
 /* 391 */ "sort_bnd_lst ::= sort_bnd_lst SEMICOLON sort_bnd",
 /* 392 */ "sort_bnd ::= sort_dcl_lst",
 /* 393 */ "sort_bnd ::= sort_bnd DBL_LTHAN sort_bnd",
 /* 394 */ "sort_bnd ::= sort_bnd DBL_GTHAN sort_bnd",
 /* 395 */ "sort_bnd ::= PAREN_L sort_bnd PAREN_R",
 /* 396 */ "sort_dcl_lst ::= IDENTIFIER",
 /* 397 */ "sort_dcl_lst ::= sort_dcl_lst COMMA IDENTIFIER",
 /* 398 */ "stmt_show ::= COLON_DASH SHOW show_lst PERIOD",
 /* 399 */ "stmt_show ::= COLON_DASH SHOW ALL PERIOD",
 /* 400 */ "stmt_hide ::= COLON_DASH HIDE show_lst PERIOD",
 /* 401 */ "stmt_hide ::= COLON_DASH HIDE ALL PERIOD",
 /* 402 */ "show_lst ::= show_elem",
 /* 403 */ "show_lst ::= show_lst COMMA show_elem",
 /* 404 */ "show_lst ::= show_lst SEMICOLON show_elem",
 /* 405 */ "show_elem ::= atomic_formula_one_const",
 /* 406 */ "stmt_noconcurrency ::= NOCONCURRENCY PERIOD",
 /* 407 */ "stmt_strong_noconcurrency ::= STRONG_NOCONCURRENCY PERIOD",
 /* 408 */ "stmt_maxafvalue ::= COLON_DASH MAXAFVALUE EQ term_int_eval PERIOD",
 /* 409 */ "stmt_maxafvalue ::= COLON_DASH MAXAFVALUE DBL_COLON term_int_eval PERIOD",
 /* 410 */ "stmt_maxadditive ::= COLON_DASH MAXADDITIVE EQ term_int_eval PERIOD",
 /* 411 */ "stmt_maxadditive ::= COLON_DASH MAXADDITIVE DBL_COLON term_int_eval PERIOD",
 /* 412 */ "stmt_query ::= COLON_DASH QUERY query_lst PERIOD",
 /* 413 */ "query_lst ::= formula_temporal",
 /* 414 */ "query_lst ::= query_maxstep_decl",
 /* 415 */ "query_lst ::= query_label_decl",
 /* 416 */ "query_lst ::= query_lst SEMICOLON formula_temporal",
 /* 417 */ "query_lst ::= query_lst SEMICOLON query_maxstep_decl",
 /* 418 */ "query_lst ::= query_lst SEMICOLON query_label_decl",
 /* 419 */ "query_maxstep_decl ::= MAXSTEP DBL_COLON INTEGER",
 /* 420 */ "query_maxstep_decl ::= MAXSTEP DBL_COLON num_range_eval",
 /* 421 */ "query_label_decl ::= LABEL DBL_COLON INTEGER",
 /* 422 */ "query_label_decl ::= LABEL DBL_COLON IDENTIFIER",
 /* 423 */ "clause_if ::= IF formula",
 /* 424 */ "clause_if ::=",
 /* 425 */ "clause_after ::= AFTER formula",
 /* 426 */ "clause_after ::=",
 /* 427 */ "clause_ifcons ::= IFCONS formula",
 /* 428 */ "clause_ifcons ::=",
 /* 429 */ "clause_unless ::= UNLESS atomic_formula_anon",
 /* 430 */ "clause_unless ::=",
 /* 431 */ "clause_where ::= WHERE formula_no_const",
 /* 432 */ "clause_where ::=",
 /* 433 */ "rate_decl ::= DDT BRACKET_L constant BRACKET_R EQ term IF MODE EQ INTEGER PERIOD",
 /* 434 */ "alwayst_stmt ::= ALWAYST formula IF MODE EQ INTEGER PERIOD",
 /* 435 */ "stmt_law ::= law_basic",
 /* 436 */ "stmt_law ::= law_caused",
 /* 437 */ "stmt_law ::= law_pcaused",
 /* 438 */ "stmt_law ::= law_impl",
 /* 439 */ "stmt_law ::= law_causes",
 /* 440 */ "stmt_law ::= law_increments",
 /* 441 */ "stmt_law ::= law_decrements",
 /* 442 */ "stmt_law ::= law_mcause",
 /* 443 */ "stmt_law ::= law_always",
 /* 444 */ "stmt_law ::= law_constraint",
 /* 445 */ "stmt_law ::= law_impossible",
 /* 446 */ "stmt_law ::= law_never",
 /* 447 */ "stmt_law ::= law_default",
 /* 448 */ "stmt_law ::= law_exogenous",
 /* 449 */ "stmt_law ::= law_inertial",
 /* 450 */ "stmt_law ::= law_nonexecutable",
 /* 451 */ "stmt_law ::= law_rigid",
 /* 452 */ "stmt_law ::= law_observed",
 /* 453 */ "stmt_law ::= law_temporal_constraint",
 /* 454 */ "law_basic ::= head_formula clause_if clause_ifcons clause_after clause_unless clause_where PERIOD",
 /* 455 */ "law_caused ::= CAUSED head_formula clause_if clause_ifcons clause_after clause_unless clause_where PERIOD",
 /* 456 */ "law_pcaused ::= POSSIBLY_CAUSED head_formula clause_if clause_ifcons clause_after clause_unless clause_where PERIOD",
 /* 457 */ "law_impl ::= head_formula ARROW_LDASH formula clause_where PERIOD",
 /* 458 */ "law_impl ::= ARROW_LDASH formula clause_where PERIOD",
 /* 459 */ "law_causes ::= atomic_formula CAUSES head_formula clause_if clause_unless clause_where PERIOD",
 /* 460 */ "law_increments ::= atomic_formula INCREMENTS constant BY term clause_if clause_unless clause_where PERIOD",
 /* 461 */ "law_decrements ::= atomic_formula DECREMENTS constant BY term clause_if clause_unless clause_where PERIOD",
 /* 462 */ "law_mcause ::= atomic_formula MAY_CAUSE head_formula clause_if clause_unless clause_where PERIOD",
 /* 463 */ "law_always ::= ALWAYS formula clause_after clause_unless clause_where PERIOD",
 /* 464 */ "law_constraint ::= CONSTRAINT formula clause_after clause_unless clause_where PERIOD",
 /* 465 */ "law_impossible ::= IMPOSSIBLE formula clause_after clause_unless clause_where PERIOD",
 /* 466 */ "law_never ::= NEVER formula clause_after clause_unless clause_where PERIOD",
 /* 467 */ "law_default ::= DEFAULT atomic_head_formula clause_if clause_ifcons clause_after clause_unless clause_where PERIOD",
 /* 468 */ "law_exogenous ::= EXOGENOUS constant clause_if clause_ifcons clause_after clause_unless clause_where PERIOD",
 /* 469 */ "law_inertial ::= INERTIAL constant clause_if clause_ifcons clause_after clause_unless clause_where PERIOD",
 /* 470 */ "law_nonexecutable ::= NONEXECUTABLE formula clause_if clause_unless clause_where PERIOD",
 /* 471 */ "law_rigid ::= RIGID constant clause_where PERIOD",
 /* 472 */ "law_observed ::= OBSERVED atomic_head_formula AT term_int_eval PERIOD",
 /* 473 */ "law_temporal_constraint ::= CONSTRAINT formula AT term_int_eval PERIOD",
 /* 474 */ "stmt_code_blk ::= ASP_GR",
 /* 475 */ "stmt_code_blk ::= ASP_CP",
 /* 476 */ "stmt_code_blk ::= F2LP_GR",
 /* 477 */ "stmt_code_blk ::= F2LP_CP",
 /* 478 */ "stmt_code_blk ::= LUA_GR",
 /* 479 */ "stmt_code_blk ::= LUA_CP",
 /* 480 */ "stmt_code_blk ::= PYTHON_GR",
 /* 481 */ "stmt_code_blk ::= PYTHON_CP",
};
#endif /* NDEBUG */


#if YYSTACKDEPTH<=0
/*
** Try to increase the size of the parser stack.
*/
static void yyGrowStack(yyParser *p){
  int newSize;
  yyStackEntry *pNew;

  newSize = p->yystksz*2 + 100;
  pNew = realloc(p->yystack, newSize*sizeof(pNew[0]));
  if( pNew ){
    p->yystack = pNew;
    p->yystksz = newSize;
#ifndef NDEBUG
    if( yyTraceFILE ){
      fprintf(yyTraceFILE,"%sStack grows to %d entries!\n",
              yyTracePrompt, p->yystksz);
    }
#endif
  }
}
#endif

/* 
** This function allocates a new parser.
** The only argument is a pointer to a function which works like
** malloc.
**
** Inputs:
** A pointer to the function used to allocate memory.
**
** Outputs:
** A pointer to a parser.  This pointer is used in subsequent calls
** to lemon_parser and lemon_parserFree.
*/
void *lemon_parserAlloc(void *(*mallocProc)(size_t)){
  yyParser *pParser;
  pParser = (yyParser*)(*mallocProc)( (size_t)sizeof(yyParser) );
  if( pParser ){
    pParser->yyidx = -1;
#ifdef YYTRACKMAXSTACKDEPTH
    pParser->yyidxMax = 0;
#endif
#if YYSTACKDEPTH<=0
    pParser->yystack = NULL;
    pParser->yystksz = 0;
    yyGrowStack(pParser);
#endif
	pParser->yylookmajor = YYNOCODE;
	pParser->yylookminor = yyzerominor;
	pParser->yysyntaxerr = 0;
  }
  return pParser;
}

/* The following function deletes the value associated with a
** symbol.  The symbol can be either a terminal or nonterminal.
** "yymajor" is the symbol code, and "yypminor" is a pointer to
** the value.
*/
static void yy_destructor(
  yyParser *yypParser,    /* The parser */
  YYCODETYPE yymajor,     /* Type code for object to destroy */
  YYMINORTYPE *yypminor   /* The object to be destroyed */
){
  lemon_parserARG_FETCH;
  switch( yymajor ){
    /* Here is inserted the actions which take place when a
    ** terminal or non-terminal is destroyed.  This can happen
    ** when the symbol is popped from the stack during a
    ** reduce or during error processing or when a parser is 
    ** being destroyed before it is finished parsing.
    **
    ** Note: during a reduce, the only symbols destroyed are those
    ** which appear on the RHS of the rule, but which are not used
    ** inside the C code.
    */
      /* TERMINAL Destructor */
    case 1: /* INTEGER */
    case 2: /* FLOAT */
    case 3: /* IDENTIFIER */
    case 4: /* POUND_IDENTIFIER */
    case 5: /* POUND_INTEGER */
    case 6: /* AT_IDENTIFIER */
    case 7: /* STRING_LITERAL */
    case 8: /* ASP_GR */
    case 9: /* ASP_CP */
    case 10: /* LUA_GR */
    case 11: /* LUA_CP */
    case 12: /* PYTHON_GR */
    case 13: /* PYTHON_CP */
    case 14: /* F2LP_GR */
    case 15: /* F2LP_CP */
    case 16: /* COMMENT */
    case 17: /* CONSTANTS */
    case 18: /* INCLUDE */
    case 19: /* MACROS */
    case 20: /* OBJECTS */
    case 21: /* QUERY */
    case 22: /* SHOW */
    case 23: /* SORTS */
    case 24: /* VARIABLES */
    case 25: /* ABACTION */
    case 26: /* ACTION */
    case 27: /* ADDITIVEACTION */
    case 28: /* ADDITIVEFLUENT */
    case 29: /* AFTER */
    case 30: /* ALL */
    case 31: /* ALWAYS */
    case 32: /* ALWAYST */
    case 33: /* ASSUMING */
    case 34: /* ATTRIBUTE */
    case 35: /* BY */
    case 36: /* CAUSED */
    case 37: /* CAUSES */
    case 38: /* IMPOSSIBLE */
    case 39: /* CONSTRAINT */
    case 40: /* DECREMENTS */
    case 41: /* DEFAULT */
    case 42: /* EXTERNALACTION */
    case 43: /* EXOGENOUS */
    case 44: /* EXOGENOUSACTION */
    case 45: /* DDT */
    case 46: /* IF */
    case 47: /* MODE */
    case 48: /* IFCONS */
    case 49: /* INCREMENTS */
    case 50: /* INERTIAL */
    case 51: /* INERTIALFLUENT */
    case 52: /* LABEL */
    case 53: /* MAY_CAUSE */
    case 54: /* MAXADDITIVE */
    case 55: /* MAXAFVALUE */
    case 56: /* MAXSTEP */
    case 57: /* NEVER */
    case 58: /* NOCONCURRENCY */
    case 59: /* STRONG_NOCONCURRENCY */
    case 60: /* NONEXECUTABLE */
    case 61: /* OF */
    case 62: /* POSSIBLY_CAUSED */
    case 63: /* REAL */
    case 64: /* CONTINUOUS */
    case 65: /* RIGID */
    case 66: /* SDFLUENT */
    case 67: /* SIMPLEFLUENT */
    case 68: /* EXTERNALFLUENT */
    case 69: /* UNLESS */
    case 70: /* WHERE */
    case 71: /* FALSE */
    case 72: /* TRUE */
    case 73: /* AT */
    case 74: /* BRACKET_L */
    case 75: /* BRACKET_R */
    case 76: /* COLON_DASH */
    case 77: /* CBRACKET_L */
    case 78: /* CBRACKET_R */
    case 79: /* PAREN_L */
    case 80: /* PAREN_R */
    case 81: /* PERIOD */
    case 82: /* MACRO_STRING */
    case 83: /* TILDE */
    case 84: /* DBL_COLON */
    case 85: /* ARROW_LEQ */
    case 86: /* ARROW_REQ */
    case 87: /* ARROW_LDASH */
    case 88: /* COLON */
    case 89: /* EQ */
    case 90: /* DBL_EQ */
    case 91: /* NEQ */
    case 92: /* NOT_EQ */
    case 93: /* LTHAN */
    case 94: /* GTHAN */
    case 95: /* LTHAN_EQ */
    case 96: /* GTHAN_EQ */
    case 97: /* DBL_PERIOD */
    case 98: /* BIG_CONJ */
    case 99: /* BIG_DISJ */
    case 100: /* POUND */
    case 101: /* SEMICOLON */
    case 102: /* EQUIV */
    case 103: /* IMPL */
    case 104: /* ARROW_RDASH */
    case 105: /* DBL_PLUS */
    case 106: /* PIPE */
    case 107: /* DBL_GTHAN */
    case 108: /* DBL_LTHAN */
    case 109: /* AMP */
    case 110: /* COMMA */
    case 111: /* DBL_AMP */
    case 112: /* NOT */
    case 113: /* DASH */
    case 114: /* PLUS */
    case 115: /* STAR */
    case 116: /* INT_DIV */
    case 117: /* MOD */
    case 118: /* ABS */
    case 119: /* CARROT */
    case 120: /* UMINUS */
    case 121: /* PREC_4 */
    case 122: /* PREC_3 */
    case 123: /* PREC_2 */
    case 124: /* PREC_1 */
    case 125: /* PREC_0 */
    case 126: /* EOF */
    case 127: /* ERR_IO */
    case 128: /* ERR_UNKNOWN_SYMBOL */
    case 129: /* ERR_UNTERMINATED_STRING */
    case 130: /* ERR_UNTERMINATED_ASP */
    case 131: /* ERR_UNTERMINATED_LUA */
    case 132: /* ERR_UNTERMINATED_PYTHON */
    case 133: /* ERR_UNTERMINATED_F2LP */
    case 134: /* ERR_UNTERMINATED_BLK_COMMENT */
    case 135: /* ERR_SYNTAX */
    case 136: /* ERR_PAREN_MISMATCH */
    case 137: /* ARG */
    case 138: /* NOOP */
    case 139: /* CONSTANT_ID */
    case 140: /* VARIABLE_ID */
    case 141: /* OBJECT_ID */
    case 142: /* SIN */
    case 143: /* COS */
    case 144: /* TAN */
    case 145: /* HIDE */
    case 146: /* OBSERVED */
{
#line 210 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy0));								
#line 2721 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 148: /* start */
    case 149: /* statement_lst */
    case 174: /* undeclared */
{
#line 220 "bcplus/parser/detail/lemon_parser.y"
 /* Intentionally left blank */			
#line 2730 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 150: /* statement */
    case 156: /* stmt_code_blk */
    case 157: /* stmt_law */
    case 158: /* stmt_show */
    case 159: /* stmt_hide */
    case 162: /* stmt_maxafvalue */
    case 163: /* stmt_maxadditive */
{
#line 224 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy76));								
#line 2743 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 151: /* stmt_macro_def */
{
#line 245 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy243));								
#line 2750 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 152: /* stmt_constant_def */
{
#line 247 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy55));								
#line 2757 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 153: /* stmt_object_def */
{
#line 249 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy24));								
#line 2764 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 154: /* stmt_variable_def */
{
#line 251 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy19));								
#line 2771 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 155: /* stmt_sort_def */
{
#line 253 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy333));								
#line 2778 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 160: /* stmt_noconcurrency */
{
#line 263 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy379));								
#line 2785 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 161: /* stmt_strong_noconcurrency */
{
#line 265 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy494));								
#line 2792 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 164: /* stmt_query */
{
#line 271 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy136));								
#line 2799 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 165: /* rate_decl */
{
#line 2971 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy175));									
#line 2806 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 166: /* alwayst_stmt */
{
#line 2982 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy416));									
#line 2813 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 167: /* base_elem */
    case 168: /* base_elem_no_const */
    case 176: /* term */
    case 179: /* term_no_const */
    case 181: /* term_strong */
    case 182: /* term_strong_candidate */
    case 183: /* term_no_const_strong */
    case 186: /* term_integral */
    case 203: /* term_temporal */
    case 204: /* term_temporal_strong */
    case 205: /* term_temporal_strong_candidate */
    case 206: /* constant_temporal */
{
#line 307 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy39));								
#line 2831 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 169: /* constant */
    case 177: /* constant_one_const */
    case 180: /* const_anon */
{
#line 311 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy189));								
#line 2840 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 170: /* object */
    case 171: /* object_nullary */
{
#line 313 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy418));								
#line 2848 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 172: /* variable */
{
#line 317 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy195));								
#line 2855 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 173: /* lua */
{
#line 319 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy237));								
#line 2862 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 175: /* term_lst */
    case 178: /* term_no_const_lst */
{
#line 323 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy457));								
#line 2870 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 184: /* num_range */
{
#line 734 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy107));								
#line 2877 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 185: /* num_range_eval */
{
#line 736 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy1));								
#line 2884 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 187: /* term_int_eval */
{
#line 740 "bcplus/parser/detail/lemon_parser.y"
 /* Initially left Blank */				
#line 2891 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 188: /* formula */
    case 189: /* formula_base */
    case 190: /* comparison */
    case 193: /* formula_card */
    case 195: /* formula_no_const */
    case 196: /* formula_no_const_base */
    case 197: /* comparison_no_const */
    case 207: /* formula_temporal */
    case 208: /* formula_temporal_base */
    case 209: /* comparison_temporal */
    case 211: /* formula_temporal_card */
    case 212: /* head_formula */
{
#line 841 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy179));								
#line 2909 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 191: /* atomic_formula */
    case 194: /* atomic_formula_anon */
    case 198: /* atomic_formula_one_const */
    case 213: /* atomic_head_formula */
{
#line 847 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy274));								
#line 2919 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 192: /* formula_quant */
    case 210: /* formula_temporal_quant */
{
#line 849 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy387));								
#line 2927 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 199: /* quant_lst */
{
#line 1028 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy445));								
#line 2934 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 200: /* quant_op */
{
#line 1030 "bcplus/parser/detail/lemon_parser.y"
 /* Intentionally left blank */			
#line 2941 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 201: /* card_var_lst */
    case 202: /* card_var_lst_inner */
{
#line 1067 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy117));								
#line 2949 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 214: /* formula_smpl_card */
{
#line 1376 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy393));								
#line 2956 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 215: /* macro_def_lst */
{
#line 1440 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy5));                              
#line 2963 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 216: /* macro_bnd */
{
#line 1442 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy437));                              
#line 2970 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 217: /* macro_args */
{
#line 1444 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy214));                              
#line 2977 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 218: /* macro_arg */
{
#line 1446 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy193));                              
#line 2984 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 219: /* sort_lst */
{
#line 1536 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy423));							
#line 2991 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 220: /* sort */
    case 221: /* sort_id_nr */
    case 222: /* sort_nr */
    case 223: /* sort_id */
{
#line 1538 "bcplus/parser/detail/lemon_parser.y"
 /* Intentionally left blank */		
#line 3001 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 224: /* constant_bnd_lst */
    case 225: /* constant_bnd */
{
#line 1647 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy451));									
#line 3009 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 226: /* constant_dcl_lst */
{
#line 1651 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy368));									
#line 3016 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 227: /* constant_dcl_type */
{
#line 1653 "bcplus/parser/detail/lemon_parser.y"
 /* Intentionally left blank */				
#line 3023 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 228: /* attrib_spec */
{
#line 1655 "bcplus/parser/detail/lemon_parser.y"
 /* Intentionally left blank */				
#line 3030 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 229: /* object_bnd_lst */
{
#line 2265 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy419));									
#line 3037 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 230: /* object_bnd */
{
#line 2267 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy332));									
#line 3044 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 231: /* object_lst */
    case 232: /* object_spec */
{
#line 2269 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy323));									
#line 3052 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 233: /* variable_bnd_lst */
    case 234: /* variable_bnd */
{
#line 2415 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy424));									
#line 3060 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 235: /* variable_lst */
{
#line 2419 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy280));									
#line 3067 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 236: /* sort_bnd_lst */
    case 237: /* sort_bnd */
    case 238: /* sort_dcl_lst */
{
#line 2515 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy523));									
#line 3076 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 239: /* show_lst */
{
#line 2619 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy331));									
#line 3083 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 240: /* show_elem */
    case 248: /* clause_unless */
{
#line 2621 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy274));									
#line 3091 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 241: /* query_lst */
{
#line 2773 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy305).l); DEALLOC((yypminor->yy305).maxstep); DEALLOC((yypminor->yy305).label);	
#line 3098 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 242: /* query_maxstep_decl */
{
#line 2775 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy1));												
#line 3105 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 244: /* query_label_Decl */
{
#line 2777 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy0));												
#line 3112 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 245: /* clause_if */
    case 246: /* clause_after */
    case 247: /* clause_ifcons */
    case 249: /* clause_where */
{
#line 2931 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy179));									
#line 3122 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 250: /* law_basic */
    case 251: /* law_caused */
    case 252: /* law_pcaused */
    case 253: /* law_impl */
    case 254: /* law_causes */
    case 255: /* law_increments */
    case 256: /* law_decrements */
    case 257: /* law_mcause */
    case 258: /* law_always */
    case 259: /* law_constraint */
    case 260: /* law_impossible */
    case 261: /* law_never */
    case 262: /* law_default */
    case 263: /* law_exogenous */
    case 264: /* law_inertial */
    case 265: /* law_nonexecutable */
    case 266: /* law_rigid */
    case 267: /* law_observed */
    case 268: /* law_temporal_constraint */
{
#line 2994 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy76));									
#line 3147 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    default:  break;   /* If no destructor action specified: do nothing */
  }
  lemon_parserARG_STORE;
}

/*
** Pop the parser's stack once.
**
** If there is a destructor routine associated with the token which
** is popped from the stack, then call it.
**
** Return the major token number for the symbol popped.
*/
static int yy_pop_parser_stack(yyParser *pParser){
  YYCODETYPE yymajor;
  yyStackEntry *yytos = &pParser->yystack[pParser->yyidx];

  if( pParser->yyidx<0 ) return 0;
#ifndef NDEBUG
  if( yyTraceFILE && pParser->yyidx>=0 ){
    fprintf(yyTraceFILE,"%sPopping %s\n",
      yyTracePrompt,
      yyTokenName[yytos->major]);
  }
#endif
  yymajor = yytos->major;
  yy_destructor(pParser, yymajor, &yytos->minor);
  pParser->yyidx--;
  return yymajor;
}

/* 
** Deallocate and destroy a parser.  Destructors are all called for
** all stack elements before shutting the parser down.
**
** Inputs:
** <ul>
** <li>  A pointer to the parser.  This should be a pointer
**       obtained from lemon_parserAlloc.
** <li>  A pointer to a function used to reclaim memory obtained
**       from malloc.
** </ul>
*/
void lemon_parserFree(
  void *p,                    /* The parser to be deleted */
  void (*freeProc)(void*)     /* Function used to reclaim memory */
){
  yyParser *pParser = (yyParser*)p;
  if( pParser==0 ) return;
  if( pParser->yylookmajor != YYNOCODE ) yy_destructor(pParser, (YYCODETYPE)pParser->yylookmajor, &pParser->yylookminor);
  while( pParser->yyidx>=0 ) yy_pop_parser_stack(pParser);
#if YYSTACKDEPTH<=0
  free(pParser->yystack);
#endif
  (*freeProc)((void*)pParser);
}

/*
** Return the peak depth of the stack for a parser.
*/
#ifdef YYTRACKMAXSTACKDEPTH
int lemon_parserStackPeak(void *p){
  yyParser *pParser = (yyParser*)p;
  return pParser->yyidxMax;
}
#endif

/*
** Find the appropriate action for a parser given the terminal
** look-ahead token iLookAhead.
**
** If the look-ahead token is YYNOCODE, then check to see if the action is
** independent of the look-ahead.  If it is, return the action, otherwise
** return YY_NO_ACTION.
*/
static int yy_find_shift_action(
  yyParser *pParser,        /* The parser */
  YYCODETYPE iLookAhead     /* The look-ahead token */
){
  int i;
  int stateno = pParser->yystack[pParser->yyidx].stateno;
 
  if( stateno>YY_SHIFT_COUNT
   || (i = yy_shift_ofst[stateno])==YY_SHIFT_USE_DFLT ){
    return yy_default[stateno];
  }
  assert( iLookAhead!=YYNOCODE );
  i += iLookAhead;
  if( i<0 || i>=YY_ACTTAB_COUNT || yy_lookahead[i]!=iLookAhead ){
    if( iLookAhead>0 ){
#ifdef YYFALLBACK
      YYCODETYPE iFallback;            /* Fallback token */
      if( iLookAhead<sizeof(yyFallback)/sizeof(yyFallback[0])
             && (iFallback = yyFallback[iLookAhead])!=0 ){
#ifndef NDEBUG
        if( yyTraceFILE ){
          fprintf(yyTraceFILE, "%sFALLBACK %s => %s\n",
             yyTracePrompt, yyTokenName[iLookAhead], yyTokenName[iFallback]);
        }
#endif
        return yy_find_shift_action(pParser, iFallback);
      }
#endif
#ifdef YYWILDCARD
      {
        int j = i - iLookAhead + YYWILDCARD;
        if( 
#if YY_SHIFT_MIN+YYWILDCARD<0
          j>=0 &&
#endif
#if YY_SHIFT_MAX+YYWILDCARD>=YY_ACTTAB_COUNT
          j<YY_ACTTAB_COUNT &&
#endif
          yy_lookahead[j]==YYWILDCARD
        ){
#ifndef NDEBUG
          if( yyTraceFILE ){
            fprintf(yyTraceFILE, "%sWILDCARD %s => %s\n",
               yyTracePrompt, yyTokenName[iLookAhead], yyTokenName[YYWILDCARD]);
          }
#endif /* NDEBUG */
          return yy_action[j];
        }
      }
#endif /* YYWILDCARD */
    }
    return yy_default[stateno];
  }else{
    return yy_action[i];
  }
}

/*
** Find the appropriate action for a parser given the non-terminal
** look-ahead token iLookAhead.
**
** If the look-ahead token is YYNOCODE, then check to see if the action is
** independent of the look-ahead.  If it is, return the action, otherwise
** return YY_NO_ACTION.
*/
static int yy_find_reduce_action(
  int stateno,              /* Current state number */
  YYCODETYPE iLookAhead     /* The look-ahead token */
){
  int i;
#ifdef YYERRORSYMBOL
  if( stateno>YY_REDUCE_COUNT ){
    return yy_default[stateno];
  }
#else
  assert( stateno<=YY_REDUCE_COUNT );
#endif
  i = yy_reduce_ofst[stateno];
  assert( i!=YY_REDUCE_USE_DFLT );
  if (iLookAhead == YYNOCODE) return YY_NO_ACTION;
  assert( iLookAhead!=YYNOCODE );
  i += iLookAhead;
#ifdef YYERRORSYMBOL
  if( i<0 || i>=YY_ACTTAB_COUNT || yy_lookahead[i]!=iLookAhead ){
    return yy_default[stateno];
  }
#else
  assert( i>=0 && i<YY_ACTTAB_COUNT );
  assert( yy_lookahead[i]==iLookAhead );
#endif
  return yy_action[i];
}

/*
** The following routine is called if the stack overflows.
*/
static void yyStackOverflow(yyParser *yypParser /*, YYMINORTYPE *yypMinor */){
   lemon_parserARG_FETCH;
   yypParser->yyidx--;
#ifndef NDEBUG
   if( yyTraceFILE ){
     fprintf(yyTraceFILE,"%sStack Overflow!\n",yyTracePrompt);
   }
#endif
   while( yypParser->yyidx>=0 ) yy_pop_parser_stack(yypParser);
   /* Here code is inserted which will execute if the parser
   ** stack every overflows */
   lemon_parserARG_STORE; /* Suppress warning about unused %extra_argument var */
}

/*
** Perform a shift action.
*/
static void yy_shift(
  yyParser *yypParser,          /* The parser to be shifted */
  int yyNewState,               /* The new state to shift in */
  int yyMajor,                  /* The major token to shift in */
  YYMINORTYPE *yypMinor         /* Pointer to the minor token to shift in */
){
  yyStackEntry *yytos;
  yypParser->yyidx++;
#ifdef YYTRACKMAXSTACKDEPTH
  if( yypParser->yyidx>yypParser->yyidxMax ){
    yypParser->yyidxMax = yypParser->yyidx;
  }
#endif
#if YYSTACKDEPTH>0 
  if( yypParser->yyidx>=YYSTACKDEPTH ){
    yyStackOverflow(yypParser/*, yypMinor */);
    return;
  }
#else
  if( yypParser->yyidx>=yypParser->yystksz ){
    yyGrowStack(yypParser);
    if( yypParser->yyidx>=yypParser->yystksz ){
      yyStackOverflow(yypParser/*, yypMinor */);
      return;
    }
  }
#endif
  yytos = &yypParser->yystack[yypParser->yyidx];
  yytos->stateno = (YYACTIONTYPE)yyNewState;
  yytos->major = (YYCODETYPE)yyMajor;
  yytos->minor = *yypMinor;
#ifndef NDEBUG
  if( yyTraceFILE && yypParser->yyidx>0 ){
    int i;
    fprintf(yyTraceFILE,"%sShift %d\n",yyTracePrompt,yyNewState);
    fprintf(yyTraceFILE,"%sStack:",yyTracePrompt);
    for(i=1; i<=yypParser->yyidx; i++)
      fprintf(yyTraceFILE," %s",yyTokenName[yypParser->yystack[i].major]);
    fprintf(yyTraceFILE,"\n");
  }
#endif
}

/* The following table contains information about every rule that
** is used during the reduce.
*/
static const struct {
  YYCODETYPE lhs;         /* Symbol on the left-hand side of the rule */
  unsigned char nrhs;     /* Number of right-hand side symbols in the rule */
} yyRuleInfo[] = {
  { 148, 2 },
  { 149, 0 },
  { 149, 2 },
  { 149, 2 },
  { 150, 1 },
  { 150, 1 },
  { 150, 1 },
  { 150, 1 },
  { 150, 1 },
  { 150, 1 },
  { 150, 1 },
  { 150, 1 },
  { 150, 1 },
  { 150, 1 },
  { 150, 1 },
  { 150, 1 },
  { 150, 1 },
  { 150, 1 },
  { 150, 1 },
  { 150, 1 },
  { 167, 1 },
  { 167, 1 },
  { 168, 1 },
  { 168, 1 },
  { 168, 1 },
  { 169, 4 },
  { 169, 1 },
  { 169, 1 },
  { 180, 1 },
  { 180, 4 },
  { 170, 4 },
  { 170, 1 },
  { 171, 1 },
  { 170, 1 },
  { 172, 1 },
  { 173, 4 },
  { 173, 1 },
  { 173, 3 },
  { 174, 4 },
  { 174, 1 },
  { 175, 1 },
  { 175, 3 },
  { 177, 4 },
  { 177, 1 },
  { 178, 1 },
  { 178, 3 },
  { 176, 1 },
  { 176, 1 },
  { 176, 1 },
  { 176, 1 },
  { 176, 3 },
  { 176, 1 },
  { 176, 1 },
  { 176, 1 },
  { 176, 1 },
  { 176, 1 },
  { 176, 2 },
  { 176, 2 },
  { 176, 4 },
  { 176, 4 },
  { 176, 4 },
  { 176, 3 },
  { 176, 3 },
  { 176, 3 },
  { 176, 3 },
  { 176, 3 },
  { 181, 1 },
  { 181, 1 },
  { 181, 1 },
  { 181, 1 },
  { 181, 3 },
  { 181, 1 },
  { 181, 1 },
  { 181, 1 },
  { 181, 2 },
  { 181, 2 },
  { 181, 4 },
  { 181, 4 },
  { 181, 4 },
  { 182, 2 },
  { 181, 3 },
  { 181, 3 },
  { 181, 3 },
  { 181, 3 },
  { 181, 3 },
  { 181, 3 },
  { 181, 3 },
  { 181, 3 },
  { 181, 3 },
  { 181, 3 },
  { 181, 3 },
  { 181, 3 },
  { 181, 3 },
  { 181, 3 },
  { 181, 3 },
  { 183, 1 },
  { 183, 1 },
  { 183, 1 },
  { 183, 1 },
  { 183, 3 },
  { 183, 1 },
  { 183, 1 },
  { 183, 1 },
  { 183, 1 },
  { 183, 2 },
  { 183, 2 },
  { 183, 3 },
  { 183, 3 },
  { 183, 3 },
  { 183, 3 },
  { 183, 3 },
  { 179, 1 },
  { 179, 1 },
  { 179, 1 },
  { 179, 1 },
  { 179, 3 },
  { 179, 1 },
  { 179, 1 },
  { 179, 1 },
  { 179, 1 },
  { 179, 1 },
  { 179, 1 },
  { 179, 2 },
  { 179, 2 },
  { 179, 3 },
  { 179, 3 },
  { 179, 3 },
  { 179, 3 },
  { 179, 3 },
  { 186, 1 },
  { 186, 3 },
  { 186, 1 },
  { 186, 1 },
  { 186, 1 },
  { 186, 1 },
  { 186, 1 },
  { 186, 2 },
  { 186, 2 },
  { 186, 3 },
  { 186, 3 },
  { 186, 3 },
  { 186, 3 },
  { 186, 3 },
  { 184, 3 },
  { 185, 3 },
  { 187, 1 },
  { 187, 3 },
  { 187, 2 },
  { 187, 2 },
  { 187, 3 },
  { 187, 3 },
  { 187, 3 },
  { 187, 3 },
  { 187, 3 },
  { 188, 1 },
  { 188, 3 },
  { 188, 2 },
  { 188, 2 },
  { 188, 3 },
  { 188, 3 },
  { 188, 3 },
  { 188, 3 },
  { 188, 3 },
  { 188, 3 },
  { 189, 1 },
  { 189, 1 },
  { 189, 1 },
  { 189, 1 },
  { 189, 1 },
  { 189, 1 },
  { 190, 3 },
  { 190, 3 },
  { 190, 3 },
  { 190, 3 },
  { 190, 3 },
  { 190, 3 },
  { 190, 3 },
  { 190, 3 },
  { 190, 3 },
  { 190, 3 },
  { 190, 3 },
  { 190, 3 },
  { 190, 3 },
  { 190, 3 },
  { 190, 3 },
  { 190, 3 },
  { 190, 3 },
  { 190, 3 },
  { 190, 3 },
  { 190, 3 },
  { 191, 1 },
  { 191, 2 },
  { 191, 3 },
  { 194, 1 },
  { 194, 1 },
  { 194, 2 },
  { 194, 3 },
  { 195, 1 },
  { 195, 3 },
  { 195, 2 },
  { 195, 2 },
  { 195, 3 },
  { 195, 3 },
  { 195, 3 },
  { 195, 3 },
  { 195, 3 },
  { 195, 3 },
  { 196, 1 },
  { 196, 1 },
  { 196, 1 },
  { 197, 3 },
  { 197, 3 },
  { 197, 3 },
  { 197, 3 },
  { 197, 3 },
  { 197, 3 },
  { 197, 3 },
  { 198, 1 },
  { 198, 2 },
  { 198, 3 },
  { 192, 5 },
  { 199, 2 },
  { 199, 3 },
  { 200, 1 },
  { 200, 1 },
  { 193, 4 },
  { 193, 5 },
  { 193, 5 },
  { 193, 6 },
  { 193, 3 },
  { 193, 4 },
  { 193, 4 },
  { 193, 5 },
  { 201, 2 },
  { 202, 1 },
  { 202, 3 },
  { 203, 1 },
  { 203, 1 },
  { 203, 1 },
  { 203, 1 },
  { 203, 3 },
  { 203, 1 },
  { 203, 1 },
  { 203, 1 },
  { 203, 1 },
  { 203, 1 },
  { 203, 1 },
  { 203, 2 },
  { 203, 2 },
  { 203, 3 },
  { 203, 3 },
  { 203, 3 },
  { 203, 3 },
  { 203, 3 },
  { 203, 3 },
  { 204, 1 },
  { 204, 1 },
  { 204, 1 },
  { 204, 1 },
  { 204, 3 },
  { 204, 1 },
  { 204, 1 },
  { 204, 1 },
  { 204, 3 },
  { 204, 2 },
  { 204, 2 },
  { 204, 3 },
  { 204, 3 },
  { 204, 3 },
  { 204, 3 },
  { 204, 3 },
  { 207, 1 },
  { 207, 3 },
  { 207, 2 },
  { 207, 2 },
  { 207, 3 },
  { 207, 3 },
  { 207, 3 },
  { 207, 3 },
  { 207, 3 },
  { 207, 3 },
  { 207, 3 },
  { 208, 1 },
  { 208, 1 },
  { 208, 1 },
  { 208, 1 },
  { 208, 1 },
  { 208, 1 },
  { 209, 3 },
  { 209, 3 },
  { 209, 3 },
  { 209, 3 },
  { 209, 3 },
  { 209, 3 },
  { 209, 3 },
  { 210, 5 },
  { 211, 4 },
  { 211, 5 },
  { 211, 5 },
  { 211, 6 },
  { 211, 3 },
  { 211, 4 },
  { 211, 4 },
  { 211, 5 },
  { 212, 3 },
  { 212, 3 },
  { 212, 1 },
  { 212, 1 },
  { 212, 1 },
  { 212, 1 },
  { 212, 1 },
  { 213, 1 },
  { 213, 2 },
  { 214, 4 },
  { 214, 5 },
  { 214, 5 },
  { 214, 6 },
  { 214, 3 },
  { 214, 4 },
  { 214, 4 },
  { 214, 5 },
  { 151, 4 },
  { 215, 1 },
  { 215, 3 },
  { 216, 6 },
  { 216, 3 },
  { 217, 1 },
  { 217, 3 },
  { 218, 1 },
  { 218, 1 },
  { 219, 1 },
  { 219, 3 },
  { 220, 1 },
  { 220, 2 },
  { 220, 2 },
  { 220, 3 },
  { 220, 3 },
  { 220, 3 },
  { 221, 1 },
  { 221, 1 },
  { 222, 1 },
  { 223, 1 },
  { 152, 4 },
  { 224, 1 },
  { 224, 3 },
  { 225, 6 },
  { 225, 9 },
  { 225, 6 },
  { 225, 3 },
  { 225, 6 },
  { 225, 3 },
  { 225, 5 },
  { 225, 8 },
  { 226, 1 },
  { 226, 4 },
  { 226, 3 },
  { 226, 6 },
  { 227, 1 },
  { 227, 1 },
  { 227, 1 },
  { 227, 1 },
  { 227, 1 },
  { 227, 1 },
  { 227, 1 },
  { 227, 1 },
  { 227, 1 },
  { 227, 1 },
  { 227, 1 },
  { 228, 1 },
  { 228, 4 },
  { 228, 7 },
  { 153, 4 },
  { 229, 1 },
  { 229, 3 },
  { 230, 3 },
  { 231, 1 },
  { 231, 3 },
  { 232, 1 },
  { 232, 4 },
  { 232, 1 },
  { 232, 1 },
  { 232, 1 },
  { 154, 4 },
  { 233, 1 },
  { 233, 3 },
  { 234, 3 },
  { 234, 1 },
  { 235, 1 },
  { 235, 3 },
  { 155, 4 },
  { 236, 1 },
  { 236, 3 },
  { 237, 1 },
  { 237, 3 },
  { 237, 3 },
  { 237, 3 },
  { 238, 1 },
  { 238, 3 },
  { 158, 4 },
  { 158, 4 },
  { 159, 4 },
  { 159, 4 },
  { 239, 1 },
  { 239, 3 },
  { 239, 3 },
  { 240, 1 },
  { 160, 2 },
  { 161, 2 },
  { 162, 5 },
  { 162, 5 },
  { 163, 5 },
  { 163, 5 },
  { 164, 4 },
  { 241, 1 },
  { 241, 1 },
  { 241, 1 },
  { 241, 3 },
  { 241, 3 },
  { 241, 3 },
  { 242, 3 },
  { 242, 3 },
  { 243, 3 },
  { 243, 3 },
  { 245, 2 },
  { 245, 0 },
  { 246, 2 },
  { 246, 0 },
  { 247, 2 },
  { 247, 0 },
  { 248, 2 },
  { 248, 0 },
  { 249, 2 },
  { 249, 0 },
  { 165, 11 },
  { 166, 7 },
  { 157, 1 },
  { 157, 1 },
  { 157, 1 },
  { 157, 1 },
  { 157, 1 },
  { 157, 1 },
  { 157, 1 },
  { 157, 1 },
  { 157, 1 },
  { 157, 1 },
  { 157, 1 },
  { 157, 1 },
  { 157, 1 },
  { 157, 1 },
  { 157, 1 },
  { 157, 1 },
  { 157, 1 },
  { 157, 1 },
  { 157, 1 },
  { 250, 7 },
  { 251, 8 },
  { 252, 8 },
  { 253, 5 },
  { 253, 4 },
  { 254, 7 },
  { 255, 9 },
  { 256, 9 },
  { 257, 7 },
  { 258, 6 },
  { 259, 6 },
  { 260, 6 },
  { 261, 6 },
  { 262, 8 },
  { 263, 8 },
  { 264, 8 },
  { 265, 6 },
  { 266, 4 },
  { 267, 5 },
  { 268, 5 },
  { 156, 1 },
  { 156, 1 },
  { 156, 1 },
  { 156, 1 },
  { 156, 1 },
  { 156, 1 },
  { 156, 1 },
  { 156, 1 },
};

/*
** Flags that a syntax error has occurred. 
*/
#define YYERROR { yypParser->yysyntaxerr = 1; yypParser->yyerrcnt = 3; }

static void yy_accept(yyParser*);  /* Forward Declaration */


/*
** Perform a reduce action and the shift that must immediately
** follow the reduce.
*/
static void yy_reduce(
  yyParser *yypParser,         /* The parser */
  int yyruleno                 /* Number of the rule by which to reduce */
){
  int yygoto;                     /* The next state */
  int yyact;                      /* The next action */
  YYMINORTYPE yygotominor;        /* The LHS of the rule reduced */
  yyStackEntry *yymsp;            /* The top of the parser's stack */
  int yysize;                     /* Amount to pop the stack */
  lemon_parserARG_FETCH;
  yymsp = &yypParser->yystack[yypParser->yyidx];
#ifndef NDEBUG
  if( yyTraceFILE && yyruleno>=0 
        && yyruleno<(int)(sizeof(yyRuleName)/sizeof(yyRuleName[0])) ){
    fprintf(yyTraceFILE, "%sReduce [%s].\n", yyTracePrompt,
      yyRuleName[yyruleno]);
  }
#endif /* NDEBUG */

  /* Silence complaints from purify about yygotominor being uninitialized
  ** in some cases when it is copied into the stack after the following
  ** switch.  yygotominor is uninitialized when a rule reduces that does
  ** not set the value of its left-hand side nonterminal.  Leaving the
  ** value of the nonterminal uninitialized is utterly harmless as long
  ** as the value is never used.  So really the only thing this code
  ** accomplishes is to quieten purify.  
  **
  ** 2007-01-16:  The wireshark project (www.wireshark.org) reports that
  ** without this code, their parser segfaults.  I'm not sure what there
  ** parser is doing to make this happen.  This is the second bug report
  ** from wireshark this week.  Clearly they are stressing Lemon in ways
  ** that it has not been previously stressed...  (SQLite ticket #2172)
  */
  /*memset(&yygotominor, 0, sizeof(yygotominor));*/
  yygotominor = yyzerominor;

  switch( yyruleno ){
  /* Beginning here are the reduction cases.  A typical example
  ** follows:
  **   case 0:
  **  #line <lineno> <grammarfile>
  **     { ... }           // User supplied code
  **  #line <lineno> <thisfile>
  **     break;
  */
      case 0: /* start ::= statement_lst EOF */
#line 226 "bcplus/parser/detail/lemon_parser.y"
{
  yy_destructor(yypParser,126,&yymsp[0].minor);
}
#line 3934 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 3: /* statement_lst ::= statement_lst statement */
#line 231 "bcplus/parser/detail/lemon_parser.y"
{
			ref_ptr<Statement> ptr = yymsp[0].minor.yy76;
			yymsp[0].minor.yy76  = NULL;
			parser->_handle_stmt(ptr);
		}
#line 3943 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 4: /* statement ::= stmt_macro_def */
#line 274 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy76 = yymsp[0].minor.yy243; }
#line 3948 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 5: /* statement ::= stmt_constant_def */
#line 275 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy76 = yymsp[0].minor.yy55; }
#line 3953 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 6: /* statement ::= stmt_object_def */
#line 276 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy76 = yymsp[0].minor.yy24; }
#line 3958 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 7: /* statement ::= stmt_variable_def */
#line 277 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy76 = yymsp[0].minor.yy19; }
#line 3963 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 8: /* statement ::= stmt_sort_def */
#line 278 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy76 = yymsp[0].minor.yy333; }
#line 3968 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 9: /* statement ::= stmt_code_blk */
      case 10: /* statement ::= stmt_law */ yytestcase(yyruleno==10);
      case 13: /* statement ::= stmt_show */ yytestcase(yyruleno==13);
      case 14: /* statement ::= stmt_hide */ yytestcase(yyruleno==14);
      case 17: /* statement ::= stmt_maxafvalue */ yytestcase(yyruleno==17);
      case 18: /* statement ::= stmt_maxadditive */ yytestcase(yyruleno==18);
#line 279 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy76 = yymsp[0].minor.yy76; }
#line 3978 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 11: /* statement ::= rate_decl */
#line 281 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy76 = yymsp[0].minor.yy175; }
#line 3983 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 12: /* statement ::= alwayst_stmt */
#line 282 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy76 = yymsp[0].minor.yy416; }
#line 3988 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 15: /* statement ::= stmt_noconcurrency */
#line 285 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy76 = yymsp[0].minor.yy379; }
#line 3993 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 16: /* statement ::= stmt_strong_noconcurrency */
#line 286 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy76 = yymsp[0].minor.yy494; }
#line 3998 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 19: /* statement ::= stmt_query */
#line 289 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy76 = yymsp[0].minor.yy136; }
#line 4003 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 20: /* base_elem ::= constant */
#line 335 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy39 = yymsp[0].minor.yy189;}
#line 4008 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 21: /* base_elem ::= base_elem_no_const */
#line 336 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy39 = yymsp[0].minor.yy39;}
#line 4013 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 22: /* base_elem_no_const ::= object */
#line 338 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy39 = yymsp[0].minor.yy418;	}
#line 4018 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 23: /* base_elem_no_const ::= variable */
#line 339 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy39 = yymsp[0].minor.yy195; }
#line 4023 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 24: /* base_elem_no_const ::= lua */
#line 340 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy39 = yymsp[0].minor.yy237; }
#line 4028 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 25: /* constant ::= CONSTANT_ID PAREN_L term_lst PAREN_R */
      case 42: /* constant_one_const ::= CONSTANT_ID PAREN_L term_no_const_lst PAREN_R */ yytestcase(yyruleno==42);
#line 467 "bcplus/parser/detail/lemon_parser.y"
{ BASE_ELEM_DEF(yygotominor.yy189, yymsp[-3].minor.yy0, yymsp[-2].minor.yy0, yymsp[-1].minor.yy457, yymsp[0].minor.yy0, Symbol::Type::CONSTANT, Constant, ConstantSymbol);	}
#line 4034 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 26: /* constant ::= CONSTANT_ID */
      case 27: /* constant ::= MODE */ yytestcase(yyruleno==27);
      case 43: /* constant_one_const ::= CONSTANT_ID */ yytestcase(yyruleno==43);
#line 468 "bcplus/parser/detail/lemon_parser.y"
{ BASE_ELEM_DEF(yygotominor.yy189, yymsp[0].minor.yy0, NULL, NULL, NULL, Symbol::Type::CONSTANT, Constant, ConstantSymbol); }
#line 4041 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 28: /* const_anon ::= IDENTIFIER */
#line 471 "bcplus/parser/detail/lemon_parser.y"
{ BASE_ELEM_DEF9(yygotominor.yy189, yymsp[0].minor.yy0, NULL, NULL, NULL, Symbol::Type::CONSTANT, Constant, ConstantSymbol, true); }
#line 4046 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 29: /* const_anon ::= IDENTIFIER PAREN_L term_lst PAREN_R */
#line 472 "bcplus/parser/detail/lemon_parser.y"
{ BASE_ELEM_DEF9(yygotominor.yy189, yymsp[-3].minor.yy0, yymsp[-2].minor.yy0, yymsp[-1].minor.yy457, yymsp[0].minor.yy0, Symbol::Type::CONSTANT, Constant, ConstantSymbol, true);	}
#line 4051 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 30: /* object ::= OBJECT_ID PAREN_L term_lst PAREN_R */
#line 475 "bcplus/parser/detail/lemon_parser.y"
{ BASE_ELEM_DEF(yygotominor.yy418, yymsp[-3].minor.yy0, yymsp[-2].minor.yy0, yymsp[-1].minor.yy457, yymsp[0].minor.yy0, Symbol::Type::OBJECT, Object, ObjectSymbol);	}
#line 4056 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 31: /* object ::= object_nullary */
#line 476 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy418 = yymsp[0].minor.yy418; }
#line 4061 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 32: /* object_nullary ::= OBJECT_ID */
#line 477 "bcplus/parser/detail/lemon_parser.y"
{ BASE_ELEM_DEF(yygotominor.yy418, yymsp[0].minor.yy0, NULL, NULL, NULL, Symbol::Type::OBJECT, Object, ObjectSymbol); }
#line 4066 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 33: /* object ::= undeclared */
#line 478 "bcplus/parser/detail/lemon_parser.y"
{ /* never called */ }
#line 4071 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 34: /* variable ::= VARIABLE_ID */
#line 481 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy195 = NULL;
		ref_ptr<const Token> id_ptr = yymsp[0].minor.yy0;

		if (!parser->lang()->support(Language::Feature::VARIABLE)) {
			parser->_feature_error(Language::Feature::VARIABLE, &yymsp[0].minor.yy0->beginLoc());
			YYERROR;
		} else {
			BASE_ELEM_BARE_DEF(yygotominor.yy195, yymsp[0].minor.yy0, Symbol::Type::VARIABLE, Variable, VariableSymbol);
		}
	}
#line 4086 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 35: /* lua ::= AT_IDENTIFIER PAREN_L term_lst PAREN_R */
#line 492 "bcplus/parser/detail/lemon_parser.y"
{ BASE_LUA_ELEM(yygotominor.yy237, yymsp[-3].minor.yy0, yymsp[-2].minor.yy0, yymsp[-1].minor.yy457, yymsp[0].minor.yy0); }
#line 4091 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 36: /* lua ::= AT_IDENTIFIER */
#line 493 "bcplus/parser/detail/lemon_parser.y"
{ BASE_LUA_ELEM(yygotominor.yy237, yymsp[0].minor.yy0, NULL, NULL, NULL); }
#line 4096 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 37: /* lua ::= AT_IDENTIFIER PAREN_L PAREN_R */
#line 494 "bcplus/parser/detail/lemon_parser.y"
{ BASE_LUA_ELEM(yygotominor.yy237, yymsp[-2].minor.yy0, yymsp[-1].minor.yy0, NULL, yymsp[0].minor.yy0); }
#line 4101 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 38: /* undeclared ::= IDENTIFIER PAREN_L term_lst PAREN_R */
#line 497 "bcplus/parser/detail/lemon_parser.y"
{ UNDECLARED(yygotominor.yy409, yymsp[-3].minor.yy0, yymsp[-1].minor.yy457);   yy_destructor(yypParser,79,&yymsp[-2].minor);
  yy_destructor(yypParser,80,&yymsp[0].minor);
}
#line 4108 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 39: /* undeclared ::= IDENTIFIER */
#line 498 "bcplus/parser/detail/lemon_parser.y"
{ UNDECLARED(yygotominor.yy409, yymsp[0].minor.yy0, NULL); }
#line 4113 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 40: /* term_lst ::= term */
      case 44: /* term_no_const_lst ::= term_no_const */ yytestcase(yyruleno==44);
#line 501 "bcplus/parser/detail/lemon_parser.y"
{
			yygotominor.yy457 = new TermList();
			yygotominor.yy457->push_back(yymsp[0].minor.yy39);
		}
#line 4122 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 41: /* term_lst ::= term_lst COMMA term */
      case 45: /* term_no_const_lst ::= term_no_const_lst COMMA term_no_const */ yytestcase(yyruleno==45);
#line 507 "bcplus/parser/detail/lemon_parser.y"
{
			yygotominor.yy457 = yymsp[-2].minor.yy457;
			yymsp[-2].minor.yy457->push_back(yymsp[0].minor.yy39);
		  yy_destructor(yypParser,110,&yymsp[-1].minor);
}
#line 4132 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 46: /* term ::= base_elem */
      case 66: /* term_strong ::= base_elem_no_const */ yytestcase(yyruleno==66);
      case 95: /* term_no_const_strong ::= base_elem_no_const */ yytestcase(yyruleno==95);
      case 111: /* term_no_const ::= base_elem_no_const */ yytestcase(yyruleno==111);
      case 236: /* term_temporal ::= base_elem_no_const */ yytestcase(yyruleno==236);
      case 255: /* term_temporal_strong ::= base_elem_no_const */ yytestcase(yyruleno==255);
#line 591 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy39 = yymsp[0].minor.yy39; }
#line 4142 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 47: /* term ::= INTEGER */
      case 48: /* term ::= FLOAT */ yytestcase(yyruleno==48);
      case 67: /* term_strong ::= INTEGER */ yytestcase(yyruleno==67);
      case 68: /* term_strong ::= FLOAT */ yytestcase(yyruleno==68);
      case 96: /* term_no_const_strong ::= INTEGER */ yytestcase(yyruleno==96);
      case 97: /* term_no_const_strong ::= FLOAT */ yytestcase(yyruleno==97);
      case 112: /* term_no_const ::= INTEGER */ yytestcase(yyruleno==112);
      case 113: /* term_no_const ::= FLOAT */ yytestcase(yyruleno==113);
      case 129: /* term_integral ::= INTEGER */ yytestcase(yyruleno==129);
      case 237: /* term_temporal ::= INTEGER */ yytestcase(yyruleno==237);
      case 238: /* term_temporal ::= FLOAT */ yytestcase(yyruleno==238);
      case 256: /* term_temporal_strong ::= INTEGER */ yytestcase(yyruleno==256);
      case 257: /* term_temporal_strong ::= FLOAT */ yytestcase(yyruleno==257);
#line 592 "bcplus/parser/detail/lemon_parser.y"
{ BASIC_TERM(yygotominor.yy39, yymsp[0].minor.yy0);	}
#line 4159 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 49: /* term ::= STRING_LITERAL */
      case 51: /* term ::= TRUE */ yytestcase(yyruleno==51);
      case 52: /* term ::= FALSE */ yytestcase(yyruleno==52);
      case 69: /* term_strong ::= STRING_LITERAL */ yytestcase(yyruleno==69);
      case 98: /* term_no_const_strong ::= STRING_LITERAL */ yytestcase(yyruleno==98);
      case 114: /* term_no_const ::= STRING_LITERAL */ yytestcase(yyruleno==114);
      case 116: /* term_no_const ::= TRUE */ yytestcase(yyruleno==116);
      case 117: /* term_no_const ::= FALSE */ yytestcase(yyruleno==117);
      case 131: /* term_integral ::= TRUE */ yytestcase(yyruleno==131);
      case 132: /* term_integral ::= FALSE */ yytestcase(yyruleno==132);
      case 239: /* term_temporal ::= STRING_LITERAL */ yytestcase(yyruleno==239);
      case 241: /* term_temporal ::= TRUE */ yytestcase(yyruleno==241);
      case 242: /* term_temporal ::= FALSE */ yytestcase(yyruleno==242);
      case 258: /* term_temporal_strong ::= STRING_LITERAL */ yytestcase(yyruleno==258);
#line 594 "bcplus/parser/detail/lemon_parser.y"
{ BASIC_TERM(yygotominor.yy39, yymsp[0].minor.yy0); }
#line 4177 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 50: /* term ::= PAREN_L term PAREN_R */
      case 70: /* term_strong ::= PAREN_L term_strong PAREN_R */ yytestcase(yyruleno==70);
      case 99: /* term_no_const_strong ::= PAREN_L term_no_const_strong PAREN_R */ yytestcase(yyruleno==99);
      case 115: /* term_no_const ::= PAREN_L term_no_const PAREN_R */ yytestcase(yyruleno==115);
      case 130: /* term_integral ::= PAREN_L term_integral PAREN_R */ yytestcase(yyruleno==130);
      case 240: /* term_temporal ::= PAREN_L term_temporal PAREN_R */ yytestcase(yyruleno==240);
      case 259: /* term_temporal_strong ::= PAREN_L term_temporal_strong PAREN_R */ yytestcase(yyruleno==259);
#line 595 "bcplus/parser/detail/lemon_parser.y"
{ TERM_PARENS(yygotominor.yy39, yymsp[-2].minor.yy0, yymsp[-1].minor.yy39, yymsp[0].minor.yy0); }
#line 4188 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 53: /* term ::= MAXSTEP */
      case 71: /* term_strong ::= MAXSTEP */ yytestcase(yyruleno==71);
      case 100: /* term_no_const_strong ::= MAXSTEP */ yytestcase(yyruleno==100);
      case 118: /* term_no_const ::= MAXSTEP */ yytestcase(yyruleno==118);
      case 133: /* term_integral ::= MAXSTEP */ yytestcase(yyruleno==133);
      case 243: /* term_temporal ::= MAXSTEP */ yytestcase(yyruleno==243);
      case 260: /* term_temporal_strong ::= MAXSTEP */ yytestcase(yyruleno==260);
#line 598 "bcplus/parser/detail/lemon_parser.y"
{ NULLARY_TERM(yygotominor.yy39, yymsp[0].minor.yy0, Language::Feature::MAXSTEP, NullaryTerm::Operator::MAXSTEP); }
#line 4199 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 54: /* term ::= MAXADDITIVE */
      case 72: /* term_strong ::= MAXADDITIVE */ yytestcase(yyruleno==72);
      case 101: /* term_no_const_strong ::= MAXADDITIVE */ yytestcase(yyruleno==101);
      case 119: /* term_no_const ::= MAXADDITIVE */ yytestcase(yyruleno==119);
      case 134: /* term_integral ::= MAXADDITIVE */ yytestcase(yyruleno==134);
      case 244: /* term_temporal ::= MAXADDITIVE */ yytestcase(yyruleno==244);
      case 261: /* term_temporal_strong ::= MAXADDITIVE */ yytestcase(yyruleno==261);
#line 599 "bcplus/parser/detail/lemon_parser.y"
{ NULLARY_TERM(yygotominor.yy39, yymsp[0].minor.yy0, Language::Feature::MAXADDITIVE, NullaryTerm::Operator::MAXADDITIVE); }
#line 4210 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 55: /* term ::= MAXAFVALUE */
      case 73: /* term_strong ::= MAXAFVALUE */ yytestcase(yyruleno==73);
      case 102: /* term_no_const_strong ::= MAXAFVALUE */ yytestcase(yyruleno==102);
      case 120: /* term_no_const ::= MAXAFVALUE */ yytestcase(yyruleno==120);
      case 135: /* term_integral ::= MAXAFVALUE */ yytestcase(yyruleno==135);
      case 245: /* term_temporal ::= MAXAFVALUE */ yytestcase(yyruleno==245);
      case 262: /* term_temporal_strong ::= MAXAFVALUE */ yytestcase(yyruleno==262);
#line 600 "bcplus/parser/detail/lemon_parser.y"
{ NULLARY_TERM(yygotominor.yy39, yymsp[0].minor.yy0, Language::Feature::MAXAFVALUE, NullaryTerm::Operator::MAXAFVALUE); }
#line 4221 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 56: /* term ::= DASH term */
      case 74: /* term_strong ::= DASH term_strong */ yytestcase(yyruleno==74);
      case 104: /* term_no_const_strong ::= DASH term_no_const_strong */ yytestcase(yyruleno==104);
      case 122: /* term_no_const ::= DASH term_no_const */ yytestcase(yyruleno==122);
      case 136: /* term_integral ::= DASH term_integral */ yytestcase(yyruleno==136);
      case 247: /* term_temporal ::= DASH term_temporal */ yytestcase(yyruleno==247);
      case 264: /* term_temporal_strong ::= DASH term_temporal_strong */ yytestcase(yyruleno==264);
#line 604 "bcplus/parser/detail/lemon_parser.y"
{ UNARY_ARITH(yygotominor.yy39, yymsp[-1].minor.yy0, yymsp[0].minor.yy39, UnaryTerm::Operator::NEGATIVE); }
#line 4232 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 57: /* term ::= ABS term */
      case 75: /* term_strong ::= ABS term */ yytestcase(yyruleno==75);
      case 105: /* term_no_const_strong ::= ABS term_no_const */ yytestcase(yyruleno==105);
      case 123: /* term_no_const ::= ABS term_no_const */ yytestcase(yyruleno==123);
      case 137: /* term_integral ::= ABS term_integral */ yytestcase(yyruleno==137);
      case 248: /* term_temporal ::= ABS term_temporal */ yytestcase(yyruleno==248);
      case 265: /* term_temporal_strong ::= ABS term_temporal */ yytestcase(yyruleno==265);
#line 605 "bcplus/parser/detail/lemon_parser.y"
{ UNARY_ARITH(yygotominor.yy39, yymsp[-1].minor.yy0, yymsp[0].minor.yy39, UnaryTerm::Operator::ABS); }
#line 4243 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 58: /* term ::= SIN PAREN_L term PAREN_R */
      case 76: /* term_strong ::= SIN PAREN_L term PAREN_R */ yytestcase(yyruleno==76);
#line 606 "bcplus/parser/detail/lemon_parser.y"
{ UNARY_ARITH(yygotominor.yy39, yymsp[-3].minor.yy0, yymsp[-1].minor.yy39, UnaryTerm::Operator::SIN);   yy_destructor(yypParser,79,&yymsp[-2].minor);
  yy_destructor(yypParser,80,&yymsp[0].minor);
}
#line 4251 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 59: /* term ::= COS PAREN_L term PAREN_R */
      case 77: /* term_strong ::= COS PAREN_L term PAREN_R */ yytestcase(yyruleno==77);
#line 607 "bcplus/parser/detail/lemon_parser.y"
{ UNARY_ARITH(yygotominor.yy39, yymsp[-3].minor.yy0, yymsp[-1].minor.yy39, UnaryTerm::Operator::COS);   yy_destructor(yypParser,79,&yymsp[-2].minor);
  yy_destructor(yypParser,80,&yymsp[0].minor);
}
#line 4259 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 60: /* term ::= TAN PAREN_L term PAREN_R */
      case 78: /* term_strong ::= TAN PAREN_L term PAREN_R */ yytestcase(yyruleno==78);
#line 608 "bcplus/parser/detail/lemon_parser.y"
{ UNARY_ARITH(yygotominor.yy39, yymsp[-3].minor.yy0, yymsp[-1].minor.yy39, UnaryTerm::Operator::TAN);   yy_destructor(yypParser,79,&yymsp[-2].minor);
  yy_destructor(yypParser,80,&yymsp[0].minor);
}
#line 4267 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 61: /* term ::= term DASH term */
      case 80: /* term_strong ::= term_strong_candidate DASH term */ yytestcase(yyruleno==80);
      case 90: /* term_strong ::= term_strong DASH term */ yytestcase(yyruleno==90);
      case 106: /* term_no_const_strong ::= term_no_const_strong DASH term_no_const */ yytestcase(yyruleno==106);
      case 124: /* term_no_const ::= term_no_const DASH term_no_const */ yytestcase(yyruleno==124);
      case 138: /* term_integral ::= term_integral DASH term_integral */ yytestcase(yyruleno==138);
      case 250: /* term_temporal ::= term_temporal DASH term_temporal */ yytestcase(yyruleno==250);
      case 266: /* term_temporal_strong ::= term_temporal_strong DASH term_temporal */ yytestcase(yyruleno==266);
#line 612 "bcplus/parser/detail/lemon_parser.y"
{ BINARY_ARITH(yygotominor.yy39, yymsp[-2].minor.yy39, yymsp[-1].minor.yy0, yymsp[0].minor.yy39, BinaryTerm::Operator::MINUS); }
#line 4279 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 62: /* term ::= term PLUS term */
      case 81: /* term_strong ::= term_strong_candidate PLUS term */ yytestcase(yyruleno==81);
      case 91: /* term_strong ::= term_strong PLUS term */ yytestcase(yyruleno==91);
      case 107: /* term_no_const_strong ::= term_no_const_strong PLUS term_no_const */ yytestcase(yyruleno==107);
      case 125: /* term_no_const ::= term_no_const PLUS term_no_const */ yytestcase(yyruleno==125);
      case 139: /* term_integral ::= term_integral PLUS term_integral */ yytestcase(yyruleno==139);
      case 251: /* term_temporal ::= term_temporal PLUS term_temporal */ yytestcase(yyruleno==251);
      case 267: /* term_temporal_strong ::= term_temporal_strong PLUS term_temporal */ yytestcase(yyruleno==267);
#line 613 "bcplus/parser/detail/lemon_parser.y"
{ BINARY_ARITH(yygotominor.yy39, yymsp[-2].minor.yy39, yymsp[-1].minor.yy0, yymsp[0].minor.yy39, BinaryTerm::Operator::PLUS); }
#line 4291 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 63: /* term ::= term STAR term */
      case 82: /* term_strong ::= term_strong_candidate STAR term */ yytestcase(yyruleno==82);
      case 92: /* term_strong ::= term_strong STAR term */ yytestcase(yyruleno==92);
      case 108: /* term_no_const_strong ::= term_no_const_strong STAR term_no_const */ yytestcase(yyruleno==108);
      case 126: /* term_no_const ::= term_no_const STAR term_no_const */ yytestcase(yyruleno==126);
      case 140: /* term_integral ::= term_integral STAR term_integral */ yytestcase(yyruleno==140);
      case 252: /* term_temporal ::= term_temporal STAR term_temporal */ yytestcase(yyruleno==252);
      case 268: /* term_temporal_strong ::= term_temporal_strong STAR term_temporal */ yytestcase(yyruleno==268);
#line 614 "bcplus/parser/detail/lemon_parser.y"
{ BINARY_ARITH(yygotominor.yy39, yymsp[-2].minor.yy39, yymsp[-1].minor.yy0, yymsp[0].minor.yy39, BinaryTerm::Operator::TIMES); }
#line 4303 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 64: /* term ::= term INT_DIV term */
      case 83: /* term_strong ::= term_strong_candidate INT_DIV term */ yytestcase(yyruleno==83);
      case 93: /* term_strong ::= term_strong INT_DIV term */ yytestcase(yyruleno==93);
      case 109: /* term_no_const_strong ::= term_no_const_strong INT_DIV term_no_const */ yytestcase(yyruleno==109);
      case 127: /* term_no_const ::= term_no_const INT_DIV term_no_const */ yytestcase(yyruleno==127);
      case 141: /* term_integral ::= term_integral INT_DIV term_integral */ yytestcase(yyruleno==141);
      case 253: /* term_temporal ::= term_temporal INT_DIV term_temporal */ yytestcase(yyruleno==253);
      case 269: /* term_temporal_strong ::= term_temporal_strong INT_DIV term_temporal */ yytestcase(yyruleno==269);
#line 615 "bcplus/parser/detail/lemon_parser.y"
{ BINARY_ARITH(yygotominor.yy39, yymsp[-2].minor.yy39, yymsp[-1].minor.yy0, yymsp[0].minor.yy39, BinaryTerm::Operator::DIVIDE); }
#line 4315 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 65: /* term ::= term MOD term */
      case 84: /* term_strong ::= term_strong_candidate MOD term */ yytestcase(yyruleno==84);
      case 94: /* term_strong ::= term_strong MOD term */ yytestcase(yyruleno==94);
      case 110: /* term_no_const_strong ::= term_no_const_strong MOD term_no_const */ yytestcase(yyruleno==110);
      case 128: /* term_no_const ::= term_no_const MOD term_no_const */ yytestcase(yyruleno==128);
      case 142: /* term_integral ::= term_integral MOD term_integral */ yytestcase(yyruleno==142);
      case 254: /* term_temporal ::= term_temporal MOD term_temporal */ yytestcase(yyruleno==254);
      case 270: /* term_temporal_strong ::= term_temporal_strong MOD term_temporal */ yytestcase(yyruleno==270);
#line 616 "bcplus/parser/detail/lemon_parser.y"
{ BINARY_ARITH(yygotominor.yy39, yymsp[-2].minor.yy39, yymsp[-1].minor.yy0, yymsp[0].minor.yy39, BinaryTerm::Operator::MOD); }
#line 4327 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 79: /* term_strong_candidate ::= DASH constant */
#line 639 "bcplus/parser/detail/lemon_parser.y"
{ UNARY_ARITH(yygotominor.yy39, yymsp[-1].minor.yy0, yymsp[0].minor.yy189, UnaryTerm::Operator::NEGATIVE); }
#line 4332 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 85: /* term_strong ::= constant DASH term */
#line 648 "bcplus/parser/detail/lemon_parser.y"
{ BINARY_ARITH(yygotominor.yy39, yymsp[-2].minor.yy189, yymsp[-1].minor.yy0, yymsp[0].minor.yy39, BinaryTerm::Operator::MINUS); }
#line 4337 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 86: /* term_strong ::= constant PLUS term */
#line 649 "bcplus/parser/detail/lemon_parser.y"
{ BINARY_ARITH(yygotominor.yy39, yymsp[-2].minor.yy189, yymsp[-1].minor.yy0, yymsp[0].minor.yy39, BinaryTerm::Operator::PLUS); }
#line 4342 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 87: /* term_strong ::= constant STAR term */
#line 650 "bcplus/parser/detail/lemon_parser.y"
{ BINARY_ARITH(yygotominor.yy39, yymsp[-2].minor.yy189, yymsp[-1].minor.yy0, yymsp[0].minor.yy39, BinaryTerm::Operator::TIMES); }
#line 4347 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 88: /* term_strong ::= constant INT_DIV term */
#line 651 "bcplus/parser/detail/lemon_parser.y"
{ BINARY_ARITH(yygotominor.yy39, yymsp[-2].minor.yy189, yymsp[-1].minor.yy0, yymsp[0].minor.yy39, BinaryTerm::Operator::DIVIDE); }
#line 4352 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 89: /* term_strong ::= constant MOD term */
#line 652 "bcplus/parser/detail/lemon_parser.y"
{ BINARY_ARITH(yygotominor.yy39, yymsp[-2].minor.yy189, yymsp[-1].minor.yy0, yymsp[0].minor.yy39, BinaryTerm::Operator::MOD); }
#line 4357 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 103: /* term_no_const_strong ::= constant */
#line 675 "bcplus/parser/detail/lemon_parser.y"
{
		// error handling for constants so they don'yygotominor.yy39 default to undeclared identifiers
		yygotominor.yy39 = NULL;
		ref_ptr<const Referenced> c_ptr = yymsp[0].minor.yy189;
		parser->_parse_error("Encountered unexpected constant symbol.", &yymsp[0].minor.yy189->beginLoc());
		YYERROR;
	}
#line 4368 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 121: /* term_no_const ::= constant */
#line 709 "bcplus/parser/detail/lemon_parser.y"
{
		// error handline for constants so they don'yygotominor.yy39 default to undeclared identifiers
		yygotominor.yy39 = NULL;
		ref_ptr<const Referenced> c_ptr = yymsp[0].minor.yy189;
		parser->_parse_error("Encountered unexpected constant symbol.", &yymsp[0].minor.yy189->beginLoc());
		YYERROR;
	}
#line 4379 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 143: /* num_range ::= term_integral DBL_PERIOD term_integral */
#line 766 "bcplus/parser/detail/lemon_parser.y"
{
	ref_ptr<const Referenced> l_ptr = yymsp[-2].minor.yy39, r_ptr = yymsp[0].minor.yy39, s_ptr = yymsp[-1].minor.yy0;
	yygotominor.yy107 = NULL;

	if (yymsp[-2].minor.yy39->domainType() != DomainType::INTEGRAL) {
		parser->_parse_error("Number ranges cannot have non-numeric operands.", &yymsp[-1].minor.yy0->beginLoc());
		YYERROR;
	}

	if (yymsp[0].minor.yy39->domainType() != DomainType::INTEGRAL) {
		parser->_parse_error("Number ranges cannot have non-numeric operands.", &yymsp[0].minor.yy39->beginLoc());
		YYERROR;
	}

	yygotominor.yy107 = new NumberRange(yymsp[-2].minor.yy39, yymsp[0].minor.yy39, yymsp[-2].minor.yy39->beginLoc(), yymsp[0].minor.yy39->endLoc());
}
#line 4399 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 144: /* num_range_eval ::= term_int_eval DBL_PERIOD term_int_eval */
#line 784 "bcplus/parser/detail/lemon_parser.y"
{
	ref_ptr<const Referenced> l_ptr = yymsp[-2].minor.yy68, r_ptr = yymsp[0].minor.yy68, s_ptr = yymsp[-1].minor.yy0;
	yygotominor.yy1 = new NumberRangeEval(yymsp[-2].minor.yy68->val(), yymsp[0].minor.yy68->val(), yymsp[-2].minor.yy68->beginLoc(), yymsp[0].minor.yy68->endLoc());
}
#line 4407 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 145: /* term_int_eval ::= INTEGER */
#line 790 "bcplus/parser/detail/lemon_parser.y"
{
	ref_ptr<const Referenced> i_ptr = yymsp[0].minor.yy0;

	yygotominor.yy68 = 0;
	try {
		yygotominor.yy68 = new Number(boost::lexical_cast<int>(*yymsp[0].minor.yy0->str()), yymsp[0].minor.yy0->beginLoc());
	} catch (boost::bad_lexical_cast const& e) {
	parser->_parse_error("INTERNAL ERROR: Failed to parse integer \"" + *yymsp[0].minor.yy0->str() + "\".", &yymsp[0].minor.yy0->beginLoc());
		YYERROR;
	}
}
#line 4422 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 146: /* term_int_eval ::= PAREN_L term_int_eval PAREN_R */
#line 802 "bcplus/parser/detail/lemon_parser.y"
{
	ref_ptr<const Referenced> pl_ptr = yymsp[-2].minor.yy0, pr_ptr = yymsp[0].minor.yy0;
	yygotominor.yy68 = yymsp[-1].minor.yy68;
	yygotominor.yy68->beginLoc(yymsp[-2].minor.yy0->beginLoc());
	yygotominor.yy68->endLoc(yymsp[0].minor.yy0->endLoc());
}
#line 4432 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 147: /* term_int_eval ::= DASH term_int_eval */
#line 822 "bcplus/parser/detail/lemon_parser.y"
{ NUM_UOP(yygotominor.yy68, yymsp[0].minor.yy68, -1 * yymsp[0].minor.yy68->val());   yy_destructor(yypParser,113,&yymsp[-1].minor);
}
#line 4438 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 148: /* term_int_eval ::= ABS term_int_eval */
#line 823 "bcplus/parser/detail/lemon_parser.y"
{ NUM_UOP(yygotominor.yy68, yymsp[0].minor.yy68, yymsp[0].minor.yy68->val() < 0 ? - yymsp[0].minor.yy68->val() : yymsp[0].minor.yy68->val());   yy_destructor(yypParser,118,&yymsp[-1].minor);
}
#line 4444 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 149: /* term_int_eval ::= term_int_eval DASH term_int_eval */
#line 825 "bcplus/parser/detail/lemon_parser.y"
{ NUM_BOP(yygotominor.yy68, yymsp[-2].minor.yy68, yymsp[0].minor.yy68, yymsp[-2].minor.yy68->val() - yymsp[0].minor.yy68->val());   yy_destructor(yypParser,113,&yymsp[-1].minor);
}
#line 4450 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 150: /* term_int_eval ::= term_int_eval PLUS term_int_eval */
#line 826 "bcplus/parser/detail/lemon_parser.y"
{ NUM_BOP(yygotominor.yy68, yymsp[-2].minor.yy68, yymsp[0].minor.yy68, yymsp[-2].minor.yy68->val() + yymsp[0].minor.yy68->val());   yy_destructor(yypParser,114,&yymsp[-1].minor);
}
#line 4456 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 151: /* term_int_eval ::= term_int_eval STAR term_int_eval */
#line 827 "bcplus/parser/detail/lemon_parser.y"
{ NUM_BOP(yygotominor.yy68, yymsp[-2].minor.yy68, yymsp[0].minor.yy68, yymsp[-2].minor.yy68->val() * yymsp[0].minor.yy68->val());   yy_destructor(yypParser,115,&yymsp[-1].minor);
}
#line 4462 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 152: /* term_int_eval ::= term_int_eval INT_DIV term_int_eval */
#line 828 "bcplus/parser/detail/lemon_parser.y"
{ NUM_BOP(yygotominor.yy68, yymsp[-2].minor.yy68, yymsp[0].minor.yy68, yymsp[-2].minor.yy68->val() / yymsp[0].minor.yy68->val());   yy_destructor(yypParser,116,&yymsp[-1].minor);
}
#line 4468 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 153: /* term_int_eval ::= term_int_eval MOD term_int_eval */
#line 829 "bcplus/parser/detail/lemon_parser.y"
{ NUM_BOP(yygotominor.yy68, yymsp[-2].minor.yy68, yymsp[0].minor.yy68, yymsp[-2].minor.yy68->val() % yymsp[0].minor.yy68->val());   yy_destructor(yypParser,117,&yymsp[-1].minor);
}
#line 4474 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 154: /* formula ::= formula_base */
      case 197: /* formula_no_const ::= formula_no_const_base */ yytestcase(yyruleno==197);
      case 271: /* formula_temporal ::= formula_temporal_base */ yytestcase(yyruleno==271);
#line 889 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy179 = yymsp[0].minor.yy179;				}
#line 4481 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 155: /* formula ::= PAREN_L formula PAREN_R */
      case 198: /* formula_no_const ::= PAREN_L formula_no_const PAREN_R */ yytestcase(yyruleno==198);
      case 272: /* formula_temporal ::= PAREN_L formula_temporal PAREN_R */ yytestcase(yyruleno==272);
#line 890 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy179 = yymsp[-1].minor.yy179; yygotominor.yy179->parens(true); 	  yy_destructor(yypParser,79,&yymsp[-2].minor);
  yy_destructor(yypParser,80,&yymsp[0].minor);
}
#line 4490 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 156: /* formula ::= NOT formula */
      case 199: /* formula_no_const ::= NOT formula_no_const */ yytestcase(yyruleno==199);
      case 273: /* formula_temporal ::= NOT formula_temporal */ yytestcase(yyruleno==273);
#line 891 "bcplus/parser/detail/lemon_parser.y"
{ NESTED_UOP(yygotominor.yy179, yymsp[-1].minor.yy0, yymsp[0].minor.yy179, UnaryFormula::Operator::NOT, Language::Feature::FORMULA_NOT_KEYWORD); }
#line 4497 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 157: /* formula ::= DASH formula */
      case 200: /* formula_no_const ::= DASH formula_no_const */ yytestcase(yyruleno==200);
      case 274: /* formula_temporal ::= DASH formula_temporal */ yytestcase(yyruleno==274);
#line 892 "bcplus/parser/detail/lemon_parser.y"
{ NESTED_UOP(yygotominor.yy179, yymsp[-1].minor.yy0, yymsp[0].minor.yy179, UnaryFormula::Operator::NOT, Language::Feature::FORMULA_NOT_DASH); }
#line 4504 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 158: /* formula ::= formula AMP formula */
      case 201: /* formula_no_const ::= formula_no_const AMP formula_no_const */ yytestcase(yyruleno==201);
      case 275: /* formula_temporal ::= formula_temporal AMP formula_temporal */ yytestcase(yyruleno==275);
#line 893 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy179 = new BinaryFormula(BinaryFormula::Operator::AND, yymsp[-2].minor.yy179, yymsp[0].minor.yy179, yymsp[-2].minor.yy179->beginLoc(), yymsp[0].minor.yy179->endLoc());   yy_destructor(yypParser,109,&yymsp[-1].minor);
}
#line 4512 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 159: /* formula ::= formula DBL_PLUS formula */
      case 160: /* formula ::= formula PIPE formula */ yytestcase(yyruleno==160);
      case 202: /* formula_no_const ::= formula_no_const DBL_PLUS formula_no_const */ yytestcase(yyruleno==202);
      case 203: /* formula_no_const ::= formula_no_const PIPE formula_no_const */ yytestcase(yyruleno==203);
      case 276: /* formula_temporal ::= formula_temporal DBL_PLUS formula_temporal */ yytestcase(yyruleno==276);
      case 277: /* formula_temporal ::= formula_temporal PIPE formula_temporal */ yytestcase(yyruleno==277);
#line 895 "bcplus/parser/detail/lemon_parser.y"
{ NESTED_BOP(yygotominor.yy179, yymsp[-2].minor.yy179, yymsp[-1].minor.yy0, yymsp[0].minor.yy179, BinaryFormula::Operator::OR); }
#line 4522 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 161: /* formula ::= formula EQUIV formula */
      case 204: /* formula_no_const ::= formula_no_const EQUIV formula_no_const */ yytestcase(yyruleno==204);
      case 278: /* formula_temporal ::= formula_temporal EQUIV formula_temporal */ yytestcase(yyruleno==278);
#line 897 "bcplus/parser/detail/lemon_parser.y"
{ NESTED_BOP(yygotominor.yy179, yymsp[-2].minor.yy179, yymsp[-1].minor.yy0, yymsp[0].minor.yy179, BinaryFormula::Operator::EQUIV); }
#line 4529 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 162: /* formula ::= formula IMPL formula */
      case 163: /* formula ::= formula ARROW_RDASH formula */ yytestcase(yyruleno==163);
      case 205: /* formula_no_const ::= formula_no_const IMPL formula_no_const */ yytestcase(yyruleno==205);
      case 206: /* formula_no_const ::= formula_no_const ARROW_RDASH formula_no_const */ yytestcase(yyruleno==206);
      case 279: /* formula_temporal ::= formula_temporal IMPL formula_temporal */ yytestcase(yyruleno==279);
      case 280: /* formula_temporal ::= formula_temporal ARROW_RDASH formula_temporal */ yytestcase(yyruleno==280);
#line 898 "bcplus/parser/detail/lemon_parser.y"
{ NESTED_BOP(yygotominor.yy179, yymsp[-2].minor.yy179, yymsp[-1].minor.yy0, yymsp[0].minor.yy179, BinaryFormula::Operator::IMPL); }
#line 4539 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 164: /* formula_base ::= comparison */
      case 207: /* formula_no_const_base ::= comparison_no_const */ yytestcase(yyruleno==207);
      case 282: /* formula_temporal_base ::= comparison_temporal */ yytestcase(yyruleno==282);
      case 306: /* head_formula ::= comparison */ yytestcase(yyruleno==306);
#line 901 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy179 = yymsp[0].minor.yy179; }
#line 4547 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 165: /* formula_base ::= atomic_formula */
      case 307: /* head_formula ::= atomic_head_formula */ yytestcase(yyruleno==307);
#line 902 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy179 = yymsp[0].minor.yy274; }
#line 4553 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 166: /* formula_base ::= formula_quant */
      case 284: /* formula_temporal_base ::= formula_temporal_quant */ yytestcase(yyruleno==284);
#line 903 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy179 = yymsp[0].minor.yy387; }
#line 4559 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 167: /* formula_base ::= formula_card */
      case 285: /* formula_temporal_base ::= formula_temporal_card */ yytestcase(yyruleno==285);
#line 905 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy179 = yymsp[0].minor.yy179;
		if (!parser->lang()->support(Language::Feature::FORMULA_CARDINALITY_BODY)) {
			parser->_feature_error(Language::Feature::FORMULA_CARDINALITY_BODY, &yymsp[0].minor.yy179->beginLoc());
			YYERROR;
		}
	}
#line 4571 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 168: /* formula_base ::= TRUE */
      case 208: /* formula_no_const_base ::= TRUE */ yytestcase(yyruleno==208);
      case 286: /* formula_temporal_base ::= TRUE */ yytestcase(yyruleno==286);
      case 309: /* head_formula ::= TRUE */ yytestcase(yyruleno==309);
#line 912 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy179 = new NullaryFormula(NullaryFormula::Operator::TRUE, yymsp[0].minor.yy0->beginLoc(), yymsp[0].minor.yy0->endLoc()); }
#line 4579 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 169: /* formula_base ::= FALSE */
      case 209: /* formula_no_const_base ::= FALSE */ yytestcase(yyruleno==209);
      case 287: /* formula_temporal_base ::= FALSE */ yytestcase(yyruleno==287);
      case 310: /* head_formula ::= FALSE */ yytestcase(yyruleno==310);
#line 913 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy179 = new NullaryFormula(NullaryFormula::Operator::FALSE, yymsp[0].minor.yy0->beginLoc(), yymsp[0].minor.yy0->endLoc()); }
#line 4587 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 170: /* comparison ::= term_strong EQ term */
      case 177: /* comparison ::= term_strong_candidate EQ term */ yytestcase(yyruleno==177);
      case 210: /* comparison_no_const ::= term_no_const_strong EQ term_no_const */ yytestcase(yyruleno==210);
      case 288: /* comparison_temporal ::= term_temporal_strong EQ term_temporal */ yytestcase(yyruleno==288);
#line 915 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy179 = new ComparisonFormula(ComparisonFormula::Operator::EQ, yymsp[-2].minor.yy39, yymsp[0].minor.yy39, yymsp[-2].minor.yy39->beginLoc(), yymsp[0].minor.yy39->endLoc());   yy_destructor(yypParser,89,&yymsp[-1].minor);
}
#line 4596 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 171: /* comparison ::= term_strong DBL_EQ term */
      case 178: /* comparison ::= term_strong_candidate DBL_EQ term */ yytestcase(yyruleno==178);
      case 211: /* comparison_no_const ::= term_no_const_strong DBL_EQ term_no_const */ yytestcase(yyruleno==211);
      case 289: /* comparison_temporal ::= term_temporal_strong DBL_EQ term_temporal */ yytestcase(yyruleno==289);
#line 916 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy179 = new ComparisonFormula(ComparisonFormula::Operator::EQ, yymsp[-2].minor.yy39, yymsp[0].minor.yy39, yymsp[-2].minor.yy39->beginLoc(), yymsp[0].minor.yy39->endLoc());   yy_destructor(yypParser,90,&yymsp[-1].minor);
}
#line 4605 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 172: /* comparison ::= term_strong NEQ term */
      case 179: /* comparison ::= term_strong_candidate NEQ term */ yytestcase(yyruleno==179);
      case 212: /* comparison_no_const ::= term_no_const_strong NEQ term_no_const */ yytestcase(yyruleno==212);
      case 290: /* comparison_temporal ::= term_temporal_strong NEQ term_temporal */ yytestcase(yyruleno==290);
#line 917 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy179 = new ComparisonFormula(ComparisonFormula::Operator::NEQ, yymsp[-2].minor.yy39, yymsp[0].minor.yy39, yymsp[-2].minor.yy39->beginLoc(), yymsp[0].minor.yy39->endLoc());   yy_destructor(yypParser,91,&yymsp[-1].minor);
}
#line 4614 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 173: /* comparison ::= term_strong LTHAN term */
      case 180: /* comparison ::= term_strong_candidate LTHAN term */ yytestcase(yyruleno==180);
      case 213: /* comparison_no_const ::= term_no_const_strong LTHAN term_no_const */ yytestcase(yyruleno==213);
      case 291: /* comparison_temporal ::= term_temporal_strong LTHAN term_temporal */ yytestcase(yyruleno==291);
#line 918 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy179 = new ComparisonFormula(ComparisonFormula::Operator::LTHAN, yymsp[-2].minor.yy39, yymsp[0].minor.yy39, yymsp[-2].minor.yy39->beginLoc(), yymsp[0].minor.yy39->endLoc());   yy_destructor(yypParser,93,&yymsp[-1].minor);
}
#line 4623 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 174: /* comparison ::= term_strong GTHAN term */
      case 181: /* comparison ::= term_strong_candidate GTHAN term */ yytestcase(yyruleno==181);
      case 214: /* comparison_no_const ::= term_no_const_strong GTHAN term_no_const */ yytestcase(yyruleno==214);
      case 292: /* comparison_temporal ::= term_temporal_strong GTHAN term_temporal */ yytestcase(yyruleno==292);
#line 919 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy179 = new ComparisonFormula(ComparisonFormula::Operator::GTHAN, yymsp[-2].minor.yy39, yymsp[0].minor.yy39, yymsp[-2].minor.yy39->beginLoc(), yymsp[0].minor.yy39->endLoc());   yy_destructor(yypParser,94,&yymsp[-1].minor);
}
#line 4632 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 175: /* comparison ::= term_strong LTHAN_EQ term */
      case 182: /* comparison ::= term_strong_candidate LTHAN_EQ term */ yytestcase(yyruleno==182);
      case 215: /* comparison_no_const ::= term_no_const_strong LTHAN_EQ term_no_const */ yytestcase(yyruleno==215);
      case 293: /* comparison_temporal ::= term_temporal_strong LTHAN_EQ term_temporal */ yytestcase(yyruleno==293);
#line 920 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy179 = new ComparisonFormula(ComparisonFormula::Operator::LTHAN_EQ, yymsp[-2].minor.yy39, yymsp[0].minor.yy39, yymsp[-2].minor.yy39->beginLoc(), yymsp[0].minor.yy39->endLoc());   yy_destructor(yypParser,95,&yymsp[-1].minor);
}
#line 4641 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 176: /* comparison ::= term_strong GTHAN_EQ term */
      case 183: /* comparison ::= term_strong_candidate GTHAN_EQ term */ yytestcase(yyruleno==183);
      case 216: /* comparison_no_const ::= term_no_const_strong GTHAN_EQ term_no_const */ yytestcase(yyruleno==216);
      case 294: /* comparison_temporal ::= term_temporal_strong GTHAN_EQ term_temporal */ yytestcase(yyruleno==294);
#line 921 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy179 = new ComparisonFormula(ComparisonFormula::Operator::GTHAN_EQ, yymsp[-2].minor.yy39, yymsp[0].minor.yy39, yymsp[-2].minor.yy39->beginLoc(), yymsp[0].minor.yy39->endLoc());   yy_destructor(yypParser,96,&yymsp[-1].minor);
}
#line 4650 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 184: /* comparison ::= constant DBL_EQ term */
#line 929 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy179 = new ComparisonFormula(ComparisonFormula::Operator::EQ, yymsp[-2].minor.yy189, yymsp[0].minor.yy39, yymsp[-2].minor.yy189->beginLoc(), yymsp[0].minor.yy39->endLoc());   yy_destructor(yypParser,90,&yymsp[-1].minor);
}
#line 4656 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 185: /* comparison ::= constant NEQ term */
#line 930 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy179 = new ComparisonFormula(ComparisonFormula::Operator::NEQ, yymsp[-2].minor.yy189, yymsp[0].minor.yy39, yymsp[-2].minor.yy189->beginLoc(), yymsp[0].minor.yy39->endLoc());   yy_destructor(yypParser,91,&yymsp[-1].minor);
}
#line 4662 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 186: /* comparison ::= constant LTHAN term */
#line 931 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy179 = new ComparisonFormula(ComparisonFormula::Operator::LTHAN, yymsp[-2].minor.yy189, yymsp[0].minor.yy39, yymsp[-2].minor.yy189->beginLoc(), yymsp[0].minor.yy39->endLoc());   yy_destructor(yypParser,93,&yymsp[-1].minor);
}
#line 4668 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 187: /* comparison ::= constant GTHAN term */
#line 932 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy179 = new ComparisonFormula(ComparisonFormula::Operator::GTHAN, yymsp[-2].minor.yy189, yymsp[0].minor.yy39, yymsp[-2].minor.yy189->beginLoc(), yymsp[0].minor.yy39->endLoc());   yy_destructor(yypParser,94,&yymsp[-1].minor);
}
#line 4674 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 188: /* comparison ::= constant LTHAN_EQ term */
#line 933 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy179 = new ComparisonFormula(ComparisonFormula::Operator::LTHAN_EQ, yymsp[-2].minor.yy189, yymsp[0].minor.yy39, yymsp[-2].minor.yy189->beginLoc(), yymsp[0].minor.yy39->endLoc());   yy_destructor(yypParser,95,&yymsp[-1].minor);
}
#line 4680 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 189: /* comparison ::= constant GTHAN_EQ term */
#line 934 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy179 = new ComparisonFormula(ComparisonFormula::Operator::GTHAN_EQ, yymsp[-2].minor.yy189, yymsp[0].minor.yy39, yymsp[-2].minor.yy189->beginLoc(), yymsp[0].minor.yy39->endLoc());   yy_destructor(yypParser,96,&yymsp[-1].minor);
}
#line 4686 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 190: /* atomic_formula ::= constant */
      case 194: /* atomic_formula_anon ::= const_anon */ yytestcase(yyruleno==194);
      case 217: /* atomic_formula_one_const ::= constant_one_const */ yytestcase(yyruleno==217);
#line 964 "bcplus/parser/detail/lemon_parser.y"
{ ATOMIC_FORMULA(yygotominor.yy274, yymsp[0].minor.yy189, true); }
#line 4693 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 191: /* atomic_formula ::= TILDE constant */
      case 195: /* atomic_formula_anon ::= TILDE const_anon */ yytestcase(yyruleno==195);
      case 218: /* atomic_formula_one_const ::= TILDE constant_one_const */ yytestcase(yyruleno==218);
#line 965 "bcplus/parser/detail/lemon_parser.y"
{ ATOMIC_FORMULA(yygotominor.yy274, yymsp[0].minor.yy189, false);   yy_destructor(yypParser,83,&yymsp[-1].minor);
}
#line 4701 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 192: /* atomic_formula ::= constant EQ term */
      case 196: /* atomic_formula_anon ::= const_anon EQ term */ yytestcase(yyruleno==196);
      case 219: /* atomic_formula_one_const ::= constant_one_const EQ term_no_const */ yytestcase(yyruleno==219);
#line 966 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy274 = new AtomicFormula(yymsp[-2].minor.yy189, yymsp[0].minor.yy39, yymsp[-2].minor.yy189->beginLoc(), yymsp[0].minor.yy39->endLoc());	  yy_destructor(yypParser,89,&yymsp[-1].minor);
}
#line 4709 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 193: /* atomic_formula_anon ::= atomic_formula */
      case 311: /* atomic_head_formula ::= atomic_formula */ yytestcase(yyruleno==311);
      case 405: /* show_elem ::= atomic_formula_one_const */ yytestcase(yyruleno==405);
#line 968 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy274 = yymsp[0].minor.yy274; }
#line 4716 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 220: /* formula_quant ::= BRACKET_L quant_lst PIPE formula BRACKET_R */
      case 295: /* formula_temporal_quant ::= BRACKET_L quant_lst PIPE formula_temporal BRACKET_R */ yytestcase(yyruleno==295);
#line 1033 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy387=NULL;
		ref_ptr<const Token> bl_ptr = yymsp[-4].minor.yy0;
		ref_ptr<QuantifierFormula::QuantifierList> lst_ptr = yymsp[-3].minor.yy445;
		ref_ptr<Formula> sub_ptr = yymsp[-1].minor.yy179;
		ref_ptr<const Token> br_ptr = yymsp[0].minor.yy0;

		if (!parser->lang()->support(Language::Feature::FORMULA_QUANTIFIER)) {
			parser->_feature_error(Language::Feature::FORMULA_QUANTIFIER, &yymsp[-4].minor.yy0->beginLoc());
			YYERROR;
		} else yygotominor.yy387 = new QuantifierFormula(yymsp[-3].minor.yy445, yymsp[-1].minor.yy179, yymsp[-4].minor.yy0->beginLoc(), yymsp[0].minor.yy0->endLoc());
	  yy_destructor(yypParser,106,&yymsp[-2].minor);
}
#line 4734 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 221: /* quant_lst ::= quant_op variable */
#line 1047 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy445 = new QuantifierFormula::QuantifierList();
		yygotominor.yy445->push_back(QuantifierFormula::Quantifier(yymsp[-1].minor.yy325, yymsp[0].minor.yy195));
	}
#line 4742 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 222: /* quant_lst ::= quant_lst quant_op variable */
#line 1053 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy445 = yymsp[-2].minor.yy445;
		yygotominor.yy445->push_back(QuantifierFormula::Quantifier(yymsp[-1].minor.yy325, yymsp[0].minor.yy195));
	}
#line 4750 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 223: /* quant_op ::= BIG_CONJ */
#line 1058 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy325 = QuantifierFormula::Operator::CONJ;   yy_destructor(yypParser,98,&yymsp[0].minor);
}
#line 4756 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 224: /* quant_op ::= BIG_DISJ */
#line 1059 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy325 = QuantifierFormula::Operator::DISJ;   yy_destructor(yypParser,99,&yymsp[0].minor);
}
#line 4762 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 225: /* formula_card ::= CBRACKET_L card_var_lst formula CBRACKET_R */
      case 296: /* formula_temporal_card ::= CBRACKET_L card_var_lst formula_temporal CBRACKET_R */ yytestcase(yyruleno==296);
#line 1105 "bcplus/parser/detail/lemon_parser.y"
{ CARD_FORMULA(yygotominor.yy179, NULL, yymsp[-3].minor.yy0, yymsp[-2].minor.yy117, yymsp[-1].minor.yy179, yymsp[0].minor.yy0, NULL);  }
#line 4768 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 226: /* formula_card ::= term_strong CBRACKET_L card_var_lst formula CBRACKET_R */
      case 297: /* formula_temporal_card ::= term_temporal_strong CBRACKET_L card_var_lst formula_temporal CBRACKET_R */ yytestcase(yyruleno==297);
#line 1106 "bcplus/parser/detail/lemon_parser.y"
{ CARD_FORMULA(yygotominor.yy179, yymsp[-4].minor.yy39, yymsp[-3].minor.yy0, yymsp[-2].minor.yy117, yymsp[-1].minor.yy179,  yymsp[0].minor.yy0, NULL);  }
#line 4774 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 227: /* formula_card ::= CBRACKET_L card_var_lst formula CBRACKET_R term */
      case 298: /* formula_temporal_card ::= CBRACKET_L card_var_lst formula_temporal CBRACKET_R term_temporal */ yytestcase(yyruleno==298);
#line 1107 "bcplus/parser/detail/lemon_parser.y"
{ CARD_FORMULA(yygotominor.yy179, NULL, yymsp[-4].minor.yy0, yymsp[-3].minor.yy117, yymsp[-2].minor.yy179, yymsp[-1].minor.yy0, yymsp[0].minor.yy39); 	}
#line 4780 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 228: /* formula_card ::= term_strong CBRACKET_L card_var_lst formula CBRACKET_R term */
      case 299: /* formula_temporal_card ::= term_temporal_strong CBRACKET_L card_var_lst formula_temporal CBRACKET_R term_temporal */ yytestcase(yyruleno==299);
#line 1108 "bcplus/parser/detail/lemon_parser.y"
{ CARD_FORMULA(yygotominor.yy179, yymsp[-5].minor.yy39, yymsp[-4].minor.yy0, yymsp[-3].minor.yy117, yymsp[-2].minor.yy179,  yymsp[-1].minor.yy0, yymsp[0].minor.yy39); 	}
#line 4786 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 229: /* formula_card ::= CBRACKET_L formula CBRACKET_R */
      case 300: /* formula_temporal_card ::= CBRACKET_L formula_temporal CBRACKET_R */ yytestcase(yyruleno==300);
#line 1109 "bcplus/parser/detail/lemon_parser.y"
{ CARD_FORMULA(yygotominor.yy179, NULL, yymsp[-2].minor.yy0, NULL, yymsp[-1].minor.yy179, yymsp[0].minor.yy0, NULL);  }
#line 4792 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 230: /* formula_card ::= term_strong CBRACKET_L formula CBRACKET_R */
      case 301: /* formula_temporal_card ::= term_temporal_strong CBRACKET_L formula_temporal CBRACKET_R */ yytestcase(yyruleno==301);
#line 1110 "bcplus/parser/detail/lemon_parser.y"
{ CARD_FORMULA(yygotominor.yy179, yymsp[-3].minor.yy39, yymsp[-2].minor.yy0, NULL, yymsp[-1].minor.yy179,  yymsp[0].minor.yy0, NULL);  }
#line 4798 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 231: /* formula_card ::= CBRACKET_L formula CBRACKET_R term */
      case 302: /* formula_temporal_card ::= CBRACKET_L formula_temporal CBRACKET_R term_temporal */ yytestcase(yyruleno==302);
#line 1111 "bcplus/parser/detail/lemon_parser.y"
{ CARD_FORMULA(yygotominor.yy179, NULL, yymsp[-3].minor.yy0, NULL, yymsp[-2].minor.yy179, yymsp[-1].minor.yy0, yymsp[0].minor.yy39); 	}
#line 4804 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 232: /* formula_card ::= term_strong CBRACKET_L formula CBRACKET_R term */
      case 303: /* formula_temporal_card ::= term_temporal_strong CBRACKET_L formula_temporal CBRACKET_R term_temporal */ yytestcase(yyruleno==303);
#line 1112 "bcplus/parser/detail/lemon_parser.y"
{ CARD_FORMULA(yygotominor.yy179, yymsp[-4].minor.yy39, yymsp[-3].minor.yy0, NULL, yymsp[-2].minor.yy179,  yymsp[-1].minor.yy0, yymsp[0].minor.yy39); 	}
#line 4810 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 233: /* card_var_lst ::= card_var_lst_inner PIPE */
#line 1116 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy117 = yymsp[-1].minor.yy117;
	  yy_destructor(yypParser,106,&yymsp[0].minor);
}
#line 4818 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 234: /* card_var_lst_inner ::= variable */
#line 1121 "bcplus/parser/detail/lemon_parser.y"
{
		ref_ptr<const Referenced> v_ptr = yymsp[0].minor.yy195;
		yygotominor.yy117 = new CardinalityFormula::VariableList();
		yygotominor.yy117->push_back(yymsp[0].minor.yy195->symbol());
	}
#line 4827 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 235: /* card_var_lst_inner ::= card_var_lst_inner COMMA variable */
#line 1128 "bcplus/parser/detail/lemon_parser.y"
{
		ref_ptr<const Referenced> v_ptr = yymsp[0].minor.yy195;
		yygotominor.yy117 = yymsp[-2].minor.yy117;
		yygotominor.yy117->push_back(yymsp[0].minor.yy195->symbol());
	  yy_destructor(yypParser,110,&yymsp[-1].minor);
}
#line 4837 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 246: /* term_temporal ::= constant */
#line 1183 "bcplus/parser/detail/lemon_parser.y"
{
		// error handline for constants so they don'yygotominor.yy39 default to undeclared identifiers
		yygotominor.yy39 = NULL;
		ref_ptr<const Referenced> c_ptr = yymsp[0].minor.yy189;
		parser->_parse_error("All constant symbols must be bound to a step using the i:F notation.", &yymsp[0].minor.yy189->beginLoc());
		YYERROR;
	}
#line 4848 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 249: /* term_temporal ::= term_temporal COLON term */
      case 263: /* term_temporal_strong ::= term_temporal_strong COLON term_strong */ yytestcase(yyruleno==263);
#line 1195 "bcplus/parser/detail/lemon_parser.y"
{ BINDING(yygotominor.yy39, yymsp[-2].minor.yy39, yymsp[-1].minor.yy0, yymsp[0].minor.yy39, BindingTerm); }
#line 4854 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 281: /* formula_temporal ::= term_temporal_strong COLON formula */
#line 1278 "bcplus/parser/detail/lemon_parser.y"
{ BINDING(yygotominor.yy179, yymsp[-2].minor.yy39, yymsp[-1].minor.yy0, yymsp[0].minor.yy179, BindingFormula); }
#line 4859 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 283: /* formula_temporal_base ::= atomic_formula */
#line 1284 "bcplus/parser/detail/lemon_parser.y"
{
		// error handline for more useful error messages
		yygotominor.yy179 = NULL;
		ref_ptr<const Referenced> l_ptr = yymsp[0].minor.yy274;
		parser->_parse_error("All constant symbols must be bound to a step using the i:F notation.", &yymsp[0].minor.yy274->beginLoc());
		YYERROR;
	}
#line 4870 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 304: /* head_formula ::= head_formula AMP head_formula */
#line 1379 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy179 = new BinaryFormula(BinaryFormula::Operator::AND, yymsp[-2].minor.yy179, yymsp[0].minor.yy179, yymsp[-2].minor.yy179->beginLoc(), yymsp[0].minor.yy179->endLoc());
	  yy_destructor(yypParser,109,&yymsp[-1].minor);
}
#line 4878 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 305: /* head_formula ::= PAREN_L head_formula PAREN_R */
#line 1387 "bcplus/parser/detail/lemon_parser.y"
{
		ref_ptr<const Referenced> lp_ptr = yymsp[-2].minor.yy0, rp_ptr = yymsp[0].minor.yy0;
		yygotominor.yy179 = yymsp[-1].minor.yy179;
		yygotominor.yy179->parens(true);																									\
		yygotominor.yy179->beginLoc(yymsp[-2].minor.yy0->beginLoc());																					\
		yygotominor.yy179->endLoc(yymsp[0].minor.yy0->endLoc());

	}
#line 4890 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 308: /* head_formula ::= formula_smpl_card */
#line 1398 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy179 = yymsp[0].minor.yy393;
		if (!parser->lang()->support(Language::Feature::FORMULA_CARDINALITY_HEAD)) {
			parser->_feature_error(Language::Feature::FORMULA_CARDINALITY_HEAD, &yymsp[0].minor.yy393->beginLoc());
			YYERROR;
		}
	}
#line 4901 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 312: /* atomic_head_formula ::= DASH constant */
#line 1411 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy274 = NULL;
		ref_ptr<const Token> d_ptr = yymsp[-1].minor.yy0;
		ref_ptr<Constant> c_ptr = yymsp[0].minor.yy189;

		if (!parser->lang()->support(Language::Feature::FORMULA_NOT_DASH_HEAD)) {
			parser->_feature_error(Language::Feature::FORMULA_NOT_DASH_HEAD);
			YYERROR;
		} else {
			ATOMIC_FORMULA(yygotominor.yy274, yymsp[0].minor.yy189, false);
		}
	}
#line 4917 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 313: /* formula_smpl_card ::= CBRACKET_L card_var_lst atomic_formula_one_const CBRACKET_R */
#line 1424 "bcplus/parser/detail/lemon_parser.y"
{ CARD_FORMULA(yygotominor.yy393, NULL, yymsp[-3].minor.yy0, yymsp[-2].minor.yy117, yymsp[-1].minor.yy274, yymsp[0].minor.yy0, NULL);  }
#line 4922 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 314: /* formula_smpl_card ::= term_strong CBRACKET_L card_var_lst atomic_formula_one_const CBRACKET_R */
#line 1425 "bcplus/parser/detail/lemon_parser.y"
{ CARD_FORMULA(yygotominor.yy393, yymsp[-4].minor.yy39, yymsp[-3].minor.yy0, yymsp[-2].minor.yy117, yymsp[-1].minor.yy274,  yymsp[0].minor.yy0, NULL);  }
#line 4927 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 315: /* formula_smpl_card ::= CBRACKET_L card_var_lst atomic_formula_one_const CBRACKET_R term */
#line 1426 "bcplus/parser/detail/lemon_parser.y"
{ CARD_FORMULA(yygotominor.yy393, NULL, yymsp[-4].minor.yy0, yymsp[-3].minor.yy117, yymsp[-2].minor.yy274, yymsp[-1].minor.yy0, yymsp[0].minor.yy39); 	}
#line 4932 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 316: /* formula_smpl_card ::= term_strong CBRACKET_L card_var_lst atomic_formula_one_const CBRACKET_R term */
#line 1427 "bcplus/parser/detail/lemon_parser.y"
{ CARD_FORMULA(yygotominor.yy393, yymsp[-5].minor.yy39, yymsp[-4].minor.yy0, yymsp[-3].minor.yy117, yymsp[-2].minor.yy274,  yymsp[-1].minor.yy0, yymsp[0].minor.yy39); 	}
#line 4937 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 317: /* formula_smpl_card ::= CBRACKET_L atomic_formula_one_const CBRACKET_R */
#line 1428 "bcplus/parser/detail/lemon_parser.y"
{ CARD_FORMULA(yygotominor.yy393, NULL, yymsp[-2].minor.yy0, NULL, yymsp[-1].minor.yy274, yymsp[0].minor.yy0, NULL);  }
#line 4942 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 318: /* formula_smpl_card ::= term_strong CBRACKET_L atomic_formula_one_const CBRACKET_R */
#line 1429 "bcplus/parser/detail/lemon_parser.y"
{ CARD_FORMULA(yygotominor.yy393, yymsp[-3].minor.yy39, yymsp[-2].minor.yy0, NULL, yymsp[-1].minor.yy274,  yymsp[0].minor.yy0, NULL);  }
#line 4947 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 319: /* formula_smpl_card ::= CBRACKET_L atomic_formula_one_const CBRACKET_R term */
#line 1430 "bcplus/parser/detail/lemon_parser.y"
{ CARD_FORMULA(yygotominor.yy393, NULL, yymsp[-3].minor.yy0, NULL, yymsp[-2].minor.yy274, yymsp[-1].minor.yy0, yymsp[0].minor.yy39); 	}
#line 4952 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 320: /* formula_smpl_card ::= term_strong CBRACKET_L atomic_formula_one_const CBRACKET_R term */
#line 1431 "bcplus/parser/detail/lemon_parser.y"
{ CARD_FORMULA(yygotominor.yy393, yymsp[-4].minor.yy39, yymsp[-3].minor.yy0, NULL, yymsp[-2].minor.yy274,  yymsp[-1].minor.yy0, yymsp[0].minor.yy39); 	}
#line 4957 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 321: /* stmt_macro_def ::= COLON_DASH MACROS macro_def_lst PERIOD */
#line 1450 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy243 = NULL;
        ref_ptr<const Token> cd_ptr = yymsp[-3].minor.yy0;
        ref_ptr<const Token> kw_ptr = yymsp[-2].minor.yy0;
        ref_ptr<MacroDeclaration::ElementList> l_ptr = yymsp[-1].minor.yy5;
        ref_ptr<const Token> p_ptr = yymsp[0].minor.yy0;

        if (!parser->lang()->support(Language::Feature::DECL_MACRO)) {
            parser->_feature_error(Language::Feature::DECL_MACRO, &yymsp[-2].minor.yy0->beginLoc());
            YYERROR;
        } else {
		    BOOST_FOREACH(symbols::MacroSymbol* m, *yymsp[-1].minor.yy5) {
			    if (!parser->symtab()->create(m)) {
	    	        // Check if it's a duplicate
	    	        symbols::MacroSymbol* m2 = (symbols::MacroSymbol*)parser->symtab()->resolve(symbols::Symbol::Type::MACRO, *m->base(), m->arity());
		            if (!m2 || m2 != m) {
		                parser->_parse_error("Detected conflicting definition of symbol \"" + *m->name() + "\".", &yygotominor.yy243->beginLoc());
		            } else {
		                parser->_parse_error("Detected a duplicate definition of symbol \"" + *m->name() + "\".", &yygotominor.yy243->beginLoc());
		            }
		        }
		    }

			yygotominor.yy243 = new MacroDeclaration(yymsp[-1].minor.yy5, yymsp[-3].minor.yy0->beginLoc(), yymsp[0].minor.yy0->endLoc());
        }
    }
#line 4987 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 322: /* macro_def_lst ::= macro_bnd */
#line 1478 "bcplus/parser/detail/lemon_parser.y"
{
        yygotominor.yy5 = new MacroDeclaration::ElementList();
        yygotominor.yy5->push_back(yymsp[0].minor.yy437);
    }
#line 4995 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 323: /* macro_def_lst ::= macro_def_lst SEMICOLON macro_bnd */
#line 1484 "bcplus/parser/detail/lemon_parser.y"
{
        yygotominor.yy5 = yymsp[-2].minor.yy5;
        yygotominor.yy5->push_back(yymsp[0].minor.yy437);
      yy_destructor(yypParser,101,&yymsp[-1].minor);
}
#line 5004 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 324: /* macro_bnd ::= IDENTIFIER PAREN_L macro_args PAREN_R ARROW_RDASH MACRO_STRING */
#line 1490 "bcplus/parser/detail/lemon_parser.y"
{
        ref_ptr<const Token> id_ptr = yymsp[-5].minor.yy0;
        ref_ptr<MacroSymbol::ArgumentList> args_ptr = yymsp[-3].minor.yy214;
        ref_ptr<const Token> def_ptr = yymsp[0].minor.yy0;

        yygotominor.yy437 = new MacroSymbol(yymsp[-5].minor.yy0->str(), yymsp[0].minor.yy0->str(), yymsp[-3].minor.yy214);
      yy_destructor(yypParser,79,&yymsp[-4].minor);
  yy_destructor(yypParser,80,&yymsp[-2].minor);
  yy_destructor(yypParser,104,&yymsp[-1].minor);
}
#line 5018 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 325: /* macro_bnd ::= IDENTIFIER ARROW_RDASH MACRO_STRING */
#line 1499 "bcplus/parser/detail/lemon_parser.y"
{
        ref_ptr<const Token> id_ptr = yymsp[-2].minor.yy0;
        ref_ptr<const Token> def_ptr = yymsp[0].minor.yy0;

        yygotominor.yy437 = new MacroSymbol(yymsp[-2].minor.yy0->str(), yymsp[0].minor.yy0->str());
      yy_destructor(yypParser,104,&yymsp[-1].minor);
}
#line 5029 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 326: /* macro_args ::= macro_arg */
#line 1507 "bcplus/parser/detail/lemon_parser.y"
{
        yygotominor.yy214 = new MacroSymbol::ArgumentList();
        yygotominor.yy214->push_back(yymsp[0].minor.yy193->str());
        delete yymsp[0].minor.yy193;
    }
#line 5038 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 327: /* macro_args ::= macro_args COMMA macro_arg */
#line 1513 "bcplus/parser/detail/lemon_parser.y"
{
        yygotominor.yy214 = yymsp[-2].minor.yy214;
        yygotominor.yy214->push_back(yymsp[0].minor.yy193->str());
        delete yymsp[0].minor.yy193;
      yy_destructor(yypParser,110,&yymsp[-1].minor);
}
#line 5048 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 328: /* macro_arg ::= POUND_INTEGER */
      case 329: /* macro_arg ::= POUND_IDENTIFIER */ yytestcase(yyruleno==329);
#line 1520 "bcplus/parser/detail/lemon_parser.y"
{
        yygotominor.yy193 = yymsp[0].minor.yy0;
    }
#line 5056 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 330: /* sort_lst ::= sort */
#line 1547 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy423 = new ConstantSymbol::SortList();
		yygotominor.yy423->push_back(yymsp[0].minor.yy69);
	}
#line 5064 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 331: /* sort_lst ::= sort_lst COMMA sort */
#line 1552 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy423 = yymsp[-2].minor.yy423;
		yygotominor.yy423->push_back(yymsp[0].minor.yy69);
	  yy_destructor(yypParser,110,&yymsp[-1].minor);
}
#line 5073 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 332: /* sort ::= sort_id_nr */
      case 338: /* sort_id_nr ::= sort_id */ yytestcase(yyruleno==338);
      case 339: /* sort_id_nr ::= sort_nr */ yytestcase(yyruleno==339);
#line 1577 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy69 = yymsp[0].minor.yy69; }
#line 5080 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 333: /* sort ::= sort_id_nr STAR */
#line 1578 "bcplus/parser/detail/lemon_parser.y"
{ DYNAMIC_SORT_PLUS(yygotominor.yy69, yymsp[-1].minor.yy69, yymsp[0].minor.yy0, Language::Feature::STAR_SORT, parser->symtab()->bobj(SymbolTable::BuiltinObject::NONE)); }
#line 5085 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 334: /* sort ::= sort_id_nr CARROT */
#line 1579 "bcplus/parser/detail/lemon_parser.y"
{ DYNAMIC_SORT_PLUS(yygotominor.yy69, yymsp[-1].minor.yy69, yymsp[0].minor.yy0, Language::Feature::CARROT_SORT, parser->symtab()->bobj(SymbolTable::BuiltinObject::UNKNOWN)); }
#line 5090 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 335: /* sort ::= sort PLUS object_nullary */
#line 1581 "bcplus/parser/detail/lemon_parser.y"
{ u::ref_ptr<const Object> o_ptr = yymsp[0].minor.yy418; DYNAMIC_SORT_PLUS(yygotominor.yy69, yymsp[-2].minor.yy69, yymsp[-1].minor.yy0, Language::Feature::SORT_PLUS, yymsp[0].minor.yy418->symbol()); }
#line 5095 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 336: /* sort ::= sort PLUS IDENTIFIER */
#line 1584 "bcplus/parser/detail/lemon_parser.y"
{
												  u::ref_ptr<const Referenced> s_ptr = yymsp[-2].minor.yy69, op_ptr = yymsp[-1].minor.yy0, id_ptr = yymsp[0].minor.yy0;
												  u::ref_ptr<const ObjectSymbol> obj = parser->symtab()->resolveOrCreate(new ObjectSymbol(yymsp[0].minor.yy0->str()));
												  if(!obj) {
													if (parser->lang()->support(Language::Feature::SORT_PLUS))
														parser->_parse_error("\"" + *yymsp[0].minor.yy0->str() + "\" could not be declared as an object as this conflicts with a previous declarations of this identifier.", &yymsp[0].minor.yy0->beginLoc());
													else
														parser->_feature_error(Language::Feature::SORT_PLUS, &yymsp[-1].minor.yy0->beginLoc());
													YYERROR;
												  } else {
													DYNAMIC_SORT_PLUS(yygotominor.yy69, yymsp[-2].minor.yy69, yymsp[-1].minor.yy0, Language::Feature::SORT_PLUS, obj);
												  }
												}
#line 5112 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 337: /* sort ::= sort PLUS INTEGER */
#line 1598 "bcplus/parser/detail/lemon_parser.y"
{
												  ref_ptr<const Object> t_ptr;
												  BASIC_TERM(t_ptr, yymsp[0].minor.yy0);
												  DYNAMIC_SORT_PLUS(yygotominor.yy69, yymsp[-2].minor.yy69, yymsp[-1].minor.yy0, Language::Feature::SORT_PLUS, t_ptr->symbol());
												}
#line 5121 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 340: /* sort_nr ::= num_range */
#line 1609 "bcplus/parser/detail/lemon_parser.y"
{
		ref_ptr<const Referenced> nr_ptr = yymsp[0].minor.yy107;

		yygotominor.yy69 = NULL;

		if (!parser->lang()->support(Language::Feature::NUMRANGE_SORT)) {
			parser->_feature_error(Language::Feature::NUMRANGE_SORT, &yymsp[0].minor.yy107->beginLoc());
			YYERROR;
		}

		// X..Y becomes __rsort_N_
		if(!(yygotominor.yy69 = parser->_newRange(yymsp[0].minor.yy107->min(), yymsp[0].minor.yy107->max()))) {
			parser->_parse_error("INTERNAL ERROR: An error occurred while instantiating the dynamic sort declaration.", &yymsp[0].minor.yy107->beginLoc());
			YYERROR;
		}
	}
#line 5141 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 341: /* sort_id ::= IDENTIFIER */
#line 1627 "bcplus/parser/detail/lemon_parser.y"
{
		// dynamically declare the sort
		yygotominor.yy69 = (SortSymbol*)parser->symtab()->resolve(Symbol::Type::SORT, *yymsp[0].minor.yy0->str());
		if (!yygotominor.yy69) {
			parser->_parse_error("\"" + Symbol::genName(*yymsp[0].minor.yy0->str(),0) + "\" is not a declared sort test.", &yymsp[0].minor.yy0->beginLoc());
			YYERROR;
		}
		delete yymsp[0].minor.yy0;
	}
#line 5154 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 342: /* stmt_constant_def ::= COLON_DASH CONSTANTS constant_bnd_lst PERIOD */
#line 1658 "bcplus/parser/detail/lemon_parser.y"
{
		ref_ptr<const Token> cd_ptr = yymsp[-3].minor.yy0;
		ref_ptr<const Token> kw_ptr = yymsp[-2].minor.yy0;
		ref_ptr<ConstantDeclaration::ElementList> l_ptr = yymsp[-1].minor.yy451;
		ref_ptr<const Token> p_ptr = yymsp[0].minor.yy0;

		if (!parser->lang()->support(Language::Feature::DECL_CONSTANT)) {
			yygotominor.yy55 = NULL;
			parser->_feature_error(Language::Feature::DECL_CONSTANT, &yymsp[-2].minor.yy0->beginLoc());
			YYERROR;
		} else {
			yygotominor.yy55 = new ConstantDeclaration(yymsp[-1].minor.yy451, yymsp[-3].minor.yy0->beginLoc(), yymsp[0].minor.yy0->endLoc());

		}
	}
#line 5173 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 343: /* constant_bnd_lst ::= constant_bnd */
#line 1675 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy451 = yymsp[0].minor.yy451;
	}
#line 5180 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 344: /* constant_bnd_lst ::= constant_bnd_lst SEMICOLON constant_bnd */
#line 1680 "bcplus/parser/detail/lemon_parser.y"
{
		ref_ptr<ConstantDeclaration::ElementList> bnd_ptr = yymsp[0].minor.yy451;
		yygotominor.yy451 = yymsp[-2].minor.yy451;
		yygotominor.yy451->splice(yygotominor.yy451->end(), *yymsp[0].minor.yy451);
	  yy_destructor(yypParser,101,&yymsp[-1].minor);
}
#line 5190 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 345: /* constant_bnd ::= constant_dcl_lst DBL_COLON constant_dcl_type PAREN_L sort PAREN_R */
#line 1700 "bcplus/parser/detail/lemon_parser.y"
{
		ref_ptr<const SortSymbol> s_ptr = yymsp[-1].minor.yy69;
		ref_ptr<const Referenced> names_ptr = yymsp[-5].minor.yy368;
		yygotominor.yy451 = new ConstantDeclaration::ElementList();

		// NOTE: additive constants default to the additive sort, not the boolean sort
		// if (yymsp[-3].minor.yy449 & ConstantSymbol::Type::M_ADDITIVE) s_ptr = parser->symtab()->bsort(SymbolTable::BuiltinSort::ADDITIVE);

		// external constants should have "unknown" in their sort
		if (yymsp[-3].minor.yy449 & ConstantSymbol::Type::M_EXTERNAL) s_ptr = parser->symtab()->carrot(yymsp[-1].minor.yy69);

		// non-boolean abActions should contain "none"
		else if (yymsp[-3].minor.yy449 == ConstantSymbol::Type::ABACTION && s_ptr->domainType() != DomainType::BOOLEAN) s_ptr = parser->symtab()->star(yymsp[-1].minor.yy69);

		BOOST_FOREACH(IdentifierDecl& decl, *yymsp[-5].minor.yy368) {
			// attempt to declare each symbol
			ref_ptr<ConstantSymbol> c = new ConstantSymbol(yymsp[-3].minor.yy449, decl.first->str(), s_ptr, decl.second);
			yygotominor.yy451->push_back(c);
			CONSTANT_DECL(c, decl.first->beginLoc());
		}
	  yy_destructor(yypParser,84,&yymsp[-4].minor);
  yy_destructor(yypParser,79,&yymsp[-2].minor);
  yy_destructor(yypParser,80,&yymsp[0].minor);
}
#line 5218 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 346: /* constant_bnd ::= constant_dcl_lst DBL_COLON constant_dcl_type PAREN_L REAL BRACKET_L num_range BRACKET_R PAREN_R */
#line 1722 "bcplus/parser/detail/lemon_parser.y"
{
		Term const* min = yymsp[-2].minor.yy107->min();
		ObjectSymbol const* minos;
		ref_ptr<const Object> minObj;
		ref_ptr<const UnaryTerm> minut;
		std::string preMin = "";
		switch(min->subType()){
			case Term::Type::OBJECT:
				minObj = (Object const*)min;
				minos = minObj->symbol();
				break;
			case Term::Type::UNARY:
				minut = (UnaryTerm const*)min;
				switch (minut->op()) {
					case UnaryTerm::Operator::NEGATIVE:			preMin = "-";			break;
					default:
					preMin = "<unknown op>";
					break;
				}
				minObj = (Object const*)minut->sub();
				minos = minObj->symbol();
				break;
			default:
				break;
		}
		Term const* max = yymsp[-2].minor.yy107->max();
		ObjectSymbol const* maxos;
		ref_ptr<const Object> maxObj;
		ref_ptr<const UnaryTerm> maxut;
		std::string preMax = "";
		switch(max->subType()){
			case Term::Type::OBJECT:
				maxObj = (Object const*)max;
				maxos = maxObj->symbol();
				break;
			case Term::Type::UNARY:
				maxut = (UnaryTerm const*)max;
				switch (maxut->op()) {
					case UnaryTerm::Operator::NEGATIVE:			preMax = "-";			break;
					default:
					preMax = "<unknown op>";
					break;
				}
				maxObj = (Object const*)maxut->sub();
				maxos = maxObj->symbol();
				break;
			default:
				break;
		}
		std::string temp = "real["+preMin+*minos->base()+".."+preMax+*maxos->base()+"]";
		ReferencedString const* domainString = new ReferencedString(temp);
		SortSymbol* s = parser->symtab()->resolveOrCreate(new SortSymbol(domainString));
		ref_ptr<const Referenced> nr_ptr = yymsp[-2].minor.yy107;
		ref_ptr<const Referenced> names_ptr = yymsp[-8].minor.yy368;
		ref_ptr<const SortSymbol> s_ptr = s;

		yygotominor.yy451 = new ConstantDeclaration::ElementList();

		// NOTE: additive constants default to the additive sort, not the boolean sort
		// if (yymsp[-6].minor.yy449 & ConstantSymbol::Type::M_ADDITIVE) s_ptr = parser->symtab()->bsort(SymbolTable::BuiltinSort::ADDITIVE);

		// external constants should have "unknown" in their sort
		if (yymsp[-6].minor.yy449 & ConstantSymbol::Type::M_EXTERNAL) s_ptr = parser->symtab()->carrot(s);

		// non-boolean abActions should contain "none"
		else if (yymsp[-6].minor.yy449 == ConstantSymbol::Type::ABACTION && s_ptr->domainType() != DomainType::BOOLEAN) s_ptr = parser->symtab()->star(s);

		BOOST_FOREACH(IdentifierDecl& decl, *yymsp[-8].minor.yy368) {
			// attempt to declare each symbol
			ref_ptr<ConstantSymbol> c = new ConstantSymbol(yymsp[-6].minor.yy449, decl.first->str(), s_ptr, decl.second);
			yygotominor.yy451->push_back(c);
			CONSTANT_DECL(c, decl.first->beginLoc());
		}
	  yy_destructor(yypParser,84,&yymsp[-7].minor);
  yy_destructor(yypParser,79,&yymsp[-5].minor);
  yy_destructor(yypParser,63,&yymsp[-4].minor);
  yy_destructor(yypParser,74,&yymsp[-3].minor);
  yy_destructor(yypParser,75,&yymsp[-1].minor);
  yy_destructor(yypParser,80,&yymsp[0].minor);
}
#line 5302 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 347: /* constant_bnd ::= constant_dcl_lst DBL_COLON CONTINUOUS PAREN_L num_range PAREN_R */
#line 1797 "bcplus/parser/detail/lemon_parser.y"
{
			Term const* min = yymsp[-1].minor.yy107->min();
			ObjectSymbol const* minos;
			ref_ptr<const Object> minObj;
			ref_ptr<const UnaryTerm> minut;
			std::string preMin = "";
			switch(min->subType()){
				case Term::Type::OBJECT:
					minObj = (Object const*)min;
					minos = minObj->symbol();
					break;
				case Term::Type::UNARY:
					minut = (UnaryTerm const*)min;
					switch (minut->op()) {
						case UnaryTerm::Operator::NEGATIVE:			preMin = "-";			break;
						default:
						preMin = "<unknown op>";
						break;
					}
					minObj = (Object const*)minut->sub();
					minos = minObj->symbol();
					break;
				default:
					break;
			}
			Term const* max = yymsp[-1].minor.yy107->max();
			ObjectSymbol const* maxos;
			ref_ptr<const Object> maxObj;
			ref_ptr<const UnaryTerm> maxut;
			std::string preMax = "";
			switch(max->subType()){
				case Term::Type::OBJECT:
					maxObj = (Object const*)max;
					maxos = maxObj->symbol();
					break;
				case Term::Type::UNARY:
					maxut = (UnaryTerm const*)max;
					switch (maxut->op()) {
						case UnaryTerm::Operator::NEGATIVE:			preMax = "-";			break;
						default:
						preMax = "<unknown op>";
						break;
					}
					maxObj = (Object const*)maxut->sub();
					maxos = maxObj->symbol();
					break;
				default:
					break;
			}
			std::string temp = "continuousFluent["+preMin+*minos->base()+".."+preMax+*maxos->base()+"]";
			ReferencedString const* domainString = new ReferencedString(temp);
			SortSymbol* s = parser->symtab()->resolveOrCreate(new SortSymbol(domainString));
			ref_ptr<const Referenced> nr_ptr = yymsp[-1].minor.yy107;
			ref_ptr<const Referenced> names_ptr = yymsp[-5].minor.yy368;
			ref_ptr<const SortSymbol> s_ptr = s;

			yygotominor.yy451 = new ConstantDeclaration::ElementList();

			BOOST_FOREACH(IdentifierDecl& decl, *yymsp[-5].minor.yy368) {
				// attempt to declare each symbol
				ref_ptr<ConstantSymbol> c = new ConstantSymbol(ConstantSymbol::Type::CONTINUOUSFLUENT, decl.first->str(), s_ptr, decl.second);
				yygotominor.yy451->push_back(c);
				CONSTANT_DECL(c, decl.first->beginLoc());
			}

			if(implicit){
				ReferencedString const* durationDecl = new ReferencedString("duration");
				ReferencedString const* durationSortString = new ReferencedString("real[0..50]");
				SortSymbol* durationSort = parser->symtab()->resolveOrCreate(new SortSymbol(durationSortString));
				ref_ptr<ConstantSymbol> duration = new ConstantSymbol(ConstantSymbol::Type::EXOGENOUSACTION, durationDecl, durationSort, NULL);
				yygotominor.yy451->push_back(duration);
				CONSTANT_DECL(duration, yymsp[-1].minor.yy107->beginLoc());

				ReferencedString const* modeDecl = new ReferencedString("mode");
				ReferencedString const* modeSortString = new ReferencedString("real[0..3]");
				SortSymbol* modeSort = parser->symtab()->resolveOrCreate(new SortSymbol(modeSortString));
				ref_ptr<ConstantSymbol> mode = new ConstantSymbol(ConstantSymbol::Type::INERTIALFLUENT, modeDecl, modeSort, NULL);
				yygotominor.yy451->push_back(mode);
				CONSTANT_DECL(mode, yymsp[-1].minor.yy107->beginLoc());

				ReferencedString const* waitDecl = new ReferencedString("wait");
				ref_ptr<SortSymbol> waitSort = parser->symtab()->bsort(SymbolTable::BuiltinSort::BOOLEAN);
				ref_ptr<ConstantSymbol> wait = new ConstantSymbol(ConstantSymbol::Type::ACTION, waitDecl, waitSort, NULL);
				yygotominor.yy451->push_back(wait);
				CONSTANT_DECL(wait, yymsp[-1].minor.yy107->beginLoc());
				implicit=false;
			}
		  yy_destructor(yypParser,84,&yymsp[-4].minor);
  yy_destructor(yypParser,64,&yymsp[-3].minor);
  yy_destructor(yypParser,79,&yymsp[-2].minor);
  yy_destructor(yypParser,80,&yymsp[0].minor);
}
#line 5398 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 348: /* constant_bnd ::= constant_dcl_lst DBL_COLON sort */
#line 1886 "bcplus/parser/detail/lemon_parser.y"
{
		ref_ptr<const Referenced> names_ptr = yymsp[-2].minor.yy368, s_ptr = yymsp[0].minor.yy69;
		yygotominor.yy451 = new ConstantDeclaration::ElementList();
		BOOST_FOREACH(IdentifierDecl& decl, *yymsp[-2].minor.yy368) {
			// attempt to declare each symbol
			ref_ptr<ConstantSymbol> c = new ConstantSymbol(ConstantSymbol::Type::RIGID, decl.first->str(), yymsp[0].minor.yy69, decl.second);
			yygotominor.yy451->push_back(c);
			CONSTANT_DECL(c, decl.first->beginLoc());
		}
	  yy_destructor(yypParser,84,&yymsp[-1].minor);
}
#line 5413 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 349: /* constant_bnd ::= constant_dcl_lst DBL_COLON REAL BRACKET_L num_range BRACKET_R */
#line 1897 "bcplus/parser/detail/lemon_parser.y"
{
		ref_ptr<const Object> min = (Object const*)yymsp[-1].minor.yy107->min();
		ref_ptr<const Object> max = (Object const*)yymsp[-1].minor.yy107->max();
		ObjectSymbol const* minos = min->symbol();
		ObjectSymbol const* maxos = max->symbol();
		std::string temp = "real["+*minos->base()+".."+*maxos->base()+"]";
		ReferencedString const* domainString = new ReferencedString(temp);
		SortSymbol* s = parser->symtab()->resolveOrCreate(new SortSymbol(domainString));
		ref_ptr<const Referenced> nr_ptr = yymsp[-1].minor.yy107;
		ref_ptr<const Referenced> names_ptr = yymsp[-5].minor.yy368;
		ref_ptr<const SortSymbol> s_ptr = s;

		yygotominor.yy451 = new ConstantDeclaration::ElementList();
		BOOST_FOREACH(IdentifierDecl& decl, *yymsp[-5].minor.yy368) {
			// attempt to declare each symbol
			ref_ptr<ConstantSymbol> c = new ConstantSymbol(ConstantSymbol::Type::RIGID, decl.first->str(), s, decl.second);
			yygotominor.yy451->push_back(c);
			CONSTANT_DECL(c, decl.first->beginLoc());
		}
	  yy_destructor(yypParser,84,&yymsp[-4].minor);
  yy_destructor(yypParser,63,&yymsp[-3].minor);
  yy_destructor(yypParser,74,&yymsp[-2].minor);
  yy_destructor(yypParser,75,&yymsp[0].minor);
}
#line 5441 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 350: /* constant_bnd ::= constant_dcl_lst DBL_COLON constant_dcl_type */
#line 1918 "bcplus/parser/detail/lemon_parser.y"
{
		ref_ptr<const Referenced> names_ptr = yymsp[-2].minor.yy368;
		yygotominor.yy451 = new ConstantDeclaration::ElementList();
		BOOST_FOREACH(IdentifierDecl& decl, *yymsp[-2].minor.yy368) {
			// attempt to declare each symbol
			ref_ptr<SortSymbol> s = parser->symtab()->bsort(SymbolTable::BuiltinSort::BOOLEAN);

			// NOTE: additive constants default to the additive sort, not the boolean sort
			if (yymsp[0].minor.yy449 & ConstantSymbol::Type::M_ADDITIVE && s->domainType() == DomainType::BOOLEAN )
				s = parser->symtab()->bsort(SymbolTable::BuiltinSort::ADDITIVE);

			// external constants should have "unknown" in their sort
			else if (yymsp[0].minor.yy449 & ConstantSymbol::Type::M_EXTERNAL)
				s = parser->symtab()->carrot(s);

			// non-boolean abActions should contain "none"
			else if (yymsp[0].minor.yy449 == ConstantSymbol::Type::ABACTION && s->domainType() != DomainType::BOOLEAN)
				s = parser->symtab()->star(s);


			ref_ptr<ConstantSymbol> c = new ConstantSymbol(yymsp[0].minor.yy449, decl.first->str(), s, decl.second);
			yygotominor.yy451->push_back(c);
			CONSTANT_DECL(c, decl.first->beginLoc());
		}
	  yy_destructor(yypParser,84,&yymsp[-1].minor);
}
#line 5471 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 351: /* constant_bnd ::= constant_dcl_lst DBL_COLON attrib_spec OF IDENTIFIER */
#line 1944 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy451 = NULL;
		ref_ptr<const Referenced> names_ptr = yymsp[-4].minor.yy368, s_ptr = yymsp[-2].minor.yy32, id_ptr = yymsp[0].minor.yy0;


		// attempt to resolve the attribute parent symbol
		ConstantSymbol const* c = (ConstantSymbol const*) parser->symtab()->resolve(Symbol::Type::CONSTANT, *yymsp[0].minor.yy0->str());

		if (!c) {
			parser->_parse_error("\"" + Symbol::genName(*yymsp[0].minor.yy0->str(), 0) + "\" is not a valid constant symbol.", &yymsp[0].minor.yy0->beginLoc());
			YYERROR;
		} else if (c->constType() != ConstantSymbol::Type::ABACTION && c->constType() != ConstantSymbol::Type::ACTION && c->constType() != ConstantSymbol::Type::EXOGENOUSACTION) {
			parser->_parse_error("Unexpected constant type of attribute parent \"" + Symbol::genName(*yymsp[0].minor.yy0->str(), 0) + "\". Attribute parents must be an \"abAction\", \"action\", or \"exogenousAction\".", &yymsp[0].minor.yy0->beginLoc());
			YYERROR;
		} else {
			yygotominor.yy451 = new ConstantDeclaration::ElementList();
			BOOST_FOREACH(IdentifierDecl& decl, *yymsp[-4].minor.yy368) {
				ref_ptr<ConstantSymbol> c= new AttributeSymbol(decl.first->str(), yymsp[-2].minor.yy32, c, decl.second);
				yygotominor.yy451->push_back(c);
				CONSTANT_DECL(c, decl.first->beginLoc());
			}
		}
	  yy_destructor(yypParser,84,&yymsp[-3].minor);
  yy_destructor(yypParser,61,&yymsp[-1].minor);
}
#line 5500 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 352: /* constant_bnd ::= constant_dcl_lst DBL_COLON attrib_spec OF IDENTIFIER PAREN_L sort_lst PAREN_R */
#line 1968 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy451 = NULL;
		ref_ptr<const Referenced> names_ptr = yymsp[-7].minor.yy368, s_ptr = yymsp[-5].minor.yy32, id_ptr = yymsp[-3].minor.yy0, lst_ptr = yymsp[-1].minor.yy423;

		// attempt to resolve the attribute parent symbol
		ConstantSymbol const* c = (ConstantSymbol const*) parser->symtab()->resolve(Symbol::Type::CONSTANT, *yymsp[-3].minor.yy0->str(), yymsp[-1].minor.yy423->size());

		if (!c) {
			parser->_parse_error("\"" + Symbol::genName(*yymsp[-3].minor.yy0->str(), yymsp[-1].minor.yy423->size()) + "\" is not a valid constant symbol.", &yymsp[-3].minor.yy0->beginLoc());
			YYERROR;
		} else if (c->constType() != ConstantSymbol::Type::ABACTION && c->constType() != ConstantSymbol::Type::ACTION && c->constType() != ConstantSymbol::Type::EXOGENOUSACTION) {
			parser->_parse_error("Unexpected constant type of attribute parent \"" + Symbol::genName(*yymsp[-3].minor.yy0->str(), yymsp[-1].minor.yy423->size()) + "\". Attribute parents must be an \"abAction\", \"action\", or \"exogenousAction\".", &yymsp[-3].minor.yy0->beginLoc());
			YYERROR;
		} else {
			// ensure that the sorts match the declaration of the symbol
			SortList::const_iterator it = yymsp[-1].minor.yy423->begin();
			BOOST_FOREACH(SortSymbol const* sort, *c) {
				if (*it != sort) {
					// check to see if it'yymsp[-5].minor.yy32 a subsort, which is also permissable
					bool found = false;
					for (SortSymbol::SortList::const_iterator it2 = sort->beginSubSorts(); it2 != sort->endSubSorts(); it2++) {
						if (*it == *it2) {
							found = true;
							break;
						}
					}

					if (!found) {
						parser->_parse_error("Detected a sort mismatch in an attribute parent declaration. \"" + *(*it)->base() + "\" is not an explicit subsort of \"" + *sort->base() + "\".", &yymsp[-3].minor.yy0->beginLoc());
						YYERROR;
					}
				}
				it++;
			}

			yygotominor.yy451 = new ConstantDeclaration::ElementList();
			BOOST_FOREACH(IdentifierDecl& decl, *yymsp[-7].minor.yy368) {
				// ensure that the sorts match the start of the sort list for each of the symbols
				if (decl.second->size() < yymsp[-1].minor.yy423->size()) {
					parser->_parse_error("Detected a malformed attribute declaration. An attribute must duplicate its parent'yymsp[-5].minor.yy32 parameters.", &decl.first->beginLoc());
					YYERROR;
				} else {
					bool good_sort = true;
					it = decl.second->begin();
					BOOST_FOREACH(SortSymbol const* sort, *yymsp[-1].minor.yy423) {
						if (*it != sort) {
							// check to see if it'yymsp[-5].minor.yy32 a subsort, which is also permissable
							bool found = false;
							for (SortSymbol::SortList::const_iterator it2 = sort->beginSubSorts(); it2 != sort->endSubSorts(); it2++) {
								if (*it == *it2) {
									found = true;
									break;
								}
							}
							if (!found) {
								good_sort = false;
								parser->_parse_error("Detected a sort mismatch in an attribute declaration. \"" + *(*it)->base() + "\" is not an explicit subsort of \"" + *sort->base() + "\".", &decl.first->beginLoc());
								YYERROR;
							}
						}
						it++;
					}

					if (good_sort) {
						ref_ptr<ConstantSymbol> sym = new AttributeSymbol(decl.first->str(), yymsp[-5].minor.yy32, c, decl.second);
						yygotominor.yy451->push_back(sym);
						CONSTANT_DECL(sym, decl.first->beginLoc());

					}
				}
			}
		}
	  yy_destructor(yypParser,84,&yymsp[-6].minor);
  yy_destructor(yypParser,61,&yymsp[-4].minor);
  yy_destructor(yypParser,79,&yymsp[-2].minor);
  yy_destructor(yypParser,80,&yymsp[0].minor);
}
#line 5581 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 353: /* constant_dcl_lst ::= IDENTIFIER */
#line 2044 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy368 = new IdentifierDeclList();
		yygotominor.yy368->push_back(IdentifierDecl(yymsp[0].minor.yy0, NULL));
	}
#line 5589 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 354: /* constant_dcl_lst ::= IDENTIFIER PAREN_L sort_lst PAREN_R */
#line 2049 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy368 = new IdentifierDeclList();
		yygotominor.yy368->push_back(IdentifierDecl(yymsp[-3].minor.yy0, yymsp[-1].minor.yy423));
	  yy_destructor(yypParser,79,&yymsp[-2].minor);
  yy_destructor(yypParser,80,&yymsp[0].minor);
}
#line 5599 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 355: /* constant_dcl_lst ::= constant_dcl_lst COMMA IDENTIFIER */
#line 2054 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy368 = yymsp[-2].minor.yy368;
		yygotominor.yy368->push_back(IdentifierDecl(yymsp[0].minor.yy0, NULL));
	  yy_destructor(yypParser,110,&yymsp[-1].minor);
}
#line 5608 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 356: /* constant_dcl_lst ::= constant_dcl_lst COMMA IDENTIFIER PAREN_L sort_lst PAREN_R */
#line 2059 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy368 = yymsp[-5].minor.yy368;
		yygotominor.yy368->push_back(IdentifierDecl(yymsp[-3].minor.yy0, yymsp[-1].minor.yy423));
	  yy_destructor(yypParser,110,&yymsp[-4].minor);
  yy_destructor(yypParser,79,&yymsp[-2].minor);
  yy_destructor(yypParser,80,&yymsp[0].minor);
}
#line 5619 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 357: /* constant_dcl_type ::= ABACTION */
#line 2066 "bcplus/parser/detail/lemon_parser.y"
{
		ref_ptr<const Token> tok_ptr = yymsp[0].minor.yy0;
		yygotominor.yy449 = ConstantSymbol::Type::ABACTION;
		if (!parser->lang()->support(Language::Feature::CONST_ABACTION)) {
			parser->_feature_error(Language::Feature::CONST_ABACTION, &yymsp[0].minor.yy0->beginLoc());
			YYERROR;
		}
	}
#line 5631 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 358: /* constant_dcl_type ::= ACTION */
#line 2075 "bcplus/parser/detail/lemon_parser.y"
{
		ref_ptr<const Token> tok_ptr = yymsp[0].minor.yy0;
		yygotominor.yy449 = ConstantSymbol::Type::ACTION;
		if (!parser->lang()->support(Language::Feature::CONST_ACTION)) {
			parser->_feature_error(Language::Feature::CONST_ACTION, &yymsp[0].minor.yy0->beginLoc());
			YYERROR;
		}
	}
#line 5643 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 359: /* constant_dcl_type ::= ADDITIVEACTION */
#line 2084 "bcplus/parser/detail/lemon_parser.y"
{
		ref_ptr<const Token> tok_ptr = yymsp[0].minor.yy0;
		yygotominor.yy449 = ConstantSymbol::Type::ADDITIVEACTION;
		if (!parser->lang()->support(Language::Feature::CONST_ADDITIVEACTION)) {
			parser->_feature_error(Language::Feature::CONST_ADDITIVEACTION, &yymsp[0].minor.yy0->beginLoc());
			YYERROR;
		}
	}
#line 5655 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 360: /* constant_dcl_type ::= ADDITIVEFLUENT */
#line 2093 "bcplus/parser/detail/lemon_parser.y"
{
		ref_ptr<const Token> tok_ptr = yymsp[0].minor.yy0;
		yygotominor.yy449 = ConstantSymbol::Type::ADDITIVEFLUENT;
		if (!parser->lang()->support(Language::Feature::CONST_ADDITIVEFLUENT)) {
			parser->_feature_error(Language::Feature::CONST_ADDITIVEFLUENT, &yymsp[0].minor.yy0->beginLoc());
			YYERROR;
		}
	}
#line 5667 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 361: /* constant_dcl_type ::= EXTERNALACTION */
#line 2102 "bcplus/parser/detail/lemon_parser.y"
{
		ref_ptr<const Token> tok_ptr = yymsp[0].minor.yy0;
		yygotominor.yy449 = ConstantSymbol::Type::EXTERNALACTION;
		if (!parser->lang()->support(Language::Feature::CONST_EXTERNALACTION)) {
			parser->_feature_error(Language::Feature::CONST_EXTERNALACTION, &yymsp[0].minor.yy0->beginLoc());
			YYERROR;
		}
	}
#line 5679 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 362: /* constant_dcl_type ::= EXTERNALFLUENT */
#line 2111 "bcplus/parser/detail/lemon_parser.y"
{
		ref_ptr<const Token> tok_ptr = yymsp[0].minor.yy0;
		yygotominor.yy449 = ConstantSymbol::Type::EXTERNALFLUENT;
		if (!parser->lang()->support(Language::Feature::CONST_EXTERNALFLUENT)) {
			parser->_feature_error(Language::Feature::CONST_EXTERNALFLUENT, &yymsp[0].minor.yy0->beginLoc());
			YYERROR;
		}
	}
#line 5691 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 363: /* constant_dcl_type ::= EXOGENOUSACTION */
#line 2120 "bcplus/parser/detail/lemon_parser.y"
{
		ref_ptr<const Token> tok_ptr = yymsp[0].minor.yy0;
		yygotominor.yy449 = ConstantSymbol::Type::EXOGENOUSACTION;
		if (!parser->lang()->support(Language::Feature::CONST_EXOGENOUSACTION)) {
			parser->_feature_error(Language::Feature::CONST_EXOGENOUSACTION, &yymsp[0].minor.yy0->beginLoc());
			YYERROR;
		}
	}
#line 5703 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 364: /* constant_dcl_type ::= INERTIALFLUENT */
#line 2129 "bcplus/parser/detail/lemon_parser.y"
{
		ref_ptr<const Token> tok_ptr = yymsp[0].minor.yy0;
		yygotominor.yy449 = ConstantSymbol::Type::INERTIALFLUENT;
		if (!parser->lang()->support(Language::Feature::CONST_INERTIALFLUENT)) {
			parser->_feature_error(Language::Feature::CONST_INERTIALFLUENT, &yymsp[0].minor.yy0->beginLoc());
			YYERROR;
		}
	}
#line 5715 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 365: /* constant_dcl_type ::= RIGID */
#line 2138 "bcplus/parser/detail/lemon_parser.y"
{
		ref_ptr<const Token> tok_ptr = yymsp[0].minor.yy0;
		yygotominor.yy449 = ConstantSymbol::Type::RIGID;
		if (!parser->lang()->support(Language::Feature::CONST_RIGID)) {
			parser->_feature_error(Language::Feature::CONST_RIGID, &yymsp[0].minor.yy0->beginLoc());
			YYERROR;
		}
	}
#line 5727 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 366: /* constant_dcl_type ::= SIMPLEFLUENT */
#line 2147 "bcplus/parser/detail/lemon_parser.y"
{
		ref_ptr<const Token> tok_ptr = yymsp[0].minor.yy0;
		yygotominor.yy449 = ConstantSymbol::Type::SIMPLEFLUENT;
		if (!parser->lang()->support(Language::Feature::CONST_SIMPLEFLUENT)) {
			parser->_feature_error(Language::Feature::CONST_SIMPLEFLUENT, &yymsp[0].minor.yy0->beginLoc());
			YYERROR;
		}
	}
#line 5739 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 367: /* constant_dcl_type ::= SDFLUENT */
#line 2157 "bcplus/parser/detail/lemon_parser.y"
{
		ref_ptr<const Token> tok_ptr = yymsp[0].minor.yy0;
		yygotominor.yy449 = ConstantSymbol::Type::SDFLUENT;
		if (!parser->lang()->support(Language::Feature::CONST_SDFLUENT)) {
			parser->_feature_error(Language::Feature::CONST_SDFLUENT, &yymsp[0].minor.yy0->beginLoc());
			YYERROR;
		}
	}
#line 5751 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 368: /* attrib_spec ::= ATTRIBUTE */
#line 2167 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy32 = NULL;
		ref_ptr<const Referenced> kw_ptr = yymsp[0].minor.yy0;
		if (!parser->lang()->support(Language::Feature::CONST_ATTRIBUTE)) {
			parser->_feature_error(Language::Feature::CONST_ATTRIBUTE, &yymsp[0].minor.yy0->beginLoc());
			YYERROR;
		} else {
			// grab the boolean sort and provide it
			yygotominor.yy32 = parser->symtab()->star(parser->symtab()->bsort(SymbolTable::BuiltinSort::BOOLEAN));
		}
	}
#line 5766 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 369: /* attrib_spec ::= ATTRIBUTE PAREN_L sort PAREN_R */
#line 2180 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy32 = NULL;
		ref_ptr<const Referenced> kw_ptr = yymsp[-3].minor.yy0, s_ptr = yymsp[-1].minor.yy69;
		if (!parser->lang()->support(Language::Feature::CONST_ATTRIBUTE)) {
			parser->_feature_error(Language::Feature::CONST_ATTRIBUTE, &yymsp[-3].minor.yy0->beginLoc());
			YYERROR;
		} else {
			yygotominor.yy32 = parser->symtab()->star(yymsp[-1].minor.yy69);
		}
	  yy_destructor(yypParser,79,&yymsp[-2].minor);
  yy_destructor(yypParser,80,&yymsp[0].minor);
}
#line 5782 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 370: /* attrib_spec ::= ATTRIBUTE PAREN_L REAL BRACKET_L num_range BRACKET_R PAREN_R */
#line 2192 "bcplus/parser/detail/lemon_parser.y"
{
			yygotominor.yy32 = NULL;
			Term const* min = yymsp[-2].minor.yy107->min();
			ObjectSymbol const* minos;
			ref_ptr<const Object> minObj;
			ref_ptr<const UnaryTerm> minut;
			std::string preMin = "";
			switch(min->subType()){
				case Term::Type::OBJECT:
					minObj = (Object const*)min;
					minos = minObj->symbol();
					break;
				case Term::Type::UNARY:
					minut = (UnaryTerm const*)min;
					switch (minut->op()) {
						case UnaryTerm::Operator::NEGATIVE:			preMin = "-";			break;
						default:
						preMin = "<unknown op>";
						break;
					}
					minObj = (Object const*)minut->sub();
					minos = minObj->symbol();
					break;
				default:
					break;
			}
			Term const* max = yymsp[-2].minor.yy107->max();
			ObjectSymbol const* maxos;
			ref_ptr<const Object> maxObj;
			ref_ptr<const UnaryTerm> maxut;
			std::string preMax = "";
			switch(max->subType()){
				case Term::Type::OBJECT:
					maxObj = (Object const*)max;
					maxos = maxObj->symbol();
					break;
				case Term::Type::UNARY:
					maxut = (UnaryTerm const*)max;
					switch (maxut->op()) {
						case UnaryTerm::Operator::NEGATIVE:			preMax = "-";			break;
						default:
						preMax = "<unknown op>";
						break;
					}
					maxObj = (Object const*)maxut->sub();
					maxos = maxObj->symbol();
					break;
				default:
					break;
			}
			std::string temp = "real["+preMin+*minos->base()+".."+preMax+*maxos->base()+"]";
			ReferencedString const* domainString = new ReferencedString(temp);
			SortSymbol* s = parser->symtab()->resolveOrCreate(new SortSymbol(domainString));
			ref_ptr<const Referenced> nr_ptr = yymsp[-2].minor.yy107;
			ref_ptr<const Referenced> kw_ptr = yymsp[-6].minor.yy0, s_ptr = s;
			if (!parser->lang()->support(Language::Feature::CONST_ATTRIBUTE)) {
				parser->_feature_error(Language::Feature::CONST_ATTRIBUTE, &yymsp[-6].minor.yy0->beginLoc());
				YYERROR;
			} else {
				yygotominor.yy32 = parser->symtab()->star(s);
			}
		  yy_destructor(yypParser,79,&yymsp[-5].minor);
  yy_destructor(yypParser,63,&yymsp[-4].minor);
  yy_destructor(yypParser,74,&yymsp[-3].minor);
  yy_destructor(yypParser,75,&yymsp[-1].minor);
  yy_destructor(yypParser,80,&yymsp[0].minor);
}
#line 5853 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 371: /* stmt_object_def ::= COLON_DASH OBJECTS object_bnd_lst PERIOD */
#line 2274 "bcplus/parser/detail/lemon_parser.y"
{
		ref_ptr<const Token> cd_ptr = yymsp[-3].minor.yy0;
		ref_ptr<const Token> p_ptr = yymsp[0].minor.yy0;
		ref_ptr<const Token> kw_ptr = yymsp[-2].minor.yy0;
		ref_ptr<ObjectDeclaration::ElementList> l_ptr = yymsp[-1].minor.yy419;

		if (!parser->lang()->support(Language::Feature::DECL_OBJECT)) {
			yygotominor.yy24 = NULL;
			parser->_feature_error(Language::Feature::DECL_OBJECT, &yymsp[-2].minor.yy0->beginLoc());
			YYERROR;
		} else {
			yygotominor.yy24 = new ObjectDeclaration(yymsp[-1].minor.yy419, yymsp[-3].minor.yy0->beginLoc(), yymsp[0].minor.yy0->endLoc());

			// Go ahead and add them to the symbol table
			BOOST_FOREACH(ObjectDeclaration::Element* bnd, *yymsp[-1].minor.yy419) {
				BOOST_FOREACH(Symbol const* o, *bnd) {
					switch (o->type()) {
					case Symbol::Type::OBJECT:
						bnd->sort()->add((ObjectSymbol const*)o);
						break;
					case Symbol::Type::RANGE:
						bnd->sort()->add((NumberRangeSymbol const*)o);
						break;
					default:
						// will not happen
						break;
					}
				}
			}
		}
	}
#line 5888 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 372: /* object_bnd_lst ::= object_bnd */
#line 2307 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy419 = new ObjectDeclaration::ElementList();
		yygotominor.yy419->push_back(yymsp[0].minor.yy332);
	}
#line 5896 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 373: /* object_bnd_lst ::= object_bnd_lst SEMICOLON object_bnd */
#line 2313 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy419 = yymsp[-2].minor.yy419;
		yygotominor.yy419->push_back(yymsp[0].minor.yy332);
	  yy_destructor(yypParser,101,&yymsp[-1].minor);
}
#line 5905 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 374: /* object_bnd ::= object_lst DBL_COLON sort_id */
#line 2319 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy332 = new ObjectDeclaration::Element(yymsp[0].minor.yy69, yymsp[-2].minor.yy323);
	  yy_destructor(yypParser,84,&yymsp[-1].minor);
}
#line 5913 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 375: /* object_lst ::= object_spec */
#line 2324 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy323 = yymsp[0].minor.yy323;
	}
#line 5920 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 376: /* object_lst ::= object_lst COMMA object_spec */
#line 2328 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy323 = yymsp[-2].minor.yy323;
		yygotominor.yy323->splice(yygotominor.yy323->end(), *yymsp[0].minor.yy323);
		delete yymsp[0].minor.yy323;
	  yy_destructor(yypParser,110,&yymsp[-1].minor);
}
#line 5930 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 377: /* object_spec ::= IDENTIFIER */
#line 2337 "bcplus/parser/detail/lemon_parser.y"
{
		ref_ptr<const Token> id_ptr = yymsp[0].minor.yy0;
		yygotominor.yy323 = NULL;
		ref_ptr<const Symbol> o = parser->symtab()->resolveOrCreate(new ObjectSymbol(yymsp[0].minor.yy0->str()));
		if (!o) {
			parser->_parse_error("Detected a conflicting definition of \"" + Symbol::genName(*yymsp[0].minor.yy0->str(),0) + "\".", &yymsp[0].minor.yy0->beginLoc());
			YYERROR;
		} else {
			yygotominor.yy323 = new ObjectDeclaration::Element::ObjectList();
			yygotominor.yy323->push_back(o);
		}
	}
#line 5946 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 378: /* object_spec ::= IDENTIFIER PAREN_L sort_lst PAREN_R */
#line 2350 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy323 = NULL;
		ref_ptr<ObjectSymbol::SortList> lst_ptr = yymsp[-1].minor.yy423;
		ref_ptr<const Token> id_ptr = yymsp[-3].minor.yy0;
		ref_ptr<ObjectSymbol> o = parser->symtab()->resolveOrCreate(new ObjectSymbol(yymsp[-3].minor.yy0->str(), yymsp[-1].minor.yy423));
		if (!o) {
			parser->_parse_error("Detected a conflicting definition of \"" + Symbol::genName(*yymsp[-3].minor.yy0->str(),yymsp[-1].minor.yy423->size()) + "\".", &yymsp[-3].minor.yy0->beginLoc());
			YYERROR;
		} else {
			yygotominor.yy323 = new  ObjectDeclaration::Element::ObjectList();
			yygotominor.yy323->push_back(o.get());
		}
	  yy_destructor(yypParser,79,&yymsp[-2].minor);
  yy_destructor(yypParser,80,&yymsp[0].minor);
}
#line 5965 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 379: /* object_spec ::= INTEGER */
#line 2365 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy323 = NULL;
		ref_ptr<const Token> id_ptr = yymsp[0].minor.yy0;
		ref_ptr<const ObjectSymbol> o = parser->symtab()->resolveOrCreate(new ObjectSymbol(yymsp[0].minor.yy0->str()));
		if (!o) {
			parser->_parse_error("Detected a conflicting definition of \"" + Symbol::genName(*yymsp[0].minor.yy0->str(),0) + "\".", &yymsp[0].minor.yy0->beginLoc());
			YYERROR;
		} else {
			yygotominor.yy323 = new ObjectDeclaration::Element::ObjectList();
			yygotominor.yy323->push_back(o.get());
		}
	}
#line 5981 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 380: /* object_spec ::= FLOAT */
#line 2379 "bcplus/parser/detail/lemon_parser.y"
{
			yygotominor.yy323 = NULL;
			ref_ptr<const Token> id_ptr = yymsp[0].minor.yy0;
			ref_ptr<const ObjectSymbol> o = parser->symtab()->resolveOrCreate(new ObjectSymbol(yymsp[0].minor.yy0->str()));
			if (!o) {
				parser->_parse_error("Detected a conflicting definition of \"" + Symbol::genName(*yymsp[0].minor.yy0->str(),0) + "\".", &yymsp[0].minor.yy0->beginLoc());
				YYERROR;
			} else {
				yygotominor.yy323 = new ObjectDeclaration::Element::ObjectList();
				yygotominor.yy323->push_back(o.get());
			}
		}
#line 5997 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 381: /* object_spec ::= num_range */
#line 2393 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy323 = new ObjectDeclaration::Element::ObjectList();
		ref_ptr<const Referenced> nr_ptr = yymsp[0].minor.yy107;

		// iterate over the range and add it to the list
		ref_ptr<const Symbol> o = parser->symtab()->resolveOrCreate(parser->_newRangeSymbol( yymsp[0].minor.yy107->min(), yymsp[0].minor.yy107->max()));
		if (!o) {
			parser->_parse_error("INTERNAL ERROR: Could not create object symbol.", &yymsp[0].minor.yy107->beginLoc());
			YYERROR;
		} else {
			yygotominor.yy323->push_back(o.get());
		}
	}
#line 6014 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 382: /* stmt_variable_def ::= COLON_DASH VARIABLES variable_bnd_lst PERIOD */
#line 2422 "bcplus/parser/detail/lemon_parser.y"
{
		ref_ptr<const Token> cd_ptr = yymsp[-3].minor.yy0;
		ref_ptr<const Token> p_ptr = yymsp[0].minor.yy0;
		ref_ptr<const Token> kw_ptr = yymsp[-2].minor.yy0;
		ref_ptr<VariableDeclaration::ElementList> l_ptr = yymsp[-1].minor.yy424;

		if (!parser->lang()->support(Language::Feature::DECL_VARIABLE)) {
			yygotominor.yy19 = NULL;
			parser->_feature_error(Language::Feature::DECL_VARIABLE, &yymsp[-2].minor.yy0->beginLoc());
			YYERROR;
		} else {

			VariableSymbol* v2;

			// Go ahead and add them to the symbol table
			BOOST_FOREACH(ref_ptr<VariableSymbol>& v, *yymsp[-1].minor.yy424) {
				if (!(v2 = parser->symtab()->resolveOrCreate(v))) {
					// Check if it's a duplicate
					v2 = (VariableSymbol*)parser->symtab()->resolve(Symbol::Type::VARIABLE, *v->base());
					if (!v2 || v2 != v) {
						parser->_parse_error("Detected conflicting definition of symbol \"" + *v->name() + "\".", &yymsp[-3].minor.yy0->beginLoc());
					} else {
						parser->_parse_error("Detected a duplicate definition of symbol \"" + *v->name() + "\".", &yymsp[-3].minor.yy0->beginLoc());
					}
				} else {
					v = v2;
				}
			}

			yygotominor.yy19 = new VariableDeclaration(yymsp[-1].minor.yy424, yymsp[-3].minor.yy0->beginLoc(), yymsp[0].minor.yy0->endLoc());


		}
	}
#line 6052 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 383: /* variable_bnd_lst ::= variable_bnd */
#line 2458 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy424 = yymsp[0].minor.yy424;
	}
#line 6059 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 384: /* variable_bnd_lst ::= variable_bnd_lst SEMICOLON variable_bnd */
#line 2463 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy424 = yymsp[-2].minor.yy424;
		yygotominor.yy424->splice(yygotominor.yy424->end(), *yymsp[0].minor.yy424);
		delete yymsp[0].minor.yy424;
	  yy_destructor(yypParser,101,&yymsp[-1].minor);
}
#line 6069 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 385: /* variable_bnd ::= variable_lst DBL_COLON sort */
#line 2470 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy424 = new VariableDeclaration::ElementList();

		BOOST_FOREACH(Token const* tok, *yymsp[-2].minor.yy280) {
			yygotominor.yy424->push_back(new VariableSymbol(tok->str(), yymsp[0].minor.yy69));
		}



		delete yymsp[-2].minor.yy280;
	  yy_destructor(yypParser,84,&yymsp[-1].minor);
}
#line 6085 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 386: /* variable_bnd ::= variable_lst */
#line 2483 "bcplus/parser/detail/lemon_parser.y"
{
		std::string temp = "tempVarSort";
		ReferencedString const* domainString = new ReferencedString(temp);
		SortSymbol* s = parser->symtab()->resolveOrCreate(new SortSymbol(domainString));
		yygotominor.yy424 = new VariableDeclaration::ElementList();

		BOOST_FOREACH(Token const* tok, *yymsp[0].minor.yy280) {
			yygotominor.yy424->push_back(new VariableSymbol(tok->str(), s));
		}
		delete yymsp[0].minor.yy280;
	}
#line 6100 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 387: /* variable_lst ::= IDENTIFIER */
#line 2496 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy280 = new TokenList();
		yygotominor.yy280->push_back(yymsp[0].minor.yy0);
	}
#line 6108 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 388: /* variable_lst ::= variable_lst COMMA IDENTIFIER */
#line 2501 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy280 = yymsp[-2].minor.yy280;
		yygotominor.yy280->push_back(yymsp[0].minor.yy0);
	  yy_destructor(yypParser,110,&yymsp[-1].minor);
}
#line 6117 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 389: /* stmt_sort_def ::= COLON_DASH SORTS sort_bnd_lst PERIOD */
#line 2522 "bcplus/parser/detail/lemon_parser.y"
{
		ref_ptr<const Token> cd_ptr = yymsp[-3].minor.yy0;
		ref_ptr<const Token> p_ptr = yymsp[0].minor.yy0;
		ref_ptr<const Token> kw_ptr = yymsp[-2].minor.yy0;
		ref_ptr<SortDeclaration::ElementList> l_ptr = yymsp[-1].minor.yy523;

		if (!parser->lang()->support(Language::Feature::DECL_SORT)) {
			yygotominor.yy333 = NULL;
			parser->_feature_error(Language::Feature::DECL_SORT, &yymsp[-2].minor.yy0->beginLoc());
			YYERROR;
		} else {
			yygotominor.yy333 = new SortDeclaration(yymsp[-1].minor.yy523, yymsp[-3].minor.yy0->beginLoc(), yymsp[0].minor.yy0->endLoc());
		}
	}
#line 6135 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 390: /* sort_bnd_lst ::= sort_bnd */
      case 392: /* sort_bnd ::= sort_dcl_lst */ yytestcase(yyruleno==392);
#line 2538 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy523 = yymsp[0].minor.yy523;
	}
#line 6143 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 391: /* sort_bnd_lst ::= sort_bnd_lst SEMICOLON sort_bnd */
#line 2543 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy523 = yymsp[-2].minor.yy523;
		yygotominor.yy523->splice(yygotominor.yy523->end(), *yymsp[0].minor.yy523);
		delete yymsp[0].minor.yy523;
	  yy_destructor(yypParser,101,&yymsp[-1].minor);
}
#line 6153 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 393: /* sort_bnd ::= sort_bnd DBL_LTHAN sort_bnd */
#line 2555 "bcplus/parser/detail/lemon_parser.y"
{
		BOOST_FOREACH(SortSymbol* sym, *yymsp[-2].minor.yy523) {
			BOOST_FOREACH(SortSymbol* sym2, *yymsp[0].minor.yy523) {
				sym2->addSubSort(sym);
			}
		}
		yygotominor.yy523 = yymsp[-2].minor.yy523;
		yygotominor.yy523->splice(yymsp[-2].minor.yy523->end(), *yymsp[0].minor.yy523);
		delete yymsp[0].minor.yy523;

	  yy_destructor(yypParser,108,&yymsp[-1].minor);
}
#line 6169 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 394: /* sort_bnd ::= sort_bnd DBL_GTHAN sort_bnd */
#line 2567 "bcplus/parser/detail/lemon_parser.y"
{
		BOOST_FOREACH(SortSymbol* sym, *yymsp[-2].minor.yy523) {
			BOOST_FOREACH(SortSymbol* sym2, *yymsp[0].minor.yy523) {
				sym->addSubSort(sym2);
			}
		}
		yygotominor.yy523 = yymsp[-2].minor.yy523;
		yygotominor.yy523->splice(yymsp[-2].minor.yy523->end(), *yymsp[0].minor.yy523);
		delete yymsp[0].minor.yy523;
	  yy_destructor(yypParser,107,&yymsp[-1].minor);
}
#line 6184 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 395: /* sort_bnd ::= PAREN_L sort_bnd PAREN_R */
#line 2578 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy523 = yymsp[-1].minor.yy523;
	  yy_destructor(yypParser,79,&yymsp[-2].minor);
  yy_destructor(yypParser,80,&yymsp[0].minor);
}
#line 6193 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 396: /* sort_dcl_lst ::= IDENTIFIER */
#line 2583 "bcplus/parser/detail/lemon_parser.y"
{
		ref_ptr<SortSymbol> s = parser->symtab()->resolveOrCreate(new SortSymbol(yymsp[0].minor.yy0->str()));
		if (!s) {
			yygotominor.yy523 = NULL;
			parser->_parse_error("Detected conflicting definition of sort symbol \"" + Symbol::genName(*yymsp[0].minor.yy0->str(),0) + "\".", &yymsp[0].minor.yy0->beginLoc());
			YYERROR;
		} else {
			yygotominor.yy523 = new SortDeclaration::ElementList();
			yygotominor.yy523->push_back(s);
		}

		delete yymsp[0].minor.yy0;
	}
#line 6210 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 397: /* sort_dcl_lst ::= sort_dcl_lst COMMA IDENTIFIER */
#line 2597 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy523 = yymsp[-2].minor.yy523;
		ref_ptr<SortSymbol> s = parser->symtab()->resolveOrCreate(new SortSymbol(yymsp[0].minor.yy0->str()));
		if (!s) {
			yymsp[-2].minor.yy523 = NULL;
			parser->_parse_error("Detected conflicting definition of sort symbol \"" + Symbol::genName(*yymsp[0].minor.yy0->str(),0) + "\".", &yymsp[0].minor.yy0->beginLoc());
			YYERROR;
		} else {
			yymsp[-2].minor.yy523->push_back(s);
		}

		delete yymsp[0].minor.yy0;

	  yy_destructor(yypParser,110,&yymsp[-1].minor);
}
#line 6229 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 398: /* stmt_show ::= COLON_DASH SHOW show_lst PERIOD */
#line 2624 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy76 = NULL;
		ref_ptr<const Token> cd_ptr = yymsp[-3].minor.yy0, kw_ptr = yymsp[-2].minor.yy0, p_ptr = yymsp[0].minor.yy0;
		ref_ptr<ShowStatement::ElementList> lst_ptr = yymsp[-1].minor.yy331;

		if (!parser->lang()->support(Language::Feature::DECL_SHOW)) {
			parser->_feature_error(Language::Feature::DECL_SHOW, &yymsp[-2].minor.yy0->beginLoc());
			YYERROR;
		} else {
			yygotominor.yy76 = new ShowStatement(yymsp[-1].minor.yy331, yymsp[-3].minor.yy0->beginLoc(), yymsp[0].minor.yy0->endLoc());
		}
	}
#line 6245 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 399: /* stmt_show ::= COLON_DASH SHOW ALL PERIOD */
#line 2638 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy76 = NULL;
		ref_ptr<const Token> cd_ptr = yymsp[-3].minor.yy0, kw_ptr = yymsp[-2].minor.yy0, p_ptr = yymsp[0].minor.yy0, all_ptr = yymsp[-1].minor.yy0;

		if (!parser->lang()->support(Language::Feature::DECL_SHOW)) {
			parser->_feature_error(Language::Feature::DECL_SHOW, &yymsp[-2].minor.yy0->beginLoc());
			YYERROR;
		} else if (!parser->lang()->support(Language::Feature::DECL_SHOW_ALL)) {
			parser->_feature_error(Language::Feature::DECL_SHOW_ALL, &yymsp[-1].minor.yy0->beginLoc());
			YYERROR;
		} else {
			yygotominor.yy76 = new ShowAllStatement(yymsp[-3].minor.yy0->beginLoc(), yymsp[0].minor.yy0->endLoc());
		}
	}
#line 6263 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 400: /* stmt_hide ::= COLON_DASH HIDE show_lst PERIOD */
#line 2655 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy76 = NULL;
		ref_ptr<const Token> cd_ptr = yymsp[-3].minor.yy0, kw_ptr = yymsp[-2].minor.yy0, p_ptr = yymsp[0].minor.yy0;
		ref_ptr<HideStatement::ElementList> lst_ptr = yymsp[-1].minor.yy331;

		if (!parser->lang()->support(Language::Feature::DECL_HIDE)) {
			parser->_feature_error(Language::Feature::DECL_HIDE, &yymsp[-2].minor.yy0->beginLoc());
			YYERROR;
		} else {
			yygotominor.yy76 = new HideStatement(yymsp[-1].minor.yy331, yymsp[-3].minor.yy0->beginLoc(), yymsp[0].minor.yy0->endLoc());
		}
	}
#line 6279 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 401: /* stmt_hide ::= COLON_DASH HIDE ALL PERIOD */
#line 2669 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy76 = NULL;
		ref_ptr<const Token> cd_ptr = yymsp[-3].minor.yy0, kw_ptr = yymsp[-2].minor.yy0, p_ptr = yymsp[0].minor.yy0, all_ptr = yymsp[-1].minor.yy0;

		if (!parser->lang()->support(Language::Feature::DECL_HIDE)) {
			parser->_feature_error(Language::Feature::DECL_HIDE, &yymsp[-2].minor.yy0->beginLoc());
			YYERROR;
		} else if (!parser->lang()->support(Language::Feature::DECL_HIDE_ALL)) {
			parser->_feature_error(Language::Feature::DECL_HIDE_ALL, &yymsp[-1].minor.yy0->beginLoc());
			YYERROR;
		} else {
			yygotominor.yy76 = new HideAllStatement(yymsp[-3].minor.yy0->beginLoc(), yymsp[0].minor.yy0->endLoc());
		}
	}
#line 6297 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 402: /* show_lst ::= show_elem */
#line 2687 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy331 = new ShowStatement::ElementList();
		yygotominor.yy331->push_back(yymsp[0].minor.yy274);
	}
#line 6305 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 403: /* show_lst ::= show_lst COMMA show_elem */
#line 2692 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy331 = yymsp[-2].minor.yy331;
		yygotominor.yy331->push_back(yymsp[0].minor.yy274);
	  yy_destructor(yypParser,110,&yymsp[-1].minor);
}
#line 6314 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 404: /* show_lst ::= show_lst SEMICOLON show_elem */
#line 2697 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy331 = yymsp[-2].minor.yy331;
		yygotominor.yy331->push_back(yymsp[0].minor.yy274);
	  yy_destructor(yypParser,101,&yymsp[-1].minor);
}
#line 6323 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 406: /* stmt_noconcurrency ::= NOCONCURRENCY PERIOD */
#line 2725 "bcplus/parser/detail/lemon_parser.y"
{ NC_STATEMENT(yygotominor.yy379, yymsp[-1].minor.yy0, yymsp[0].minor.yy0, Language::Feature::NOCONCURRENCY, NCStatement); }
#line 6328 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 407: /* stmt_strong_noconcurrency ::= STRONG_NOCONCURRENCY PERIOD */
#line 2726 "bcplus/parser/detail/lemon_parser.y"
{ NC_STATEMENT(yygotominor.yy494, yymsp[-1].minor.yy0, yymsp[0].minor.yy0, Language::Feature::STRONG_NOCONCURRENCY, StrongNCStatement); }
#line 6333 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 408: /* stmt_maxafvalue ::= COLON_DASH MAXAFVALUE EQ term_int_eval PERIOD */
#line 2752 "bcplus/parser/detail/lemon_parser.y"
{ VALUE_DECL(yygotominor.yy76, yymsp[-4].minor.yy0, yymsp[-3].minor.yy0, yymsp[-1].minor.yy68, yymsp[0].minor.yy0, Language::Feature::DECL_MAXAFVALUE, MaxAFValueStatement);   yy_destructor(yypParser,89,&yymsp[-2].minor);
}
#line 6339 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 409: /* stmt_maxafvalue ::= COLON_DASH MAXAFVALUE DBL_COLON term_int_eval PERIOD */
#line 2753 "bcplus/parser/detail/lemon_parser.y"
{ VALUE_DECL(yygotominor.yy76, yymsp[-4].minor.yy0, yymsp[-3].minor.yy0, yymsp[-1].minor.yy68, yymsp[0].minor.yy0, Language::Feature::DECL_MAXAFVALUE, MaxAFValueStatement);   yy_destructor(yypParser,84,&yymsp[-2].minor);
}
#line 6345 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 410: /* stmt_maxadditive ::= COLON_DASH MAXADDITIVE EQ term_int_eval PERIOD */
#line 2754 "bcplus/parser/detail/lemon_parser.y"
{ VALUE_DECL(yygotominor.yy76, yymsp[-4].minor.yy0, yymsp[-3].minor.yy0, yymsp[-1].minor.yy68, yymsp[0].minor.yy0, Language::Feature::DECL_MAXADDITIVE, MaxAdditiveStatement);   yy_destructor(yypParser,89,&yymsp[-2].minor);
}
#line 6351 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 411: /* stmt_maxadditive ::= COLON_DASH MAXADDITIVE DBL_COLON term_int_eval PERIOD */
#line 2755 "bcplus/parser/detail/lemon_parser.y"
{ VALUE_DECL(yygotominor.yy76, yymsp[-4].minor.yy0, yymsp[-3].minor.yy0, yymsp[-1].minor.yy68, yymsp[0].minor.yy0, Language::Feature::DECL_MAXADDITIVE, MaxAdditiveStatement);   yy_destructor(yypParser,84,&yymsp[-2].minor);
}
#line 6357 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 412: /* stmt_query ::= COLON_DASH QUERY query_lst PERIOD */
#line 2780 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy136 = NULL;
		ref_ptr<const Referenced> cd_ptr = yymsp[-3].minor.yy0, kw_ptr = yymsp[-2].minor.yy0, data_l_ptr = yymsp[-1].minor.yy305.l, p_ptr = yymsp[0].minor.yy0;
		ref_ptr<const Referenced> data_maxstep_ptr = yymsp[-1].minor.yy305.maxstep, data_label_ptr = yymsp[-1].minor.yy305.label;

		ref_ptr<const ReferencedString> label;
		if (yymsp[-1].minor.yy305.label) label = yymsp[-1].minor.yy305.label->str();
		else label = new ReferencedString("0");

		int min = -1, max = -1;
		if (yymsp[-1].minor.yy305.maxstep) {
			min = yymsp[-1].minor.yy305.maxstep->min();
			max = yymsp[-1].minor.yy305.maxstep->max();
		}

		if (!parser->lang()->support(Language::Feature::DECL_QUERY)) {
			parser->_feature_error(Language::Feature::DECL_QUERY, &yymsp[-2].minor.yy0->beginLoc());
			YYERROR;
		} else {
			bool good = true;

			// resolve the query label
			ref_ptr<QuerySymbol> sym = new QuerySymbol(label, min, max);
			if (!parser->symtab()->create(sym)) {
				parser->_parse_error("Could not create query, the label \"" + *label + "\" already exists.", (yymsp[-1].minor.yy305.label ? &yymsp[-1].minor.yy305.label->beginLoc() : &yymsp[-2].minor.yy0->beginLoc()));
				good = false;
				YYERROR;
			}


			if (good) yygotominor.yy136 = new QueryStatement(sym, yymsp[-1].minor.yy305.l, yymsp[-3].minor.yy0->beginLoc(), yymsp[0].minor.yy0->endLoc());
		}
	}
#line 6394 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 413: /* query_lst ::= formula_temporal */
#line 2816 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy305.l = new QueryStatement::FormulaList();
		yygotominor.yy305.maxstep = NULL;
		yygotominor.yy305.label = NULL;

		yygotominor.yy305.l->push_back(yymsp[0].minor.yy179);
	}
#line 6405 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 414: /* query_lst ::= query_maxstep_decl */
#line 2825 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy305.l = new QueryStatement::FormulaList();
		yygotominor.yy305.maxstep = yymsp[0].minor.yy1;
		yygotominor.yy305.label = NULL;
	}
#line 6414 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 415: /* query_lst ::= query_label_decl */
#line 2832 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy305.l = new QueryStatement::FormulaList();
		yygotominor.yy305.maxstep = NULL;
		yygotominor.yy305.label = yymsp[0].minor.yy193;
	}
#line 6423 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 416: /* query_lst ::= query_lst SEMICOLON formula_temporal */
#line 2839 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy305 = yymsp[-2].minor.yy305;
		yymsp[-2].minor.yy305.l->push_back(yymsp[0].minor.yy179);
	  yy_destructor(yypParser,101,&yymsp[-1].minor);
}
#line 6432 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 417: /* query_lst ::= query_lst SEMICOLON query_maxstep_decl */
#line 2845 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy305 = yymsp[-2].minor.yy305;

		if (yygotominor.yy305.maxstep) {
			parser->_parse_error("Encountered multiple maxstep definitions within a query.", &yymsp[0].minor.yy1->beginLoc());
			delete yymsp[0].minor.yy1;
			YYERROR;
		} else {
			yygotominor.yy305.maxstep = yymsp[0].minor.yy1;
		}
	  yy_destructor(yypParser,101,&yymsp[-1].minor);
}
#line 6448 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 418: /* query_lst ::= query_lst SEMICOLON query_label_decl */
#line 2858 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy305 = yymsp[-2].minor.yy305;
		if (yygotominor.yy305.label) {
			parser->_parse_error("Encountered multiple maxstep definitions within a query.", &yymsp[0].minor.yy193->beginLoc());
			delete yymsp[0].minor.yy193;
			YYERROR;

		} else {
			yygotominor.yy305.label = yymsp[0].minor.yy193;
		}
	  yy_destructor(yypParser,101,&yymsp[-1].minor);
}
#line 6464 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 419: /* query_maxstep_decl ::= MAXSTEP DBL_COLON INTEGER */
#line 2884 "bcplus/parser/detail/lemon_parser.y"
{
	yygotominor.yy1 = NULL;
	ref_ptr<const Referenced> kw_ptr = yymsp[-2].minor.yy0, i_ptr = yymsp[0].minor.yy0;


	if (!parser->lang()->support(Language::Feature::QUERY_MAXSTEP)) {
		parser->_feature_error(Language::Feature::QUERY_MAXSTEP, &yymsp[-2].minor.yy0->beginLoc());
		YYERROR;
	} else {

		int max = -1;
		try {
			max = boost::lexical_cast<int>(*yymsp[0].minor.yy0->str());
			yygotominor.yy1 = new NumberRangeEval(-1, max, yymsp[0].minor.yy0->beginLoc(), yymsp[0].minor.yy0->endLoc());
		} catch (boost::bad_lexical_cast const& e) {
			parser->_parse_error("INTERNAL ERROR: An error occurred extracting an integer from \"" + *yymsp[0].minor.yy0->str() + "\".", &yymsp[0].minor.yy0->beginLoc());
			YYERROR;
		}
	}
  yy_destructor(yypParser,84,&yymsp[-1].minor);
}
#line 6489 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 420: /* query_maxstep_decl ::= MAXSTEP DBL_COLON num_range_eval */
#line 2905 "bcplus/parser/detail/lemon_parser.y"
{
	yygotominor.yy1 = NULL;
	ref_ptr<const Referenced> kw_ptr = yymsp[-2].minor.yy0, nr_ptr = yymsp[0].minor.yy1;

	if (!parser->lang()->support(Language::Feature::QUERY_MAXSTEP)) {
		parser->_feature_error(Language::Feature::QUERY_MAXSTEP, &yymsp[-2].minor.yy0->beginLoc());
		YYERROR;
	} else {
		yygotominor.yy1 = yymsp[0].minor.yy1;
		nr_ptr.release();
	}
  yy_destructor(yypParser,84,&yymsp[-1].minor);
}
#line 6506 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 421: /* query_label_decl ::= LABEL DBL_COLON INTEGER */
      case 422: /* query_label_decl ::= LABEL DBL_COLON IDENTIFIER */ yytestcase(yyruleno==422);
#line 2919 "bcplus/parser/detail/lemon_parser.y"
{ QUERY_DECL(yygotominor.yy193, yymsp[-2].minor.yy0, yymsp[0].minor.yy0, Language::Feature::QUERY_LABEL);   yy_destructor(yypParser,84,&yymsp[-1].minor);
}
#line 6513 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 423: /* clause_if ::= IF formula */
#line 2954 "bcplus/parser/detail/lemon_parser.y"
{ CLAUSE(yygotominor.yy179, yymsp[-1].minor.yy0, yymsp[0].minor.yy179, Language::Feature::CLAUSE_IF); 		}
#line 6518 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 424: /* clause_if ::= */
      case 426: /* clause_after ::= */ yytestcase(yyruleno==426);
      case 428: /* clause_ifcons ::= */ yytestcase(yyruleno==428);
      case 432: /* clause_where ::= */ yytestcase(yyruleno==432);
#line 2955 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy179 = NULL; }
#line 6526 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 425: /* clause_after ::= AFTER formula */
#line 2956 "bcplus/parser/detail/lemon_parser.y"
{ CLAUSE(yygotominor.yy179, yymsp[-1].minor.yy0, yymsp[0].minor.yy179, Language::Feature::CLAUSE_AFTER);	}
#line 6531 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 427: /* clause_ifcons ::= IFCONS formula */
#line 2958 "bcplus/parser/detail/lemon_parser.y"
{ CLAUSE(yygotominor.yy179, yymsp[-1].minor.yy0, yymsp[0].minor.yy179, Language::Feature::CLAUSE_IFCONS); 	}
#line 6536 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 429: /* clause_unless ::= UNLESS atomic_formula_anon */
#line 2960 "bcplus/parser/detail/lemon_parser.y"
{ CLAUSE(yygotominor.yy274, yymsp[-1].minor.yy0, yymsp[0].minor.yy274, Language::Feature::CLAUSE_UNLESS); 	}
#line 6541 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 430: /* clause_unless ::= */
#line 2961 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy274 = NULL; }
#line 6546 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 431: /* clause_where ::= WHERE formula_no_const */
#line 2962 "bcplus/parser/detail/lemon_parser.y"
{ CLAUSE(yygotominor.yy179, yymsp[-1].minor.yy0, yymsp[0].minor.yy179, Language::Feature::CLAUSE_WHERE); 	}
#line 6551 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 433: /* rate_decl ::= DDT BRACKET_L constant BRACKET_R EQ term IF MODE EQ INTEGER PERIOD */
#line 2973 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy175 = new RateDeclaration(yymsp[-8].minor.yy189,yymsp[-5].minor.yy39,yymsp[-1].minor.yy0->str());   yy_destructor(yypParser,45,&yymsp[-10].minor);
  yy_destructor(yypParser,74,&yymsp[-9].minor);
  yy_destructor(yypParser,75,&yymsp[-7].minor);
  yy_destructor(yypParser,89,&yymsp[-6].minor);
  yy_destructor(yypParser,46,&yymsp[-4].minor);
  yy_destructor(yypParser,47,&yymsp[-3].minor);
  yy_destructor(yypParser,89,&yymsp[-2].minor);
  yy_destructor(yypParser,81,&yymsp[0].minor);
}
#line 6564 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 434: /* alwayst_stmt ::= ALWAYST formula IF MODE EQ INTEGER PERIOD */
#line 2984 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy416 = new ForallTStatement(yymsp[-5].minor.yy179,yymsp[-1].minor.yy0->str());   yy_destructor(yypParser,32,&yymsp[-6].minor);
  yy_destructor(yypParser,46,&yymsp[-4].minor);
  yy_destructor(yypParser,47,&yymsp[-3].minor);
  yy_destructor(yypParser,89,&yymsp[-2].minor);
  yy_destructor(yypParser,81,&yymsp[0].minor);
}
#line 6574 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 435: /* stmt_law ::= law_basic */
      case 436: /* stmt_law ::= law_caused */ yytestcase(yyruleno==436);
      case 437: /* stmt_law ::= law_pcaused */ yytestcase(yyruleno==437);
      case 438: /* stmt_law ::= law_impl */ yytestcase(yyruleno==438);
      case 439: /* stmt_law ::= law_causes */ yytestcase(yyruleno==439);
      case 440: /* stmt_law ::= law_increments */ yytestcase(yyruleno==440);
      case 441: /* stmt_law ::= law_decrements */ yytestcase(yyruleno==441);
      case 442: /* stmt_law ::= law_mcause */ yytestcase(yyruleno==442);
      case 443: /* stmt_law ::= law_always */ yytestcase(yyruleno==443);
      case 444: /* stmt_law ::= law_constraint */ yytestcase(yyruleno==444);
      case 445: /* stmt_law ::= law_impossible */ yytestcase(yyruleno==445);
      case 446: /* stmt_law ::= law_never */ yytestcase(yyruleno==446);
      case 447: /* stmt_law ::= law_default */ yytestcase(yyruleno==447);
      case 448: /* stmt_law ::= law_exogenous */ yytestcase(yyruleno==448);
      case 449: /* stmt_law ::= law_inertial */ yytestcase(yyruleno==449);
      case 450: /* stmt_law ::= law_nonexecutable */ yytestcase(yyruleno==450);
      case 451: /* stmt_law ::= law_rigid */ yytestcase(yyruleno==451);
      case 452: /* stmt_law ::= law_observed */ yytestcase(yyruleno==452);
      case 453: /* stmt_law ::= law_temporal_constraint */ yytestcase(yyruleno==453);
#line 3032 "bcplus/parser/detail/lemon_parser.y"
{yygotominor.yy76 = yymsp[0].minor.yy76;}
#line 6597 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 454: /* law_basic ::= head_formula clause_if clause_ifcons clause_after clause_unless clause_where PERIOD */
#line 3153 "bcplus/parser/detail/lemon_parser.y"
{
		if (yymsp[-5].minor.yy179 || yymsp[-4].minor.yy179 || yymsp[-3].minor.yy179 || yymsp[-2].minor.yy274 || yymsp[-1].minor.yy179) {
			LAW_BASIC_FORM(yygotominor.yy76, NULL, yymsp[-6].minor.yy179, yymsp[-5].minor.yy179, yymsp[-4].minor.yy179, yymsp[-3].minor.yy179,
				yymsp[-2].minor.yy274, yymsp[-1].minor.yy179, yymsp[0].minor.yy0, Language::Feature::LAW_BASIC_S,
				Language::Feature::LAW_BASIC_D, BasicLaw);
		} else {
			LAW_BASIC_FORM(yygotominor.yy76, NULL, yymsp[-6].minor.yy179, yymsp[-5].minor.yy179, yymsp[-4].minor.yy179, yymsp[-3].minor.yy179,
				yymsp[-2].minor.yy274, yymsp[-1].minor.yy179, yymsp[0].minor.yy0, Language::Feature::LAW_BASIC_FACT,
				Language::Feature::LAW_BASIC_FACT, BasicLaw);
		}
	}
#line 6612 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 455: /* law_caused ::= CAUSED head_formula clause_if clause_ifcons clause_after clause_unless clause_where PERIOD */
#line 3165 "bcplus/parser/detail/lemon_parser.y"
{ LAW_BASIC_FORM(yygotominor.yy76, yymsp[-7].minor.yy0, yymsp[-6].minor.yy179, yymsp[-5].minor.yy179, yymsp[-4].minor.yy179, yymsp[-3].minor.yy179,
																																														yymsp[-2].minor.yy274, yymsp[-1].minor.yy179, yymsp[0].minor.yy0, Language::Feature::LAW_CAUSED_S,
																																															Language::Feature::LAW_CAUSED_D, CausedLaw); }
#line 6619 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 456: /* law_pcaused ::= POSSIBLY_CAUSED head_formula clause_if clause_ifcons clause_after clause_unless clause_where PERIOD */
#line 3169 "bcplus/parser/detail/lemon_parser.y"
{ LAW_BASIC_FORM(yygotominor.yy76, yymsp[-7].minor.yy0, yymsp[-6].minor.yy179, yymsp[-5].minor.yy179, yymsp[-4].minor.yy179, yymsp[-3].minor.yy179,
																																														yymsp[-2].minor.yy274, yymsp[-1].minor.yy179, yymsp[0].minor.yy0, Language::Feature::LAW_PCAUSED_S,
																																															Language::Feature::LAW_PCAUSED_D, PossiblyCausedLaw); }
#line 6626 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 457: /* law_impl ::= head_formula ARROW_LDASH formula clause_where PERIOD */
#line 3173 "bcplus/parser/detail/lemon_parser.y"
{ LAW_IMPL_FORM(yygotominor.yy76, yymsp[-4].minor.yy179, yymsp[-3].minor.yy0, yymsp[-2].minor.yy179, yymsp[-1].minor.yy179, yymsp[0].minor.yy0,
																																														Language::Feature::LAW_IMPL, ImplicationLaw); }
#line 6632 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 458: /* law_impl ::= ARROW_LDASH formula clause_where PERIOD */
#line 3176 "bcplus/parser/detail/lemon_parser.y"
{ LAW_IMPL_FORM(yygotominor.yy76, NULL, yymsp[-3].minor.yy0, yymsp[-2].minor.yy179, yymsp[-1].minor.yy179, yymsp[0].minor.yy0,
																																														Language::Feature::LAW_IMPL, ImplicationLaw); }
#line 6638 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 459: /* law_causes ::= atomic_formula CAUSES head_formula clause_if clause_unless clause_where PERIOD */
#line 3179 "bcplus/parser/detail/lemon_parser.y"
{ LAW_DYNAMIC_FORM(yygotominor.yy76, yymsp[-6].minor.yy274, yymsp[-5].minor.yy0, yymsp[-4].minor.yy179, yymsp[-3].minor.yy179, yymsp[-2].minor.yy274, yymsp[-1].minor.yy179, yymsp[0].minor.yy0,
																																														Language::Feature::LAW_CAUSES, CausesLaw); }
#line 6644 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 460: /* law_increments ::= atomic_formula INCREMENTS constant BY term clause_if clause_unless clause_where PERIOD */
#line 3183 "bcplus/parser/detail/lemon_parser.y"
{ LAW_INCREMENTAL_FORM(yygotominor.yy76, yymsp[-8].minor.yy274, yymsp[-7].minor.yy0, yymsp[-6].minor.yy189, yymsp[-4].minor.yy39, yymsp[-3].minor.yy179, yymsp[-2].minor.yy274, yymsp[-1].minor.yy179, yymsp[0].minor.yy0,
																																														Language::Feature::LAW_INCREMENTS, IncrementsLaw);   yy_destructor(yypParser,35,&yymsp[-5].minor);
}
#line 6651 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 461: /* law_decrements ::= atomic_formula DECREMENTS constant BY term clause_if clause_unless clause_where PERIOD */
#line 3186 "bcplus/parser/detail/lemon_parser.y"
{ LAW_INCREMENTAL_FORM(yygotominor.yy76, yymsp[-8].minor.yy274, yymsp[-7].minor.yy0, yymsp[-6].minor.yy189, yymsp[-4].minor.yy39, yymsp[-3].minor.yy179, yymsp[-2].minor.yy274, yymsp[-1].minor.yy179, yymsp[0].minor.yy0,
																																														Language::Feature::LAW_DECREMENTS, DecrementsLaw);   yy_destructor(yypParser,35,&yymsp[-5].minor);
}
#line 6658 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 462: /* law_mcause ::= atomic_formula MAY_CAUSE head_formula clause_if clause_unless clause_where PERIOD */
#line 3190 "bcplus/parser/detail/lemon_parser.y"
{ LAW_DYNAMIC_FORM(yygotominor.yy76, yymsp[-6].minor.yy274, yymsp[-5].minor.yy0, yymsp[-4].minor.yy179, yymsp[-3].minor.yy179, yymsp[-2].minor.yy274, yymsp[-1].minor.yy179, yymsp[0].minor.yy0,
																																														Language::Feature::LAW_MCAUSE, MayCauseLaw); }
#line 6664 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 463: /* law_always ::= ALWAYS formula clause_after clause_unless clause_where PERIOD */
#line 3194 "bcplus/parser/detail/lemon_parser.y"
{ LAW_CONSTRAINT_FORM(yygotominor.yy76, yymsp[-5].minor.yy0, yymsp[-4].minor.yy179, yymsp[-3].minor.yy179, yymsp[-2].minor.yy274, yymsp[-1].minor.yy179, yymsp[0].minor.yy0,
																																														Language::Feature::LAW_ALWAYS_S,
																																															Language::Feature::LAW_ALWAYS_D, AlwaysLaw); }
#line 6671 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 464: /* law_constraint ::= CONSTRAINT formula clause_after clause_unless clause_where PERIOD */
#line 3198 "bcplus/parser/detail/lemon_parser.y"
{ LAW_CONSTRAINT_FORM(yygotominor.yy76, yymsp[-5].minor.yy0, yymsp[-4].minor.yy179, yymsp[-3].minor.yy179, yymsp[-2].minor.yy274, yymsp[-1].minor.yy179, yymsp[0].minor.yy0,
																																														Language::Feature::LAW_CONSTRAINT_S,
																																															Language::Feature::LAW_CONSTRAINT_D, ConstraintLaw); }
#line 6678 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 465: /* law_impossible ::= IMPOSSIBLE formula clause_after clause_unless clause_where PERIOD */
#line 3202 "bcplus/parser/detail/lemon_parser.y"
{ LAW_CONSTRAINT_FORM(yygotominor.yy76, yymsp[-5].minor.yy0, yymsp[-4].minor.yy179, yymsp[-3].minor.yy179, yymsp[-2].minor.yy274, yymsp[-1].minor.yy179, yymsp[0].minor.yy0,
																																														Language::Feature::LAW_IMPOSSIBLE_S,
																																															Language::Feature::LAW_IMPOSSIBLE_D, ImpossibleLaw); }
#line 6685 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 466: /* law_never ::= NEVER formula clause_after clause_unless clause_where PERIOD */
#line 3206 "bcplus/parser/detail/lemon_parser.y"
{ LAW_CONSTRAINT_FORM(yygotominor.yy76, yymsp[-5].minor.yy0, yymsp[-4].minor.yy179, yymsp[-3].minor.yy179, yymsp[-2].minor.yy274, yymsp[-1].minor.yy179, yymsp[0].minor.yy0,
																																														Language::Feature::LAW_NEVER_S,
																																															Language::Feature::LAW_NEVER_D, NeverLaw); }
#line 6692 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 467: /* law_default ::= DEFAULT atomic_head_formula clause_if clause_ifcons clause_after clause_unless clause_where PERIOD */
#line 3210 "bcplus/parser/detail/lemon_parser.y"
{ LAW_BASIC_FORM(yygotominor.yy76, yymsp[-7].minor.yy0, yymsp[-6].minor.yy274, yymsp[-5].minor.yy179, yymsp[-4].minor.yy179, yymsp[-3].minor.yy179,
																																														yymsp[-2].minor.yy274, yymsp[-1].minor.yy179, yymsp[0].minor.yy0, Language::Feature::LAW_DEFAULT_S,
																																															Language::Feature::LAW_DEFAULT_D, DefaultLaw); }
#line 6699 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 468: /* law_exogenous ::= EXOGENOUS constant clause_if clause_ifcons clause_after clause_unless clause_where PERIOD */
#line 3214 "bcplus/parser/detail/lemon_parser.y"
{ LAW_BASIC_FORM(yygotominor.yy76, yymsp[-7].minor.yy0, yymsp[-6].minor.yy189, yymsp[-5].minor.yy179, yymsp[-4].minor.yy179, yymsp[-3].minor.yy179,
																																														yymsp[-2].minor.yy274, yymsp[-1].minor.yy179, yymsp[0].minor.yy0, Language::Feature::LAW_EXOGENOUS_S,
																																															Language::Feature::LAW_EXOGENOUS_D, ExogenousLaw); }
#line 6706 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 469: /* law_inertial ::= INERTIAL constant clause_if clause_ifcons clause_after clause_unless clause_where PERIOD */
#line 3218 "bcplus/parser/detail/lemon_parser.y"
{ LAW_BASIC_FORM(yygotominor.yy76, yymsp[-7].minor.yy0, yymsp[-6].minor.yy189, yymsp[-5].minor.yy179, yymsp[-4].minor.yy179, yymsp[-3].minor.yy179,
																																														yymsp[-2].minor.yy274, yymsp[-1].minor.yy179, yymsp[0].minor.yy0, Language::Feature::LAW_INERTIAL_S,
																																															Language::Feature::LAW_INERTIAL_D, InertialLaw); }
#line 6713 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 470: /* law_nonexecutable ::= NONEXECUTABLE formula clause_if clause_unless clause_where PERIOD */
#line 3222 "bcplus/parser/detail/lemon_parser.y"
{ LAW_DYNAMIC_CONSTRAINT_FORM(yygotominor.yy76, yymsp[-5].minor.yy0, yymsp[-4].minor.yy179, yymsp[-3].minor.yy179, yymsp[-2].minor.yy274, yymsp[-1].minor.yy179,
																																														yymsp[0].minor.yy0, Language::Feature::LAW_NONEXECUTABLE, NonexecutableLaw); }
#line 6719 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 471: /* law_rigid ::= RIGID constant clause_where PERIOD */
#line 3226 "bcplus/parser/detail/lemon_parser.y"
{ LAW_SIMPLE_FORM(yygotominor.yy76, yymsp[-3].minor.yy0, yymsp[-2].minor.yy189, yymsp[-1].minor.yy179, yymsp[0].minor.yy0,
																																														Language::Feature::LAW_RIGID, RigidLaw); }
#line 6725 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 472: /* law_observed ::= OBSERVED atomic_head_formula AT term_int_eval PERIOD */
#line 3231 "bcplus/parser/detail/lemon_parser.y"
{
			LAW_SIMPLE_FORM(yygotominor.yy76, yymsp[-4].minor.yy0, yymsp[-3].minor.yy274, yymsp[-1].minor.yy68, yymsp[0].minor.yy0, Language::Feature::LAW_OBSERVED, ObservedLaw);
		  yy_destructor(yypParser,73,&yymsp[-2].minor);
}
#line 6733 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 473: /* law_temporal_constraint ::= CONSTRAINT formula AT term_int_eval PERIOD */
#line 3236 "bcplus/parser/detail/lemon_parser.y"
{
			LAW_SIMPLE_FORM(yygotominor.yy76, yymsp[-4].minor.yy0, yymsp[-3].minor.yy179, yymsp[-1].minor.yy68, yymsp[0].minor.yy0, Language::Feature::LAW_TEMPORAL_CONSTRAINT, TemporalConstraintLaw);
		  yy_destructor(yypParser,73,&yymsp[-2].minor);
}
#line 6741 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 474: /* stmt_code_blk ::= ASP_GR */
#line 3259 "bcplus/parser/detail/lemon_parser.y"
{ CODE_BLK(yygotominor.yy76, yymsp[0].minor.yy0, Language::Feature::CODE_ASP_GR, ASPBlock);	}
#line 6746 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 475: /* stmt_code_blk ::= ASP_CP */
#line 3260 "bcplus/parser/detail/lemon_parser.y"
{ CODE_BLK(yygotominor.yy76, yymsp[0].minor.yy0, Language::Feature::CODE_ASP_CP, ASPBlock);	}
#line 6751 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 476: /* stmt_code_blk ::= F2LP_GR */
#line 3261 "bcplus/parser/detail/lemon_parser.y"
{ CODE_BLK(yygotominor.yy76, yymsp[0].minor.yy0, Language::Feature::CODE_F2LP_GR, F2LPBlock);	}
#line 6756 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 477: /* stmt_code_blk ::= F2LP_CP */
#line 3262 "bcplus/parser/detail/lemon_parser.y"
{ CODE_BLK(yygotominor.yy76, yymsp[0].minor.yy0, Language::Feature::CODE_F2LP_CP, F2LPBlock); }
#line 6761 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 478: /* stmt_code_blk ::= LUA_GR */
#line 3263 "bcplus/parser/detail/lemon_parser.y"
{ CODE_BLK(yygotominor.yy76, yymsp[0].minor.yy0, Language::Feature::CODE_LUA_GR, LUABlock);   }
#line 6766 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 479: /* stmt_code_blk ::= LUA_CP */
#line 3264 "bcplus/parser/detail/lemon_parser.y"
{ CODE_BLK(yygotominor.yy76, yymsp[0].minor.yy0, Language::Feature::CODE_LUA_CP, LUABlock);   }
#line 6771 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 480: /* stmt_code_blk ::= PYTHON_GR */
#line 3265 "bcplus/parser/detail/lemon_parser.y"
{ CODE_BLK(yygotominor.yy76, yymsp[0].minor.yy0, Language::Feature::CODE_PYTHON_GR, PYTHONBlock);   }
#line 6776 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 481: /* stmt_code_blk ::= PYTHON_CP */
#line 3266 "bcplus/parser/detail/lemon_parser.y"
{ CODE_BLK(yygotominor.yy76, yymsp[0].minor.yy0, Language::Feature::CODE_PYTHON_CP, PYTHONBlock);   }
#line 6781 "bcplus/parser/detail/lemon_parser.c"
        break;
      default:
      /* (1) statement_lst ::= */ yytestcase(yyruleno==1);
      /* (2) statement_lst ::= statement_lst error */ yytestcase(yyruleno==2);
        break;
  };
  yygoto = yyRuleInfo[yyruleno].lhs;
  yysize = yyRuleInfo[yyruleno].nrhs;
  yypParser->yyidx -= yysize;
  yyact = yy_find_reduce_action(yymsp[-yysize].stateno,(YYCODETYPE)yygoto);
  if( yyact < YYNSTATE ){
#ifdef NDEBUG
    /* If we are not debugging and the reduce action popped at least
    ** one element off the stack, then we can push the new element back
    ** onto the stack here, and skip the stack overflow test in yy_shift().
    ** That gives a significant speed improvement. */
    if( yysize ){
      yypParser->yyidx++;
      yymsp -= yysize-1;
      yymsp->stateno = (YYACTIONTYPE)yyact;
      yymsp->major = (YYCODETYPE)yygoto;
      yymsp->minor = yygotominor;
    }else
#endif
    {
      yy_shift(yypParser,yyact,yygoto,&yygotominor);
    }
  }else{
    assert( yyact == YYNSTATE + YYNRULE + 1 );
    yy_accept(yypParser);
  }
}

/*
** The following code executes when the parse fails
*/
#ifndef YYNOERRORRECOVERY
static void yy_parse_failed(
  yyParser *yypParser           /* The parser */
){
  lemon_parserARG_FETCH;
#ifndef NDEBUG
  if( yyTraceFILE ){
    fprintf(yyTraceFILE,"%sFail!\n",yyTracePrompt);
  }
#endif
  while( yypParser->yyidx>=0 ) yy_pop_parser_stack(yypParser);
  /* Here code is inserted which will be executed whenever the
  ** parser fails */
  lemon_parserARG_STORE; /* Suppress warning about unused %extra_argument variable */
}
#endif /* YYNOERRORRECOVERY */

/*
** The following code executes when a syntax error first occurs.
*/
static void yy_syntax_error(
  yyParser *yypParser,           /* The parser */
  int yymajor,                   /* The major type of the error token */
  YYMINORTYPE yyminor            /* The minor type of the error token */
){
  lemon_parserARG_FETCH;
#define TOKEN (yyminor.yy0)
#line 211 "bcplus/parser/detail/lemon_parser.y"
 parser->_parse_error("Syntax error.");	
#line 6847 "bcplus/parser/detail/lemon_parser.c"
  lemon_parserARG_STORE; /* Suppress warning about unused %extra_argument variable */
}

/*
** The following is executed when the parser accepts
*/
static void yy_accept(
  yyParser *yypParser           /* The parser */
){
  lemon_parserARG_FETCH;
#ifndef NDEBUG
  if( yyTraceFILE ){
    fprintf(yyTraceFILE,"%sAccept!\n",yyTracePrompt);
  }
#endif
  while( yypParser->yyidx>=0 ) yy_pop_parser_stack(yypParser);
  /* Here code is inserted which will be executed whenever the
  ** parser accepts */
  lemon_parserARG_STORE; /* Suppress warning about unused %extra_argument variable */
}


/*
** Handles a syntax error within the parser.
*/
static void yy_handle_err(yyParser* yypParser, int* yyerrorhit) {
      int yyact;
#ifdef YYERRORSYMBOL
  int yymx;
#endif
#ifndef NDEBUG
      if( yyTraceFILE ){
        fprintf(yyTraceFILE,"%sSyntax Error!\n",yyTracePrompt);
      }
#endif
#ifdef YYERRORSYMBOL
      /* A syntax error has occurred.
      ** The response to an error depends upon whether or not the
      ** grammar defines an error token "ERROR".  
      **
      ** This is what we do if the grammar does define ERROR:
      **
      **  * Call the %syntax_error function.
      **
      **  * Begin popping the stack until we enter a state where
      **    it is legal to shift the error symbol, then shift
      **    the error symbol.
      **
      **  * Set the error count to three.
      **
      **  * Begin accepting and shifting new tokens.  No new error
      **    processing will occur until three tokens have been
      **    shifted successfully.
      **
      */
	  yyact = YY_ERROR_ACTION;
      if( yypParser->yyerrcnt<0 ){
        yy_syntax_error(yypParser,yypParser->yylookmajor,yypParser->yylookminor);
      }
      yymx = yypParser->yystack[yypParser->yyidx].major;
      if( yymx==YYERRORSYMBOL || *yyerrorhit ){
#ifndef NDEBUG
        if( yyTraceFILE ){
          fprintf(yyTraceFILE,"%sDiscard input token %s\n",
             yyTracePrompt,yyTokenName[yypParser->yylookmajor]);
        }
#endif
        yy_destructor(yypParser, (YYCODETYPE)yypParser->yylookmajor,&yypParser->yylookminor);
        yypParser->yylookmajor = YYNOCODE;
        yypParser->yylookminor = yyzerominor;
      }else{
         while(
          yypParser->yyidx >= 0 &&
          yymx != YYERRORSYMBOL &&
          (yyact = yy_find_reduce_action(
                        yypParser->yystack[yypParser->yyidx].stateno,
                        YYERRORSYMBOL)) >= YYNSTATE
        ){
          yy_pop_parser_stack(yypParser);
        }
        if( yypParser->yyidx < 0 || yypParser->yylookmajor==0 ){
          yy_destructor(yypParser,(YYCODETYPE)yypParser->yylookmajor,&yypParser->yylookminor);
          yy_parse_failed(yypParser);
          yypParser->yylookmajor = YYNOCODE;
          yypParser->yylookminor = yyzerominor;
        }else if( yymx!=YYERRORSYMBOL ){
          YYMINORTYPE u2;
          u2.YYERRSYMDT = 0;
          yy_shift(yypParser,yyact,YYERRORSYMBOL,&u2);
        }
      }
      yypParser->yyerrcnt = 3;
      *yyerrorhit = 1;
#elif defined(YYNOERRORRECOVERY)
      /* If the YYNOERRORRECOVERY macro is defined, then do not attempt to
      ** do any kind of error recovery.  Instead, simply invoke the syntax
      ** error routine and continue going as if nothing had happened.
      **
      ** Applications can set this macro (for example inside %include) if
      ** they intend to abandon the parse upon the first syntax error seen.
      */
      yy_syntax_error(yypParser,yypParser->yylookmajor,yypParser->yylookminor);
      yy_destructor(yypParser,(YYCODETYPE)yypParser->yylookmajor,&yypParser->yylookminor);
      yypParser->yylookmajor = YYNOCODE;
      yypParser->yylookminor = yyzerominor;
      
#else  /* YYERRORSYMBOL is not defined */
      /* This is what we do if the grammar does not define ERROR:
      **
      **  * Report an error message, and throw away the input token.
      **
      **  * If the input token is $, then fail the parse.
      **
      ** As before, subsequent error messages are suppressed until
      ** three input tokens have been successfully shifted.
      */
      if( yypParser->yyerrcnt<=0 ){
        yy_syntax_error(yypParser,yypParser->yylookmajor,yypParser->yylookminor);
      }
      yypParser->yyerrcnt = 3;
      yy_destructor(yypParser,(YYCODETYPE)yypParser->yylookmajor,&yypParser->yylookminor);
      if( yyendofinput ){
        yy_parse_failed(yypParser);
      }
      yypParser->yylookmajor = YYNOCODE;
      yypParser->yylookminor = yyzerominor;
#endif
      yypParser->yysyntaxerr = 0;
}


/*
** Prepares the parser to accept tokens injected at the current
** location by extracting the lookahead token so that it can be
** reintroduced into the stream.
** Also pops the latest symbol off the parser's stack if the pop
** option is asserted.
** 
** returns the major type of the lookahead token that has been 
** cleared from the parser or YYNOCODE and sets the lookahead minor
** type appropriately.
*/
int lemon_parserPreInject(void* yyp, int pop, lemon_parserTOKENTYPE* lookahead) {
	yyParser* pParser = (yyParser*)yyp;
	int code = pParser->yylookmajor;
	if (pop && pParser->yyidx) yy_pop_parser_stack(pParser);
	if (code != YYNOCODE) {
		*lookahead = pParser->yylookminor.yy0;
		pParser->yylookmajor = YYNOCODE;
	    pParser->yylookminor = yyzerominor;
		return code;
	} else {
		*lookahead = yyzerominor.yy0;
		return 0;

	}
}

/*
** Gets the name of the provided token.
** Primarily for debugging purposes.
**
*/
char const* lemon_parserTokenName(int tok) {
	if (tok < 1) return "<INVALID_TOKEN>";
	else if (tok == YYNOCODE) return "<NOCODE_TOKEN>";
#ifdef YYERRORSYMBOL
	else if (tok == YYERRORSYMBOL) return "<ERROR_TOKEN>";
#endif
	return yyTokenName[tok];
}


/*
** Checks to see if there is a next-token independent reduction rule
** and executes it.
*/
void lemon_parserAttemptReduce(void* yyp lemon_parserARG_PDECL) {
	yyParser* yypParser = (yyParser*)yyp;
	lemon_parserARG_STORE;
	int act = 0;
	int yyerrorhit = 0;
	do {
		yypParser->yysyntaxerr = 0;
		act = yy_find_reduce_action(yypParser->yystack[yypParser->yyidx].stateno, YYNOCODE);
		if (act >= YYNSTATE && act < YYNSTATE + YYNRULE) {
			// There is a reduce action. Do it.
			yy_reduce(yypParser, act-YYNSTATE);	
		}

		if (yypParser->yysyntaxerr) {
			yy_handle_err(yypParser, &yyerrorhit);
		}

	} while (act >= YYNSTATE && act < YYNSTATE + YYNRULE);
}

/* The main parser program.
** The first argument is a pointer to a structure obtained from
** "lemon_parserAlloc" which describes the current state of the parser.
** The second argument is the major token number.  The third is
** the minor token.  The fourth optional argument is whatever the
** user wants (and specified in the grammar) and is available for
** use by the action routines.
**
** Inputs:
** <ul>
** <li> A pointer to the parser (an opaque structure.)
** <li> The major token number.
** <li> The minor token number.
** <li> An option argument of a grammar-specified type.
** </ul>
**
** Outputs:
** None.
*/
void lemon_parser(
  void *yyp,                   /* The parser */
  int yymajor,                 /* The major token code number */
  lemon_parserTOKENTYPE yyminor       /* The value for the token */
  lemon_parserARG_PDECL               /* Optional %extra_argument parameter */
){
  int yyact;            /* The parser action. */
  int yyendofinput;     /* True if we are at the end of input */
  int yyerrorhit = 0;
  yyParser *yypParser;  /* The parser */

  /* (re)initialize the parser, if necessary */
  yypParser = (yyParser*)yyp;
  if( yypParser->yyidx<0 ){
#if YYSTACKDEPTH<=0
    if( yypParser->yystksz <=0 ){
      /*memset(&yyminorunion, 0, sizeof(yyminorunion));*/
      yypParser->yylookmajor = YYNOCODE;
      yypParser->yylookminor = yyzerominor;
      yyStackOverflow(yypParser/*, &yyminorunion */);
      return;
    }
#endif
    yypParser->yyidx = 0;
    yypParser->yyerrcnt = -1;
    yypParser->yystack[0].stateno = 0;
    yypParser->yystack[0].major = 0;
  }
  yypParser->yylookmajor = yymajor;
  yypParser->yylookminor.yy0 = yyminor;
  yyendofinput = (yypParser->yylookmajor==0);
  lemon_parserARG_STORE;

#ifndef NDEBUG
  if( yyTraceFILE ){
    fprintf(yyTraceFILE,"%sInput %s\n",yyTracePrompt,yyTokenName[yypParser->yylookmajor]);
  }
#endif

  do{
    yyact = yy_find_shift_action(yypParser,(YYCODETYPE)yypParser->yylookmajor);
    if( yyact<YYNSTATE ){
      assert( !yyendofinput );  /* Impossible to shift the $ token */
      yy_shift(yypParser,yyact,yypParser->yylookmajor,&yypParser->yylookminor);
      yypParser->yyerrcnt--;
      yypParser->yylookmajor = YYNOCODE;
      yypParser->yylookminor = yyzerominor;
    }else if( yyact < YYNSTATE + YYNRULE ) {
      yy_reduce(yypParser,yyact-YYNSTATE);
    } else {
      	assert( yyact == YY_ERROR_ACTION );
		yypParser->yysyntaxerr = 1; 
	}
	
	if (yypParser->yysyntaxerr) {
		yy_handle_err(yypParser, &yyerrorhit);
    }
  }while( yypParser->yylookmajor!=YYNOCODE && yypParser->yyidx>=0 );
  return;
}
