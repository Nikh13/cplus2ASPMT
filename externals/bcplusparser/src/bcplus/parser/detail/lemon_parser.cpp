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

		
#line 346 "bcplus/parser/detail/lemon_parser.y"

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

#line 547 "bcplus/parser/detail/lemon_parser.y"

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

#line 812 "bcplus/parser/detail/lemon_parser.y"

	#define NUM_UOP(t_new, t, val) \
		ref_ptr<const Referenced> t_ptr = t; \
		t_new = new Number(val, t->beginLoc(), t->endLoc());


	#define NUM_BOP(t_new, l, r, val) \
		ref_ptr<const Referenced> l_ptr = l, r_ptr = r; \
		t_new = new Number(val, l->beginLoc(), r->endLoc());

#line 858 "bcplus/parser/detail/lemon_parser.y"

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

#line 939 "bcplus/parser/detail/lemon_parser.y"


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



#line 1075 "bcplus/parser/detail/lemon_parser.y"

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



#line 1144 "bcplus/parser/detail/lemon_parser.y"

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

#line 1561 "bcplus/parser/detail/lemon_parser.y"


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
#line 1689 "bcplus/parser/detail/lemon_parser.y"

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
#line 2877 "bcplus/parser/detail/lemon_parser.y"

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

#line 2900 "bcplus/parser/detail/lemon_parser.y"

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
#line 2929 "bcplus/parser/detail/lemon_parser.y"

	struct QueryData {
		QueryStatement::FormulaList* l;
		NumberRangeEval* maxstep;
		Token const* label;
	};

#line 3036 "bcplus/parser/detail/lemon_parser.y"

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

#line 3108 "bcplus/parser/detail/lemon_parser.y"

	#define CLAUSE(elem, kw, f, feature) 														\
		ref_ptr<const Token> kw_ptr = kw;														\
		elem = f;																				\
		if (!parser->lang()->support(feature)) {												\
			parser->_feature_error(feature, &kw->beginLoc());									\
			YYERROR;																			\
		}
#line 3219 "bcplus/parser/detail/lemon_parser.y"

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


#line 3412 "bcplus/parser/detail/lemon_parser.y"

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
#define YYNOCODE 273
#define YYACTIONTYPE unsigned short int
#define lemon_parserTOKENTYPE  Token const* 								
typedef union {
  int yyinit;
  lemon_parserTOKENTYPE yy0;
  StrongNCStatement* yy10;
  ObjectDeclaration::Element::ObjectList* yy13;
  ConstantDeclaration* yy15;
  NumberRangeEval* yy21;
  Variable* yy45;
  QuantifierFormula::Operator::type yy49;
  SortDeclaration::ElementList* yy71;
  Token const* yy75;
  QuantifierFormula* yy101;
  CardinalityFormula::VariableList* yy111;
  UNUSED yy113;
  Term* yy115;
  TermList* yy147;
  ForallTStatement* yy180;
  NumberRange* yy205;
  SortSymbol const* yy220;
  ShowStatement::ElementList* yy235;
  ConstantSymbol::Type::type yy245;
  Statement* yy248;
  Constant* yy257;
  VariableDeclaration* yy267;
  ObjectDeclaration::Element* yy278;
  ObjectDeclaration* yy288;
  Number* yy289;
  Formula* yy297;
  MacroSymbol::ArgumentList* yy338;
  Object* yy342;
  CardinalityFormula* yy369;
  QueryData yy373;
  QuantifierFormula::QuantifierList* yy381;
  TokenList* yy400;
  IdentifierDeclList* yy410;
  AtomicFormula* yy426;
  SortDeclaration* yy429;
  VariableDeclaration::ElementList* yy445;
  ConstantDeclaration::ElementList* yy465;
  MacroSymbol* yy483;
  ObjectDeclaration::ElementList* yy486;
  QueryStatement* yy490;
  MacroDeclaration* yy495;
  LuaTerm* yy497;
  NCStatement* yy505;
  ConstantSymbol::SortList* yy507;
  SortSymbol* yy521;
  MacroDeclaration::ElementList* yy529;
  RateDeclaration* yy541;
  int yy545;
} YYMINORTYPE;
#ifndef YYSTACKDEPTH
#define YYSTACKDEPTH 100
#endif
#define lemon_parserARG_SDECL  BCParser* parser						;
#define lemon_parserARG_PDECL , BCParser* parser						
#define lemon_parserARG_FETCH  BCParser* parser						 = yypParser->parser						
#define lemon_parserARG_STORE yypParser->parser						 = parser						
#define YYNSTATE 953
#define YYNRULE 485
#define YYERRORSYMBOL 150
#define YYERRSYMDT yy545
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
#define YY_ACTTAB_COUNT (3677)
static const YYACTIONTYPE yy_action[] = {
 /*     0 */   952,  217,  218,  951,  950,  949,  948,  947,  946,  945,
 /*    10 */   944,  941,  940,  939,  938,  937,  936,  935,  943,  942,
 /*    20 */   767,  902,  339,  934,  926,  933,  932,  925,  128,  126,
 /*    30 */   124,  122,  120,  929,  335,  340,  902,  339,  934,  926,
 /*    40 */   504,  932,  925,  856,  446,  124,  122,  120,  927,  334,
 /*    50 */   340,  769,  839,  381,  261,  953,  354,  848,  845,  844,
 /*    60 */   843,  842,  769,  129,  381,  263,  855,  854,  749,   19,
 /*    70 */   506,  902,  339,  934,  926,  933,  932,  925,  129,   24,
 /*    80 */    23,   22,   26,   25,  334,  340,   27,  558,  497,  770,
 /*    90 */   771,  386,  848,  845,  844,  843,  842,  495,  559,  497,
 /*   100 */   770,  771,  261,  653,  652,  651,  650,  649,  648,  647,
 /*   110 */   646,  645,  644,  643,  642,  641,  640,  639,  638,  637,
 /*   120 */   636,  635,  901,  900,  607,  502,  792,  608,  899,  619,
 /*   130 */   618,  615,  614,  613,  612,  617,  616,  920,  930,  931,
 /*   140 */   934,  926,  933,  932,  925,  511,  445,  181,  179,  177,
 /*   150 */   175,  174,   12,   14,  177,  175,  174,   33,  874,   10,
 /*   160 */    11,  876,  200,  602,  266,  327,   73,  534,   64,  928,
 /*   170 */   928,   26,   25,  265,  220,   27,  850,  872,  871,  873,
 /*   180 */     9,  536,  535,    8,  600,   32,   63,  223,  506,  264,
 /*   190 */    24,   23,   22,   26,   25,  852,  853,   27,   60,  577,
 /*   200 */   341,  193,  769,   37,  381,   36,  276,  276,   31,    7,
 /*   210 */    62,   13,  702,  893,  883,  934,  926,  933,  932,  925,
 /*   220 */    15,  146,  145,  144,  436,  143,  142,  141,  140,  828,
 /*   230 */   817,  934,  926,  933,  932,  925,  267,  132,  546,  497,
 /*   240 */   770,  771,  103,  134,  337,  159,  150,  149,  148,  147,
 /*   250 */   611,   16,  789,  769,  768,  381,  383,  814,  811,  230,
 /*   260 */   229,  228,  610,  610,  924,  609,  599,  598,  597,  550,
 /*   270 */   199,   54,   53,   36,  121,   55,  760,  759,  758,  757,
 /*   280 */   777,  901,  900,  607,  776,  557,  608,  899,  493,  559,
 /*   290 */   497,  770,  771,  756,  227,  754,  701,  691,  934,  926,
 /*   300 */   933,  932,  925,  800,  753,  795,  796,  784,  783,  785,
 /*   310 */   234,  232,  230,  229,  228,   31,  566,  564,  568,  752,
 /*   320 */   750,  751,  755,  312,   66,  786,  787,  837,  836,  928,
 /*   330 */  1335,  450,  769,  235,  381,   21,  872,  871,  873,  253,
 /*   340 */   252,  251,  706,  591,  934,  926,  933,  932,  925,  157,
 /*   350 */   155,  153,  152,  151,  840,  841, 1335,  221,  602,  923,
 /*   360 */     2,  661,   30,  660,  761,  673,  276,  233,  576,  497,
 /*   370 */   770,  771,  231,  710,  194,  575,  562,  898,  330,  723,
 /*   380 */    36,  362,  677,  674,  672,  671,  112,  111,  110,  129,
 /*   390 */   109,  108,  107,  106,  191,   28,   29,  901,  900,  607,
 /*   400 */  1187,  103,  608,  899, 1187,  257,  255,  253,  252,  251,
 /*   410 */   117,  116,  115,  114,  113,  477,  659,  658,  737,  119,
 /*   420 */   381,  724,  610,  924,  609,  599,  598,  597,  701,  691,
 /*   430 */   934,  926,  933,  932,  925,  902,  339,  934,  926,  504,
 /*   440 */   932,  925,  173,   45,   44,  928,  727,   46,  334,  340,
 /*   450 */   591,  118,  872,  871,  873,  356,  848,  845,  844,  843,
 /*   460 */   842,  590,  916,  350,  742,  489,  736,  194,   20,  506,
 /*   470 */   852,  853,  830,  217,  218,  829,  193,  133,   37,  112,
 /*   480 */   111,  110,  276,  109,  108,  107,  106,  311,  706,  591,
 /*   490 */   934,  926,  504,  932,  925,  128,  126,  124,  122,  120,
 /*   500 */   697,  105,  602,  117,  116,  115,  114,  113,   66,  733,
 /*   510 */   486,  673,  132,  198,  705,  704,  607,  103,  104,  608,
 /*   520 */   703,   38,  506,  723,  330,  102,  791,  346,  677,  674,
 /*   530 */   672,  671,  726,  157,  155,  153,  152,  151,  610,  924,
 /*   540 */   609,  599,  598,  597,   17,  205,  225,  226,  189,    4,
 /*   550 */   197,  203,  204,  828,  817,  934,  926,  933,  932,  925,
 /*   560 */   790,  498,  928,  725,  456,  720,  743,  537,  333,  681,
 /*   570 */   680,  538,  190,  706,  591,  934,  926,  504,  932,  925,
 /*   580 */   351,  814,  811,  201,  479,  480,  192,  669,  670,  602,
 /*   590 */   215,  246,  202,    6,  101,   49,  673,   75,  545,  276,
 /*   600 */   100,   24,   23,   22,   26,   25,   39,  506,   27,  330,
 /*   610 */   601,  216,  348,  677,  674,  672,  671,  153,  152,  151,
 /*   620 */    24,   23,   22,   26,   25,  837,  836,   27,   47,   48,
 /*   630 */   919,  918,  607,   40,  139,  608,  917,  665,  602,  363,
 /*   640 */   902,  339,  934,  926,  933,  932,  925,  709,   94,   93,
 /*   650 */    92,   91,   90,  331,  340,  610,  924,  609,  921,  723,
 /*   660 */   352,  848,  845,  844,  843,  842,  706,  591,  934,  926,
 /*   670 */   933,  932,  925,  499,  744,  498,  196,   74,  928,  257,
 /*   680 */   255,  253,  252,  251,  928,  912,  911,  913,  129,  673,
 /*   690 */   920,  930,  931,  934,  926,  933,  932,  925,  510,  445,
 /*   700 */   455,  720,  330,  914,  915,  361,  677,  674,  672,  671,
 /*   710 */    27,  127,  922,  705,  704,  607,   61,    3,  608,  703,
 /*   720 */   898,  893,  883,  934,  926,  933,  932,  925,   76,  112,
 /*   730 */   111,  110,  470,  109,  108,  107,  106,  542,  719,  328,
 /*   740 */   663,  662,  487,  730,  486,  125,  247,  485,  481,  544,
 /*   750 */   123,  528,   69,  117,  116,  115,  114,  113,  201,  262,
 /*   760 */   325,  928,  257,  255,  253,  252,  251,  202,  681,  680,
 /*   770 */   682,  610,  924,  609,  606,  605,  604,  610,  894,  893,
 /*   780 */   883,  934,  926,  933,  932,  925,  669,  670,  832,  215,
 /*   790 */   391,   55,    6,  328,   49,  603,  924,  737,  276,  381,
 /*   800 */   734,  902,  338,  934,  926,  933,  932,  925,  182,   24,
 /*   810 */    23,   22,   26,   25,  849,  340,   27,  579,  129,  806,
 /*   820 */   224,  834,  848,  845,  844,  843,  842,   47,   48,  919,
 /*   830 */   918,  607,  602,  139,  608,  917,  805,  902,  339,  934,
 /*   840 */   926,  933,  932,  925,  769,  740,  381,  271,  746,  603,
 /*   850 */   334,  340,    7,  596,  610,  924,  609,  847,  848,  845,
 /*   860 */   844,  843,  842,   15,  146,  145,  144,  804,  143,  142,
 /*   870 */   141,  140,   99,   98,   97,   96,   95,  928,  191,  492,
 /*   880 */   559,  497,  770,  771,  912,  911,  913,  591,  159,  150,
 /*   890 */   149,  148,  147,  893,  883,  934,  926,  933,  932,  925,
 /*   900 */   729,   68,  914,  915,  471,   23,   22,   26,   25,  851,
 /*   910 */   127,   27,  901,  900,  607,  745,   67,  608,  899,  803,
 /*   920 */   219,  920,  930,  931,  934,  926,  933,  932,  925,  508,
 /*   930 */   445,  294, 1375,  902,  339,  934,  926,  933,  932,  925,
 /*   940 */   837,  836,  802,  250,  125,  191,  334,  340,  259,  123,
 /*   950 */   500,  794, 1375,  846,  848,  845,  844,  843,  842,  801,
 /*   960 */   928,  234,  232,  230,  229,  228,    3,  872,  871,  873,
 /*   970 */   610,  924,  609,  606,  605,  604,  532,  328,  112,  111,
 /*   980 */   110,  248,  109,  108,  107,  106,  249,   52,   51,   50,
 /*   990 */    54,   53,  578,  131,   55,  827,  826,  607,  484,  544,
 /*  1000 */   608,  825,  117,  116,  115,  114,  113,  701,  691,  934,
 /*  1010 */   926,  933,  932,  925,  739,  902,  339,  934,  926,  933,
 /*  1020 */   932,  925,  257,  255,  253,  252,  251,  130,  334,  340,
 /*  1030 */   483,  544,  103,  603,  798,  594,  848,  845,  844,  843,
 /*  1040 */   842,  793,  451,  928,  191,  128,  126,  124,  122,  120,
 /*  1050 */   819,  818,  820,  610,  924,  609,  599,  598,  597,  261,
 /*  1060 */   893,  883,  934,  926,  933,  932,  925,  188,  809,  810,
 /*  1070 */   507,  435,  708,  482,  544,  766,   58,  858,  892,  891,
 /*  1080 */   607,  457,  544,  608,  890,  260,  325,  824,  831,  706,
 /*  1090 */   591,  934,  926,  933,  932,  925,  167,  166,  165,  212,
 /*  1100 */   164,  163,  162,  161,  257,  255,  253,  252,  251,   56,
 /*  1110 */    57,  573,  673,  381,  772,  160,  773,  769,  572,  381,
 /*  1120 */   172,  171,  170,  169,  168,  329,  928,  602,  344,  677,
 /*  1130 */   674,  672,  671,  885,  884,  886,  610,  924,  609,  211,
 /*  1140 */   664,  706,  591,  934,  926,  933,  932,  925,  723, 1439,
 /*  1150 */     1,  887,  888,  496,  497,  770,  771,  765,  668,  180,
 /*  1160 */     5,  700,  699,  607,  673,  569,  608,  698,  893,  883,
 /*  1170 */   934,  926,  933,  932,  925,  210,  209,  679,  908,  882,
 /*  1180 */   667,  677,  674,  672,  671,   43,   42,   41,   45,   44,
 /*  1190 */   722,  764,   46,  178,  570,  567,  381,  381,  176,  920,
 /*  1200 */   930,  931,  934,  926,  933,  932,  925,  503,  445,  928,
 /*  1210 */   763,  128,  126,  124,  122,  120,  693,  692,  694,  610,
 /*  1220 */   924,  609,  208,  902,  339,  934,  926,  933,  932,  925,
 /*  1230 */   769,  762,  381,  592,  695,  696,  334,  340,  737,  561,
 /*  1240 */   381,  560,  158,  593,  848,  845,  844,  843,  842,  207,
 /*  1250 */   902,  339,  934,  926,  933,  932,  925,  775,  565,  592,
 /*  1260 */   381,  907,  186,  334,  340,  488,  559,  497,  770,  771,
 /*  1270 */   413,  848,  845,  844,  843,  842,  156,  187,  563,  928,
 /*  1280 */   381,  154,  554,  490,  735,  489,  736,  902,  339,  934,
 /*  1290 */   926,  933,  932,  925,  128,  126,  124,  122,  120,  707,
 /*  1300 */   334,  340,  610,  924,  609,  928,  748,  465,  848,  845,
 /*  1310 */   844,  843,  842,  206,  747,  706,  591,  934,  926,  933,
 /*  1320 */   932,  925,  551,  902,  339,  934,  926,  933,  932,  925,
 /*  1330 */   185,  257,  255,  253,  252,  251,  334,  340,  673,  591,
 /*  1340 */   549,  184,  214,  464,  848,  845,  844,  843,  842,  183,
 /*  1350 */   555,  330,  381,  732,  676,  677,  674,  672,  671,   35,
 /*  1360 */   543,  851,  273,  728,  721,  902,  339,  934,  926,  933,
 /*  1370 */   932,  925,  610,  274,  552,   72,  381,   34,  334,  340,
 /*  1380 */   718,   46,  213,  512,  476,  357,  848,  845,  844,  843,
 /*  1390 */   842,  902,  339,  934,  926,  933,  932,  925,  610,   24,
 /*  1400 */    23,   22,   26,   25,  334,  340,   27,  657,  656,   65,
 /*  1410 */   270,  355,  848,  845,  844,  843,  842,  902,  339,  934,
 /*  1420 */   926,  933,  932,  925,  541,  531,  530,   71,  529,  655,
 /*  1430 */   334,  340,  491,  738,  547,  527,  526,  353,  848,  845,
 /*  1440 */   844,  843,  842,  902,  339,  934,  926,  933,  932,  925,
 /*  1450 */   525,   24,   23,   22,   26,   25,  334,  340,   27,  654,
 /*  1460 */   245,  634,  633,  385,  848,  845,  844,  843,  842,  632,
 /*  1470 */   877,  631,  902,  339,  934,  926,  933,  932,  925,  630,
 /*  1480 */   328,  628,  627,  625,  624,  334,  340,  784,  783,  785,
 /*  1490 */   623,  622,  384,  848,  845,  844,  843,  842,  902,  339,
 /*  1500 */   934,  926,  933,  932,  925,  786,  787,  621,  875,  603,
 /*  1510 */   838,  334,  340,  235,  924,  835,  323,   18,  242,  848,
 /*  1520 */   845,  844,  843,  842,  322,  920,  930,  931,  934,  926,
 /*  1530 */   933,  932,  925,  509,  445,  321,  603,  902,  339,  934,
 /*  1540 */   926,  933,  932,  925,   17,  587,  195,  233,   59,  833,
 /*  1550 */   336,  340,  231,   31,  319,  799,  585,  375,  848,  845,
 /*  1560 */   844,  843,  842,  902,  339,  934,  926,  933,  932,  925,
 /*  1570 */   317,   24,   23,   22,   26,   25,  334,  340,   27,  501,
 /*  1580 */   583,  315,  313,  343,  848,  845,  844,  843,  842,  902,
 /*  1590 */   339,  934,  926,  933,  932,  925,  741,  906,  768,  293,
 /*  1600 */   581,  580,  334,  340,  789,  308,  768,  309,  305,  241,
 /*  1610 */   848,  845,  844,  843,  842,  902,  339,  934,  926,  933,
 /*  1620 */   932,  925,  128,  126,  124,  122,  120,   31,  334,  340,
 /*  1630 */   128,  126,  124,  122,  120,  240,  848,  845,  844,  843,
 /*  1640 */   842,  307,  304,  524,  902,  339,  934,  926,  933,  932,
 /*  1650 */   925,  858,  303,  292,  523,  301,  299,  334,  340,  784,
 /*  1660 */   783,  785,  521,  520,  236,  848,  845,  844,  843,  842,
 /*  1670 */   902,  339,  934,  926,  933,  932,  925,  786,  787,  297,
 /*  1680 */   288,  519,  518,  334,  340,  235,  295,  291,  290,  287,
 /*  1690 */   239,  848,  845,  844,  843,  842,  920,  930,  931,  934,
 /*  1700 */   926,  933,  932,  925,  517,  444,  286,  285,  283,  902,
 /*  1710 */   339,  934,  926,  933,  932,  925,  516,  515,  282,  233,
 /*  1720 */   281,  807,  334,  340,  231,  584,  320,  280,  278,  238,
 /*  1730 */   848,  845,  844,  843,  842,  902,  339,  934,  926,  933,
 /*  1740 */   932,  925,  514,   52,   51,   50,   54,   53,  334,  340,
 /*  1750 */    55,  582,  513,  314,  797,  237,  848,  845,  844,  843,
 /*  1760 */   842,  706,  591,  934,  926,  933,  932,  925,   51,   50,
 /*  1770 */    54,   53,  533,  310,   55,  706,  591,  934,  926,  933,
 /*  1780 */   932,  925,  306,  626,  673,  706,  591,  934,  926,  933,
 /*  1790 */   932,  925,  289,  284,  277,  324,  326,  330,  673,  774,
 /*  1800 */   675,  677,  674,  672,  671,  379,  380,  453,  673,  715,
 /*  1810 */   717,  330,  478,  454,  540,  677,  674,  672,  671,  714,
 /*  1820 */   713,  330,  712,  711,  539,  677,  674,  672,  671,  706,
 /*  1830 */   591,  934,  926,  933,  932,  925,  378,  706,  591,  934,
 /*  1840 */   926,  933,  932,  925,  902,  339,  934,  926,  933,  932,
 /*  1850 */   925,  377,  673,   42,   41,   45,   44,  332,  340,   46,
 /*  1860 */   673,  376,  396,  548,  359,  330,  856,  851,  397,  677,
 /*  1870 */   674,  672,  671,  330,  358,  318,  448,  677,  674,  672,
 /*  1880 */   671,  706,  591,  934,  926,  933,  932,  925,  505,  855,
 /*  1890 */   854,  258,  316,  258,  586,  706,  591,  934,  926,  933,
 /*  1900 */   932,  925,  522,  302,  673,  706,  591,  934,  926,  933,
 /*  1910 */   932,  925,  298,  296,  300,   31,  279,  330,  673,  382,
 /*  1920 */   447,  677,  674,  672,  671,  256,  458,  256,  673,  782,
 /*  1930 */   254,  330,  254,  459,  349,  677,  674,  672,  671,  781,
 /*  1940 */    70,  330,  780,  779,  347,  677,  674,  672,  671,  706,
 /*  1950 */   591,  934,  926,  933,  932,  925,  902,  339,  934,  926,
 /*  1960 */   933,  932,  925,  778,   24,   23,   22,   26,   25,  335,
 /*  1970 */   340,   27,  673,   24,   23,   22,   26,   25,  856,  851,
 /*  1980 */    27,  399,  731, 1440, 1440,  330,  138, 1440,  345,  677,
 /*  1990 */   674,  672,  671,  902,  339,  934,  926,  933,  932,  925,
 /*  2000 */   857,  855,  854, 1440,  874, 1440,  335,  340, 1440,  602,
 /*  2010 */    43,   42,   41,   45,   44,  856,  851,   46,  902,  339,
 /*  2020 */   934,  926,  933,  932,  925, 1440, 1440,  137, 1440, 1440,
 /*  2030 */   595,  335,  340,  222,  506, 1440, 1440,  275,  855,  854,
 /*  2040 */   856,  851,  889,  902,  339,  934,  926,  933,  932,  925,
 /*  2050 */  1440,   43,   42,   41,   45,   44,  335,  340,   46, 1440,
 /*  2060 */  1440, 1440,  272,  855,  854,  856,  851, 1440,  902,  339,
 /*  2070 */   934,  926,  933,  932,  925,  181,  179,  177,  175,  174,
 /*  2080 */  1440,  335,  340, 1440, 1440, 1440, 1440,  269,  855,  854,
 /*  2090 */   856,  851,   89,   88,   87, 1440,   86,   85,   84,   83,
 /*  2100 */    76,   82,   81, 1440,   80,   79,   78,   77, 1440, 1440,
 /*  2110 */  1440, 1440,  268,  855,  854, 1440,   94,   93,   92,   91,
 /*  2120 */    90, 1440, 1440, 1440,   99,   98,   97,   96,   95, 1440,
 /*  2130 */  1032, 1032, 1032, 1440, 1032, 1032, 1032, 1032,  167,  166,
 /*  2140 */   165, 1440,  164,  163,  162,  161,  789, 1440,  768, 1440,
 /*  2150 */   789, 1440,  768, 1440, 1032, 1032, 1032, 1032, 1032, 1440,
 /*  2160 */  1440, 1440,  172,  171,  170,  169,  168,  112,  111,  110,
 /*  2170 */  1440,  109,  108,  107,  106, 1440, 1440,  920,  930,  931,
 /*  2180 */   934,  926,  933,  932,  925, 1440,  474, 1440, 1440, 1440,
 /*  2190 */  1440,  117,  116,  115,  114,  113, 1440, 1440, 1440, 1440,
 /*  2200 */  1440,  784,  783,  785, 1440,  784,  783,  785, 1440, 1440,
 /*  2210 */   574,  571, 1440, 1440,  556,  553, 1440, 1440, 1440,  786,
 /*  2220 */   787, 1440, 1440,  786,  787, 1440, 1440,  235, 1440, 1440,
 /*  2230 */  1440,  235, 1440, 1440, 1440,  828,  817,  934,  926,  933,
 /*  2240 */   932,  925,  920,  930,  931,  934,  926,  933,  932,  925,
 /*  2250 */   816,  395, 1440,  828,  817,  934,  926,  933,  932,  925,
 /*  2260 */  1440,  233,  808,  814,  811,  233,  231, 1440,  337, 1440,
 /*  2270 */   231,  828,  817,  934,  926,  933,  932,  925, 1440, 1440,
 /*  2280 */   813,  814,  811, 1440, 1440, 1440,  337, 1440,  828,  817,
 /*  2290 */   934,  926,  933,  932,  925, 1440, 1440, 1440,  812,  814,
 /*  2300 */   811, 1440, 1440,  337,  828,  817,  934,  926,  933,  932,
 /*  2310 */   925, 1440, 1440, 1440, 1440,  589,  814,  811, 1440,  337,
 /*  2320 */  1440, 1440,  828,  817,  934,  926,  933,  932,  925, 1440,
 /*  2330 */  1440,  588,  814,  811, 1440,  898, 1440,  337,  828,  817,
 /*  2340 */   934,  926,  933,  932,  925, 1440, 1440, 1440, 1440,  400,
 /*  2350 */   814,  811,  789,  337,  920,  930,  931,  934,  926,  933,
 /*  2360 */   932,  925, 1265,  475, 1440,  461,  814,  811,  117,  116,
 /*  2370 */   115,  114,  113,  828,  817,  934,  926,  933,  932,  925,
 /*  2380 */  1265, 1440, 1440, 1265, 1440, 1440, 1440,  136,  337, 1440,
 /*  2390 */   920,  930,  931,  934,  926,  933,  932,  925, 1440,  910,
 /*  2400 */   460,  814,  811, 1440, 1440, 1265, 1265,  784,  783,  785,
 /*  2410 */  1440,   43,   42,   41,   45,   44, 1265, 1265,   46, 1440,
 /*  2420 */  1440, 1440, 1440, 1265,  868,  786,  787, 1440, 1440, 1440,
 /*  2430 */  1440, 1440, 1440,  235,  902,  342,  934,  926,  933,  932,
 /*  2440 */   925, 1440, 1440, 1440, 1440, 1265, 1440,  870,  431,  902,
 /*  2450 */   430,  934,  926,  933,  932,  925, 1440,  128,  126,  124,
 /*  2460 */   122,  120,  390,  431, 1440, 1440, 1440,  233, 1440, 1440,
 /*  2470 */  1440, 1440,  231, 1440, 1440,  902,  865,  934,  926,  933,
 /*  2480 */   932,  925, 1440, 1440, 1440, 1440, 1440, 1440,  870,  431,
 /*  2490 */   920,  930,  931,  934,  926,  933,  932,  925, 1440,  903,
 /*  2500 */  1440, 1440,  920,  930,  931,  934,  926,  933,  932,  925,
 /*  2510 */  1440,  909,  920,  930,  931,  934,  926,  933,  932,  925,
 /*  2520 */  1440,  904,  920,  930,  931,  934,  926,  933,  932,  925,
 /*  2530 */  1440,  394,  920,  930,  931,  934,  926,  933,  932,  925,
 /*  2540 */  1440,  905, 1440, 1440,  920,  930,  931,  934,  926,  933,
 /*  2550 */   932,  925, 1440,  393,  920,  930,  931,  934,  926,  933,
 /*  2560 */   932,  925, 1440,  392,  920,  930,  931,  934,  926,  933,
 /*  2570 */   932,  925, 1440,  473, 1440, 1440,  920,  930,  931,  934,
 /*  2580 */   926,  933,  932,  925, 1440,  472, 1440,  920,  930,  931,
 /*  2590 */   934,  926,  933,  932,  925,  867,  897,  920,  930,  931,
 /*  2600 */   934,  926,  933,  932,  925, 1440,  896,  920,  930,  931,
 /*  2610 */   934,  926,  933,  932,  925, 1440,  895, 1440,  920,  930,
 /*  2620 */   931,  934,  926,  933,  932,  925, 1440,  443,  128,  126,
 /*  2630 */   124,  122,  120,  920,  930,  931,  934,  926,  933,  932,
 /*  2640 */   925, 1440,  442,  920,  930,  931,  934,  926,  933,  932,
 /*  2650 */   925, 1440,  441, 1440, 1440, 1440, 1440, 1440, 1440,  920,
 /*  2660 */   930,  931,  934,  926,  933,  932,  925, 1440,  440, 1440,
 /*  2670 */   920,  930,  931,  934,  926,  933,  932,  925, 1440,  439,
 /*  2680 */   920,  930,  931,  934,  926,  933,  932,  925, 1440,  438,
 /*  2690 */   920,  930,  931,  934,  926,  933,  932,  925, 1440,  437,
 /*  2700 */   920,  930,  931,  934,  926,  933,  932,  925, 1440,  433,
 /*  2710 */   920,  930,  931,  934,  926,  933,  932,  925, 1440,  432,
 /*  2720 */   920,  930,  931,  934,  926,  933,  932,  925, 1440,  869,
 /*  2730 */   920,  930,  931,  934,  926,  933,  932,  925, 1440,  389,
 /*  2740 */   920,  930,  931,  934,  926,  933,  932,  925, 1440,  388,
 /*  2750 */   920,  930,  931,  934,  926,  933,  932,  925, 1440,  387,
 /*  2760 */   920,  930,  931,  934,  926,  933,  932,  925, 1440,  469,
 /*  2770 */   920,  930,  931,  934,  926,  933,  932,  925, 1440,  468,
 /*  2780 */   920,  930,  931,  934,  926,  933,  932,  925, 1440,  864,
 /*  2790 */   920,  930,  931,  934,  926,  933,  932,  925, 1440,  863,
 /*  2800 */  1440, 1440, 1440, 1440,  920,  930,  931,  934,  926,  933,
 /*  2810 */   932,  925, 1440,  862,  920,  930,  931,  934,  926,  933,
 /*  2820 */   932,  925, 1440,  467, 1440, 1440, 1440, 1440, 1440, 1440,
 /*  2830 */   920,  930,  931,  934,  926,  933,  932,  925, 1440,  466,
 /*  2840 */  1440,  920,  930,  931,  934,  926,  933,  932,  925, 1440,
 /*  2850 */   861,  920,  930,  931,  934,  926,  933,  932,  925, 1440,
 /*  2860 */   860,  920,  930,  931,  934,  926,  933,  932,  925, 1440,
 /*  2870 */   859,  920,  930,  931,  934,  926,  933,  932,  925, 1440,
 /*  2880 */   429,  920,  930,  931,  934,  926,  933,  932,  925, 1440,
 /*  2890 */   428,  920,  930,  931,  934,  926,  933,  932,  925, 1440,
 /*  2900 */   427,  920,  930,  931,  934,  926,  933,  932,  925, 1440,
 /*  2910 */   426,  920,  930,  931,  934,  926,  933,  932,  925, 1440,
 /*  2920 */   425,  920,  930,  931,  934,  926,  933,  932,  925, 1440,
 /*  2930 */   424,  920,  930,  931,  934,  926,  933,  932,  925, 1440,
 /*  2940 */   423,  920,  930,  931,  934,  926,  933,  932,  925, 1440,
 /*  2950 */   422,  920,  930,  931,  934,  926,  933,  932,  925, 1440,
 /*  2960 */   421,  920,  930,  931,  934,  926,  933,  932,  925, 1440,
 /*  2970 */   420, 1440, 1440, 1440, 1440,  920,  930,  931,  934,  926,
 /*  2980 */   933,  932,  925, 1440,  419,  920,  930,  931,  934,  926,
 /*  2990 */   933,  932,  925, 1440,  418, 1440, 1440, 1440, 1440, 1440,
 /*  3000 */  1440,  920,  930,  931,  934,  926,  933,  932,  925, 1440,
 /*  3010 */   417, 1440,  920,  930,  931,  934,  926,  933,  932,  925,
 /*  3020 */  1440,  416,  920,  930,  931,  934,  926,  933,  932,  925,
 /*  3030 */  1440,  415,  920,  930,  931,  934,  926,  933,  932,  925,
 /*  3040 */  1440,  414,  920,  930,  931,  934,  926,  933,  932,  925,
 /*  3050 */  1440,  412,  920,  930,  931,  934,  926,  933,  932,  925,
 /*  3060 */  1440,  411,  920,  930,  931,  934,  926,  933,  932,  925,
 /*  3070 */  1440,  410,  920,  930,  931,  934,  926,  933,  932,  925,
 /*  3080 */  1440,  409,  920,  930,  931,  934,  926,  933,  932,  925,
 /*  3090 */  1440,  408,  920,  930,  931,  934,  926,  933,  932,  925,
 /*  3100 */  1440,  244,  920,  930,  931,  934,  926,  933,  932,  925,
 /*  3110 */  1440,  243,  920,  930,  931,  934,  926,  933,  932,  925,
 /*  3120 */  1440,  398,  920,  930,  931,  934,  926,  933,  932,  925,
 /*  3130 */  1440,  360,  893,  883,  934,  926,  933,  932,  925, 1440,
 /*  3140 */  1440, 1440, 1440,  878,  769, 1440,  381,  893,  883,  934,
 /*  3150 */   926,  933,  932,  925, 1440, 1440, 1440, 1440,  881,  893,
 /*  3160 */   883,  934,  926,  933,  932,  925, 1440, 1440, 1440, 1440,
 /*  3170 */   880, 1440, 1440,  893,  883,  934,  926,  933,  932,  925,
 /*  3180 */   494,  497,  770,  771,  879,  893,  883,  934,  926,  933,
 /*  3190 */   932,  925, 1440, 1440, 1440, 1440,  434,  893,  883,  934,
 /*  3200 */   926,  933,  932,  925, 1440, 1440, 1440, 1440,  463,  893,
 /*  3210 */   883,  934,  926,  933,  932,  925, 1440, 1440, 1440, 1440,
 /*  3220 */   462,  893,  883,  934,  926,  933,  932,  925, 1440, 1440,
 /*  3230 */  1440, 1440,  823,  893,  883,  934,  926,  933,  932,  925,
 /*  3240 */  1440, 1440, 1440, 1440,  822,  893,  883,  934,  926,  933,
 /*  3250 */   932,  925, 1440, 1440, 1440, 1440,  821,  893,  883,  934,
 /*  3260 */   926,  933,  932,  925, 1440, 1440, 1440, 1440,  407,  893,
 /*  3270 */   883,  934,  926,  933,  932,  925, 1440, 1440, 1440, 1440,
 /*  3280 */   406,  893,  883,  934,  926,  933,  932,  925, 1440, 1440,
 /*  3290 */  1440, 1440,  405,  893,  883,  934,  926,  933,  932,  925,
 /*  3300 */  1440, 1440, 1440, 1440,  404,  893,  883,  934,  926,  933,
 /*  3310 */   932,  925, 1440, 1440, 1440, 1440,  403, 1440, 1440,  893,
 /*  3320 */   883,  934,  926,  933,  932,  925, 1440, 1440,   17, 1440,
 /*  3330 */   402,  893,  883,  934,  926,  933,  932,  925, 1440, 1440,
 /*  3340 */  1440, 1440,  401, 1440, 1440,  893,  883,  934,  926,  933,
 /*  3350 */   932,  925, 1440, 1440, 1440, 1440,  815,  701,  691,  934,
 /*  3360 */   926,  933,  932,  925, 1440, 1440, 1440, 1440,  701,  691,
 /*  3370 */   934,  926,  933,  932,  925,  701,  691,  934,  926,  933,
 /*  3380 */   932,  925,  701,  691,  934,  926,  933,  932,  925, 1440,
 /*  3390 */  1440, 1440,  690,  701,  691,  934,  926,  933,  932,  925,
 /*  3400 */  1440, 1440, 1440,  452,   24,   23,   22,   26,   25, 1440,
 /*  3410 */   689,   27, 1440, 1440, 1440,  866, 1440,  688,  701,  691,
 /*  3420 */   934,  926,  933,  932,  925, 1440, 1440, 1440,  687,  701,
 /*  3430 */   691,  934,  926,  933,  932,  925, 1440, 1440, 1440, 1440,
 /*  3440 */   701,  691,  934,  926,  933,  932,  925, 1440,  128,  126,
 /*  3450 */   124,  122,  120,  686,  701,  691,  934,  926,  933,  932,
 /*  3460 */   925,  666, 1440, 1440,  449,  701,  691,  934,  926,  933,
 /*  3470 */   932,  925, 1440, 1440, 1440,  685,  701,  691,  934,  926,
 /*  3480 */   933,  932,  925,   43,   42,   41,   45,   44,  788,  684,
 /*  3490 */    46,  701,  691,  934,  926,  933,  932,  925, 1440, 1440,
 /*  3500 */   683, 1440,  701,  691,  934,  926,  933,  932,  925, 1440,
 /*  3510 */  1440,  374, 1440, 1440,  701,  691,  934,  926,  933,  932,
 /*  3520 */   925,  234,  232,  230,  229,  228,  373, 1440,  701,  691,
 /*  3530 */   934,  926,  933,  932,  925, 1440, 1440,  372, 1440, 1440,
 /*  3540 */   701,  691,  934,  926,  933,  932,  925, 1440, 1440,  371,
 /*  3550 */   701,  691,  934,  926,  933,  932,  925, 1440, 1440, 1440,
 /*  3560 */  1440, 1440, 1440,  370,  701,  691,  934,  926,  933,  932,
 /*  3570 */   925, 1440, 1440, 1440, 1440,  369,   43,   42,   41,   45,
 /*  3580 */    44, 1440, 1440,   46, 1440,  368, 1440, 1440, 1440,  701,
 /*  3590 */   691,  934,  926,  933,  932,  925,  629, 1440, 1440,  678,
 /*  3600 */   701,  691,  934,  926,  933,  932,  925,  701,  691,  934,
 /*  3610 */   926,  933,  932,  925,  701,  691,  934,  926,  933,  932,
 /*  3620 */   925, 1440, 1440, 1440,  367, 1440,  135,   59,  257,  255,
 /*  3630 */   253,  252,  251, 1440,  716,  366, 1440, 1440, 1440, 1440,
 /*  3640 */   620, 1440,  365, 1440, 1440, 1440, 1440, 1440, 1440,  364,
 /*  3650 */    43,   42,   41,   45,   44, 1440, 1440,   46, 1440,   24,
 /*  3660 */    23,   22,   26,   25, 1440, 1440,   27,  257,  255,  253,
 /*  3670 */   252,  251,  257,  255,  253,  252,  251,
};
static const YYCODETYPE yy_lookahead[] = {
 /*     0 */   150,  110,  111,  153,  154,  155,  156,  157,  158,  159,
 /*    10 */   160,  161,  162,  163,  164,  165,  166,  167,  168,  169,
 /*    20 */    83,  171,  172,  173,  174,  175,  176,  177,  116,  117,
 /*    30 */   118,  119,  120,   83,  184,  185,  171,  172,  173,  174,
 /*    40 */   175,  176,  177,  193,  194,  118,  119,  120,   83,  184,
 /*    50 */   185,  187,   78,  189,  117,    0,  191,  192,  193,  194,
 /*    60 */   195,  196,  187,  113,  189,  215,  216,  217,   83,  204,
 /*    70 */   205,  171,  172,  173,  174,  175,  176,  177,  113,  105,
 /*    80 */   106,  107,  108,  109,  184,  185,  112,  223,  224,  225,
 /*    90 */   226,  191,  192,  193,  194,  195,  196,  222,  223,  224,
 /*   100 */   225,  226,  117,  253,  254,  255,  256,  257,  258,  259,
 /*   110 */   260,  261,  262,  263,  264,  265,  266,  267,  268,  269,
 /*   120 */   270,  271,    1,    2,    3,  218,  219,    6,    7,    8,
 /*   130 */     9,   10,   11,   12,   13,   14,   15,  170,  171,  172,
 /*   140 */   173,  174,  175,  176,  177,  178,  179,  116,  117,  118,
 /*   150 */   119,  120,   31,   32,  118,  119,  120,   36,  175,   38,
 /*   160 */    39,  109,   41,  180,   43,  113,   81,   46,   82,   49,
 /*   170 */    49,  108,  109,   52,   82,  112,   83,   56,   57,   58,
 /*   180 */    59,   60,   61,   62,  201,   64,   82,  204,  205,   68,
 /*   190 */   105,  106,  107,  108,  109,   74,   75,  112,   82,  107,
 /*   200 */    79,   80,  187,   82,  189,  112,   86,   86,   47,   80,
 /*   210 */    82,   90,   83,  171,  172,  173,  174,  175,  176,  177,
 /*   220 */    91,   92,   93,   94,  182,   96,   97,   98,   99,  171,
 /*   230 */   172,  173,  174,  175,  176,  177,  116,  116,  223,  224,
 /*   240 */   225,  226,  121,   87,  186,  116,  117,  118,  119,  120,
 /*   250 */   129,   90,    1,  187,    3,  189,  198,  199,  200,  118,
 /*   260 */   119,  120,  142,  142,  143,  144,  145,  146,  147,  113,
 /*   270 */   149,  108,  109,  112,   82,  112,   25,   26,   27,   28,
 /*   280 */   118,    1,    2,    3,  122,   34,    6,    7,  222,  223,
 /*   290 */   224,  225,  226,   42,  100,   44,  171,  172,  173,  174,
 /*   300 */   175,  176,  177,   84,   53,    4,    5,   56,   57,   58,
 /*   310 */   116,  117,  118,  119,  120,   47,   65,   66,   67,   68,
 /*   320 */    69,   70,   71,  104,   91,   74,   75,  101,  102,   49,
 /*   330 */    87,  206,  187,   82,  189,  109,   56,   57,   58,  118,
 /*   340 */   119,  120,  171,  172,  173,  174,  175,  176,  177,  116,
 /*   350 */   117,  118,  119,  120,   74,   75,  113,   77,  180,   83,
 /*   360 */    80,    1,   82,    3,   83,  194,   86,  116,  223,  224,
 /*   370 */   225,  226,  121,   84,   80,  230,  231,   83,  207,  201,
 /*   380 */   112,  210,  211,  212,  213,  214,   92,   93,   94,  113,
 /*   390 */    96,   97,   98,   99,  113,  115,  116,    1,    2,    3,
 /*   400 */   109,  121,    6,    7,  113,  116,  117,  118,  119,  120,
 /*   410 */   116,  117,  118,  119,  120,  244,  245,  246,  187,   82,
 /*   420 */   189,  243,  142,  143,  144,  145,  146,  147,  171,  172,
 /*   430 */   173,  174,  175,  176,  177,  171,  172,  173,  174,  175,
 /*   440 */   176,  177,   92,  108,  109,   49,   83,  112,  184,  185,
 /*   450 */   172,   82,   56,   57,   58,  191,  192,  193,  194,  195,
 /*   460 */   196,  183,   83,  206,  233,  234,  235,   80,  204,  205,
 /*   470 */    74,   75,  194,  110,  111,  197,   80,   82,   82,   92,
 /*   480 */    93,   94,   86,   96,   97,   98,   99,   87,  171,  172,
 /*   490 */   173,  174,  175,  176,  177,  116,  117,  118,  119,  120,
 /*   500 */    83,   81,  180,  116,  117,  118,  119,  120,   91,  237,
 /*   510 */   238,  194,  116,  113,    1,    2,    3,  121,   81,    6,
 /*   520 */     7,  204,  205,  201,  207,   82,   84,  210,  211,  212,
 /*   530 */   213,  214,    3,  116,  117,  118,  119,  120,  142,  143,
 /*   540 */   144,  145,  146,  147,   29,   17,  104,   19,   20,   21,
 /*   550 */    22,   23,   24,  171,  172,  173,  174,  175,  176,  177,
 /*   560 */   228,  229,   49,   84,  242,  243,   84,   54,  186,   56,
 /*   570 */    57,   58,   87,  171,  172,  173,  174,  175,  176,  177,
 /*   580 */   198,  199,  200,  104,   56,   57,  104,   74,   75,  180,
 /*   590 */    77,   76,  113,   80,   82,   82,  194,   81,  113,   86,
 /*   600 */    82,  105,  106,  107,  108,  109,  204,  205,  112,  207,
 /*   610 */   201,   82,  210,  211,  212,  213,  214,  118,  119,  120,
 /*   620 */   105,  106,  107,  108,  109,  101,  102,  112,  115,  116,
 /*   630 */     1,    2,    3,  109,  121,    6,    7,  188,  180,  190,
 /*   640 */   171,  172,  173,  174,  175,  176,  177,   84,  116,  117,
 /*   650 */   118,  119,  120,  184,  185,  142,  143,  144,   83,  201,
 /*   660 */   191,  192,  193,  194,  195,  196,  171,  172,  173,  174,
 /*   670 */   175,  176,  177,  227,  228,  229,  148,   81,   49,  116,
 /*   680 */   117,  118,  119,  120,   49,   56,   57,   58,  113,  194,
 /*   690 */   170,  171,  172,  173,  174,  175,  176,  177,  178,  179,
 /*   700 */   242,  243,  207,   74,   75,  210,  211,  212,  213,  214,
 /*   710 */   112,   82,   83,    1,    2,    3,   82,   80,    6,    7,
 /*   720 */    83,  171,  172,  173,  174,  175,  176,  177,   92,   92,
 /*   730 */    93,   94,  182,   96,   97,   98,   99,   30,   84,   86,
 /*   740 */   245,  246,  236,  237,  238,  116,  100,  239,  240,  241,
 /*   750 */   121,   47,   92,  116,  117,  118,  119,  120,  104,  202,
 /*   760 */   203,   49,  116,  117,  118,  119,  120,  113,   56,   57,
 /*   770 */    58,  142,  143,  144,  145,  146,  147,  142,   83,  171,
 /*   780 */   172,  173,  174,  175,  176,  177,   74,   75,   83,   77,
 /*   790 */   182,  112,   80,   86,   82,  142,  143,  187,   86,  189,
 /*   800 */    84,  171,  172,  173,  174,  175,  176,  177,  113,  105,
 /*   810 */   106,  107,  108,  109,  184,  185,  112,   83,  113,   84,
 /*   820 */   104,  191,  192,  193,  194,  195,  196,  115,  116,    1,
 /*   830 */     2,    3,  180,  121,    6,    7,   84,  171,  172,  173,
 /*   840 */   174,  175,  176,  177,  187,  235,  189,  113,   83,  142,
 /*   850 */   184,  185,   80,  201,  142,  143,  144,  191,  192,  193,
 /*   860 */   194,  195,  196,   91,   92,   93,   94,   84,   96,   97,
 /*   870 */    98,   99,  116,  117,  118,  119,  120,   49,  113,  222,
 /*   880 */   223,  224,  225,  226,   56,   57,   58,  172,  116,  117,
 /*   890 */   118,  119,  120,  171,  172,  173,  174,  175,  176,  177,
 /*   900 */    84,   35,   74,   75,  182,  106,  107,  108,  109,  194,
 /*   910 */    82,  112,    1,    2,    3,   83,   35,    6,    7,   84,
 /*   920 */   104,  170,  171,  172,  173,  174,  175,  176,  177,  178,
 /*   930 */   179,  216,   84,  171,  172,  173,  174,  175,  176,  177,
 /*   940 */   101,  102,   84,   87,  116,  113,  184,  185,   92,  121,
 /*   950 */   220,  221,  104,  191,  192,  193,  194,  195,  196,   84,
 /*   960 */    49,  116,  117,  118,  119,  120,   80,   56,   57,   58,
 /*   970 */   142,  143,  144,  145,  146,  147,   47,   86,   92,   93,
 /*   980 */    94,   87,   96,   97,   98,   99,   92,  105,  106,  107,
 /*   990 */   108,  109,  107,   82,  112,    1,    2,    3,  240,  241,
 /*  1000 */     6,    7,  116,  117,  118,  119,  120,  171,  172,  173,
 /*  1010 */   174,  175,  176,  177,   83,  171,  172,  173,  174,  175,
 /*  1020 */   176,  177,  116,  117,  118,  119,  120,  116,  184,  185,
 /*  1030 */   240,  241,  121,  142,   85,  191,  192,  193,  194,  195,
 /*  1040 */   196,   85,  206,   49,  113,  116,  117,  118,  119,  120,
 /*  1050 */    56,   57,   58,  142,  143,  144,  145,  146,  147,  117,
 /*  1060 */   171,  172,  173,  174,  175,  176,  177,   82,   74,   75,
 /*  1070 */   181,  182,   84,  240,  241,   83,   82,  172,    1,    2,
 /*  1080 */     3,  240,  241,    6,    7,  202,  203,   83,  183,  171,
 /*  1090 */   172,  173,  174,  175,  176,  177,   92,   93,   94,   77,
 /*  1100 */    96,   97,   98,   99,  116,  117,  118,  119,  120,  115,
 /*  1110 */   116,  187,  194,  189,    1,  121,    3,  187,   78,  189,
 /*  1120 */   116,  117,  118,  119,  120,  207,   49,  180,  210,  211,
 /*  1130 */   212,  213,  214,   56,   57,   58,  142,  143,  144,   77,
 /*  1140 */    84,  171,  172,  173,  174,  175,  176,  177,  201,  151,
 /*  1150 */   152,   74,   75,  223,  224,  225,  226,   83,   78,   82,
 /*  1160 */   104,    1,    2,    3,  194,   78,    6,    7,  171,  172,
 /*  1170 */   173,  174,  175,  176,  177,   82,   77,  207,   83,  182,
 /*  1180 */   210,  211,  212,  213,  214,  105,  106,  107,  108,  109,
 /*  1190 */   243,   83,  112,  116,  187,  187,  189,  189,  121,  170,
 /*  1200 */   171,  172,  173,  174,  175,  176,  177,  178,  179,   49,
 /*  1210 */    78,  116,  117,  118,  119,  120,   56,   57,   58,  142,
 /*  1220 */   143,  144,   77,  171,  172,  173,  174,  175,  176,  177,
 /*  1230 */   187,   78,  189,    3,   74,   75,  184,  185,  187,   63,
 /*  1240 */   189,    3,   82,  191,  192,  193,  194,  195,  196,   77,
 /*  1250 */   171,  172,  173,  174,  175,  176,  177,  144,  187,    3,
 /*  1260 */   189,   83,   82,  184,  185,  222,  223,  224,  225,  226,
 /*  1270 */   191,  192,  193,  194,  195,  196,  116,   82,  187,   49,
 /*  1280 */   189,  121,   78,  232,  233,  234,  235,  171,  172,  173,
 /*  1290 */   174,  175,  176,  177,  116,  117,  118,  119,  120,   84,
 /*  1300 */   184,  185,  142,  143,  144,   49,   83,  191,  192,  193,
 /*  1310 */   194,  195,  196,   77,   83,  171,  172,  173,  174,  175,
 /*  1320 */   176,  177,   78,  171,  172,  173,  174,  175,  176,  177,
 /*  1330 */    82,  116,  117,  118,  119,  120,  184,  185,  194,  172,
 /*  1340 */     3,   82,   86,  191,  192,  193,  194,  195,  196,   82,
 /*  1350 */   187,  207,  189,    3,  210,  211,  212,  213,  214,   37,
 /*  1360 */   113,  194,   40,    3,   84,  171,  172,  173,  174,  175,
 /*  1370 */   176,  177,  142,   51,  187,   81,  189,   55,  184,  185,
 /*  1380 */    84,  112,   87,  216,   87,  191,  192,  193,  194,  195,
 /*  1390 */   196,  171,  172,  173,  174,  175,  176,  177,  142,  105,
 /*  1400 */   106,  107,  108,  109,  184,  185,  112,   84,   84,   48,
 /*  1410 */    63,  191,  192,  193,  194,  195,  196,  171,  172,  173,
 /*  1420 */   174,  175,  176,  177,   30,   49,   92,   81,    1,   84,
 /*  1430 */   184,  185,    1,    2,    3,   49,   92,  191,  192,  193,
 /*  1440 */   194,  195,  196,  171,  172,  173,  174,  175,  176,  177,
 /*  1450 */     1,  105,  106,  107,  108,  109,  184,  185,  112,   84,
 /*  1460 */    76,   84,   84,  191,  192,  193,  194,  195,  196,   84,
 /*  1470 */   180,   84,  171,  172,  173,  174,  175,  176,  177,   84,
 /*  1480 */    86,   84,   84,   84,   84,  184,  185,   56,   57,   58,
 /*  1490 */    84,   84,  191,  192,  193,  194,  195,  196,  171,  172,
 /*  1500 */   173,  174,  175,  176,  177,   74,   75,   84,  175,  142,
 /*  1510 */   175,  184,  185,   82,  143,  175,  250,   50,  191,  192,
 /*  1520 */   193,  194,  195,  196,  249,  170,  171,  172,  173,  174,
 /*  1530 */   175,  176,  177,  178,  179,  251,  142,  171,  172,  173,
 /*  1540 */   174,  175,  176,  177,   29,  252,   72,  116,   73,   83,
 /*  1550 */   184,  185,  121,   47,  251,  219,  252,  191,  192,  193,
 /*  1560 */   194,  195,  196,  171,  172,  173,  174,  175,  176,  177,
 /*  1570 */   251,  105,  106,  107,  108,  109,  184,  185,  112,    3,
 /*  1580 */   252,  251,  251,  191,  192,  193,  194,  195,  196,  171,
 /*  1590 */   172,  173,  174,  175,  176,  177,  226,   83,    3,  248,
 /*  1600 */   252,  252,  184,  185,    1,  249,    3,  250,  250,  191,
 /*  1610 */   192,  193,  194,  195,  196,  171,  172,  173,  174,  175,
 /*  1620 */   176,  177,  116,  117,  118,  119,  120,   47,  184,  185,
 /*  1630 */   116,  117,  118,  119,  120,  191,  192,  193,  194,  195,
 /*  1640 */   196,  251,  249,  252,  171,  172,  173,  174,  175,  176,
 /*  1650 */   177,  172,  251,  250,  252,  251,  251,  184,  185,   56,
 /*  1660 */    57,   58,  252,  252,  191,  192,  193,  194,  195,  196,
 /*  1670 */   171,  172,  173,  174,  175,  176,  177,   74,   75,  251,
 /*  1680 */   248,  252,  252,  184,  185,   82,  251,  249,  251,  250,
 /*  1690 */   191,  192,  193,  194,  195,  196,  170,  171,  172,  173,
 /*  1700 */   174,  175,  176,  177,  252,  179,  249,  251,  248,  171,
 /*  1710 */   172,  173,  174,  175,  176,  177,  252,  252,  250,  116,
 /*  1720 */   249,   83,  184,  185,  121,  172,  248,  251,  251,  191,
 /*  1730 */   192,  193,  194,  195,  196,  171,  172,  173,  174,  175,
 /*  1740 */   176,  177,  252,  105,  106,  107,  108,  109,  184,  185,
 /*  1750 */   112,  172,  252,  248,  221,  191,  192,  193,  194,  195,
 /*  1760 */   196,  171,  172,  173,  174,  175,  176,  177,  106,  107,
 /*  1770 */   108,  109,  172,  248,  112,  171,  172,  173,  174,  175,
 /*  1780 */   176,  177,  248,  172,  194,  171,  172,  173,  174,  175,
 /*  1790 */   176,  177,  172,  172,  172,  248,  203,  207,  194,  174,
 /*  1800 */   210,  211,  212,  213,  214,  190,  190,  190,  194,  190,
 /*  1810 */     1,  207,    1,  190,  210,  211,  212,  213,  214,  190,
 /*  1820 */   190,  207,  190,  190,  210,  211,  212,  213,  214,  171,
 /*  1830 */   172,  173,  174,  175,  176,  177,  190,  171,  172,  173,
 /*  1840 */   174,  175,  176,  177,  171,  172,  173,  174,  175,  176,
 /*  1850 */   177,  190,  194,  106,  107,  108,  109,  184,  185,  112,
 /*  1860 */   194,  190,  190,    3,  190,  207,  193,  194,  210,  211,
 /*  1870 */   212,  213,  214,  207,  190,  248,  210,  211,  212,  213,
 /*  1880 */   214,  171,  172,  173,  174,  175,  176,  177,  215,  216,
 /*  1890 */   217,   82,  248,   82,  252,  171,  172,  173,  174,  175,
 /*  1900 */   176,  177,  252,  249,  194,  171,  172,  173,  174,  175,
 /*  1910 */   176,  177,  249,  249,  249,   47,  248,  207,  194,  189,
 /*  1920 */   210,  211,  212,  213,  214,  116,  189,  116,  194,  189,
 /*  1930 */   121,  207,  121,  189,  210,  211,  212,  213,  214,  189,
 /*  1940 */    81,  207,  189,  189,  210,  211,  212,  213,  214,  171,
 /*  1950 */   172,  173,  174,  175,  176,  177,  171,  172,  173,  174,
 /*  1960 */   175,  176,  177,  189,  105,  106,  107,  108,  109,  184,
 /*  1970 */   185,  112,  194,  105,  106,  107,  108,  109,  193,  194,
 /*  1980 */   112,  189,    3,  272,  272,  207,   81,  272,  210,  211,
 /*  1990 */   212,  213,  214,  171,  172,  173,  174,  175,  176,  177,
 /*  2000 */   215,  216,  217,  272,  175,  272,  184,  185,  272,  180,
 /*  2010 */   105,  106,  107,  108,  109,  193,  194,  112,  171,  172,
 /*  2020 */   173,  174,  175,  176,  177,  272,  272,   81,  272,  272,
 /*  2030 */   201,  184,  185,  204,  205,  272,  272,  215,  216,  217,
 /*  2040 */   193,  194,   83,  171,  172,  173,  174,  175,  176,  177,
 /*  2050 */   272,  105,  106,  107,  108,  109,  184,  185,  112,  272,
 /*  2060 */   272,  272,  215,  216,  217,  193,  194,  272,  171,  172,
 /*  2070 */   173,  174,  175,  176,  177,  116,  117,  118,  119,  120,
 /*  2080 */   272,  184,  185,  272,  272,  272,  272,  215,  216,  217,
 /*  2090 */   193,  194,   92,   93,   94,  272,   96,   97,   98,   99,
 /*  2100 */    92,   93,   94,  272,   96,   97,   98,   99,  272,  272,
 /*  2110 */   272,  272,  215,  216,  217,  272,  116,  117,  118,  119,
 /*  2120 */   120,  272,  272,  272,  116,  117,  118,  119,  120,  272,
 /*  2130 */    92,   93,   94,  272,   96,   97,   98,   99,   92,   93,
 /*  2140 */    94,  272,   96,   97,   98,   99,    1,  272,    3,  272,
 /*  2150 */     1,  272,    3,  272,  116,  117,  118,  119,  120,  272,
 /*  2160 */   272,  272,  116,  117,  118,  119,  120,   92,   93,   94,
 /*  2170 */   272,   96,   97,   98,   99,  272,  272,  170,  171,  172,
 /*  2180 */   173,  174,  175,  176,  177,  272,  179,  272,  272,  272,
 /*  2190 */   272,  116,  117,  118,  119,  120,  272,  272,  272,  272,
 /*  2200 */   272,   56,   57,   58,  272,   56,   57,   58,  272,  272,
 /*  2210 */    65,   66,  272,  272,   65,   66,  272,  272,  272,   74,
 /*  2220 */    75,  272,  272,   74,   75,  272,  272,   82,  272,  272,
 /*  2230 */   272,   82,  272,  272,  272,  171,  172,  173,  174,  175,
 /*  2240 */   176,  177,  170,  171,  172,  173,  174,  175,  176,  177,
 /*  2250 */   186,  179,  272,  171,  172,  173,  174,  175,  176,  177,
 /*  2260 */   272,  116,  198,  199,  200,  116,  121,  272,  186,  272,
 /*  2270 */   121,  171,  172,  173,  174,  175,  176,  177,  272,  272,
 /*  2280 */   198,  199,  200,  272,  272,  272,  186,  272,  171,  172,
 /*  2290 */   173,  174,  175,  176,  177,  272,  272,  272,  198,  199,
 /*  2300 */   200,  272,  272,  186,  171,  172,  173,  174,  175,  176,
 /*  2310 */   177,  272,  272,  272,  272,  198,  199,  200,  272,  186,
 /*  2320 */   272,  272,  171,  172,  173,  174,  175,  176,  177,  272,
 /*  2330 */   272,  198,  199,  200,  272,   83,  272,  186,  171,  172,
 /*  2340 */   173,  174,  175,  176,  177,  272,  272,  272,  272,  198,
 /*  2350 */   199,  200,    1,  186,  170,  171,  172,  173,  174,  175,
 /*  2360 */   176,  177,   29,  179,  272,  198,  199,  200,  116,  117,
 /*  2370 */   118,  119,  120,  171,  172,  173,  174,  175,  176,  177,
 /*  2380 */    47,  272,  272,   50,  272,  272,  272,   81,  186,  272,
 /*  2390 */   170,  171,  172,  173,  174,  175,  176,  177,  272,  179,
 /*  2400 */   198,  199,  200,  272,  272,   72,   73,   56,   57,   58,
 /*  2410 */   272,  105,  106,  107,  108,  109,   83,   84,  112,  272,
 /*  2420 */   272,  272,  272,   90,   83,   74,   75,  272,  272,  272,
 /*  2430 */   272,  272,  272,   82,  171,  172,  173,  174,  175,  176,
 /*  2440 */   177,  272,  272,  272,  272,  112,  272,  184,  185,  171,
 /*  2450 */   172,  173,  174,  175,  176,  177,  272,  116,  117,  118,
 /*  2460 */   119,  120,  184,  185,  272,  272,  272,  116,  272,  272,
 /*  2470 */   272,  272,  121,  272,  272,  171,  172,  173,  174,  175,
 /*  2480 */   176,  177,  272,  272,  272,  272,  272,  272,  184,  185,
 /*  2490 */   170,  171,  172,  173,  174,  175,  176,  177,  272,  179,
 /*  2500 */   272,  272,  170,  171,  172,  173,  174,  175,  176,  177,
 /*  2510 */   272,  179,  170,  171,  172,  173,  174,  175,  176,  177,
 /*  2520 */   272,  179,  170,  171,  172,  173,  174,  175,  176,  177,
 /*  2530 */   272,  179,  170,  171,  172,  173,  174,  175,  176,  177,
 /*  2540 */   272,  179,  272,  272,  170,  171,  172,  173,  174,  175,
 /*  2550 */   176,  177,  272,  179,  170,  171,  172,  173,  174,  175,
 /*  2560 */   176,  177,  272,  179,  170,  171,  172,  173,  174,  175,
 /*  2570 */   176,  177,  272,  179,  272,  272,  170,  171,  172,  173,
 /*  2580 */   174,  175,  176,  177,  272,  179,  272,  170,  171,  172,
 /*  2590 */   173,  174,  175,  176,  177,   83,  179,  170,  171,  172,
 /*  2600 */   173,  174,  175,  176,  177,  272,  179,  170,  171,  172,
 /*  2610 */   173,  174,  175,  176,  177,  272,  179,  272,  170,  171,
 /*  2620 */   172,  173,  174,  175,  176,  177,  272,  179,  116,  117,
 /*  2630 */   118,  119,  120,  170,  171,  172,  173,  174,  175,  176,
 /*  2640 */   177,  272,  179,  170,  171,  172,  173,  174,  175,  176,
 /*  2650 */   177,  272,  179,  272,  272,  272,  272,  272,  272,  170,
 /*  2660 */   171,  172,  173,  174,  175,  176,  177,  272,  179,  272,
 /*  2670 */   170,  171,  172,  173,  174,  175,  176,  177,  272,  179,
 /*  2680 */   170,  171,  172,  173,  174,  175,  176,  177,  272,  179,
 /*  2690 */   170,  171,  172,  173,  174,  175,  176,  177,  272,  179,
 /*  2700 */   170,  171,  172,  173,  174,  175,  176,  177,  272,  179,
 /*  2710 */   170,  171,  172,  173,  174,  175,  176,  177,  272,  179,
 /*  2720 */   170,  171,  172,  173,  174,  175,  176,  177,  272,  179,
 /*  2730 */   170,  171,  172,  173,  174,  175,  176,  177,  272,  179,
 /*  2740 */   170,  171,  172,  173,  174,  175,  176,  177,  272,  179,
 /*  2750 */   170,  171,  172,  173,  174,  175,  176,  177,  272,  179,
 /*  2760 */   170,  171,  172,  173,  174,  175,  176,  177,  272,  179,
 /*  2770 */   170,  171,  172,  173,  174,  175,  176,  177,  272,  179,
 /*  2780 */   170,  171,  172,  173,  174,  175,  176,  177,  272,  179,
 /*  2790 */   170,  171,  172,  173,  174,  175,  176,  177,  272,  179,
 /*  2800 */   272,  272,  272,  272,  170,  171,  172,  173,  174,  175,
 /*  2810 */   176,  177,  272,  179,  170,  171,  172,  173,  174,  175,
 /*  2820 */   176,  177,  272,  179,  272,  272,  272,  272,  272,  272,
 /*  2830 */   170,  171,  172,  173,  174,  175,  176,  177,  272,  179,
 /*  2840 */   272,  170,  171,  172,  173,  174,  175,  176,  177,  272,
 /*  2850 */   179,  170,  171,  172,  173,  174,  175,  176,  177,  272,
 /*  2860 */   179,  170,  171,  172,  173,  174,  175,  176,  177,  272,
 /*  2870 */   179,  170,  171,  172,  173,  174,  175,  176,  177,  272,
 /*  2880 */   179,  170,  171,  172,  173,  174,  175,  176,  177,  272,
 /*  2890 */   179,  170,  171,  172,  173,  174,  175,  176,  177,  272,
 /*  2900 */   179,  170,  171,  172,  173,  174,  175,  176,  177,  272,
 /*  2910 */   179,  170,  171,  172,  173,  174,  175,  176,  177,  272,
 /*  2920 */   179,  170,  171,  172,  173,  174,  175,  176,  177,  272,
 /*  2930 */   179,  170,  171,  172,  173,  174,  175,  176,  177,  272,
 /*  2940 */   179,  170,  171,  172,  173,  174,  175,  176,  177,  272,
 /*  2950 */   179,  170,  171,  172,  173,  174,  175,  176,  177,  272,
 /*  2960 */   179,  170,  171,  172,  173,  174,  175,  176,  177,  272,
 /*  2970 */   179,  272,  272,  272,  272,  170,  171,  172,  173,  174,
 /*  2980 */   175,  176,  177,  272,  179,  170,  171,  172,  173,  174,
 /*  2990 */   175,  176,  177,  272,  179,  272,  272,  272,  272,  272,
 /*  3000 */   272,  170,  171,  172,  173,  174,  175,  176,  177,  272,
 /*  3010 */   179,  272,  170,  171,  172,  173,  174,  175,  176,  177,
 /*  3020 */   272,  179,  170,  171,  172,  173,  174,  175,  176,  177,
 /*  3030 */   272,  179,  170,  171,  172,  173,  174,  175,  176,  177,
 /*  3040 */   272,  179,  170,  171,  172,  173,  174,  175,  176,  177,
 /*  3050 */   272,  179,  170,  171,  172,  173,  174,  175,  176,  177,
 /*  3060 */   272,  179,  170,  171,  172,  173,  174,  175,  176,  177,
 /*  3070 */   272,  179,  170,  171,  172,  173,  174,  175,  176,  177,
 /*  3080 */   272,  179,  170,  171,  172,  173,  174,  175,  176,  177,
 /*  3090 */   272,  179,  170,  171,  172,  173,  174,  175,  176,  177,
 /*  3100 */   272,  179,  170,  171,  172,  173,  174,  175,  176,  177,
 /*  3110 */   272,  179,  170,  171,  172,  173,  174,  175,  176,  177,
 /*  3120 */   272,  179,  170,  171,  172,  173,  174,  175,  176,  177,
 /*  3130 */   272,  179,  171,  172,  173,  174,  175,  176,  177,  272,
 /*  3140 */   272,  272,  272,  182,  187,  272,  189,  171,  172,  173,
 /*  3150 */   174,  175,  176,  177,  272,  272,  272,  272,  182,  171,
 /*  3160 */   172,  173,  174,  175,  176,  177,  272,  272,  272,  272,
 /*  3170 */   182,  272,  272,  171,  172,  173,  174,  175,  176,  177,
 /*  3180 */   223,  224,  225,  226,  182,  171,  172,  173,  174,  175,
 /*  3190 */   176,  177,  272,  272,  272,  272,  182,  171,  172,  173,
 /*  3200 */   174,  175,  176,  177,  272,  272,  272,  272,  182,  171,
 /*  3210 */   172,  173,  174,  175,  176,  177,  272,  272,  272,  272,
 /*  3220 */   182,  171,  172,  173,  174,  175,  176,  177,  272,  272,
 /*  3230 */   272,  272,  182,  171,  172,  173,  174,  175,  176,  177,
 /*  3240 */   272,  272,  272,  272,  182,  171,  172,  173,  174,  175,
 /*  3250 */   176,  177,  272,  272,  272,  272,  182,  171,  172,  173,
 /*  3260 */   174,  175,  176,  177,  272,  272,  272,  272,  182,  171,
 /*  3270 */   172,  173,  174,  175,  176,  177,  272,  272,  272,  272,
 /*  3280 */   182,  171,  172,  173,  174,  175,  176,  177,  272,  272,
 /*  3290 */   272,  272,  182,  171,  172,  173,  174,  175,  176,  177,
 /*  3300 */   272,  272,  272,  272,  182,  171,  172,  173,  174,  175,
 /*  3310 */   176,  177,  272,  272,  272,  272,  182,  272,  272,  171,
 /*  3320 */   172,  173,  174,  175,  176,  177,  272,  272,   29,  272,
 /*  3330 */   182,  171,  172,  173,  174,  175,  176,  177,  272,  272,
 /*  3340 */   272,  272,  182,  272,  272,  171,  172,  173,  174,  175,
 /*  3350 */   176,  177,  272,  272,  272,  272,  182,  171,  172,  173,
 /*  3360 */   174,  175,  176,  177,  272,  272,  272,  272,  171,  172,
 /*  3370 */   173,  174,  175,  176,  177,  171,  172,  173,  174,  175,
 /*  3380 */   176,  177,  171,  172,  173,  174,  175,  176,  177,  272,
 /*  3390 */   272,  272,  206,  171,  172,  173,  174,  175,  176,  177,
 /*  3400 */   272,  272,  272,  206,  105,  106,  107,  108,  109,  272,
 /*  3410 */   206,  112,  272,  272,  272,   83,  272,  206,  171,  172,
 /*  3420 */   173,  174,  175,  176,  177,  272,  272,  272,  206,  171,
 /*  3430 */   172,  173,  174,  175,  176,  177,  272,  272,  272,  272,
 /*  3440 */   171,  172,  173,  174,  175,  176,  177,  272,  116,  117,
 /*  3450 */   118,  119,  120,  206,  171,  172,  173,  174,  175,  176,
 /*  3460 */   177,   83,  272,  272,  206,  171,  172,  173,  174,  175,
 /*  3470 */   176,  177,  272,  272,  272,  206,  171,  172,  173,  174,
 /*  3480 */   175,  176,  177,  105,  106,  107,  108,  109,   83,  206,
 /*  3490 */   112,  171,  172,  173,  174,  175,  176,  177,  272,  272,
 /*  3500 */   206,  272,  171,  172,  173,  174,  175,  176,  177,  272,
 /*  3510 */   272,  206,  272,  272,  171,  172,  173,  174,  175,  176,
 /*  3520 */   177,  116,  117,  118,  119,  120,  206,  272,  171,  172,
 /*  3530 */   173,  174,  175,  176,  177,  272,  272,  206,  272,  272,
 /*  3540 */   171,  172,  173,  174,  175,  176,  177,  272,  272,  206,
 /*  3550 */   171,  172,  173,  174,  175,  176,  177,  272,  272,  272,
 /*  3560 */   272,  272,  272,  206,  171,  172,  173,  174,  175,  176,
 /*  3570 */   177,  272,  272,  272,  272,  206,  105,  106,  107,  108,
 /*  3580 */   109,  272,  272,  112,  272,  206,  272,  272,  272,  171,
 /*  3590 */   172,  173,  174,  175,  176,  177,   84,  272,  272,  206,
 /*  3600 */   171,  172,  173,  174,  175,  176,  177,  171,  172,  173,
 /*  3610 */   174,  175,  176,  177,  171,  172,  173,  174,  175,  176,
 /*  3620 */   177,  272,  272,  272,  206,  272,   81,   73,  116,  117,
 /*  3630 */   118,  119,  120,  272,   83,  206,  272,  272,  272,  272,
 /*  3640 */    84,  272,  206,  272,  272,  272,  272,  272,  272,  206,
 /*  3650 */   105,  106,  107,  108,  109,  272,  272,  112,  272,  105,
 /*  3660 */   106,  107,  108,  109,  272,  272,  112,  116,  117,  118,
 /*  3670 */   119,  120,  116,  117,  118,  119,  120,
};
#define YY_SHIFT_USE_DFLT (-110)
#define YY_SHIFT_COUNT (611)
#define YY_SHIFT_MIN   (-109)
#define YY_SHIFT_MAX   (3556)
static const short yy_shift_ofst[] = {
 /*     0 */  -110,  121,  280,  280,  513,  513,  712,  712,  280,  280,
 /*    10 */   280,  280,  280,  280,  280,  280,  280,  280,  280,  280,
 /*    20 */   280,  280,  280,  280,  280,  280,  280,  280,  280,  280,
 /*    30 */   280,  280,  396,  396,  396,  396,  396,  396,  712,  712,
 /*    40 */   712,  712,  712,  712,  712,  712,  712,  712,  712,  712,
 /*    50 */   994,  994,  994,  994,  994,  994,  994,  994,  994,  994,
 /*    60 */   629,  828,  828,  828,  828,  828,  828,  828,  828,  828,
 /*    70 */   828,  828,  828,  828,  828,  828,  828,  828,  828,  828,
 /*    80 */   828,  828,  828,  828,  828,  828,  828,  828,  828,  828,
 /*    90 */   828,  828,  828,  828,  828,  828,  828,  828,  828,  828,
 /*   100 */   828,  828,  828,  828,  828,  828,  828,  828,  828,  828,
 /*   110 */   828,  828,  828,  828,  828,  828,  828,  828,  828,  828,
 /*   120 */   828,  828,  828,  828,  828,  828,  828,  828,  828,  828,
 /*   130 */   911,  911,  911, 1077,  251, 1160, 1160, 1160, 1160, 1160,
 /*   140 */  1160, 1160, 1160, 1160, 1160, 1160, 1160, 1160, 1160, 1160,
 /*   150 */  1160, 1160, 1160, 1160, 1160, 1160, 1160, 1160, 1160, 1160,
 /*   160 */  1077, 1077, 1077, 1077, 1077, 1077, 1077, 1077, 1077, 1077,
 /*   170 */  1077, 1077, 1077, 1077, 1077, 1077, 1077, 1077, 1077, 1077,
 /*   180 */  1077, 1077, 1077, 1603, 1603, 1603, 1603, 2149, 2145, 1431,
 /*   190 */  1603, 1603, 1431,  653,  653, 1256, 1394,  707, 1431,  120,
 /*   200 */   120,  891,  891,  529, 1979, 1860, 2351, 2351, 2351, 2351,
 /*   210 */  2351, 2351, 2351, 1811, 1230,  839,  529,  529,  529,  529,
 /*   220 */   301,  839,  891,  891, 1979, 1860, 1576, 2351, 2351, 2351,
 /*   230 */  2351, 2351, 2351, 2351, 2351, 2351,  515, 1868, 3299, 3299,
 /*   240 */  3299, 3554, 3554, 1506, 1506, 1809, 1809, 1809, 1809, 1809,
 /*   250 */  1809, 1809, 1809, 1809, 1809, 1809, 1809, 1809, 1809, 1809,
 /*   260 */   524, 1113,  226,  161,  635,  635,  635,  635,  268,  268,
 /*   270 */   635,  301,  268,  635,  635,  268,  635, 1475, 1475, 1474,
 /*   280 */  1475, 1474, 1515, 1467, 1580, 1475, 1474, 1515, 1467, 1580,
 /*   290 */  1475, 1474, 1515, 1467, 1580, 1475, 1474, 1475, 1474, 1475,
 /*   300 */  1474, 1475, 1474, 1475, 1474, 1515, 1467, 1475, 1474, 1515,
 /*   310 */  1467, 1595, 1576, 1475, 1474, 1475, 1474, 1475, 1474, 1475,
 /*   320 */  1474, 1475, 1474, 1515, 1467, 1371, 1371, 1371, 1367,  129,
 /*   330 */   772,  637,  294, 1004,  886,  387, 2075, 2046, 2038, 2008,
 /*   340 */  2000,  528, 2333,  704, 3378, 3545, 2306, 1946, 1905, 1080,
 /*   350 */   417, 1638, 1466, 1859, 1346, 1294,   85,  -26, 3556, 3512,
 /*   360 */   929, 3471, 3471,  646,  233,  233,  233,  233,  233,  233,
 /*   370 */   233,  233,  233,  233,  233,  496, 1215,  988,  563,  289,
 /*   380 */  3551,  194, 3405,  882,  496,  496,  496, 3332, 2512, 2341,
 /*   390 */  2252, 1959, 1514, 1178, 1095,  379,  906, 1747,  -88,  845,
 /*   400 */  1662,   31,   31,   31,   31,   31,   31,   31,  -88,  -88,
 /*   410 */   -88,  -88,  -88,  799,  -88,  -88,  -88,  -88,  -88,  -88,
 /*   420 */   -88,  -88,  -88,  -88,  -88,  -88,  -88,  -88,  -88,  -88,
 /*   430 */   756,  532,  -88,  -88,   31,   31,   31,  -88,  -88,  -88,
 /*   440 */   -88,  -88,  -88,  -88,  -88,  -88, 1322,  335,  335,  499,
 /*   450 */   499,  499,  499,  221,  221,  654,  479,  363,  141,  141,
 /*   460 */   163,  163,   36,   36,   63,   63,  -73,  -73,  -73,  -73,
 /*   470 */    36,   36,  -73,  -73,  -73,  -73,  360, 1056,  848,  894,
 /*   480 */   856, -109, -109, -109, -109,  816,  485,  716,  931,  400,
 /*   490 */   482,  243,  832,  765,  -15,  281,  -63,  162,  156,  442,
 /*   500 */   734,   92,  219,  705,  291,   93,   52,  695,  575,  276,
 /*   510 */   -35,  -50, 1384, 1423, 1407, 1406, 1400, 1399, 1398, 1397,
 /*   520 */  1395, 1387, 1385, 1378, 1377, 1375, 1449, 1344, 1386, 1345,
 /*   530 */  1427, 1334, 1376, 1361, 1347, 1324, 1323, 1297, 1295, 1269,
 /*   540 */  1269, 1296, 1280, 1360, 1247, 1350,  942, 1267, 1259, 1248,
 /*   550 */  1337, 1231, 1244, 1236, 1223, 1204, 1172, 1195,  942,  942,
 /*   560 */  1180, 1238, 1176, 1153, 1145, 1132, 1099, 1108, 1093, 1074,
 /*   570 */  1087, 1062,  992, 1040, 1022,  985,  942,  956,  949,  885,
 /*   580 */   875,  858,  881,  835,  866,  783,  752,  735,  679,  679,
 /*   590 */   660,  636,  634,  598,  598,  596,  516,  518,  512,  443,
 /*   600 */   437,  420,  350,  395,  369,  337,  192,  128,  116,  104,
 /*   610 */    86,   55,
};
#define YY_REDUCE_USE_DFLT (-151)
#define YY_REDUCE_COUNT (328)
#define YY_REDUCE_MIN   (-150)
#define YY_REDUCE_MAX   (3443)
static const short yy_reduce_ofst[] = {
 /*     0 */   998, -150,  264, -135,  171,  495,  402,  317, 1564, 1538,
 /*    10 */  1499, 1473, 1444, 1418, 1392, 1366, 1327, 1301, 1272, 1246,
 /*    20 */  1220, 1194, 1152, 1116, 1079, 1052,  844,  762,  666,  630,
 /*    30 */   469, -100, 1897, 1872, 1847, 1822, 1785, 1673, 1778, 1734,
 /*    40 */  1724, 1710, 1666, 1658, 1614, 1604, 1590, 1144,  970,  918,
 /*    50 */  2202, 2167, 2151, 2133, 2117, 2100, 2082, 2064,  382,   58,
 /*    60 */  1355, 1029,  751,  520,  -33, 2952, 2942, 2932, 2922, 2912,
 /*    70 */  2902, 2892, 2882, 2872, 2862, 2852, 2842, 2831, 2815, 2805,
 /*    80 */  2791, 2781, 2771, 2761, 2751, 2741, 2731, 2721, 2711, 2701,
 /*    90 */  2691, 2681, 2671, 2660, 2644, 2634, 2620, 2610, 2600, 2590,
 /*   100 */  2580, 2570, 2560, 2550, 2540, 2530, 2520, 2510, 2500, 2489,
 /*   110 */  2473, 2463, 2448, 2437, 2427, 2417, 2406, 2394, 2384, 2374,
 /*   120 */  2362, 2352, 2342, 2332, 2320, 2220, 2184, 2072, 2007, 1526,
 /*   130 */  2304, 2278, 2263,  889,  145, 3443, 3436, 3429, 3418, 3393,
 /*   140 */  3379, 3369, 3357, 3343, 3331, 3320, 3305, 3294, 3283, 3269,
 /*   150 */  3258, 3247, 3222, 3211, 3204, 3197, 3186,  836,  257,  125,
 /*   160 */  3174, 3160, 3148, 3134, 3122, 3110, 3098, 3086, 3074, 3062,
 /*   170 */  3050, 3038, 3026, 3014, 3002, 2988, 2976, 2961,  997,  722,
 /*   180 */   608,  550,   42, 1043,  657,   66, -125, 2957,  930, 1051,
 /*   190 */    15, -136,  231, 1829,  -17,  278,  458,  322,  610, 1167,
 /*   200 */   715,  947,  178,  508,  506,  446, 1187, 1163, 1091, 1071,
 /*   210 */  1008, 1007,  924,  449,  905,  883,  841,  833,  790,  758,
 /*   220 */   730,  557,  652,  409,  272,  332,  -93, 1792, 1774, 1754,
 /*   230 */  1753, 1750, 1744, 1740, 1737, 1730, 1665, 1668, 1664, 1663,
 /*   240 */  1654, 1650, 1642, 1644, 1627, 1684, 1674, 1672, 1671, 1661,
 /*   250 */  1646, 1633, 1632, 1630, 1629, 1623, 1619, 1617, 1616, 1615,
 /*   260 */  1593, 1625, 1593, 1547, 1622, 1621, 1620, 1611, 1534, 1525,
 /*   270 */  1600, 1533, 1505, 1579, 1553, 1478, 1479, 1500, 1490, 1477,
 /*   280 */  1465, 1476, 1471, 1468, 1460, 1464, 1456, 1457, 1439, 1432,
 /*   290 */  1452, 1437, 1438, 1403, 1351, 1430, 1435, 1429, 1428, 1411,
 /*   300 */  1405, 1410, 1404, 1402, 1401, 1393, 1358, 1391, 1390, 1356,
 /*   310 */  1357, 1370, 1336, 1349, 1331, 1348, 1330, 1328, 1319, 1304,
 /*   320 */  1303, 1293, 1284, 1275, 1266, 1340, 1335, 1333, 1290,
};
static const YYACTIONTYPE yy_default[] = {
 /*     0 */   954, 1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438,
 /*    10 */  1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438,
 /*    20 */  1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438,
 /*    30 */  1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438,
 /*    40 */  1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438,
 /*    50 */  1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438,
 /*    60 */  1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438,
 /*    70 */  1179, 1183, 1178, 1182, 1270, 1266, 1438, 1438, 1438, 1438,
 /*    80 */  1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438,
 /*    90 */  1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438,
 /*   100 */  1438, 1438, 1438, 1438, 1271, 1267, 1438, 1438, 1438, 1438,
 /*   110 */  1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438,
 /*   120 */  1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438,
 /*   130 */  1438, 1438, 1438, 1438, 1438, 1250, 1254, 1249, 1253, 1438,
 /*   140 */  1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438,
 /*   150 */  1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438,
 /*   160 */  1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438,
 /*   170 */  1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438,
 /*   180 */  1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438,
 /*   190 */  1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438,
 /*   200 */  1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438,
 /*   210 */  1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438,
 /*   220 */  1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438,
 /*   230 */  1438, 1438, 1438, 1438, 1438, 1438, 1382, 1380, 1382, 1382,
 /*   240 */  1382, 1388, 1388, 1380, 1380, 1438, 1438, 1438, 1438, 1438,
 /*   250 */  1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438,
 /*   260 */  1438, 1438, 1438, 1380, 1438, 1438, 1438, 1438, 1380, 1380,
 /*   270 */  1438, 1438, 1380, 1438, 1438, 1380, 1438, 1388, 1388, 1386,
 /*   280 */  1388, 1386, 1382, 1384, 1380, 1388, 1386, 1382, 1384, 1380,
 /*   290 */  1388, 1386, 1382, 1384, 1380, 1388, 1386, 1388, 1386, 1388,
 /*   300 */  1386, 1388, 1386, 1388, 1386, 1382, 1384, 1388, 1386, 1382,
 /*   310 */  1384, 1438, 1438, 1388, 1386, 1388, 1386, 1388, 1386, 1388,
 /*   320 */  1386, 1388, 1386, 1382, 1384, 1438, 1438, 1438, 1438, 1438,
 /*   330 */  1438, 1438, 1438, 1438, 1438, 1438, 1216, 1438, 1143, 1143,
 /*   340 */  1438, 1438, 1032, 1438, 1438, 1438, 1438, 1438, 1438, 1438,
 /*   350 */  1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438,
 /*   360 */  1438, 1372, 1369, 1438, 1252, 1256, 1251, 1255, 1247, 1246,
 /*   370 */  1245, 1244, 1243, 1242, 1241, 1234, 1438, 1438, 1438, 1438,
 /*   380 */  1438, 1438, 1438, 1387, 1381, 1383, 1379, 1438, 1438, 1438,
 /*   390 */  1438, 1438, 1438, 1438, 1438, 1438, 1097, 1231, 1202, 1096,
 /*   400 */  1157, 1169, 1168, 1167, 1166, 1165, 1164, 1163, 1149, 1181,
 /*   410 */  1185, 1180, 1184, 1114, 1272, 1268, 1145, 1142, 1141, 1140,
 /*   420 */  1139, 1138, 1137, 1136, 1135, 1134, 1133, 1132, 1131, 1130,
 /*   430 */  1438, 1438, 1273, 1269, 1172,  997,  998, 1129, 1128, 1127,
 /*   440 */  1126, 1125, 1124, 1123,  994,  993, 1264, 1233, 1232, 1220,
 /*   450 */  1219, 1203, 1204, 1102, 1103, 1438, 1438, 1438, 1091, 1092,
 /*   460 */  1159, 1158, 1060, 1059, 1116, 1115, 1034, 1033, 1039, 1038,
 /*   470 */  1077, 1078, 1044, 1043, 1014, 1015, 1438, 1438, 1098, 1438,
 /*   480 */  1438, 1346, 1350, 1349, 1347, 1438, 1342, 1438, 1438, 1438,
 /*   490 */  1438, 1082, 1438, 1438, 1438, 1438, 1438, 1285, 1438, 1438,
 /*   500 */  1438, 1438, 1438, 1438,  976, 1438, 1438, 1438, 1438, 1438,
 /*   510 */  1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438,
 /*   520 */  1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438,
 /*   530 */  1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438, 1213, 1230,
 /*   540 */  1229, 1438, 1438, 1438, 1348, 1438, 1341, 1333, 1308, 1310,
 /*   550 */  1438, 1438, 1438, 1438, 1438, 1438, 1438, 1323, 1284, 1283,
 /*   560 */  1306, 1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438,
 /*   570 */  1438, 1438, 1438, 1438, 1438, 1305, 1302, 1438, 1438, 1438,
 /*   580 */  1438, 1438, 1438, 1438, 1438, 1438, 1438, 1438, 1156, 1155,
 /*   590 */  1147, 1143,  981, 1113, 1112, 1438, 1438, 1438, 1438, 1438,
 /*   600 */  1438, 1438, 1170,  996, 1438, 1438, 1438,  992,  989,  985,
 /*   610 */   979, 1438, 1437, 1436, 1435, 1434, 1433, 1432, 1431, 1430,
 /*   620 */  1428, 1427, 1426, 1425, 1424, 1423, 1265, 1422, 1421, 1429,
 /*   630 */  1420, 1419, 1414, 1412, 1411, 1409, 1408, 1407, 1406, 1405,
 /*   640 */  1404, 1403, 1402, 1401, 1400, 1399, 1398, 1397, 1396, 1395,
 /*   650 */  1394, 1393, 1392, 1391, 1390, 1389, 1363, 1362, 1371, 1370,
 /*   660 */  1378, 1377, 1374, 1373, 1368, 1376, 1225, 1227, 1248, 1240,
 /*   670 */  1239, 1238, 1237, 1236, 1235, 1228, 1226, 1224, 1218, 1217,
 /*   680 */  1215, 1214, 1213, 1223, 1222, 1221, 1207, 1206, 1205, 1201,
 /*   690 */  1200, 1199, 1198, 1197, 1196, 1195, 1194, 1193, 1192, 1191,
 /*   700 */  1190, 1189, 1212, 1211, 1210, 1209, 1208, 1367, 1366, 1365,
 /*   710 */  1364, 1106, 1105, 1104, 1101, 1100, 1099, 1098, 1357, 1356,
 /*   720 */  1358, 1355, 1360, 1361, 1359, 1354, 1352, 1351, 1353, 1345,
 /*   730 */  1339, 1343, 1344, 1340, 1338, 1328, 1331, 1337, 1336, 1334,
 /*   740 */  1332, 1330, 1329, 1327, 1296, 1309, 1311, 1326, 1325, 1324,
 /*   750 */  1322, 1321, 1320, 1319, 1318, 1317, 1316, 1315, 1314, 1313,
 /*   760 */  1312, 1307, 1304, 1303, 1301, 1300, 1299, 1298, 1294, 1293,
 /*   770 */  1292, 1291, 1290, 1289, 1288,  985, 1287, 1286, 1095, 1094,
 /*   780 */  1093, 1090, 1089, 1088, 1087, 1086, 1085, 1084, 1083, 1082,
 /*   790 */  1297, 1295, 1275, 1278, 1279, 1282, 1281, 1280, 1277, 1276,
 /*   800 */  1274, 1418, 1417, 1416, 1415, 1413, 1410, 1151, 1153, 1162,
 /*   810 */  1161, 1160, 1154, 1152, 1150, 1058, 1057, 1056, 1055, 1054,
 /*   820 */  1053, 1063, 1062, 1061, 1052, 1051, 1050, 1049, 1048, 1385,
 /*   830 */  1146, 1148,  982, 1108, 1110, 1174, 1177, 1176, 1175, 1173,
 /*   840 */  1122, 1121, 1120, 1119, 1118, 1117, 1111, 1109, 1107, 1027,
 /*   850 */  1258, 1264, 1263, 1262, 1261, 1260, 1259, 1257, 1144, 1037,
 /*   860 */  1036, 1035, 1042, 1041, 1040, 1032, 1031, 1030, 1029, 1028,
 /*   870 */  1027, 1026, 1025, 1024, 1187, 1188, 1186, 1171, 1079, 1081,
 /*   880 */  1080, 1076, 1075, 1074, 1073, 1072, 1071, 1070, 1069, 1068,
 /*   890 */  1067, 1066, 1065, 1064,  995, 1047, 1046, 1045, 1023, 1022,
 /*   900 */  1021, 1020, 1019, 1016, 1017, 1018, 1013, 1012, 1011, 1010,
 /*   910 */  1009, 1008, 1007, 1006, 1005, 1004, 1003, 1002, 1001, 1000,
 /*   920 */   999,  991,  990,  988,  987,  986,  984,  983,  980,  978,
 /*   930 */   974,  973,  977,  976,  975,  972,  971,  970,  969,  968,
 /*   940 */   967,  966,  965,  964,  963,  962,  961,  960,  959,  958,
 /*   950 */   957,  956,  955,
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
    0,  /* DERIVATIVE => nothing */
    0,  /*         IF => nothing */
    0,  /*         IS => nothing */
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
    0,  /* INTEGER_TYPE => nothing */
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
  "EXOGENOUSACTION",  "DDT",           "DERIVATIVE",    "IF",          
  "IS",            "MODE",          "IFCONS",        "INCREMENTS",  
  "INERTIAL",      "INERTIALFLUENT",  "LABEL",         "MAY_CAUSE",   
  "MAXADDITIVE",   "MAXAFVALUE",    "MAXSTEP",       "NEVER",       
  "NOCONCURRENCY",  "STRONG_NOCONCURRENCY",  "NONEXECUTABLE",  "OF",          
  "POSSIBLY_CAUSED",  "REAL",          "INTEGER_TYPE",  "CONTINUOUS",  
  "RIGID",         "SDFLUENT",      "SIMPLEFLUENT",  "EXTERNALFLUENT",
  "UNLESS",        "WHERE",         "FALSE",         "TRUE",        
  "AT",            "BRACKET_L",     "BRACKET_R",     "COLON_DASH",  
  "CBRACKET_L",    "CBRACKET_R",    "PAREN_L",       "PAREN_R",     
  "PERIOD",        "MACRO_STRING",  "TILDE",         "DBL_COLON",   
  "ARROW_LEQ",     "ARROW_REQ",     "ARROW_LDASH",   "COLON",       
  "EQ",            "DBL_EQ",        "NEQ",           "NOT_EQ",      
  "LTHAN",         "GTHAN",         "LTHAN_EQ",      "GTHAN_EQ",    
  "DBL_PERIOD",    "BIG_CONJ",      "BIG_DISJ",      "POUND",       
  "SEMICOLON",     "EQUIV",         "IMPL",          "ARROW_RDASH", 
  "DBL_PLUS",      "PIPE",          "DBL_GTHAN",     "DBL_LTHAN",   
  "AMP",           "COMMA",         "DBL_AMP",       "NOT",         
  "DASH",          "PLUS",          "STAR",          "INT_DIV",     
  "MOD",           "ABS",           "CARROT",        "UMINUS",      
  "PREC_4",        "PREC_3",        "PREC_2",        "PREC_1",      
  "PREC_0",        "EOF",           "ERR_IO",        "ERR_UNKNOWN_SYMBOL",
  "ERR_UNTERMINATED_STRING",  "ERR_UNTERMINATED_ASP",  "ERR_UNTERMINATED_LUA",  "ERR_UNTERMINATED_PYTHON",
  "ERR_UNTERMINATED_F2LP",  "ERR_UNTERMINATED_BLK_COMMENT",  "ERR_SYNTAX",    "ERR_PAREN_MISMATCH",
  "ARG",           "NOOP",          "CONSTANT_ID",   "VARIABLE_ID", 
  "OBJECT_ID",     "SIN",           "COS",           "TAN",         
  "HIDE",          "OBSERVED",      "error",         "start",       
  "statement_lst",  "statement",     "stmt_macro_def",  "stmt_constant_def",
  "stmt_object_def",  "stmt_variable_def",  "stmt_sort_def",  "stmt_code_blk",
  "stmt_law",      "stmt_show",     "stmt_hide",     "stmt_noconcurrency",
  "stmt_strong_noconcurrency",  "stmt_maxafvalue",  "stmt_maxadditive",  "stmt_query",  
  "rate_decl",     "alwayst_stmt",  "base_elem",     "base_elem_no_const",
  "constant",      "object",        "object_nullary",  "variable",    
  "lua",           "undeclared",    "term_lst",      "term",        
  "constant_one_const",  "term_no_const_lst",  "term_no_const",  "const_anon",  
  "term_strong",   "term_strong_candidate",  "term_no_const_strong",  "num_range",   
  "num_range_eval",  "term_integral",  "term_int_eval",  "formula",     
  "formula_base",  "comparison",    "atomic_formula",  "formula_quant",
  "formula_card",  "atomic_formula_anon",  "formula_no_const",  "formula_no_const_base",
  "comparison_no_const",  "atomic_formula_one_const",  "quant_lst",     "quant_op",    
  "card_var_lst",  "card_var_lst_inner",  "term_temporal",  "term_temporal_strong",
  "term_temporal_strong_candidate",  "constant_temporal",  "formula_temporal",  "formula_temporal_base",
  "comparison_temporal",  "formula_temporal_quant",  "formula_temporal_card",  "head_formula",
  "atomic_head_formula",  "formula_smpl_card",  "macro_def_lst",  "macro_bnd",   
  "macro_args",    "macro_arg",     "sort_lst",      "sort",        
  "sort_id_nr",    "sort_nr",       "sort_id",       "constant_bnd_lst",
  "constant_bnd",  "constant_dcl_lst",  "constant_dcl_type",  "attrib_spec", 
  "object_bnd_lst",  "object_bnd",    "object_lst",    "object_spec", 
  "variable_bnd_lst",  "variable_bnd",  "variable_lst",  "sort_bnd_lst",
  "sort_bnd",      "sort_dcl_lst",  "show_lst",      "show_elem",   
  "query_lst",     "query_maxstep_decl",  "query_label_decl",  "query_label_Decl",
  "clause_if",     "clause_after",  "clause_ifcons",  "clause_unless",
  "clause_where",  "law_basic",     "law_caused",    "law_pcaused", 
  "law_impl",      "law_causes",    "law_increments",  "law_decrements",
  "law_mcause",    "law_always",    "law_constraint",  "law_impossible",
  "law_never",     "law_default",   "law_exogenous",  "law_inertial",
  "law_nonexecutable",  "law_rigid",     "law_observed",  "law_temporal_constraint",
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
 /* 347 */ "constant_bnd ::= constant_dcl_lst DBL_COLON constant_dcl_type PAREN_L INTEGER_TYPE BRACKET_L num_range BRACKET_R PAREN_R",
 /* 348 */ "constant_bnd ::= constant_dcl_lst DBL_COLON CONTINUOUS PAREN_L num_range PAREN_R",
 /* 349 */ "constant_bnd ::= constant_dcl_lst DBL_COLON sort",
 /* 350 */ "constant_bnd ::= constant_dcl_lst DBL_COLON REAL BRACKET_L num_range BRACKET_R",
 /* 351 */ "constant_bnd ::= constant_dcl_lst DBL_COLON INTEGER_TYPE BRACKET_L num_range BRACKET_R",
 /* 352 */ "constant_bnd ::= constant_dcl_lst DBL_COLON constant_dcl_type",
 /* 353 */ "constant_bnd ::= constant_dcl_lst DBL_COLON attrib_spec OF IDENTIFIER",
 /* 354 */ "constant_bnd ::= constant_dcl_lst DBL_COLON attrib_spec OF IDENTIFIER PAREN_L sort_lst PAREN_R",
 /* 355 */ "constant_dcl_lst ::= IDENTIFIER",
 /* 356 */ "constant_dcl_lst ::= IDENTIFIER PAREN_L sort_lst PAREN_R",
 /* 357 */ "constant_dcl_lst ::= constant_dcl_lst COMMA IDENTIFIER",
 /* 358 */ "constant_dcl_lst ::= constant_dcl_lst COMMA IDENTIFIER PAREN_L sort_lst PAREN_R",
 /* 359 */ "constant_dcl_type ::= ABACTION",
 /* 360 */ "constant_dcl_type ::= ACTION",
 /* 361 */ "constant_dcl_type ::= ADDITIVEACTION",
 /* 362 */ "constant_dcl_type ::= ADDITIVEFLUENT",
 /* 363 */ "constant_dcl_type ::= EXTERNALACTION",
 /* 364 */ "constant_dcl_type ::= EXTERNALFLUENT",
 /* 365 */ "constant_dcl_type ::= EXOGENOUSACTION",
 /* 366 */ "constant_dcl_type ::= INERTIALFLUENT",
 /* 367 */ "constant_dcl_type ::= RIGID",
 /* 368 */ "constant_dcl_type ::= SIMPLEFLUENT",
 /* 369 */ "constant_dcl_type ::= SDFLUENT",
 /* 370 */ "attrib_spec ::= ATTRIBUTE",
 /* 371 */ "attrib_spec ::= ATTRIBUTE PAREN_L sort PAREN_R",
 /* 372 */ "attrib_spec ::= ATTRIBUTE PAREN_L REAL BRACKET_L num_range BRACKET_R PAREN_R",
 /* 373 */ "attrib_spec ::= ATTRIBUTE PAREN_L INTEGER_TYPE BRACKET_L num_range BRACKET_R PAREN_R",
 /* 374 */ "stmt_object_def ::= COLON_DASH OBJECTS object_bnd_lst PERIOD",
 /* 375 */ "object_bnd_lst ::= object_bnd",
 /* 376 */ "object_bnd_lst ::= object_bnd_lst SEMICOLON object_bnd",
 /* 377 */ "object_bnd ::= object_lst DBL_COLON sort_id",
 /* 378 */ "object_lst ::= object_spec",
 /* 379 */ "object_lst ::= object_lst COMMA object_spec",
 /* 380 */ "object_spec ::= IDENTIFIER",
 /* 381 */ "object_spec ::= IDENTIFIER PAREN_L sort_lst PAREN_R",
 /* 382 */ "object_spec ::= INTEGER",
 /* 383 */ "object_spec ::= FLOAT",
 /* 384 */ "object_spec ::= num_range",
 /* 385 */ "stmt_variable_def ::= COLON_DASH VARIABLES variable_bnd_lst PERIOD",
 /* 386 */ "variable_bnd_lst ::= variable_bnd",
 /* 387 */ "variable_bnd_lst ::= variable_bnd_lst SEMICOLON variable_bnd",
 /* 388 */ "variable_bnd ::= variable_lst DBL_COLON sort",
 /* 389 */ "variable_bnd ::= variable_lst",
 /* 390 */ "variable_lst ::= IDENTIFIER",
 /* 391 */ "variable_lst ::= variable_lst COMMA IDENTIFIER",
 /* 392 */ "stmt_sort_def ::= COLON_DASH SORTS sort_bnd_lst PERIOD",
 /* 393 */ "sort_bnd_lst ::= sort_bnd",
 /* 394 */ "sort_bnd_lst ::= sort_bnd_lst SEMICOLON sort_bnd",
 /* 395 */ "sort_bnd ::= sort_dcl_lst",
 /* 396 */ "sort_bnd ::= sort_bnd DBL_LTHAN sort_bnd",
 /* 397 */ "sort_bnd ::= sort_bnd DBL_GTHAN sort_bnd",
 /* 398 */ "sort_bnd ::= PAREN_L sort_bnd PAREN_R",
 /* 399 */ "sort_dcl_lst ::= IDENTIFIER",
 /* 400 */ "sort_dcl_lst ::= sort_dcl_lst COMMA IDENTIFIER",
 /* 401 */ "stmt_show ::= COLON_DASH SHOW show_lst PERIOD",
 /* 402 */ "stmt_show ::= COLON_DASH SHOW ALL PERIOD",
 /* 403 */ "stmt_hide ::= COLON_DASH HIDE show_lst PERIOD",
 /* 404 */ "stmt_hide ::= COLON_DASH HIDE ALL PERIOD",
 /* 405 */ "show_lst ::= show_elem",
 /* 406 */ "show_lst ::= show_lst COMMA show_elem",
 /* 407 */ "show_lst ::= show_lst SEMICOLON show_elem",
 /* 408 */ "show_elem ::= atomic_formula_one_const",
 /* 409 */ "stmt_noconcurrency ::= NOCONCURRENCY PERIOD",
 /* 410 */ "stmt_strong_noconcurrency ::= STRONG_NOCONCURRENCY PERIOD",
 /* 411 */ "stmt_maxafvalue ::= COLON_DASH MAXAFVALUE EQ term_int_eval PERIOD",
 /* 412 */ "stmt_maxafvalue ::= COLON_DASH MAXAFVALUE DBL_COLON term_int_eval PERIOD",
 /* 413 */ "stmt_maxadditive ::= COLON_DASH MAXADDITIVE EQ term_int_eval PERIOD",
 /* 414 */ "stmt_maxadditive ::= COLON_DASH MAXADDITIVE DBL_COLON term_int_eval PERIOD",
 /* 415 */ "stmt_query ::= COLON_DASH QUERY query_lst PERIOD",
 /* 416 */ "query_lst ::= formula_temporal",
 /* 417 */ "query_lst ::= query_maxstep_decl",
 /* 418 */ "query_lst ::= query_label_decl",
 /* 419 */ "query_lst ::= query_lst SEMICOLON formula_temporal",
 /* 420 */ "query_lst ::= query_lst SEMICOLON query_maxstep_decl",
 /* 421 */ "query_lst ::= query_lst SEMICOLON query_label_decl",
 /* 422 */ "query_maxstep_decl ::= MAXSTEP DBL_COLON INTEGER",
 /* 423 */ "query_maxstep_decl ::= MAXSTEP DBL_COLON num_range_eval",
 /* 424 */ "query_label_decl ::= LABEL DBL_COLON INTEGER",
 /* 425 */ "query_label_decl ::= LABEL DBL_COLON IDENTIFIER",
 /* 426 */ "clause_if ::= IF formula",
 /* 427 */ "clause_if ::=",
 /* 428 */ "clause_after ::= AFTER formula",
 /* 429 */ "clause_after ::=",
 /* 430 */ "clause_ifcons ::= IFCONS formula",
 /* 431 */ "clause_ifcons ::=",
 /* 432 */ "clause_unless ::= UNLESS atomic_formula_anon",
 /* 433 */ "clause_unless ::=",
 /* 434 */ "clause_where ::= WHERE formula_no_const",
 /* 435 */ "clause_where ::=",
 /* 436 */ "rate_decl ::= DERIVATIVE OF constant IS term IF MODE EQ INTEGER PERIOD",
 /* 437 */ "alwayst_stmt ::= ALWAYST formula IF MODE EQ INTEGER PERIOD",
 /* 438 */ "stmt_law ::= law_basic",
 /* 439 */ "stmt_law ::= law_caused",
 /* 440 */ "stmt_law ::= law_pcaused",
 /* 441 */ "stmt_law ::= law_impl",
 /* 442 */ "stmt_law ::= law_causes",
 /* 443 */ "stmt_law ::= law_increments",
 /* 444 */ "stmt_law ::= law_decrements",
 /* 445 */ "stmt_law ::= law_mcause",
 /* 446 */ "stmt_law ::= law_always",
 /* 447 */ "stmt_law ::= law_constraint",
 /* 448 */ "stmt_law ::= law_impossible",
 /* 449 */ "stmt_law ::= law_never",
 /* 450 */ "stmt_law ::= law_default",
 /* 451 */ "stmt_law ::= law_exogenous",
 /* 452 */ "stmt_law ::= law_inertial",
 /* 453 */ "stmt_law ::= law_nonexecutable",
 /* 454 */ "stmt_law ::= law_rigid",
 /* 455 */ "stmt_law ::= law_observed",
 /* 456 */ "stmt_law ::= law_temporal_constraint",
 /* 457 */ "law_basic ::= head_formula clause_if clause_ifcons clause_after clause_unless clause_where PERIOD",
 /* 458 */ "law_caused ::= CAUSED head_formula clause_if clause_ifcons clause_after clause_unless clause_where PERIOD",
 /* 459 */ "law_pcaused ::= POSSIBLY_CAUSED head_formula clause_if clause_ifcons clause_after clause_unless clause_where PERIOD",
 /* 460 */ "law_impl ::= head_formula ARROW_LDASH formula clause_where PERIOD",
 /* 461 */ "law_impl ::= ARROW_LDASH formula clause_where PERIOD",
 /* 462 */ "law_causes ::= atomic_formula CAUSES head_formula clause_if clause_unless clause_where PERIOD",
 /* 463 */ "law_increments ::= atomic_formula INCREMENTS constant BY term clause_if clause_unless clause_where PERIOD",
 /* 464 */ "law_decrements ::= atomic_formula DECREMENTS constant BY term clause_if clause_unless clause_where PERIOD",
 /* 465 */ "law_mcause ::= atomic_formula MAY_CAUSE head_formula clause_if clause_unless clause_where PERIOD",
 /* 466 */ "law_always ::= ALWAYS formula clause_after clause_unless clause_where PERIOD",
 /* 467 */ "law_constraint ::= CONSTRAINT formula clause_after clause_unless clause_where PERIOD",
 /* 468 */ "law_impossible ::= IMPOSSIBLE formula clause_after clause_unless clause_where PERIOD",
 /* 469 */ "law_never ::= NEVER formula clause_after clause_unless clause_where PERIOD",
 /* 470 */ "law_default ::= DEFAULT atomic_head_formula clause_if clause_ifcons clause_after clause_unless clause_where PERIOD",
 /* 471 */ "law_exogenous ::= EXOGENOUS constant clause_if clause_ifcons clause_after clause_unless clause_where PERIOD",
 /* 472 */ "law_inertial ::= INERTIAL constant clause_if clause_ifcons clause_after clause_unless clause_where PERIOD",
 /* 473 */ "law_nonexecutable ::= NONEXECUTABLE formula clause_if clause_unless clause_where PERIOD",
 /* 474 */ "law_rigid ::= RIGID constant clause_where PERIOD",
 /* 475 */ "law_observed ::= OBSERVED atomic_head_formula AT term_int_eval PERIOD",
 /* 476 */ "law_temporal_constraint ::= CONSTRAINT formula AT term_int_eval PERIOD",
 /* 477 */ "stmt_code_blk ::= ASP_GR",
 /* 478 */ "stmt_code_blk ::= ASP_CP",
 /* 479 */ "stmt_code_blk ::= F2LP_GR",
 /* 480 */ "stmt_code_blk ::= F2LP_CP",
 /* 481 */ "stmt_code_blk ::= LUA_GR",
 /* 482 */ "stmt_code_blk ::= LUA_CP",
 /* 483 */ "stmt_code_blk ::= PYTHON_GR",
 /* 484 */ "stmt_code_blk ::= PYTHON_CP",
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
    case 46: /* DERIVATIVE */
    case 47: /* IF */
    case 48: /* IS */
    case 49: /* MODE */
    case 50: /* IFCONS */
    case 51: /* INCREMENTS */
    case 52: /* INERTIAL */
    case 53: /* INERTIALFLUENT */
    case 54: /* LABEL */
    case 55: /* MAY_CAUSE */
    case 56: /* MAXADDITIVE */
    case 57: /* MAXAFVALUE */
    case 58: /* MAXSTEP */
    case 59: /* NEVER */
    case 60: /* NOCONCURRENCY */
    case 61: /* STRONG_NOCONCURRENCY */
    case 62: /* NONEXECUTABLE */
    case 63: /* OF */
    case 64: /* POSSIBLY_CAUSED */
    case 65: /* REAL */
    case 66: /* INTEGER_TYPE */
    case 67: /* CONTINUOUS */
    case 68: /* RIGID */
    case 69: /* SDFLUENT */
    case 70: /* SIMPLEFLUENT */
    case 71: /* EXTERNALFLUENT */
    case 72: /* UNLESS */
    case 73: /* WHERE */
    case 74: /* FALSE */
    case 75: /* TRUE */
    case 76: /* AT */
    case 77: /* BRACKET_L */
    case 78: /* BRACKET_R */
    case 79: /* COLON_DASH */
    case 80: /* CBRACKET_L */
    case 81: /* CBRACKET_R */
    case 82: /* PAREN_L */
    case 83: /* PAREN_R */
    case 84: /* PERIOD */
    case 85: /* MACRO_STRING */
    case 86: /* TILDE */
    case 87: /* DBL_COLON */
    case 88: /* ARROW_LEQ */
    case 89: /* ARROW_REQ */
    case 90: /* ARROW_LDASH */
    case 91: /* COLON */
    case 92: /* EQ */
    case 93: /* DBL_EQ */
    case 94: /* NEQ */
    case 95: /* NOT_EQ */
    case 96: /* LTHAN */
    case 97: /* GTHAN */
    case 98: /* LTHAN_EQ */
    case 99: /* GTHAN_EQ */
    case 100: /* DBL_PERIOD */
    case 101: /* BIG_CONJ */
    case 102: /* BIG_DISJ */
    case 103: /* POUND */
    case 104: /* SEMICOLON */
    case 105: /* EQUIV */
    case 106: /* IMPL */
    case 107: /* ARROW_RDASH */
    case 108: /* DBL_PLUS */
    case 109: /* PIPE */
    case 110: /* DBL_GTHAN */
    case 111: /* DBL_LTHAN */
    case 112: /* AMP */
    case 113: /* COMMA */
    case 114: /* DBL_AMP */
    case 115: /* NOT */
    case 116: /* DASH */
    case 117: /* PLUS */
    case 118: /* STAR */
    case 119: /* INT_DIV */
    case 120: /* MOD */
    case 121: /* ABS */
    case 122: /* CARROT */
    case 123: /* UMINUS */
    case 124: /* PREC_4 */
    case 125: /* PREC_3 */
    case 126: /* PREC_2 */
    case 127: /* PREC_1 */
    case 128: /* PREC_0 */
    case 129: /* EOF */
    case 130: /* ERR_IO */
    case 131: /* ERR_UNKNOWN_SYMBOL */
    case 132: /* ERR_UNTERMINATED_STRING */
    case 133: /* ERR_UNTERMINATED_ASP */
    case 134: /* ERR_UNTERMINATED_LUA */
    case 135: /* ERR_UNTERMINATED_PYTHON */
    case 136: /* ERR_UNTERMINATED_F2LP */
    case 137: /* ERR_UNTERMINATED_BLK_COMMENT */
    case 138: /* ERR_SYNTAX */
    case 139: /* ERR_PAREN_MISMATCH */
    case 140: /* ARG */
    case 141: /* NOOP */
    case 142: /* CONSTANT_ID */
    case 143: /* VARIABLE_ID */
    case 144: /* OBJECT_ID */
    case 145: /* SIN */
    case 146: /* COS */
    case 147: /* TAN */
    case 148: /* HIDE */
    case 149: /* OBSERVED */
{
#line 213 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy0));								
#line 2711 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 151: /* start */
    case 152: /* statement_lst */
    case 177: /* undeclared */
{
#line 223 "bcplus/parser/detail/lemon_parser.y"
 /* Intentionally left blank */			
#line 2720 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 153: /* statement */
    case 159: /* stmt_code_blk */
    case 160: /* stmt_law */
    case 161: /* stmt_show */
    case 162: /* stmt_hide */
    case 165: /* stmt_maxafvalue */
    case 166: /* stmt_maxadditive */
{
#line 227 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy248));								
#line 2733 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 154: /* stmt_macro_def */
{
#line 248 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy495));								
#line 2740 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 155: /* stmt_constant_def */
{
#line 250 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy15));								
#line 2747 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 156: /* stmt_object_def */
{
#line 252 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy288));								
#line 2754 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 157: /* stmt_variable_def */
{
#line 254 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy267));								
#line 2761 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 158: /* stmt_sort_def */
{
#line 256 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy429));								
#line 2768 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 163: /* stmt_noconcurrency */
{
#line 266 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy505));								
#line 2775 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 164: /* stmt_strong_noconcurrency */
{
#line 268 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy10));								
#line 2782 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 167: /* stmt_query */
{
#line 274 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy490));								
#line 2789 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 168: /* rate_decl */
{
#line 3137 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy541));									
#line 2796 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 169: /* alwayst_stmt */
{
#line 3148 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy180));									
#line 2803 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 170: /* base_elem */
    case 171: /* base_elem_no_const */
    case 179: /* term */
    case 182: /* term_no_const */
    case 184: /* term_strong */
    case 185: /* term_strong_candidate */
    case 186: /* term_no_const_strong */
    case 189: /* term_integral */
    case 206: /* term_temporal */
    case 207: /* term_temporal_strong */
    case 208: /* term_temporal_strong_candidate */
    case 209: /* constant_temporal */
{
#line 310 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy115));								
#line 2821 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 172: /* constant */
    case 180: /* constant_one_const */
    case 183: /* const_anon */
{
#line 314 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy257));								
#line 2830 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 173: /* object */
    case 174: /* object_nullary */
{
#line 316 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy342));								
#line 2838 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 175: /* variable */
{
#line 320 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy45));								
#line 2845 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 176: /* lua */
{
#line 322 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy497));								
#line 2852 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 178: /* term_lst */
    case 181: /* term_no_const_lst */
{
#line 326 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy147));								
#line 2860 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 187: /* num_range */
{
#line 737 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy205));								
#line 2867 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 188: /* num_range_eval */
{
#line 739 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy21));								
#line 2874 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 190: /* term_int_eval */
{
#line 743 "bcplus/parser/detail/lemon_parser.y"
 /* Initially left Blank */				
#line 2881 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 191: /* formula */
    case 192: /* formula_base */
    case 193: /* comparison */
    case 196: /* formula_card */
    case 198: /* formula_no_const */
    case 199: /* formula_no_const_base */
    case 200: /* comparison_no_const */
    case 210: /* formula_temporal */
    case 211: /* formula_temporal_base */
    case 212: /* comparison_temporal */
    case 214: /* formula_temporal_card */
    case 215: /* head_formula */
{
#line 844 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy297));								
#line 2899 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 194: /* atomic_formula */
    case 197: /* atomic_formula_anon */
    case 201: /* atomic_formula_one_const */
    case 216: /* atomic_head_formula */
{
#line 850 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy426));								
#line 2909 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 195: /* formula_quant */
    case 213: /* formula_temporal_quant */
{
#line 852 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy101));								
#line 2917 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 202: /* quant_lst */
{
#line 1031 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy381));								
#line 2924 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 203: /* quant_op */
{
#line 1033 "bcplus/parser/detail/lemon_parser.y"
 /* Intentionally left blank */			
#line 2931 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 204: /* card_var_lst */
    case 205: /* card_var_lst_inner */
{
#line 1070 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy111));								
#line 2939 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 217: /* formula_smpl_card */
{
#line 1379 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy369));								
#line 2946 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 218: /* macro_def_lst */
{
#line 1443 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy529));                              
#line 2953 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 219: /* macro_bnd */
{
#line 1445 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy483));                              
#line 2960 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 220: /* macro_args */
{
#line 1447 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy338));                              
#line 2967 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 221: /* macro_arg */
{
#line 1449 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy75));                              
#line 2974 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 222: /* sort_lst */
{
#line 1539 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy507));							
#line 2981 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 223: /* sort */
    case 224: /* sort_id_nr */
    case 225: /* sort_nr */
    case 226: /* sort_id */
{
#line 1541 "bcplus/parser/detail/lemon_parser.y"
 /* Intentionally left blank */		
#line 2991 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 227: /* constant_bnd_lst */
    case 228: /* constant_bnd */
{
#line 1650 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy465));									
#line 2999 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 229: /* constant_dcl_lst */
{
#line 1654 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy410));									
#line 3006 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 230: /* constant_dcl_type */
{
#line 1656 "bcplus/parser/detail/lemon_parser.y"
 /* Intentionally left blank */				
#line 3013 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 231: /* attrib_spec */
{
#line 1658 "bcplus/parser/detail/lemon_parser.y"
 /* Intentionally left blank */				
#line 3020 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 232: /* object_bnd_lst */
{
#line 2431 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy486));									
#line 3027 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 233: /* object_bnd */
{
#line 2433 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy278));									
#line 3034 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 234: /* object_lst */
    case 235: /* object_spec */
{
#line 2435 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy13));									
#line 3042 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 236: /* variable_bnd_lst */
    case 237: /* variable_bnd */
{
#line 2581 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy445));									
#line 3050 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 238: /* variable_lst */
{
#line 2585 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy400));									
#line 3057 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 239: /* sort_bnd_lst */
    case 240: /* sort_bnd */
    case 241: /* sort_dcl_lst */
{
#line 2681 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy71));									
#line 3066 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 242: /* show_lst */
{
#line 2785 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy235));									
#line 3073 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 243: /* show_elem */
    case 251: /* clause_unless */
{
#line 2787 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy426));									
#line 3081 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 244: /* query_lst */
{
#line 2939 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy373).l); DEALLOC((yypminor->yy373).maxstep); DEALLOC((yypminor->yy373).label);	
#line 3088 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 245: /* query_maxstep_decl */
{
#line 2941 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy21));												
#line 3095 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 247: /* query_label_Decl */
{
#line 2943 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy0));												
#line 3102 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 248: /* clause_if */
    case 249: /* clause_after */
    case 250: /* clause_ifcons */
    case 252: /* clause_where */
{
#line 3097 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy297));									
#line 3112 "bcplus/parser/detail/lemon_parser.c"
}
      break;
    case 253: /* law_basic */
    case 254: /* law_caused */
    case 255: /* law_pcaused */
    case 256: /* law_impl */
    case 257: /* law_causes */
    case 258: /* law_increments */
    case 259: /* law_decrements */
    case 260: /* law_mcause */
    case 261: /* law_always */
    case 262: /* law_constraint */
    case 263: /* law_impossible */
    case 264: /* law_never */
    case 265: /* law_default */
    case 266: /* law_exogenous */
    case 267: /* law_inertial */
    case 268: /* law_nonexecutable */
    case 269: /* law_rigid */
    case 270: /* law_observed */
    case 271: /* law_temporal_constraint */
{
#line 3160 "bcplus/parser/detail/lemon_parser.y"
 DEALLOC((yypminor->yy248));									
#line 3137 "bcplus/parser/detail/lemon_parser.c"
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
  { 151, 2 },
  { 152, 0 },
  { 152, 2 },
  { 152, 2 },
  { 153, 1 },
  { 153, 1 },
  { 153, 1 },
  { 153, 1 },
  { 153, 1 },
  { 153, 1 },
  { 153, 1 },
  { 153, 1 },
  { 153, 1 },
  { 153, 1 },
  { 153, 1 },
  { 153, 1 },
  { 153, 1 },
  { 153, 1 },
  { 153, 1 },
  { 153, 1 },
  { 170, 1 },
  { 170, 1 },
  { 171, 1 },
  { 171, 1 },
  { 171, 1 },
  { 172, 4 },
  { 172, 1 },
  { 172, 1 },
  { 183, 1 },
  { 183, 4 },
  { 173, 4 },
  { 173, 1 },
  { 174, 1 },
  { 173, 1 },
  { 175, 1 },
  { 176, 4 },
  { 176, 1 },
  { 176, 3 },
  { 177, 4 },
  { 177, 1 },
  { 178, 1 },
  { 178, 3 },
  { 180, 4 },
  { 180, 1 },
  { 181, 1 },
  { 181, 3 },
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
  { 179, 2 },
  { 179, 2 },
  { 179, 4 },
  { 179, 4 },
  { 179, 4 },
  { 179, 3 },
  { 179, 3 },
  { 179, 3 },
  { 179, 3 },
  { 179, 3 },
  { 184, 1 },
  { 184, 1 },
  { 184, 1 },
  { 184, 1 },
  { 184, 3 },
  { 184, 1 },
  { 184, 1 },
  { 184, 1 },
  { 184, 2 },
  { 184, 2 },
  { 184, 4 },
  { 184, 4 },
  { 184, 4 },
  { 185, 2 },
  { 184, 3 },
  { 184, 3 },
  { 184, 3 },
  { 184, 3 },
  { 184, 3 },
  { 184, 3 },
  { 184, 3 },
  { 184, 3 },
  { 184, 3 },
  { 184, 3 },
  { 184, 3 },
  { 184, 3 },
  { 184, 3 },
  { 184, 3 },
  { 184, 3 },
  { 186, 1 },
  { 186, 1 },
  { 186, 1 },
  { 186, 1 },
  { 186, 3 },
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
  { 182, 1 },
  { 182, 1 },
  { 182, 1 },
  { 182, 1 },
  { 182, 3 },
  { 182, 1 },
  { 182, 1 },
  { 182, 1 },
  { 182, 1 },
  { 182, 1 },
  { 182, 1 },
  { 182, 2 },
  { 182, 2 },
  { 182, 3 },
  { 182, 3 },
  { 182, 3 },
  { 182, 3 },
  { 182, 3 },
  { 189, 1 },
  { 189, 3 },
  { 189, 1 },
  { 189, 1 },
  { 189, 1 },
  { 189, 1 },
  { 189, 1 },
  { 189, 2 },
  { 189, 2 },
  { 189, 3 },
  { 189, 3 },
  { 189, 3 },
  { 189, 3 },
  { 189, 3 },
  { 187, 3 },
  { 188, 3 },
  { 190, 1 },
  { 190, 3 },
  { 190, 2 },
  { 190, 2 },
  { 190, 3 },
  { 190, 3 },
  { 190, 3 },
  { 190, 3 },
  { 190, 3 },
  { 191, 1 },
  { 191, 3 },
  { 191, 2 },
  { 191, 2 },
  { 191, 3 },
  { 191, 3 },
  { 191, 3 },
  { 191, 3 },
  { 191, 3 },
  { 191, 3 },
  { 192, 1 },
  { 192, 1 },
  { 192, 1 },
  { 192, 1 },
  { 192, 1 },
  { 192, 1 },
  { 193, 3 },
  { 193, 3 },
  { 193, 3 },
  { 193, 3 },
  { 193, 3 },
  { 193, 3 },
  { 193, 3 },
  { 193, 3 },
  { 193, 3 },
  { 193, 3 },
  { 193, 3 },
  { 193, 3 },
  { 193, 3 },
  { 193, 3 },
  { 193, 3 },
  { 193, 3 },
  { 193, 3 },
  { 193, 3 },
  { 193, 3 },
  { 193, 3 },
  { 194, 1 },
  { 194, 2 },
  { 194, 3 },
  { 197, 1 },
  { 197, 1 },
  { 197, 2 },
  { 197, 3 },
  { 198, 1 },
  { 198, 3 },
  { 198, 2 },
  { 198, 2 },
  { 198, 3 },
  { 198, 3 },
  { 198, 3 },
  { 198, 3 },
  { 198, 3 },
  { 198, 3 },
  { 199, 1 },
  { 199, 1 },
  { 199, 1 },
  { 200, 3 },
  { 200, 3 },
  { 200, 3 },
  { 200, 3 },
  { 200, 3 },
  { 200, 3 },
  { 200, 3 },
  { 201, 1 },
  { 201, 2 },
  { 201, 3 },
  { 195, 5 },
  { 202, 2 },
  { 202, 3 },
  { 203, 1 },
  { 203, 1 },
  { 196, 4 },
  { 196, 5 },
  { 196, 5 },
  { 196, 6 },
  { 196, 3 },
  { 196, 4 },
  { 196, 4 },
  { 196, 5 },
  { 204, 2 },
  { 205, 1 },
  { 205, 3 },
  { 206, 1 },
  { 206, 1 },
  { 206, 1 },
  { 206, 1 },
  { 206, 3 },
  { 206, 1 },
  { 206, 1 },
  { 206, 1 },
  { 206, 1 },
  { 206, 1 },
  { 206, 1 },
  { 206, 2 },
  { 206, 2 },
  { 206, 3 },
  { 206, 3 },
  { 206, 3 },
  { 206, 3 },
  { 206, 3 },
  { 206, 3 },
  { 207, 1 },
  { 207, 1 },
  { 207, 1 },
  { 207, 1 },
  { 207, 3 },
  { 207, 1 },
  { 207, 1 },
  { 207, 1 },
  { 207, 3 },
  { 207, 2 },
  { 207, 2 },
  { 207, 3 },
  { 207, 3 },
  { 207, 3 },
  { 207, 3 },
  { 207, 3 },
  { 210, 1 },
  { 210, 3 },
  { 210, 2 },
  { 210, 2 },
  { 210, 3 },
  { 210, 3 },
  { 210, 3 },
  { 210, 3 },
  { 210, 3 },
  { 210, 3 },
  { 210, 3 },
  { 211, 1 },
  { 211, 1 },
  { 211, 1 },
  { 211, 1 },
  { 211, 1 },
  { 211, 1 },
  { 212, 3 },
  { 212, 3 },
  { 212, 3 },
  { 212, 3 },
  { 212, 3 },
  { 212, 3 },
  { 212, 3 },
  { 213, 5 },
  { 214, 4 },
  { 214, 5 },
  { 214, 5 },
  { 214, 6 },
  { 214, 3 },
  { 214, 4 },
  { 214, 4 },
  { 214, 5 },
  { 215, 3 },
  { 215, 3 },
  { 215, 1 },
  { 215, 1 },
  { 215, 1 },
  { 215, 1 },
  { 215, 1 },
  { 216, 1 },
  { 216, 2 },
  { 217, 4 },
  { 217, 5 },
  { 217, 5 },
  { 217, 6 },
  { 217, 3 },
  { 217, 4 },
  { 217, 4 },
  { 217, 5 },
  { 154, 4 },
  { 218, 1 },
  { 218, 3 },
  { 219, 6 },
  { 219, 3 },
  { 220, 1 },
  { 220, 3 },
  { 221, 1 },
  { 221, 1 },
  { 222, 1 },
  { 222, 3 },
  { 223, 1 },
  { 223, 2 },
  { 223, 2 },
  { 223, 3 },
  { 223, 3 },
  { 223, 3 },
  { 224, 1 },
  { 224, 1 },
  { 225, 1 },
  { 226, 1 },
  { 155, 4 },
  { 227, 1 },
  { 227, 3 },
  { 228, 6 },
  { 228, 9 },
  { 228, 9 },
  { 228, 6 },
  { 228, 3 },
  { 228, 6 },
  { 228, 6 },
  { 228, 3 },
  { 228, 5 },
  { 228, 8 },
  { 229, 1 },
  { 229, 4 },
  { 229, 3 },
  { 229, 6 },
  { 230, 1 },
  { 230, 1 },
  { 230, 1 },
  { 230, 1 },
  { 230, 1 },
  { 230, 1 },
  { 230, 1 },
  { 230, 1 },
  { 230, 1 },
  { 230, 1 },
  { 230, 1 },
  { 231, 1 },
  { 231, 4 },
  { 231, 7 },
  { 231, 7 },
  { 156, 4 },
  { 232, 1 },
  { 232, 3 },
  { 233, 3 },
  { 234, 1 },
  { 234, 3 },
  { 235, 1 },
  { 235, 4 },
  { 235, 1 },
  { 235, 1 },
  { 235, 1 },
  { 157, 4 },
  { 236, 1 },
  { 236, 3 },
  { 237, 3 },
  { 237, 1 },
  { 238, 1 },
  { 238, 3 },
  { 158, 4 },
  { 239, 1 },
  { 239, 3 },
  { 240, 1 },
  { 240, 3 },
  { 240, 3 },
  { 240, 3 },
  { 241, 1 },
  { 241, 3 },
  { 161, 4 },
  { 161, 4 },
  { 162, 4 },
  { 162, 4 },
  { 242, 1 },
  { 242, 3 },
  { 242, 3 },
  { 243, 1 },
  { 163, 2 },
  { 164, 2 },
  { 165, 5 },
  { 165, 5 },
  { 166, 5 },
  { 166, 5 },
  { 167, 4 },
  { 244, 1 },
  { 244, 1 },
  { 244, 1 },
  { 244, 3 },
  { 244, 3 },
  { 244, 3 },
  { 245, 3 },
  { 245, 3 },
  { 246, 3 },
  { 246, 3 },
  { 248, 2 },
  { 248, 0 },
  { 249, 2 },
  { 249, 0 },
  { 250, 2 },
  { 250, 0 },
  { 251, 2 },
  { 251, 0 },
  { 252, 2 },
  { 252, 0 },
  { 168, 10 },
  { 169, 7 },
  { 160, 1 },
  { 160, 1 },
  { 160, 1 },
  { 160, 1 },
  { 160, 1 },
  { 160, 1 },
  { 160, 1 },
  { 160, 1 },
  { 160, 1 },
  { 160, 1 },
  { 160, 1 },
  { 160, 1 },
  { 160, 1 },
  { 160, 1 },
  { 160, 1 },
  { 160, 1 },
  { 160, 1 },
  { 160, 1 },
  { 160, 1 },
  { 253, 7 },
  { 254, 8 },
  { 255, 8 },
  { 256, 5 },
  { 256, 4 },
  { 257, 7 },
  { 258, 9 },
  { 259, 9 },
  { 260, 7 },
  { 261, 6 },
  { 262, 6 },
  { 263, 6 },
  { 264, 6 },
  { 265, 8 },
  { 266, 8 },
  { 267, 8 },
  { 268, 6 },
  { 269, 4 },
  { 270, 5 },
  { 271, 5 },
  { 159, 1 },
  { 159, 1 },
  { 159, 1 },
  { 159, 1 },
  { 159, 1 },
  { 159, 1 },
  { 159, 1 },
  { 159, 1 },
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
#line 229 "bcplus/parser/detail/lemon_parser.y"
{
  yy_destructor(yypParser,129,&yymsp[0].minor);
}
#line 3927 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 3: /* statement_lst ::= statement_lst statement */
#line 234 "bcplus/parser/detail/lemon_parser.y"
{
			ref_ptr<Statement> ptr = yymsp[0].minor.yy248;
			yymsp[0].minor.yy248  = NULL;
			parser->_handle_stmt(ptr);
		}
#line 3936 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 4: /* statement ::= stmt_macro_def */
#line 277 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy248 = yymsp[0].minor.yy495; }
#line 3941 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 5: /* statement ::= stmt_constant_def */
#line 278 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy248 = yymsp[0].minor.yy15; }
#line 3946 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 6: /* statement ::= stmt_object_def */
#line 279 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy248 = yymsp[0].minor.yy288; }
#line 3951 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 7: /* statement ::= stmt_variable_def */
#line 280 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy248 = yymsp[0].minor.yy267; }
#line 3956 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 8: /* statement ::= stmt_sort_def */
#line 281 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy248 = yymsp[0].minor.yy429; }
#line 3961 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 9: /* statement ::= stmt_code_blk */
      case 10: /* statement ::= stmt_law */ yytestcase(yyruleno==10);
      case 13: /* statement ::= stmt_show */ yytestcase(yyruleno==13);
      case 14: /* statement ::= stmt_hide */ yytestcase(yyruleno==14);
      case 17: /* statement ::= stmt_maxafvalue */ yytestcase(yyruleno==17);
      case 18: /* statement ::= stmt_maxadditive */ yytestcase(yyruleno==18);
#line 282 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy248 = yymsp[0].minor.yy248; }
#line 3971 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 11: /* statement ::= rate_decl */
#line 284 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy248 = yymsp[0].minor.yy541; }
#line 3976 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 12: /* statement ::= alwayst_stmt */
#line 285 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy248 = yymsp[0].minor.yy180; }
#line 3981 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 15: /* statement ::= stmt_noconcurrency */
#line 288 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy248 = yymsp[0].minor.yy505; }
#line 3986 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 16: /* statement ::= stmt_strong_noconcurrency */
#line 289 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy248 = yymsp[0].minor.yy10; }
#line 3991 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 19: /* statement ::= stmt_query */
#line 292 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy248 = yymsp[0].minor.yy490; }
#line 3996 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 20: /* base_elem ::= constant */
#line 338 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy115 = yymsp[0].minor.yy257;}
#line 4001 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 21: /* base_elem ::= base_elem_no_const */
#line 339 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy115 = yymsp[0].minor.yy115;}
#line 4006 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 22: /* base_elem_no_const ::= object */
#line 341 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy115 = yymsp[0].minor.yy342;	}
#line 4011 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 23: /* base_elem_no_const ::= variable */
#line 342 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy115 = yymsp[0].minor.yy45; }
#line 4016 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 24: /* base_elem_no_const ::= lua */
#line 343 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy115 = yymsp[0].minor.yy497; }
#line 4021 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 25: /* constant ::= CONSTANT_ID PAREN_L term_lst PAREN_R */
      case 42: /* constant_one_const ::= CONSTANT_ID PAREN_L term_no_const_lst PAREN_R */ yytestcase(yyruleno==42);
#line 470 "bcplus/parser/detail/lemon_parser.y"
{ BASE_ELEM_DEF(yygotominor.yy257, yymsp[-3].minor.yy0, yymsp[-2].minor.yy0, yymsp[-1].minor.yy147, yymsp[0].minor.yy0, Symbol::Type::CONSTANT, Constant, ConstantSymbol);	}
#line 4027 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 26: /* constant ::= CONSTANT_ID */
      case 27: /* constant ::= MODE */ yytestcase(yyruleno==27);
      case 43: /* constant_one_const ::= CONSTANT_ID */ yytestcase(yyruleno==43);
#line 471 "bcplus/parser/detail/lemon_parser.y"
{ BASE_ELEM_DEF(yygotominor.yy257, yymsp[0].minor.yy0, NULL, NULL, NULL, Symbol::Type::CONSTANT, Constant, ConstantSymbol); }
#line 4034 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 28: /* const_anon ::= IDENTIFIER */
#line 474 "bcplus/parser/detail/lemon_parser.y"
{ BASE_ELEM_DEF9(yygotominor.yy257, yymsp[0].minor.yy0, NULL, NULL, NULL, Symbol::Type::CONSTANT, Constant, ConstantSymbol, true); }
#line 4039 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 29: /* const_anon ::= IDENTIFIER PAREN_L term_lst PAREN_R */
#line 475 "bcplus/parser/detail/lemon_parser.y"
{ BASE_ELEM_DEF9(yygotominor.yy257, yymsp[-3].minor.yy0, yymsp[-2].minor.yy0, yymsp[-1].minor.yy147, yymsp[0].minor.yy0, Symbol::Type::CONSTANT, Constant, ConstantSymbol, true);	}
#line 4044 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 30: /* object ::= OBJECT_ID PAREN_L term_lst PAREN_R */
#line 478 "bcplus/parser/detail/lemon_parser.y"
{ BASE_ELEM_DEF(yygotominor.yy342, yymsp[-3].minor.yy0, yymsp[-2].minor.yy0, yymsp[-1].minor.yy147, yymsp[0].minor.yy0, Symbol::Type::OBJECT, Object, ObjectSymbol);	}
#line 4049 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 31: /* object ::= object_nullary */
#line 479 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy342 = yymsp[0].minor.yy342; }
#line 4054 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 32: /* object_nullary ::= OBJECT_ID */
#line 480 "bcplus/parser/detail/lemon_parser.y"
{ BASE_ELEM_DEF(yygotominor.yy342, yymsp[0].minor.yy0, NULL, NULL, NULL, Symbol::Type::OBJECT, Object, ObjectSymbol); }
#line 4059 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 33: /* object ::= undeclared */
#line 481 "bcplus/parser/detail/lemon_parser.y"
{ /* never called */ }
#line 4064 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 34: /* variable ::= VARIABLE_ID */
#line 484 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy45 = NULL;
		ref_ptr<const Token> id_ptr = yymsp[0].minor.yy0;

		if (!parser->lang()->support(Language::Feature::VARIABLE)) {
			parser->_feature_error(Language::Feature::VARIABLE, &yymsp[0].minor.yy0->beginLoc());
			YYERROR;
		} else {
			BASE_ELEM_BARE_DEF(yygotominor.yy45, yymsp[0].minor.yy0, Symbol::Type::VARIABLE, Variable, VariableSymbol);
		}
	}
#line 4079 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 35: /* lua ::= AT_IDENTIFIER PAREN_L term_lst PAREN_R */
#line 495 "bcplus/parser/detail/lemon_parser.y"
{ BASE_LUA_ELEM(yygotominor.yy497, yymsp[-3].minor.yy0, yymsp[-2].minor.yy0, yymsp[-1].minor.yy147, yymsp[0].minor.yy0); }
#line 4084 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 36: /* lua ::= AT_IDENTIFIER */
#line 496 "bcplus/parser/detail/lemon_parser.y"
{ BASE_LUA_ELEM(yygotominor.yy497, yymsp[0].minor.yy0, NULL, NULL, NULL); }
#line 4089 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 37: /* lua ::= AT_IDENTIFIER PAREN_L PAREN_R */
#line 497 "bcplus/parser/detail/lemon_parser.y"
{ BASE_LUA_ELEM(yygotominor.yy497, yymsp[-2].minor.yy0, yymsp[-1].minor.yy0, NULL, yymsp[0].minor.yy0); }
#line 4094 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 38: /* undeclared ::= IDENTIFIER PAREN_L term_lst PAREN_R */
#line 500 "bcplus/parser/detail/lemon_parser.y"
{ UNDECLARED(yygotominor.yy113, yymsp[-3].minor.yy0, yymsp[-1].minor.yy147);   yy_destructor(yypParser,82,&yymsp[-2].minor);
  yy_destructor(yypParser,83,&yymsp[0].minor);
}
#line 4101 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 39: /* undeclared ::= IDENTIFIER */
#line 501 "bcplus/parser/detail/lemon_parser.y"
{ UNDECLARED(yygotominor.yy113, yymsp[0].minor.yy0, NULL); }
#line 4106 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 40: /* term_lst ::= term */
      case 44: /* term_no_const_lst ::= term_no_const */ yytestcase(yyruleno==44);
#line 504 "bcplus/parser/detail/lemon_parser.y"
{
			yygotominor.yy147 = new TermList();
			yygotominor.yy147->push_back(yymsp[0].minor.yy115);
		}
#line 4115 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 41: /* term_lst ::= term_lst COMMA term */
      case 45: /* term_no_const_lst ::= term_no_const_lst COMMA term_no_const */ yytestcase(yyruleno==45);
#line 510 "bcplus/parser/detail/lemon_parser.y"
{
			yygotominor.yy147 = yymsp[-2].minor.yy147;
			yymsp[-2].minor.yy147->push_back(yymsp[0].minor.yy115);
		  yy_destructor(yypParser,113,&yymsp[-1].minor);
}
#line 4125 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 46: /* term ::= base_elem */
      case 66: /* term_strong ::= base_elem_no_const */ yytestcase(yyruleno==66);
      case 95: /* term_no_const_strong ::= base_elem_no_const */ yytestcase(yyruleno==95);
      case 111: /* term_no_const ::= base_elem_no_const */ yytestcase(yyruleno==111);
      case 236: /* term_temporal ::= base_elem_no_const */ yytestcase(yyruleno==236);
      case 255: /* term_temporal_strong ::= base_elem_no_const */ yytestcase(yyruleno==255);
#line 594 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy115 = yymsp[0].minor.yy115; }
#line 4135 "bcplus/parser/detail/lemon_parser.c"
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
#line 595 "bcplus/parser/detail/lemon_parser.y"
{ BASIC_TERM(yygotominor.yy115, yymsp[0].minor.yy0);	}
#line 4152 "bcplus/parser/detail/lemon_parser.c"
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
#line 597 "bcplus/parser/detail/lemon_parser.y"
{ BASIC_TERM(yygotominor.yy115, yymsp[0].minor.yy0); }
#line 4170 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 50: /* term ::= PAREN_L term PAREN_R */
      case 70: /* term_strong ::= PAREN_L term_strong PAREN_R */ yytestcase(yyruleno==70);
      case 99: /* term_no_const_strong ::= PAREN_L term_no_const_strong PAREN_R */ yytestcase(yyruleno==99);
      case 115: /* term_no_const ::= PAREN_L term_no_const PAREN_R */ yytestcase(yyruleno==115);
      case 130: /* term_integral ::= PAREN_L term_integral PAREN_R */ yytestcase(yyruleno==130);
      case 240: /* term_temporal ::= PAREN_L term_temporal PAREN_R */ yytestcase(yyruleno==240);
      case 259: /* term_temporal_strong ::= PAREN_L term_temporal_strong PAREN_R */ yytestcase(yyruleno==259);
#line 598 "bcplus/parser/detail/lemon_parser.y"
{ TERM_PARENS(yygotominor.yy115, yymsp[-2].minor.yy0, yymsp[-1].minor.yy115, yymsp[0].minor.yy0); }
#line 4181 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 53: /* term ::= MAXSTEP */
      case 71: /* term_strong ::= MAXSTEP */ yytestcase(yyruleno==71);
      case 100: /* term_no_const_strong ::= MAXSTEP */ yytestcase(yyruleno==100);
      case 118: /* term_no_const ::= MAXSTEP */ yytestcase(yyruleno==118);
      case 133: /* term_integral ::= MAXSTEP */ yytestcase(yyruleno==133);
      case 243: /* term_temporal ::= MAXSTEP */ yytestcase(yyruleno==243);
      case 260: /* term_temporal_strong ::= MAXSTEP */ yytestcase(yyruleno==260);
#line 601 "bcplus/parser/detail/lemon_parser.y"
{ NULLARY_TERM(yygotominor.yy115, yymsp[0].minor.yy0, Language::Feature::MAXSTEP, NullaryTerm::Operator::MAXSTEP); }
#line 4192 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 54: /* term ::= MAXADDITIVE */
      case 72: /* term_strong ::= MAXADDITIVE */ yytestcase(yyruleno==72);
      case 101: /* term_no_const_strong ::= MAXADDITIVE */ yytestcase(yyruleno==101);
      case 119: /* term_no_const ::= MAXADDITIVE */ yytestcase(yyruleno==119);
      case 134: /* term_integral ::= MAXADDITIVE */ yytestcase(yyruleno==134);
      case 244: /* term_temporal ::= MAXADDITIVE */ yytestcase(yyruleno==244);
      case 261: /* term_temporal_strong ::= MAXADDITIVE */ yytestcase(yyruleno==261);
#line 602 "bcplus/parser/detail/lemon_parser.y"
{ NULLARY_TERM(yygotominor.yy115, yymsp[0].minor.yy0, Language::Feature::MAXADDITIVE, NullaryTerm::Operator::MAXADDITIVE); }
#line 4203 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 55: /* term ::= MAXAFVALUE */
      case 73: /* term_strong ::= MAXAFVALUE */ yytestcase(yyruleno==73);
      case 102: /* term_no_const_strong ::= MAXAFVALUE */ yytestcase(yyruleno==102);
      case 120: /* term_no_const ::= MAXAFVALUE */ yytestcase(yyruleno==120);
      case 135: /* term_integral ::= MAXAFVALUE */ yytestcase(yyruleno==135);
      case 245: /* term_temporal ::= MAXAFVALUE */ yytestcase(yyruleno==245);
      case 262: /* term_temporal_strong ::= MAXAFVALUE */ yytestcase(yyruleno==262);
#line 603 "bcplus/parser/detail/lemon_parser.y"
{ NULLARY_TERM(yygotominor.yy115, yymsp[0].minor.yy0, Language::Feature::MAXAFVALUE, NullaryTerm::Operator::MAXAFVALUE); }
#line 4214 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 56: /* term ::= DASH term */
      case 74: /* term_strong ::= DASH term_strong */ yytestcase(yyruleno==74);
      case 104: /* term_no_const_strong ::= DASH term_no_const_strong */ yytestcase(yyruleno==104);
      case 122: /* term_no_const ::= DASH term_no_const */ yytestcase(yyruleno==122);
      case 136: /* term_integral ::= DASH term_integral */ yytestcase(yyruleno==136);
      case 247: /* term_temporal ::= DASH term_temporal */ yytestcase(yyruleno==247);
      case 264: /* term_temporal_strong ::= DASH term_temporal_strong */ yytestcase(yyruleno==264);
#line 607 "bcplus/parser/detail/lemon_parser.y"
{ UNARY_ARITH(yygotominor.yy115, yymsp[-1].minor.yy0, yymsp[0].minor.yy115, UnaryTerm::Operator::NEGATIVE); }
#line 4225 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 57: /* term ::= ABS term */
      case 75: /* term_strong ::= ABS term */ yytestcase(yyruleno==75);
      case 105: /* term_no_const_strong ::= ABS term_no_const */ yytestcase(yyruleno==105);
      case 123: /* term_no_const ::= ABS term_no_const */ yytestcase(yyruleno==123);
      case 137: /* term_integral ::= ABS term_integral */ yytestcase(yyruleno==137);
      case 248: /* term_temporal ::= ABS term_temporal */ yytestcase(yyruleno==248);
      case 265: /* term_temporal_strong ::= ABS term_temporal */ yytestcase(yyruleno==265);
#line 608 "bcplus/parser/detail/lemon_parser.y"
{ UNARY_ARITH(yygotominor.yy115, yymsp[-1].minor.yy0, yymsp[0].minor.yy115, UnaryTerm::Operator::ABS); }
#line 4236 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 58: /* term ::= SIN PAREN_L term PAREN_R */
      case 76: /* term_strong ::= SIN PAREN_L term PAREN_R */ yytestcase(yyruleno==76);
#line 609 "bcplus/parser/detail/lemon_parser.y"
{ UNARY_ARITH(yygotominor.yy115, yymsp[-3].minor.yy0, yymsp[-1].minor.yy115, UnaryTerm::Operator::SIN);   yy_destructor(yypParser,82,&yymsp[-2].minor);
  yy_destructor(yypParser,83,&yymsp[0].minor);
}
#line 4244 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 59: /* term ::= COS PAREN_L term PAREN_R */
      case 77: /* term_strong ::= COS PAREN_L term PAREN_R */ yytestcase(yyruleno==77);
#line 610 "bcplus/parser/detail/lemon_parser.y"
{ UNARY_ARITH(yygotominor.yy115, yymsp[-3].minor.yy0, yymsp[-1].minor.yy115, UnaryTerm::Operator::COS);   yy_destructor(yypParser,82,&yymsp[-2].minor);
  yy_destructor(yypParser,83,&yymsp[0].minor);
}
#line 4252 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 60: /* term ::= TAN PAREN_L term PAREN_R */
      case 78: /* term_strong ::= TAN PAREN_L term PAREN_R */ yytestcase(yyruleno==78);
#line 611 "bcplus/parser/detail/lemon_parser.y"
{ UNARY_ARITH(yygotominor.yy115, yymsp[-3].minor.yy0, yymsp[-1].minor.yy115, UnaryTerm::Operator::TAN);   yy_destructor(yypParser,82,&yymsp[-2].minor);
  yy_destructor(yypParser,83,&yymsp[0].minor);
}
#line 4260 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 61: /* term ::= term DASH term */
      case 80: /* term_strong ::= term_strong_candidate DASH term */ yytestcase(yyruleno==80);
      case 90: /* term_strong ::= term_strong DASH term */ yytestcase(yyruleno==90);
      case 106: /* term_no_const_strong ::= term_no_const_strong DASH term_no_const */ yytestcase(yyruleno==106);
      case 124: /* term_no_const ::= term_no_const DASH term_no_const */ yytestcase(yyruleno==124);
      case 138: /* term_integral ::= term_integral DASH term_integral */ yytestcase(yyruleno==138);
      case 250: /* term_temporal ::= term_temporal DASH term_temporal */ yytestcase(yyruleno==250);
      case 266: /* term_temporal_strong ::= term_temporal_strong DASH term_temporal */ yytestcase(yyruleno==266);
#line 615 "bcplus/parser/detail/lemon_parser.y"
{ BINARY_ARITH(yygotominor.yy115, yymsp[-2].minor.yy115, yymsp[-1].minor.yy0, yymsp[0].minor.yy115, BinaryTerm::Operator::MINUS); }
#line 4272 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 62: /* term ::= term PLUS term */
      case 81: /* term_strong ::= term_strong_candidate PLUS term */ yytestcase(yyruleno==81);
      case 91: /* term_strong ::= term_strong PLUS term */ yytestcase(yyruleno==91);
      case 107: /* term_no_const_strong ::= term_no_const_strong PLUS term_no_const */ yytestcase(yyruleno==107);
      case 125: /* term_no_const ::= term_no_const PLUS term_no_const */ yytestcase(yyruleno==125);
      case 139: /* term_integral ::= term_integral PLUS term_integral */ yytestcase(yyruleno==139);
      case 251: /* term_temporal ::= term_temporal PLUS term_temporal */ yytestcase(yyruleno==251);
      case 267: /* term_temporal_strong ::= term_temporal_strong PLUS term_temporal */ yytestcase(yyruleno==267);
#line 616 "bcplus/parser/detail/lemon_parser.y"
{ BINARY_ARITH(yygotominor.yy115, yymsp[-2].minor.yy115, yymsp[-1].minor.yy0, yymsp[0].minor.yy115, BinaryTerm::Operator::PLUS); }
#line 4284 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 63: /* term ::= term STAR term */
      case 82: /* term_strong ::= term_strong_candidate STAR term */ yytestcase(yyruleno==82);
      case 92: /* term_strong ::= term_strong STAR term */ yytestcase(yyruleno==92);
      case 108: /* term_no_const_strong ::= term_no_const_strong STAR term_no_const */ yytestcase(yyruleno==108);
      case 126: /* term_no_const ::= term_no_const STAR term_no_const */ yytestcase(yyruleno==126);
      case 140: /* term_integral ::= term_integral STAR term_integral */ yytestcase(yyruleno==140);
      case 252: /* term_temporal ::= term_temporal STAR term_temporal */ yytestcase(yyruleno==252);
      case 268: /* term_temporal_strong ::= term_temporal_strong STAR term_temporal */ yytestcase(yyruleno==268);
#line 617 "bcplus/parser/detail/lemon_parser.y"
{ BINARY_ARITH(yygotominor.yy115, yymsp[-2].minor.yy115, yymsp[-1].minor.yy0, yymsp[0].minor.yy115, BinaryTerm::Operator::TIMES); }
#line 4296 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 64: /* term ::= term INT_DIV term */
      case 83: /* term_strong ::= term_strong_candidate INT_DIV term */ yytestcase(yyruleno==83);
      case 93: /* term_strong ::= term_strong INT_DIV term */ yytestcase(yyruleno==93);
      case 109: /* term_no_const_strong ::= term_no_const_strong INT_DIV term_no_const */ yytestcase(yyruleno==109);
      case 127: /* term_no_const ::= term_no_const INT_DIV term_no_const */ yytestcase(yyruleno==127);
      case 141: /* term_integral ::= term_integral INT_DIV term_integral */ yytestcase(yyruleno==141);
      case 253: /* term_temporal ::= term_temporal INT_DIV term_temporal */ yytestcase(yyruleno==253);
      case 269: /* term_temporal_strong ::= term_temporal_strong INT_DIV term_temporal */ yytestcase(yyruleno==269);
#line 618 "bcplus/parser/detail/lemon_parser.y"
{ BINARY_ARITH(yygotominor.yy115, yymsp[-2].minor.yy115, yymsp[-1].minor.yy0, yymsp[0].minor.yy115, BinaryTerm::Operator::DIVIDE); }
#line 4308 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 65: /* term ::= term MOD term */
      case 84: /* term_strong ::= term_strong_candidate MOD term */ yytestcase(yyruleno==84);
      case 94: /* term_strong ::= term_strong MOD term */ yytestcase(yyruleno==94);
      case 110: /* term_no_const_strong ::= term_no_const_strong MOD term_no_const */ yytestcase(yyruleno==110);
      case 128: /* term_no_const ::= term_no_const MOD term_no_const */ yytestcase(yyruleno==128);
      case 142: /* term_integral ::= term_integral MOD term_integral */ yytestcase(yyruleno==142);
      case 254: /* term_temporal ::= term_temporal MOD term_temporal */ yytestcase(yyruleno==254);
      case 270: /* term_temporal_strong ::= term_temporal_strong MOD term_temporal */ yytestcase(yyruleno==270);
#line 619 "bcplus/parser/detail/lemon_parser.y"
{ BINARY_ARITH(yygotominor.yy115, yymsp[-2].minor.yy115, yymsp[-1].minor.yy0, yymsp[0].minor.yy115, BinaryTerm::Operator::MOD); }
#line 4320 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 79: /* term_strong_candidate ::= DASH constant */
#line 642 "bcplus/parser/detail/lemon_parser.y"
{ UNARY_ARITH(yygotominor.yy115, yymsp[-1].minor.yy0, yymsp[0].minor.yy257, UnaryTerm::Operator::NEGATIVE); }
#line 4325 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 85: /* term_strong ::= constant DASH term */
#line 651 "bcplus/parser/detail/lemon_parser.y"
{ BINARY_ARITH(yygotominor.yy115, yymsp[-2].minor.yy257, yymsp[-1].minor.yy0, yymsp[0].minor.yy115, BinaryTerm::Operator::MINUS); }
#line 4330 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 86: /* term_strong ::= constant PLUS term */
#line 652 "bcplus/parser/detail/lemon_parser.y"
{ BINARY_ARITH(yygotominor.yy115, yymsp[-2].minor.yy257, yymsp[-1].minor.yy0, yymsp[0].minor.yy115, BinaryTerm::Operator::PLUS); }
#line 4335 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 87: /* term_strong ::= constant STAR term */
#line 653 "bcplus/parser/detail/lemon_parser.y"
{ BINARY_ARITH(yygotominor.yy115, yymsp[-2].minor.yy257, yymsp[-1].minor.yy0, yymsp[0].minor.yy115, BinaryTerm::Operator::TIMES); }
#line 4340 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 88: /* term_strong ::= constant INT_DIV term */
#line 654 "bcplus/parser/detail/lemon_parser.y"
{ BINARY_ARITH(yygotominor.yy115, yymsp[-2].minor.yy257, yymsp[-1].minor.yy0, yymsp[0].minor.yy115, BinaryTerm::Operator::DIVIDE); }
#line 4345 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 89: /* term_strong ::= constant MOD term */
#line 655 "bcplus/parser/detail/lemon_parser.y"
{ BINARY_ARITH(yygotominor.yy115, yymsp[-2].minor.yy257, yymsp[-1].minor.yy0, yymsp[0].minor.yy115, BinaryTerm::Operator::MOD); }
#line 4350 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 103: /* term_no_const_strong ::= constant */
#line 678 "bcplus/parser/detail/lemon_parser.y"
{
		// error handling for constants so they don'yygotominor.yy115 default to undeclared identifiers
		yygotominor.yy115 = NULL;
		ref_ptr<const Referenced> c_ptr = yymsp[0].minor.yy257;
		parser->_parse_error("Encountered unexpected constant symbol.", &yymsp[0].minor.yy257->beginLoc());
		YYERROR;
	}
#line 4361 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 121: /* term_no_const ::= constant */
#line 712 "bcplus/parser/detail/lemon_parser.y"
{
		// error handline for constants so they don'yygotominor.yy115 default to undeclared identifiers
		yygotominor.yy115 = NULL;
		ref_ptr<const Referenced> c_ptr = yymsp[0].minor.yy257;
		parser->_parse_error("Encountered unexpected constant symbol.", &yymsp[0].minor.yy257->beginLoc());
		YYERROR;
	}
#line 4372 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 143: /* num_range ::= term_integral DBL_PERIOD term_integral */
#line 769 "bcplus/parser/detail/lemon_parser.y"
{
	ref_ptr<const Referenced> l_ptr = yymsp[-2].minor.yy115, r_ptr = yymsp[0].minor.yy115, s_ptr = yymsp[-1].minor.yy0;
	yygotominor.yy205 = NULL;

	if (yymsp[-2].minor.yy115->domainType() != DomainType::INTEGRAL) {
		parser->_parse_error("Number ranges cannot have non-numeric operands.", &yymsp[-1].minor.yy0->beginLoc());
		YYERROR;
	}

	if (yymsp[0].minor.yy115->domainType() != DomainType::INTEGRAL) {
		parser->_parse_error("Number ranges cannot have non-numeric operands.", &yymsp[0].minor.yy115->beginLoc());
		YYERROR;
	}

	yygotominor.yy205 = new NumberRange(yymsp[-2].minor.yy115, yymsp[0].minor.yy115, yymsp[-2].minor.yy115->beginLoc(), yymsp[0].minor.yy115->endLoc());
}
#line 4392 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 144: /* num_range_eval ::= term_int_eval DBL_PERIOD term_int_eval */
#line 787 "bcplus/parser/detail/lemon_parser.y"
{
	ref_ptr<const Referenced> l_ptr = yymsp[-2].minor.yy289, r_ptr = yymsp[0].minor.yy289, s_ptr = yymsp[-1].minor.yy0;
	yygotominor.yy21 = new NumberRangeEval(yymsp[-2].minor.yy289->val(), yymsp[0].minor.yy289->val(), yymsp[-2].minor.yy289->beginLoc(), yymsp[0].minor.yy289->endLoc());
}
#line 4400 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 145: /* term_int_eval ::= INTEGER */
#line 793 "bcplus/parser/detail/lemon_parser.y"
{
	ref_ptr<const Referenced> i_ptr = yymsp[0].minor.yy0;

	yygotominor.yy289 = 0;
	try {
		yygotominor.yy289 = new Number(boost::lexical_cast<int>(*yymsp[0].minor.yy0->str()), yymsp[0].minor.yy0->beginLoc());
	} catch (boost::bad_lexical_cast const& e) {
	parser->_parse_error("INTERNAL ERROR: Failed to parse integer \"" + *yymsp[0].minor.yy0->str() + "\".", &yymsp[0].minor.yy0->beginLoc());
		YYERROR;
	}
}
#line 4415 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 146: /* term_int_eval ::= PAREN_L term_int_eval PAREN_R */
#line 805 "bcplus/parser/detail/lemon_parser.y"
{
	ref_ptr<const Referenced> pl_ptr = yymsp[-2].minor.yy0, pr_ptr = yymsp[0].minor.yy0;
	yygotominor.yy289 = yymsp[-1].minor.yy289;
	yygotominor.yy289->beginLoc(yymsp[-2].minor.yy0->beginLoc());
	yygotominor.yy289->endLoc(yymsp[0].minor.yy0->endLoc());
}
#line 4425 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 147: /* term_int_eval ::= DASH term_int_eval */
#line 825 "bcplus/parser/detail/lemon_parser.y"
{ NUM_UOP(yygotominor.yy289, yymsp[0].minor.yy289, -1 * yymsp[0].minor.yy289->val());   yy_destructor(yypParser,116,&yymsp[-1].minor);
}
#line 4431 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 148: /* term_int_eval ::= ABS term_int_eval */
#line 826 "bcplus/parser/detail/lemon_parser.y"
{ NUM_UOP(yygotominor.yy289, yymsp[0].minor.yy289, yymsp[0].minor.yy289->val() < 0 ? - yymsp[0].minor.yy289->val() : yymsp[0].minor.yy289->val());   yy_destructor(yypParser,121,&yymsp[-1].minor);
}
#line 4437 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 149: /* term_int_eval ::= term_int_eval DASH term_int_eval */
#line 828 "bcplus/parser/detail/lemon_parser.y"
{ NUM_BOP(yygotominor.yy289, yymsp[-2].minor.yy289, yymsp[0].minor.yy289, yymsp[-2].minor.yy289->val() - yymsp[0].minor.yy289->val());   yy_destructor(yypParser,116,&yymsp[-1].minor);
}
#line 4443 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 150: /* term_int_eval ::= term_int_eval PLUS term_int_eval */
#line 829 "bcplus/parser/detail/lemon_parser.y"
{ NUM_BOP(yygotominor.yy289, yymsp[-2].minor.yy289, yymsp[0].minor.yy289, yymsp[-2].minor.yy289->val() + yymsp[0].minor.yy289->val());   yy_destructor(yypParser,117,&yymsp[-1].minor);
}
#line 4449 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 151: /* term_int_eval ::= term_int_eval STAR term_int_eval */
#line 830 "bcplus/parser/detail/lemon_parser.y"
{ NUM_BOP(yygotominor.yy289, yymsp[-2].minor.yy289, yymsp[0].minor.yy289, yymsp[-2].minor.yy289->val() * yymsp[0].minor.yy289->val());   yy_destructor(yypParser,118,&yymsp[-1].minor);
}
#line 4455 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 152: /* term_int_eval ::= term_int_eval INT_DIV term_int_eval */
#line 831 "bcplus/parser/detail/lemon_parser.y"
{ NUM_BOP(yygotominor.yy289, yymsp[-2].minor.yy289, yymsp[0].minor.yy289, yymsp[-2].minor.yy289->val() / yymsp[0].minor.yy289->val());   yy_destructor(yypParser,119,&yymsp[-1].minor);
}
#line 4461 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 153: /* term_int_eval ::= term_int_eval MOD term_int_eval */
#line 832 "bcplus/parser/detail/lemon_parser.y"
{ NUM_BOP(yygotominor.yy289, yymsp[-2].minor.yy289, yymsp[0].minor.yy289, yymsp[-2].minor.yy289->val() % yymsp[0].minor.yy289->val());   yy_destructor(yypParser,120,&yymsp[-1].minor);
}
#line 4467 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 154: /* formula ::= formula_base */
      case 197: /* formula_no_const ::= formula_no_const_base */ yytestcase(yyruleno==197);
      case 271: /* formula_temporal ::= formula_temporal_base */ yytestcase(yyruleno==271);
#line 892 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy297 = yymsp[0].minor.yy297;				}
#line 4474 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 155: /* formula ::= PAREN_L formula PAREN_R */
      case 198: /* formula_no_const ::= PAREN_L formula_no_const PAREN_R */ yytestcase(yyruleno==198);
      case 272: /* formula_temporal ::= PAREN_L formula_temporal PAREN_R */ yytestcase(yyruleno==272);
#line 893 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy297 = yymsp[-1].minor.yy297; yygotominor.yy297->parens(true); 	  yy_destructor(yypParser,82,&yymsp[-2].minor);
  yy_destructor(yypParser,83,&yymsp[0].minor);
}
#line 4483 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 156: /* formula ::= NOT formula */
      case 199: /* formula_no_const ::= NOT formula_no_const */ yytestcase(yyruleno==199);
      case 273: /* formula_temporal ::= NOT formula_temporal */ yytestcase(yyruleno==273);
#line 894 "bcplus/parser/detail/lemon_parser.y"
{ NESTED_UOP(yygotominor.yy297, yymsp[-1].minor.yy0, yymsp[0].minor.yy297, UnaryFormula::Operator::NOT, Language::Feature::FORMULA_NOT_KEYWORD); }
#line 4490 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 157: /* formula ::= DASH formula */
      case 200: /* formula_no_const ::= DASH formula_no_const */ yytestcase(yyruleno==200);
      case 274: /* formula_temporal ::= DASH formula_temporal */ yytestcase(yyruleno==274);
#line 895 "bcplus/parser/detail/lemon_parser.y"
{ NESTED_UOP(yygotominor.yy297, yymsp[-1].minor.yy0, yymsp[0].minor.yy297, UnaryFormula::Operator::NOT, Language::Feature::FORMULA_NOT_DASH); }
#line 4497 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 158: /* formula ::= formula AMP formula */
      case 201: /* formula_no_const ::= formula_no_const AMP formula_no_const */ yytestcase(yyruleno==201);
      case 275: /* formula_temporal ::= formula_temporal AMP formula_temporal */ yytestcase(yyruleno==275);
#line 896 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy297 = new BinaryFormula(BinaryFormula::Operator::AND, yymsp[-2].minor.yy297, yymsp[0].minor.yy297, yymsp[-2].minor.yy297->beginLoc(), yymsp[0].minor.yy297->endLoc());   yy_destructor(yypParser,112,&yymsp[-1].minor);
}
#line 4505 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 159: /* formula ::= formula DBL_PLUS formula */
      case 160: /* formula ::= formula PIPE formula */ yytestcase(yyruleno==160);
      case 202: /* formula_no_const ::= formula_no_const DBL_PLUS formula_no_const */ yytestcase(yyruleno==202);
      case 203: /* formula_no_const ::= formula_no_const PIPE formula_no_const */ yytestcase(yyruleno==203);
      case 276: /* formula_temporal ::= formula_temporal DBL_PLUS formula_temporal */ yytestcase(yyruleno==276);
      case 277: /* formula_temporal ::= formula_temporal PIPE formula_temporal */ yytestcase(yyruleno==277);
#line 898 "bcplus/parser/detail/lemon_parser.y"
{ NESTED_BOP(yygotominor.yy297, yymsp[-2].minor.yy297, yymsp[-1].minor.yy0, yymsp[0].minor.yy297, BinaryFormula::Operator::OR); }
#line 4515 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 161: /* formula ::= formula EQUIV formula */
      case 204: /* formula_no_const ::= formula_no_const EQUIV formula_no_const */ yytestcase(yyruleno==204);
      case 278: /* formula_temporal ::= formula_temporal EQUIV formula_temporal */ yytestcase(yyruleno==278);
#line 900 "bcplus/parser/detail/lemon_parser.y"
{ NESTED_BOP(yygotominor.yy297, yymsp[-2].minor.yy297, yymsp[-1].minor.yy0, yymsp[0].minor.yy297, BinaryFormula::Operator::EQUIV); }
#line 4522 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 162: /* formula ::= formula IMPL formula */
      case 163: /* formula ::= formula ARROW_RDASH formula */ yytestcase(yyruleno==163);
      case 205: /* formula_no_const ::= formula_no_const IMPL formula_no_const */ yytestcase(yyruleno==205);
      case 206: /* formula_no_const ::= formula_no_const ARROW_RDASH formula_no_const */ yytestcase(yyruleno==206);
      case 279: /* formula_temporal ::= formula_temporal IMPL formula_temporal */ yytestcase(yyruleno==279);
      case 280: /* formula_temporal ::= formula_temporal ARROW_RDASH formula_temporal */ yytestcase(yyruleno==280);
#line 901 "bcplus/parser/detail/lemon_parser.y"
{ NESTED_BOP(yygotominor.yy297, yymsp[-2].minor.yy297, yymsp[-1].minor.yy0, yymsp[0].minor.yy297, BinaryFormula::Operator::IMPL); }
#line 4532 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 164: /* formula_base ::= comparison */
      case 207: /* formula_no_const_base ::= comparison_no_const */ yytestcase(yyruleno==207);
      case 282: /* formula_temporal_base ::= comparison_temporal */ yytestcase(yyruleno==282);
      case 306: /* head_formula ::= comparison */ yytestcase(yyruleno==306);
#line 904 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy297 = yymsp[0].minor.yy297; }
#line 4540 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 165: /* formula_base ::= atomic_formula */
      case 307: /* head_formula ::= atomic_head_formula */ yytestcase(yyruleno==307);
#line 905 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy297 = yymsp[0].minor.yy426; }
#line 4546 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 166: /* formula_base ::= formula_quant */
      case 284: /* formula_temporal_base ::= formula_temporal_quant */ yytestcase(yyruleno==284);
#line 906 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy297 = yymsp[0].minor.yy101; }
#line 4552 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 167: /* formula_base ::= formula_card */
      case 285: /* formula_temporal_base ::= formula_temporal_card */ yytestcase(yyruleno==285);
#line 908 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy297 = yymsp[0].minor.yy297;
		if (!parser->lang()->support(Language::Feature::FORMULA_CARDINALITY_BODY)) {
			parser->_feature_error(Language::Feature::FORMULA_CARDINALITY_BODY, &yymsp[0].minor.yy297->beginLoc());
			YYERROR;
		}
	}
#line 4564 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 168: /* formula_base ::= TRUE */
      case 208: /* formula_no_const_base ::= TRUE */ yytestcase(yyruleno==208);
      case 286: /* formula_temporal_base ::= TRUE */ yytestcase(yyruleno==286);
      case 309: /* head_formula ::= TRUE */ yytestcase(yyruleno==309);
#line 915 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy297 = new NullaryFormula(NullaryFormula::Operator::TRUE, yymsp[0].minor.yy0->beginLoc(), yymsp[0].minor.yy0->endLoc()); }
#line 4572 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 169: /* formula_base ::= FALSE */
      case 209: /* formula_no_const_base ::= FALSE */ yytestcase(yyruleno==209);
      case 287: /* formula_temporal_base ::= FALSE */ yytestcase(yyruleno==287);
      case 310: /* head_formula ::= FALSE */ yytestcase(yyruleno==310);
#line 916 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy297 = new NullaryFormula(NullaryFormula::Operator::FALSE, yymsp[0].minor.yy0->beginLoc(), yymsp[0].minor.yy0->endLoc()); }
#line 4580 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 170: /* comparison ::= term_strong EQ term */
      case 177: /* comparison ::= term_strong_candidate EQ term */ yytestcase(yyruleno==177);
      case 210: /* comparison_no_const ::= term_no_const_strong EQ term_no_const */ yytestcase(yyruleno==210);
      case 288: /* comparison_temporal ::= term_temporal_strong EQ term_temporal */ yytestcase(yyruleno==288);
#line 918 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy297 = new ComparisonFormula(ComparisonFormula::Operator::EQ, yymsp[-2].minor.yy115, yymsp[0].minor.yy115, yymsp[-2].minor.yy115->beginLoc(), yymsp[0].minor.yy115->endLoc());   yy_destructor(yypParser,92,&yymsp[-1].minor);
}
#line 4589 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 171: /* comparison ::= term_strong DBL_EQ term */
      case 178: /* comparison ::= term_strong_candidate DBL_EQ term */ yytestcase(yyruleno==178);
      case 211: /* comparison_no_const ::= term_no_const_strong DBL_EQ term_no_const */ yytestcase(yyruleno==211);
      case 289: /* comparison_temporal ::= term_temporal_strong DBL_EQ term_temporal */ yytestcase(yyruleno==289);
#line 919 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy297 = new ComparisonFormula(ComparisonFormula::Operator::EQ, yymsp[-2].minor.yy115, yymsp[0].minor.yy115, yymsp[-2].minor.yy115->beginLoc(), yymsp[0].minor.yy115->endLoc());   yy_destructor(yypParser,93,&yymsp[-1].minor);
}
#line 4598 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 172: /* comparison ::= term_strong NEQ term */
      case 179: /* comparison ::= term_strong_candidate NEQ term */ yytestcase(yyruleno==179);
      case 212: /* comparison_no_const ::= term_no_const_strong NEQ term_no_const */ yytestcase(yyruleno==212);
      case 290: /* comparison_temporal ::= term_temporal_strong NEQ term_temporal */ yytestcase(yyruleno==290);
#line 920 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy297 = new ComparisonFormula(ComparisonFormula::Operator::NEQ, yymsp[-2].minor.yy115, yymsp[0].minor.yy115, yymsp[-2].minor.yy115->beginLoc(), yymsp[0].minor.yy115->endLoc());   yy_destructor(yypParser,94,&yymsp[-1].minor);
}
#line 4607 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 173: /* comparison ::= term_strong LTHAN term */
      case 180: /* comparison ::= term_strong_candidate LTHAN term */ yytestcase(yyruleno==180);
      case 213: /* comparison_no_const ::= term_no_const_strong LTHAN term_no_const */ yytestcase(yyruleno==213);
      case 291: /* comparison_temporal ::= term_temporal_strong LTHAN term_temporal */ yytestcase(yyruleno==291);
#line 921 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy297 = new ComparisonFormula(ComparisonFormula::Operator::LTHAN, yymsp[-2].minor.yy115, yymsp[0].minor.yy115, yymsp[-2].minor.yy115->beginLoc(), yymsp[0].minor.yy115->endLoc());   yy_destructor(yypParser,96,&yymsp[-1].minor);
}
#line 4616 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 174: /* comparison ::= term_strong GTHAN term */
      case 181: /* comparison ::= term_strong_candidate GTHAN term */ yytestcase(yyruleno==181);
      case 214: /* comparison_no_const ::= term_no_const_strong GTHAN term_no_const */ yytestcase(yyruleno==214);
      case 292: /* comparison_temporal ::= term_temporal_strong GTHAN term_temporal */ yytestcase(yyruleno==292);
#line 922 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy297 = new ComparisonFormula(ComparisonFormula::Operator::GTHAN, yymsp[-2].minor.yy115, yymsp[0].minor.yy115, yymsp[-2].minor.yy115->beginLoc(), yymsp[0].minor.yy115->endLoc());   yy_destructor(yypParser,97,&yymsp[-1].minor);
}
#line 4625 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 175: /* comparison ::= term_strong LTHAN_EQ term */
      case 182: /* comparison ::= term_strong_candidate LTHAN_EQ term */ yytestcase(yyruleno==182);
      case 215: /* comparison_no_const ::= term_no_const_strong LTHAN_EQ term_no_const */ yytestcase(yyruleno==215);
      case 293: /* comparison_temporal ::= term_temporal_strong LTHAN_EQ term_temporal */ yytestcase(yyruleno==293);
#line 923 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy297 = new ComparisonFormula(ComparisonFormula::Operator::LTHAN_EQ, yymsp[-2].minor.yy115, yymsp[0].minor.yy115, yymsp[-2].minor.yy115->beginLoc(), yymsp[0].minor.yy115->endLoc());   yy_destructor(yypParser,98,&yymsp[-1].minor);
}
#line 4634 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 176: /* comparison ::= term_strong GTHAN_EQ term */
      case 183: /* comparison ::= term_strong_candidate GTHAN_EQ term */ yytestcase(yyruleno==183);
      case 216: /* comparison_no_const ::= term_no_const_strong GTHAN_EQ term_no_const */ yytestcase(yyruleno==216);
      case 294: /* comparison_temporal ::= term_temporal_strong GTHAN_EQ term_temporal */ yytestcase(yyruleno==294);
#line 924 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy297 = new ComparisonFormula(ComparisonFormula::Operator::GTHAN_EQ, yymsp[-2].minor.yy115, yymsp[0].minor.yy115, yymsp[-2].minor.yy115->beginLoc(), yymsp[0].minor.yy115->endLoc());   yy_destructor(yypParser,99,&yymsp[-1].minor);
}
#line 4643 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 184: /* comparison ::= constant DBL_EQ term */
#line 932 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy297 = new ComparisonFormula(ComparisonFormula::Operator::EQ, yymsp[-2].minor.yy257, yymsp[0].minor.yy115, yymsp[-2].minor.yy257->beginLoc(), yymsp[0].minor.yy115->endLoc());   yy_destructor(yypParser,93,&yymsp[-1].minor);
}
#line 4649 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 185: /* comparison ::= constant NEQ term */
#line 933 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy297 = new ComparisonFormula(ComparisonFormula::Operator::NEQ, yymsp[-2].minor.yy257, yymsp[0].minor.yy115, yymsp[-2].minor.yy257->beginLoc(), yymsp[0].minor.yy115->endLoc());   yy_destructor(yypParser,94,&yymsp[-1].minor);
}
#line 4655 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 186: /* comparison ::= constant LTHAN term */
#line 934 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy297 = new ComparisonFormula(ComparisonFormula::Operator::LTHAN, yymsp[-2].minor.yy257, yymsp[0].minor.yy115, yymsp[-2].minor.yy257->beginLoc(), yymsp[0].minor.yy115->endLoc());   yy_destructor(yypParser,96,&yymsp[-1].minor);
}
#line 4661 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 187: /* comparison ::= constant GTHAN term */
#line 935 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy297 = new ComparisonFormula(ComparisonFormula::Operator::GTHAN, yymsp[-2].minor.yy257, yymsp[0].minor.yy115, yymsp[-2].minor.yy257->beginLoc(), yymsp[0].minor.yy115->endLoc());   yy_destructor(yypParser,97,&yymsp[-1].minor);
}
#line 4667 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 188: /* comparison ::= constant LTHAN_EQ term */
#line 936 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy297 = new ComparisonFormula(ComparisonFormula::Operator::LTHAN_EQ, yymsp[-2].minor.yy257, yymsp[0].minor.yy115, yymsp[-2].minor.yy257->beginLoc(), yymsp[0].minor.yy115->endLoc());   yy_destructor(yypParser,98,&yymsp[-1].minor);
}
#line 4673 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 189: /* comparison ::= constant GTHAN_EQ term */
#line 937 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy297 = new ComparisonFormula(ComparisonFormula::Operator::GTHAN_EQ, yymsp[-2].minor.yy257, yymsp[0].minor.yy115, yymsp[-2].minor.yy257->beginLoc(), yymsp[0].minor.yy115->endLoc());   yy_destructor(yypParser,99,&yymsp[-1].minor);
}
#line 4679 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 190: /* atomic_formula ::= constant */
      case 194: /* atomic_formula_anon ::= const_anon */ yytestcase(yyruleno==194);
      case 217: /* atomic_formula_one_const ::= constant_one_const */ yytestcase(yyruleno==217);
#line 967 "bcplus/parser/detail/lemon_parser.y"
{ ATOMIC_FORMULA(yygotominor.yy426, yymsp[0].minor.yy257, true); }
#line 4686 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 191: /* atomic_formula ::= TILDE constant */
      case 195: /* atomic_formula_anon ::= TILDE const_anon */ yytestcase(yyruleno==195);
      case 218: /* atomic_formula_one_const ::= TILDE constant_one_const */ yytestcase(yyruleno==218);
#line 968 "bcplus/parser/detail/lemon_parser.y"
{ ATOMIC_FORMULA(yygotominor.yy426, yymsp[0].minor.yy257, false);   yy_destructor(yypParser,86,&yymsp[-1].minor);
}
#line 4694 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 192: /* atomic_formula ::= constant EQ term */
      case 196: /* atomic_formula_anon ::= const_anon EQ term */ yytestcase(yyruleno==196);
      case 219: /* atomic_formula_one_const ::= constant_one_const EQ term_no_const */ yytestcase(yyruleno==219);
#line 969 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy426 = new AtomicFormula(yymsp[-2].minor.yy257, yymsp[0].minor.yy115, yymsp[-2].minor.yy257->beginLoc(), yymsp[0].minor.yy115->endLoc());	  yy_destructor(yypParser,92,&yymsp[-1].minor);
}
#line 4702 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 193: /* atomic_formula_anon ::= atomic_formula */
      case 311: /* atomic_head_formula ::= atomic_formula */ yytestcase(yyruleno==311);
      case 408: /* show_elem ::= atomic_formula_one_const */ yytestcase(yyruleno==408);
#line 971 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy426 = yymsp[0].minor.yy426; }
#line 4709 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 220: /* formula_quant ::= BRACKET_L quant_lst PIPE formula BRACKET_R */
      case 295: /* formula_temporal_quant ::= BRACKET_L quant_lst PIPE formula_temporal BRACKET_R */ yytestcase(yyruleno==295);
#line 1036 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy101=NULL;
		ref_ptr<const Token> bl_ptr = yymsp[-4].minor.yy0;
		ref_ptr<QuantifierFormula::QuantifierList> lst_ptr = yymsp[-3].minor.yy381;
		ref_ptr<Formula> sub_ptr = yymsp[-1].minor.yy297;
		ref_ptr<const Token> br_ptr = yymsp[0].minor.yy0;

		if (!parser->lang()->support(Language::Feature::FORMULA_QUANTIFIER)) {
			parser->_feature_error(Language::Feature::FORMULA_QUANTIFIER, &yymsp[-4].minor.yy0->beginLoc());
			YYERROR;
		} else yygotominor.yy101 = new QuantifierFormula(yymsp[-3].minor.yy381, yymsp[-1].minor.yy297, yymsp[-4].minor.yy0->beginLoc(), yymsp[0].minor.yy0->endLoc());
	  yy_destructor(yypParser,109,&yymsp[-2].minor);
}
#line 4727 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 221: /* quant_lst ::= quant_op variable */
#line 1050 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy381 = new QuantifierFormula::QuantifierList();
		yygotominor.yy381->push_back(QuantifierFormula::Quantifier(yymsp[-1].minor.yy49, yymsp[0].minor.yy45));
	}
#line 4735 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 222: /* quant_lst ::= quant_lst quant_op variable */
#line 1056 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy381 = yymsp[-2].minor.yy381;
		yygotominor.yy381->push_back(QuantifierFormula::Quantifier(yymsp[-1].minor.yy49, yymsp[0].minor.yy45));
	}
#line 4743 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 223: /* quant_op ::= BIG_CONJ */
#line 1061 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy49 = QuantifierFormula::Operator::CONJ;   yy_destructor(yypParser,101,&yymsp[0].minor);
}
#line 4749 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 224: /* quant_op ::= BIG_DISJ */
#line 1062 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy49 = QuantifierFormula::Operator::DISJ;   yy_destructor(yypParser,102,&yymsp[0].minor);
}
#line 4755 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 225: /* formula_card ::= CBRACKET_L card_var_lst formula CBRACKET_R */
      case 296: /* formula_temporal_card ::= CBRACKET_L card_var_lst formula_temporal CBRACKET_R */ yytestcase(yyruleno==296);
#line 1108 "bcplus/parser/detail/lemon_parser.y"
{ CARD_FORMULA(yygotominor.yy297, NULL, yymsp[-3].minor.yy0, yymsp[-2].minor.yy111, yymsp[-1].minor.yy297, yymsp[0].minor.yy0, NULL);  }
#line 4761 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 226: /* formula_card ::= term_strong CBRACKET_L card_var_lst formula CBRACKET_R */
      case 297: /* formula_temporal_card ::= term_temporal_strong CBRACKET_L card_var_lst formula_temporal CBRACKET_R */ yytestcase(yyruleno==297);
#line 1109 "bcplus/parser/detail/lemon_parser.y"
{ CARD_FORMULA(yygotominor.yy297, yymsp[-4].minor.yy115, yymsp[-3].minor.yy0, yymsp[-2].minor.yy111, yymsp[-1].minor.yy297,  yymsp[0].minor.yy0, NULL);  }
#line 4767 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 227: /* formula_card ::= CBRACKET_L card_var_lst formula CBRACKET_R term */
      case 298: /* formula_temporal_card ::= CBRACKET_L card_var_lst formula_temporal CBRACKET_R term_temporal */ yytestcase(yyruleno==298);
#line 1110 "bcplus/parser/detail/lemon_parser.y"
{ CARD_FORMULA(yygotominor.yy297, NULL, yymsp[-4].minor.yy0, yymsp[-3].minor.yy111, yymsp[-2].minor.yy297, yymsp[-1].minor.yy0, yymsp[0].minor.yy115); 	}
#line 4773 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 228: /* formula_card ::= term_strong CBRACKET_L card_var_lst formula CBRACKET_R term */
      case 299: /* formula_temporal_card ::= term_temporal_strong CBRACKET_L card_var_lst formula_temporal CBRACKET_R term_temporal */ yytestcase(yyruleno==299);
#line 1111 "bcplus/parser/detail/lemon_parser.y"
{ CARD_FORMULA(yygotominor.yy297, yymsp[-5].minor.yy115, yymsp[-4].minor.yy0, yymsp[-3].minor.yy111, yymsp[-2].minor.yy297,  yymsp[-1].minor.yy0, yymsp[0].minor.yy115); 	}
#line 4779 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 229: /* formula_card ::= CBRACKET_L formula CBRACKET_R */
      case 300: /* formula_temporal_card ::= CBRACKET_L formula_temporal CBRACKET_R */ yytestcase(yyruleno==300);
#line 1112 "bcplus/parser/detail/lemon_parser.y"
{ CARD_FORMULA(yygotominor.yy297, NULL, yymsp[-2].minor.yy0, NULL, yymsp[-1].minor.yy297, yymsp[0].minor.yy0, NULL);  }
#line 4785 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 230: /* formula_card ::= term_strong CBRACKET_L formula CBRACKET_R */
      case 301: /* formula_temporal_card ::= term_temporal_strong CBRACKET_L formula_temporal CBRACKET_R */ yytestcase(yyruleno==301);
#line 1113 "bcplus/parser/detail/lemon_parser.y"
{ CARD_FORMULA(yygotominor.yy297, yymsp[-3].minor.yy115, yymsp[-2].minor.yy0, NULL, yymsp[-1].minor.yy297,  yymsp[0].minor.yy0, NULL);  }
#line 4791 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 231: /* formula_card ::= CBRACKET_L formula CBRACKET_R term */
      case 302: /* formula_temporal_card ::= CBRACKET_L formula_temporal CBRACKET_R term_temporal */ yytestcase(yyruleno==302);
#line 1114 "bcplus/parser/detail/lemon_parser.y"
{ CARD_FORMULA(yygotominor.yy297, NULL, yymsp[-3].minor.yy0, NULL, yymsp[-2].minor.yy297, yymsp[-1].minor.yy0, yymsp[0].minor.yy115); 	}
#line 4797 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 232: /* formula_card ::= term_strong CBRACKET_L formula CBRACKET_R term */
      case 303: /* formula_temporal_card ::= term_temporal_strong CBRACKET_L formula_temporal CBRACKET_R term_temporal */ yytestcase(yyruleno==303);
#line 1115 "bcplus/parser/detail/lemon_parser.y"
{ CARD_FORMULA(yygotominor.yy297, yymsp[-4].minor.yy115, yymsp[-3].minor.yy0, NULL, yymsp[-2].minor.yy297,  yymsp[-1].minor.yy0, yymsp[0].minor.yy115); 	}
#line 4803 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 233: /* card_var_lst ::= card_var_lst_inner PIPE */
#line 1119 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy111 = yymsp[-1].minor.yy111;
	  yy_destructor(yypParser,109,&yymsp[0].minor);
}
#line 4811 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 234: /* card_var_lst_inner ::= variable */
#line 1124 "bcplus/parser/detail/lemon_parser.y"
{
		ref_ptr<const Referenced> v_ptr = yymsp[0].minor.yy45;
		yygotominor.yy111 = new CardinalityFormula::VariableList();
		yygotominor.yy111->push_back(yymsp[0].minor.yy45->symbol());
	}
#line 4820 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 235: /* card_var_lst_inner ::= card_var_lst_inner COMMA variable */
#line 1131 "bcplus/parser/detail/lemon_parser.y"
{
		ref_ptr<const Referenced> v_ptr = yymsp[0].minor.yy45;
		yygotominor.yy111 = yymsp[-2].minor.yy111;
		yygotominor.yy111->push_back(yymsp[0].minor.yy45->symbol());
	  yy_destructor(yypParser,113,&yymsp[-1].minor);
}
#line 4830 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 246: /* term_temporal ::= constant */
#line 1186 "bcplus/parser/detail/lemon_parser.y"
{
		// error handline for constants so they don'yygotominor.yy115 default to undeclared identifiers
		yygotominor.yy115 = NULL;
		ref_ptr<const Referenced> c_ptr = yymsp[0].minor.yy257;
		parser->_parse_error("All constant symbols must be bound to a step using the i:F notation.", &yymsp[0].minor.yy257->beginLoc());
		YYERROR;
	}
#line 4841 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 249: /* term_temporal ::= term_temporal COLON term */
      case 263: /* term_temporal_strong ::= term_temporal_strong COLON term_strong */ yytestcase(yyruleno==263);
#line 1198 "bcplus/parser/detail/lemon_parser.y"
{ BINDING(yygotominor.yy115, yymsp[-2].minor.yy115, yymsp[-1].minor.yy0, yymsp[0].minor.yy115, BindingTerm); }
#line 4847 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 281: /* formula_temporal ::= term_temporal_strong COLON formula */
#line 1281 "bcplus/parser/detail/lemon_parser.y"
{ BINDING(yygotominor.yy297, yymsp[-2].minor.yy115, yymsp[-1].minor.yy0, yymsp[0].minor.yy297, BindingFormula); }
#line 4852 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 283: /* formula_temporal_base ::= atomic_formula */
#line 1287 "bcplus/parser/detail/lemon_parser.y"
{
		// error handline for more useful error messages
		yygotominor.yy297 = NULL;
		ref_ptr<const Referenced> l_ptr = yymsp[0].minor.yy426;
		parser->_parse_error("All constant symbols must be bound to a step using the i:F notation.", &yymsp[0].minor.yy426->beginLoc());
		YYERROR;
	}
#line 4863 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 304: /* head_formula ::= head_formula AMP head_formula */
#line 1382 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy297 = new BinaryFormula(BinaryFormula::Operator::AND, yymsp[-2].minor.yy297, yymsp[0].minor.yy297, yymsp[-2].minor.yy297->beginLoc(), yymsp[0].minor.yy297->endLoc());
	  yy_destructor(yypParser,112,&yymsp[-1].minor);
}
#line 4871 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 305: /* head_formula ::= PAREN_L head_formula PAREN_R */
#line 1390 "bcplus/parser/detail/lemon_parser.y"
{
		ref_ptr<const Referenced> lp_ptr = yymsp[-2].minor.yy0, rp_ptr = yymsp[0].minor.yy0;
		yygotominor.yy297 = yymsp[-1].minor.yy297;
		yygotominor.yy297->parens(true);																									\
		yygotominor.yy297->beginLoc(yymsp[-2].minor.yy0->beginLoc());																					\
		yygotominor.yy297->endLoc(yymsp[0].minor.yy0->endLoc());

	}
#line 4883 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 308: /* head_formula ::= formula_smpl_card */
#line 1401 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy297 = yymsp[0].minor.yy369;
		if (!parser->lang()->support(Language::Feature::FORMULA_CARDINALITY_HEAD)) {
			parser->_feature_error(Language::Feature::FORMULA_CARDINALITY_HEAD, &yymsp[0].minor.yy369->beginLoc());
			YYERROR;
		}
	}
#line 4894 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 312: /* atomic_head_formula ::= DASH constant */
#line 1414 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy426 = NULL;
		ref_ptr<const Token> d_ptr = yymsp[-1].minor.yy0;
		ref_ptr<Constant> c_ptr = yymsp[0].minor.yy257;

		if (!parser->lang()->support(Language::Feature::FORMULA_NOT_DASH_HEAD)) {
			parser->_feature_error(Language::Feature::FORMULA_NOT_DASH_HEAD);
			YYERROR;
		} else {
			ATOMIC_FORMULA(yygotominor.yy426, yymsp[0].minor.yy257, false);
		}
	}
#line 4910 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 313: /* formula_smpl_card ::= CBRACKET_L card_var_lst atomic_formula_one_const CBRACKET_R */
#line 1427 "bcplus/parser/detail/lemon_parser.y"
{ CARD_FORMULA(yygotominor.yy369, NULL, yymsp[-3].minor.yy0, yymsp[-2].minor.yy111, yymsp[-1].minor.yy426, yymsp[0].minor.yy0, NULL);  }
#line 4915 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 314: /* formula_smpl_card ::= term_strong CBRACKET_L card_var_lst atomic_formula_one_const CBRACKET_R */
#line 1428 "bcplus/parser/detail/lemon_parser.y"
{ CARD_FORMULA(yygotominor.yy369, yymsp[-4].minor.yy115, yymsp[-3].minor.yy0, yymsp[-2].minor.yy111, yymsp[-1].minor.yy426,  yymsp[0].minor.yy0, NULL);  }
#line 4920 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 315: /* formula_smpl_card ::= CBRACKET_L card_var_lst atomic_formula_one_const CBRACKET_R term */
#line 1429 "bcplus/parser/detail/lemon_parser.y"
{ CARD_FORMULA(yygotominor.yy369, NULL, yymsp[-4].minor.yy0, yymsp[-3].minor.yy111, yymsp[-2].minor.yy426, yymsp[-1].minor.yy0, yymsp[0].minor.yy115); 	}
#line 4925 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 316: /* formula_smpl_card ::= term_strong CBRACKET_L card_var_lst atomic_formula_one_const CBRACKET_R term */
#line 1430 "bcplus/parser/detail/lemon_parser.y"
{ CARD_FORMULA(yygotominor.yy369, yymsp[-5].minor.yy115, yymsp[-4].minor.yy0, yymsp[-3].minor.yy111, yymsp[-2].minor.yy426,  yymsp[-1].minor.yy0, yymsp[0].minor.yy115); 	}
#line 4930 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 317: /* formula_smpl_card ::= CBRACKET_L atomic_formula_one_const CBRACKET_R */
#line 1431 "bcplus/parser/detail/lemon_parser.y"
{ CARD_FORMULA(yygotominor.yy369, NULL, yymsp[-2].minor.yy0, NULL, yymsp[-1].minor.yy426, yymsp[0].minor.yy0, NULL);  }
#line 4935 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 318: /* formula_smpl_card ::= term_strong CBRACKET_L atomic_formula_one_const CBRACKET_R */
#line 1432 "bcplus/parser/detail/lemon_parser.y"
{ CARD_FORMULA(yygotominor.yy369, yymsp[-3].minor.yy115, yymsp[-2].minor.yy0, NULL, yymsp[-1].minor.yy426,  yymsp[0].minor.yy0, NULL);  }
#line 4940 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 319: /* formula_smpl_card ::= CBRACKET_L atomic_formula_one_const CBRACKET_R term */
#line 1433 "bcplus/parser/detail/lemon_parser.y"
{ CARD_FORMULA(yygotominor.yy369, NULL, yymsp[-3].minor.yy0, NULL, yymsp[-2].minor.yy426, yymsp[-1].minor.yy0, yymsp[0].minor.yy115); 	}
#line 4945 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 320: /* formula_smpl_card ::= term_strong CBRACKET_L atomic_formula_one_const CBRACKET_R term */
#line 1434 "bcplus/parser/detail/lemon_parser.y"
{ CARD_FORMULA(yygotominor.yy369, yymsp[-4].minor.yy115, yymsp[-3].minor.yy0, NULL, yymsp[-2].minor.yy426,  yymsp[-1].minor.yy0, yymsp[0].minor.yy115); 	}
#line 4950 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 321: /* stmt_macro_def ::= COLON_DASH MACROS macro_def_lst PERIOD */
#line 1453 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy495 = NULL;
        ref_ptr<const Token> cd_ptr = yymsp[-3].minor.yy0;
        ref_ptr<const Token> kw_ptr = yymsp[-2].minor.yy0;
        ref_ptr<MacroDeclaration::ElementList> l_ptr = yymsp[-1].minor.yy529;
        ref_ptr<const Token> p_ptr = yymsp[0].minor.yy0;

        if (!parser->lang()->support(Language::Feature::DECL_MACRO)) {
            parser->_feature_error(Language::Feature::DECL_MACRO, &yymsp[-2].minor.yy0->beginLoc());
            YYERROR;
        } else {
		    BOOST_FOREACH(symbols::MacroSymbol* m, *yymsp[-1].minor.yy529) {
			    if (!parser->symtab()->create(m)) {
	    	        // Check if it's a duplicate
	    	        symbols::MacroSymbol* m2 = (symbols::MacroSymbol*)parser->symtab()->resolve(symbols::Symbol::Type::MACRO, *m->base(), m->arity());
		            if (!m2 || m2 != m) {
		                parser->_parse_error("Detected conflicting definition of symbol \"" + *m->name() + "\".", &yygotominor.yy495->beginLoc());
		            } else {
		                parser->_parse_error("Detected a duplicate definition of symbol \"" + *m->name() + "\".", &yygotominor.yy495->beginLoc());
		            }
		        }
		    }

			yygotominor.yy495 = new MacroDeclaration(yymsp[-1].minor.yy529, yymsp[-3].minor.yy0->beginLoc(), yymsp[0].minor.yy0->endLoc());
        }
    }
#line 4980 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 322: /* macro_def_lst ::= macro_bnd */
#line 1481 "bcplus/parser/detail/lemon_parser.y"
{
        yygotominor.yy529 = new MacroDeclaration::ElementList();
        yygotominor.yy529->push_back(yymsp[0].minor.yy483);
    }
#line 4988 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 323: /* macro_def_lst ::= macro_def_lst SEMICOLON macro_bnd */
#line 1487 "bcplus/parser/detail/lemon_parser.y"
{
        yygotominor.yy529 = yymsp[-2].minor.yy529;
        yygotominor.yy529->push_back(yymsp[0].minor.yy483);
      yy_destructor(yypParser,104,&yymsp[-1].minor);
}
#line 4997 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 324: /* macro_bnd ::= IDENTIFIER PAREN_L macro_args PAREN_R ARROW_RDASH MACRO_STRING */
#line 1493 "bcplus/parser/detail/lemon_parser.y"
{
        ref_ptr<const Token> id_ptr = yymsp[-5].minor.yy0;
        ref_ptr<MacroSymbol::ArgumentList> args_ptr = yymsp[-3].minor.yy338;
        ref_ptr<const Token> def_ptr = yymsp[0].minor.yy0;

        yygotominor.yy483 = new MacroSymbol(yymsp[-5].minor.yy0->str(), yymsp[0].minor.yy0->str(), yymsp[-3].minor.yy338);
      yy_destructor(yypParser,82,&yymsp[-4].minor);
  yy_destructor(yypParser,83,&yymsp[-2].minor);
  yy_destructor(yypParser,107,&yymsp[-1].minor);
}
#line 5011 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 325: /* macro_bnd ::= IDENTIFIER ARROW_RDASH MACRO_STRING */
#line 1502 "bcplus/parser/detail/lemon_parser.y"
{
        ref_ptr<const Token> id_ptr = yymsp[-2].minor.yy0;
        ref_ptr<const Token> def_ptr = yymsp[0].minor.yy0;

        yygotominor.yy483 = new MacroSymbol(yymsp[-2].minor.yy0->str(), yymsp[0].minor.yy0->str());
      yy_destructor(yypParser,107,&yymsp[-1].minor);
}
#line 5022 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 326: /* macro_args ::= macro_arg */
#line 1510 "bcplus/parser/detail/lemon_parser.y"
{
        yygotominor.yy338 = new MacroSymbol::ArgumentList();
        yygotominor.yy338->push_back(yymsp[0].minor.yy75->str());
        delete yymsp[0].minor.yy75;
    }
#line 5031 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 327: /* macro_args ::= macro_args COMMA macro_arg */
#line 1516 "bcplus/parser/detail/lemon_parser.y"
{
        yygotominor.yy338 = yymsp[-2].minor.yy338;
        yygotominor.yy338->push_back(yymsp[0].minor.yy75->str());
        delete yymsp[0].minor.yy75;
      yy_destructor(yypParser,113,&yymsp[-1].minor);
}
#line 5041 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 328: /* macro_arg ::= POUND_INTEGER */
      case 329: /* macro_arg ::= POUND_IDENTIFIER */ yytestcase(yyruleno==329);
#line 1523 "bcplus/parser/detail/lemon_parser.y"
{
        yygotominor.yy75 = yymsp[0].minor.yy0;
    }
#line 5049 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 330: /* sort_lst ::= sort */
#line 1550 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy507 = new ConstantSymbol::SortList();
		yygotominor.yy507->push_back(yymsp[0].minor.yy521);
	}
#line 5057 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 331: /* sort_lst ::= sort_lst COMMA sort */
#line 1555 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy507 = yymsp[-2].minor.yy507;
		yygotominor.yy507->push_back(yymsp[0].minor.yy521);
	  yy_destructor(yypParser,113,&yymsp[-1].minor);
}
#line 5066 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 332: /* sort ::= sort_id_nr */
      case 338: /* sort_id_nr ::= sort_id */ yytestcase(yyruleno==338);
      case 339: /* sort_id_nr ::= sort_nr */ yytestcase(yyruleno==339);
#line 1580 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy521 = yymsp[0].minor.yy521; }
#line 5073 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 333: /* sort ::= sort_id_nr STAR */
#line 1581 "bcplus/parser/detail/lemon_parser.y"
{ DYNAMIC_SORT_PLUS(yygotominor.yy521, yymsp[-1].minor.yy521, yymsp[0].minor.yy0, Language::Feature::STAR_SORT, parser->symtab()->bobj(SymbolTable::BuiltinObject::NONE)); }
#line 5078 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 334: /* sort ::= sort_id_nr CARROT */
#line 1582 "bcplus/parser/detail/lemon_parser.y"
{ DYNAMIC_SORT_PLUS(yygotominor.yy521, yymsp[-1].minor.yy521, yymsp[0].minor.yy0, Language::Feature::CARROT_SORT, parser->symtab()->bobj(SymbolTable::BuiltinObject::UNKNOWN)); }
#line 5083 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 335: /* sort ::= sort PLUS object_nullary */
#line 1584 "bcplus/parser/detail/lemon_parser.y"
{ u::ref_ptr<const Object> o_ptr = yymsp[0].minor.yy342; DYNAMIC_SORT_PLUS(yygotominor.yy521, yymsp[-2].minor.yy521, yymsp[-1].minor.yy0, Language::Feature::SORT_PLUS, yymsp[0].minor.yy342->symbol()); }
#line 5088 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 336: /* sort ::= sort PLUS IDENTIFIER */
#line 1587 "bcplus/parser/detail/lemon_parser.y"
{
												  u::ref_ptr<const Referenced> s_ptr = yymsp[-2].minor.yy521, op_ptr = yymsp[-1].minor.yy0, id_ptr = yymsp[0].minor.yy0;
												  u::ref_ptr<const ObjectSymbol> obj = parser->symtab()->resolveOrCreate(new ObjectSymbol(yymsp[0].minor.yy0->str()));
												  if(!obj) {
													if (parser->lang()->support(Language::Feature::SORT_PLUS))
														parser->_parse_error("\"" + *yymsp[0].minor.yy0->str() + "\" could not be declared as an object as this conflicts with a previous declarations of this identifier.", &yymsp[0].minor.yy0->beginLoc());
													else
														parser->_feature_error(Language::Feature::SORT_PLUS, &yymsp[-1].minor.yy0->beginLoc());
													YYERROR;
												  } else {
													DYNAMIC_SORT_PLUS(yygotominor.yy521, yymsp[-2].minor.yy521, yymsp[-1].minor.yy0, Language::Feature::SORT_PLUS, obj);
												  }
												}
#line 5105 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 337: /* sort ::= sort PLUS INTEGER */
#line 1601 "bcplus/parser/detail/lemon_parser.y"
{
												  ref_ptr<const Object> t_ptr;
												  BASIC_TERM(t_ptr, yymsp[0].minor.yy0);
												  DYNAMIC_SORT_PLUS(yygotominor.yy521, yymsp[-2].minor.yy521, yymsp[-1].minor.yy0, Language::Feature::SORT_PLUS, t_ptr->symbol());
												}
#line 5114 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 340: /* sort_nr ::= num_range */
#line 1612 "bcplus/parser/detail/lemon_parser.y"
{
		ref_ptr<const Referenced> nr_ptr = yymsp[0].minor.yy205;

		yygotominor.yy521 = NULL;

		if (!parser->lang()->support(Language::Feature::NUMRANGE_SORT)) {
			parser->_feature_error(Language::Feature::NUMRANGE_SORT, &yymsp[0].minor.yy205->beginLoc());
			YYERROR;
		}

		// X..Y becomes __rsort_N_
		if(!(yygotominor.yy521 = parser->_newRange(yymsp[0].minor.yy205->min(), yymsp[0].minor.yy205->max()))) {
			parser->_parse_error("INTERNAL ERROR: An error occurred while instantiating the dynamic sort declaration.", &yymsp[0].minor.yy205->beginLoc());
			YYERROR;
		}
	}
#line 5134 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 341: /* sort_id ::= IDENTIFIER */
#line 1630 "bcplus/parser/detail/lemon_parser.y"
{
		// dynamically declare the sort
		yygotominor.yy521 = (SortSymbol*)parser->symtab()->resolve(Symbol::Type::SORT, *yymsp[0].minor.yy0->str());
		if (!yygotominor.yy521) {
			parser->_parse_error("\"" + Symbol::genName(*yymsp[0].minor.yy0->str(),0) + "\" is not a declared sort test.", &yymsp[0].minor.yy0->beginLoc());
			YYERROR;
		}
		delete yymsp[0].minor.yy0;
	}
#line 5147 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 342: /* stmt_constant_def ::= COLON_DASH CONSTANTS constant_bnd_lst PERIOD */
#line 1661 "bcplus/parser/detail/lemon_parser.y"
{
		ref_ptr<const Token> cd_ptr = yymsp[-3].minor.yy0;
		ref_ptr<const Token> kw_ptr = yymsp[-2].minor.yy0;
		ref_ptr<ConstantDeclaration::ElementList> l_ptr = yymsp[-1].minor.yy465;
		ref_ptr<const Token> p_ptr = yymsp[0].minor.yy0;

		if (!parser->lang()->support(Language::Feature::DECL_CONSTANT)) {
			yygotominor.yy15 = NULL;
			parser->_feature_error(Language::Feature::DECL_CONSTANT, &yymsp[-2].minor.yy0->beginLoc());
			YYERROR;
		} else {
			yygotominor.yy15 = new ConstantDeclaration(yymsp[-1].minor.yy465, yymsp[-3].minor.yy0->beginLoc(), yymsp[0].minor.yy0->endLoc());

		}
	}
#line 5166 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 343: /* constant_bnd_lst ::= constant_bnd */
#line 1678 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy465 = yymsp[0].minor.yy465;
	}
#line 5173 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 344: /* constant_bnd_lst ::= constant_bnd_lst SEMICOLON constant_bnd */
#line 1683 "bcplus/parser/detail/lemon_parser.y"
{
		ref_ptr<ConstantDeclaration::ElementList> bnd_ptr = yymsp[0].minor.yy465;
		yygotominor.yy465 = yymsp[-2].minor.yy465;
		yygotominor.yy465->splice(yygotominor.yy465->end(), *yymsp[0].minor.yy465);
	  yy_destructor(yypParser,104,&yymsp[-1].minor);
}
#line 5183 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 345: /* constant_bnd ::= constant_dcl_lst DBL_COLON constant_dcl_type PAREN_L sort PAREN_R */
#line 1703 "bcplus/parser/detail/lemon_parser.y"
{
		ref_ptr<const SortSymbol> s_ptr = yymsp[-1].minor.yy521;
		ref_ptr<const Referenced> names_ptr = yymsp[-5].minor.yy410;
		yygotominor.yy465 = new ConstantDeclaration::ElementList();

		// NOTE: additive constants default to the additive sort, not the boolean sort
		// if (yymsp[-3].minor.yy245 & ConstantSymbol::Type::M_ADDITIVE) s_ptr = parser->symtab()->bsort(SymbolTable::BuiltinSort::ADDITIVE);

		// external constants should have "unknown" in their sort
		if (yymsp[-3].minor.yy245 & ConstantSymbol::Type::M_EXTERNAL) s_ptr = parser->symtab()->carrot(yymsp[-1].minor.yy521);

		// non-boolean abActions should contain "none"
		else if (yymsp[-3].minor.yy245 == ConstantSymbol::Type::ABACTION && s_ptr->domainType() != DomainType::BOOLEAN) s_ptr = parser->symtab()->star(yymsp[-1].minor.yy521);

		BOOST_FOREACH(IdentifierDecl& decl, *yymsp[-5].minor.yy410) {
			// attempt to declare each symbol
			ref_ptr<ConstantSymbol> c = new ConstantSymbol(yymsp[-3].minor.yy245, decl.first->str(), s_ptr, decl.second);
			yygotominor.yy465->push_back(c);
			CONSTANT_DECL(c, decl.first->beginLoc());
		}
	  yy_destructor(yypParser,87,&yymsp[-4].minor);
  yy_destructor(yypParser,82,&yymsp[-2].minor);
  yy_destructor(yypParser,83,&yymsp[0].minor);
}
#line 5211 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 346: /* constant_bnd ::= constant_dcl_lst DBL_COLON constant_dcl_type PAREN_L REAL BRACKET_L num_range BRACKET_R PAREN_R */
#line 1725 "bcplus/parser/detail/lemon_parser.y"
{
		Term const* min = yymsp[-2].minor.yy205->min();
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
		Term const* max = yymsp[-2].minor.yy205->max();
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
		ref_ptr<const Referenced> nr_ptr = yymsp[-2].minor.yy205;
		ref_ptr<const Referenced> names_ptr = yymsp[-8].minor.yy410;
		ref_ptr<const SortSymbol> s_ptr = s;

		yygotominor.yy465 = new ConstantDeclaration::ElementList();

		// NOTE: additive constants default to the additive sort, not the boolean sort
		// if (yymsp[-6].minor.yy245 & ConstantSymbol::Type::M_ADDITIVE) s_ptr = parser->symtab()->bsort(SymbolTable::BuiltinSort::ADDITIVE);

		// external constants should have "unknown" in their sort
		if (yymsp[-6].minor.yy245 & ConstantSymbol::Type::M_EXTERNAL) s_ptr = parser->symtab()->carrot(s);

		// non-boolean abActions should contain "none"
		else if (yymsp[-6].minor.yy245 == ConstantSymbol::Type::ABACTION && s_ptr->domainType() != DomainType::BOOLEAN) s_ptr = parser->symtab()->star(s);

		BOOST_FOREACH(IdentifierDecl& decl, *yymsp[-8].minor.yy410) {
			// attempt to declare each symbol
			ref_ptr<ConstantSymbol> c = new ConstantSymbol(yymsp[-6].minor.yy245, decl.first->str(), s_ptr, decl.second);
			yygotominor.yy465->push_back(c);
			CONSTANT_DECL(c, decl.first->beginLoc());
		}
	  yy_destructor(yypParser,87,&yymsp[-7].minor);
  yy_destructor(yypParser,82,&yymsp[-5].minor);
  yy_destructor(yypParser,65,&yymsp[-4].minor);
  yy_destructor(yypParser,77,&yymsp[-3].minor);
  yy_destructor(yypParser,78,&yymsp[-1].minor);
  yy_destructor(yypParser,83,&yymsp[0].minor);
}
#line 5295 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 347: /* constant_bnd ::= constant_dcl_lst DBL_COLON constant_dcl_type PAREN_L INTEGER_TYPE BRACKET_L num_range BRACKET_R PAREN_R */
#line 1800 "bcplus/parser/detail/lemon_parser.y"
{
			Term const* min = yymsp[-2].minor.yy205->min();
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
			Term const* max = yymsp[-2].minor.yy205->max();
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
			std::string temp = "integer["+preMin+*minos->base()+".."+preMax+*maxos->base()+"]";
			ReferencedString const* domainString = new ReferencedString(temp);
			SortSymbol* s = parser->symtab()->resolveOrCreate(new SortSymbol(domainString));
			ref_ptr<const Referenced> nr_ptr = yymsp[-2].minor.yy205;
			ref_ptr<const Referenced> names_ptr = yymsp[-8].minor.yy410;
			ref_ptr<const SortSymbol> s_ptr = s;

			yygotominor.yy465 = new ConstantDeclaration::ElementList();

			// NOTE: additive constants default to the additive sort, not the boolean sort
			// if (yymsp[-6].minor.yy245 & ConstantSymbol::Type::M_ADDITIVE) s_ptr = parser->symtab()->bsort(SymbolTable::BuiltinSort::ADDITIVE);

			// external constants should have "unknown" in their sort
			if (yymsp[-6].minor.yy245 & ConstantSymbol::Type::M_EXTERNAL) s_ptr = parser->symtab()->carrot(s);

			// non-boolean abActions should contain "none"
			else if (yymsp[-6].minor.yy245 == ConstantSymbol::Type::ABACTION && s_ptr->domainType() != DomainType::BOOLEAN) s_ptr = parser->symtab()->star(s);

			BOOST_FOREACH(IdentifierDecl& decl, *yymsp[-8].minor.yy410) {
				// attempt to declare each symbol
				ref_ptr<ConstantSymbol> c = new ConstantSymbol(yymsp[-6].minor.yy245, decl.first->str(), s_ptr, decl.second);
				yygotominor.yy465->push_back(c);
				CONSTANT_DECL(c, decl.first->beginLoc());
			}
		  yy_destructor(yypParser,87,&yymsp[-7].minor);
  yy_destructor(yypParser,82,&yymsp[-5].minor);
  yy_destructor(yypParser,66,&yymsp[-4].minor);
  yy_destructor(yypParser,77,&yymsp[-3].minor);
  yy_destructor(yypParser,78,&yymsp[-1].minor);
  yy_destructor(yypParser,83,&yymsp[0].minor);
}
#line 5379 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 348: /* constant_bnd ::= constant_dcl_lst DBL_COLON CONTINUOUS PAREN_L num_range PAREN_R */
#line 1875 "bcplus/parser/detail/lemon_parser.y"
{
			Term const* min = yymsp[-1].minor.yy205->min();
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
			Term const* max = yymsp[-1].minor.yy205->max();
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
			ref_ptr<const Referenced> nr_ptr = yymsp[-1].minor.yy205;
			ref_ptr<const Referenced> names_ptr = yymsp[-5].minor.yy410;
			ref_ptr<const SortSymbol> s_ptr = s;

			yygotominor.yy465 = new ConstantDeclaration::ElementList();

			if(implicit){

				ReferencedString const* modeDecl = new ReferencedString("mode");
				ReferencedString const* modeSortString = new ReferencedString("real");
				SortSymbol* modeSort = parser->symtab()->resolveOrCreate(new SortSymbol(modeSortString));
				ref_ptr<ConstantSymbol> mode = new ConstantSymbol(ConstantSymbol::Type::INERTIALFLUENT, modeDecl, modeSort, NULL);
				yygotominor.yy465->push_back(mode);

				CONSTANT_DECL(mode, yymsp[-1].minor.yy205->beginLoc());

				ReferencedString const* durationDecl = new ReferencedString("duration");
				ReferencedString const* durationSortString = new ReferencedString("real[0..50]");
				SortSymbol* durationSort = parser->symtab()->resolveOrCreate(new SortSymbol(durationSortString));
				ref_ptr<ConstantSymbol> duration = new ConstantSymbol(ConstantSymbol::Type::EXOGENOUSACTION, durationDecl, durationSort, NULL);
				yygotominor.yy465->push_back(duration);
				CONSTANT_DECL(duration, yymsp[-1].minor.yy205->beginLoc());

				ReferencedString const* waitDecl = new ReferencedString("wait");
				ref_ptr<SortSymbol> waitSort = parser->symtab()->bsort(SymbolTable::BuiltinSort::BOOLEAN);
				ref_ptr<ConstantSymbol> wait = new ConstantSymbol(ConstantSymbol::Type::ACTION, waitDecl, waitSort, NULL);
				yygotominor.yy465->push_back(wait);
				CONSTANT_DECL(wait, yymsp[-1].minor.yy205->beginLoc());
				implicit=false;
			}

			BOOST_FOREACH(IdentifierDecl& decl, *yymsp[-5].minor.yy410) {
				// attempt to declare each symbol
				ref_ptr<ConstantSymbol> c = new ConstantSymbol(ConstantSymbol::Type::CONTINUOUSFLUENT, decl.first->str(), s_ptr, decl.second);
				yygotominor.yy465->push_back(c);
				CONSTANT_DECL(c, decl.first->beginLoc());
			}


		  yy_destructor(yypParser,87,&yymsp[-4].minor);
  yy_destructor(yypParser,67,&yymsp[-3].minor);
  yy_destructor(yypParser,82,&yymsp[-2].minor);
  yy_destructor(yypParser,83,&yymsp[0].minor);
}
#line 5479 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 349: /* constant_bnd ::= constant_dcl_lst DBL_COLON sort */
#line 1968 "bcplus/parser/detail/lemon_parser.y"
{
		ref_ptr<const Referenced> names_ptr = yymsp[-2].minor.yy410, s_ptr = yymsp[0].minor.yy521;
		yygotominor.yy465 = new ConstantDeclaration::ElementList();
		BOOST_FOREACH(IdentifierDecl& decl, *yymsp[-2].minor.yy410) {
			// attempt to declare each symbol
			ref_ptr<ConstantSymbol> c = new ConstantSymbol(ConstantSymbol::Type::RIGID, decl.first->str(), yymsp[0].minor.yy521, decl.second);
			yygotominor.yy465->push_back(c);
			CONSTANT_DECL(c, decl.first->beginLoc());
		}
	  yy_destructor(yypParser,87,&yymsp[-1].minor);
}
#line 5494 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 350: /* constant_bnd ::= constant_dcl_lst DBL_COLON REAL BRACKET_L num_range BRACKET_R */
#line 1979 "bcplus/parser/detail/lemon_parser.y"
{
		ref_ptr<const Object> min = (Object const*)yymsp[-1].minor.yy205->min();
		ref_ptr<const Object> max = (Object const*)yymsp[-1].minor.yy205->max();
		ObjectSymbol const* minos = min->symbol();
		ObjectSymbol const* maxos = max->symbol();
		std::string temp = "real["+*minos->base()+".."+*maxos->base()+"]";
		ReferencedString const* domainString = new ReferencedString(temp);
		SortSymbol* s = parser->symtab()->resolveOrCreate(new SortSymbol(domainString));
		ref_ptr<const Referenced> nr_ptr = yymsp[-1].minor.yy205;
		ref_ptr<const Referenced> names_ptr = yymsp[-5].minor.yy410;
		ref_ptr<const SortSymbol> s_ptr = s;

		yygotominor.yy465 = new ConstantDeclaration::ElementList();
		BOOST_FOREACH(IdentifierDecl& decl, *yymsp[-5].minor.yy410) {
			// attempt to declare each symbol
			ref_ptr<ConstantSymbol> c = new ConstantSymbol(ConstantSymbol::Type::RIGID, decl.first->str(), s, decl.second);
			yygotominor.yy465->push_back(c);
			CONSTANT_DECL(c, decl.first->beginLoc());
		}
	  yy_destructor(yypParser,87,&yymsp[-4].minor);
  yy_destructor(yypParser,65,&yymsp[-3].minor);
  yy_destructor(yypParser,77,&yymsp[-2].minor);
  yy_destructor(yypParser,78,&yymsp[0].minor);
}
#line 5522 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 351: /* constant_bnd ::= constant_dcl_lst DBL_COLON INTEGER_TYPE BRACKET_L num_range BRACKET_R */
#line 2000 "bcplus/parser/detail/lemon_parser.y"
{
		ref_ptr<const Object> min = (Object const*)yymsp[-1].minor.yy205->min();
		ref_ptr<const Object> max = (Object const*)yymsp[-1].minor.yy205->max();
		ObjectSymbol const* minos = min->symbol();
		ObjectSymbol const* maxos = max->symbol();
		std::string temp = "integer["+*minos->base()+".."+*maxos->base()+"]";
		ReferencedString const* domainString = new ReferencedString(temp);
		SortSymbol* s = parser->symtab()->resolveOrCreate(new SortSymbol(domainString));
		ref_ptr<const Referenced> nr_ptr = yymsp[-1].minor.yy205;
		ref_ptr<const Referenced> names_ptr = yymsp[-5].minor.yy410;
		ref_ptr<const SortSymbol> s_ptr = s;

		yygotominor.yy465 = new ConstantDeclaration::ElementList();
		BOOST_FOREACH(IdentifierDecl& decl, *yymsp[-5].minor.yy410) {
			// attempt to declare each symbol
			ref_ptr<ConstantSymbol> c = new ConstantSymbol(ConstantSymbol::Type::RIGID, decl.first->str(), s, decl.second);
			yygotominor.yy465->push_back(c);
			CONSTANT_DECL(c, decl.first->beginLoc());
		}
	  yy_destructor(yypParser,87,&yymsp[-4].minor);
  yy_destructor(yypParser,66,&yymsp[-3].minor);
  yy_destructor(yypParser,77,&yymsp[-2].minor);
  yy_destructor(yypParser,78,&yymsp[0].minor);
}
#line 5550 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 352: /* constant_bnd ::= constant_dcl_lst DBL_COLON constant_dcl_type */
#line 2021 "bcplus/parser/detail/lemon_parser.y"
{
		ref_ptr<const Referenced> names_ptr = yymsp[-2].minor.yy410;
		yygotominor.yy465 = new ConstantDeclaration::ElementList();
		BOOST_FOREACH(IdentifierDecl& decl, *yymsp[-2].minor.yy410) {
			// attempt to declare each symbol
			ref_ptr<SortSymbol> s = parser->symtab()->bsort(SymbolTable::BuiltinSort::BOOLEAN);

			// NOTE: additive constants default to the additive sort, not the boolean sort
			if (yymsp[0].minor.yy245 & ConstantSymbol::Type::M_ADDITIVE && s->domainType() == DomainType::BOOLEAN )
				s = parser->symtab()->bsort(SymbolTable::BuiltinSort::ADDITIVE);

			// external constants should have "unknown" in their sort
			else if (yymsp[0].minor.yy245 & ConstantSymbol::Type::M_EXTERNAL)
				s = parser->symtab()->carrot(s);

			// non-boolean abActions should contain "none"
			else if (yymsp[0].minor.yy245 == ConstantSymbol::Type::ABACTION && s->domainType() != DomainType::BOOLEAN)
				s = parser->symtab()->star(s);


			ref_ptr<ConstantSymbol> c = new ConstantSymbol(yymsp[0].minor.yy245, decl.first->str(), s, decl.second);
			yygotominor.yy465->push_back(c);
			CONSTANT_DECL(c, decl.first->beginLoc());
		}
	  yy_destructor(yypParser,87,&yymsp[-1].minor);
}
#line 5580 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 353: /* constant_bnd ::= constant_dcl_lst DBL_COLON attrib_spec OF IDENTIFIER */
#line 2047 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy465 = NULL;
		ref_ptr<const Referenced> names_ptr = yymsp[-4].minor.yy410, s_ptr = yymsp[-2].minor.yy220, id_ptr = yymsp[0].minor.yy0;


		// attempt to resolve the attribute parent symbol
		ConstantSymbol const* c = (ConstantSymbol const*) parser->symtab()->resolve(Symbol::Type::CONSTANT, *yymsp[0].minor.yy0->str());

		if (!c) {
			parser->_parse_error("\"" + Symbol::genName(*yymsp[0].minor.yy0->str(), 0) + "\" is not a valid constant symbol.", &yymsp[0].minor.yy0->beginLoc());
			YYERROR;
		} else if (c->constType() != ConstantSymbol::Type::ABACTION && c->constType() != ConstantSymbol::Type::ACTION && c->constType() != ConstantSymbol::Type::EXOGENOUSACTION) {
			parser->_parse_error("Unexpected constant type of attribute parent \"" + Symbol::genName(*yymsp[0].minor.yy0->str(), 0) + "\". Attribute parents must be an \"abAction\", \"action\", or \"exogenousAction\".", &yymsp[0].minor.yy0->beginLoc());
			YYERROR;
		} else {
			yygotominor.yy465 = new ConstantDeclaration::ElementList();
			BOOST_FOREACH(IdentifierDecl& decl, *yymsp[-4].minor.yy410) {
				ref_ptr<ConstantSymbol> c= new AttributeSymbol(decl.first->str(), yymsp[-2].minor.yy220, c, decl.second);
				yygotominor.yy465->push_back(c);
				CONSTANT_DECL(c, decl.first->beginLoc());
			}
		}
	  yy_destructor(yypParser,87,&yymsp[-3].minor);
  yy_destructor(yypParser,63,&yymsp[-1].minor);
}
#line 5609 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 354: /* constant_bnd ::= constant_dcl_lst DBL_COLON attrib_spec OF IDENTIFIER PAREN_L sort_lst PAREN_R */
#line 2071 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy465 = NULL;
		ref_ptr<const Referenced> names_ptr = yymsp[-7].minor.yy410, s_ptr = yymsp[-5].minor.yy220, id_ptr = yymsp[-3].minor.yy0, lst_ptr = yymsp[-1].minor.yy507;

		// attempt to resolve the attribute parent symbol
		ConstantSymbol const* c = (ConstantSymbol const*) parser->symtab()->resolve(Symbol::Type::CONSTANT, *yymsp[-3].minor.yy0->str(), yymsp[-1].minor.yy507->size());

		if (!c) {
			parser->_parse_error("\"" + Symbol::genName(*yymsp[-3].minor.yy0->str(), yymsp[-1].minor.yy507->size()) + "\" is not a valid constant symbol.", &yymsp[-3].minor.yy0->beginLoc());
			YYERROR;
		} else if (c->constType() != ConstantSymbol::Type::ABACTION && c->constType() != ConstantSymbol::Type::ACTION && c->constType() != ConstantSymbol::Type::EXOGENOUSACTION) {
			parser->_parse_error("Unexpected constant type of attribute parent \"" + Symbol::genName(*yymsp[-3].minor.yy0->str(), yymsp[-1].minor.yy507->size()) + "\". Attribute parents must be an \"abAction\", \"action\", or \"exogenousAction\".", &yymsp[-3].minor.yy0->beginLoc());
			YYERROR;
		} else {
			// ensure that the sorts match the declaration of the symbol
			SortList::const_iterator it = yymsp[-1].minor.yy507->begin();
			BOOST_FOREACH(SortSymbol const* sort, *c) {
				if (*it != sort) {
					// check to see if it'yymsp[-5].minor.yy220 a subsort, which is also permissable
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

			yygotominor.yy465 = new ConstantDeclaration::ElementList();
			BOOST_FOREACH(IdentifierDecl& decl, *yymsp[-7].minor.yy410) {
				// ensure that the sorts match the start of the sort list for each of the symbols
				if (decl.second->size() < yymsp[-1].minor.yy507->size()) {
					parser->_parse_error("Detected a malformed attribute declaration. An attribute must duplicate its parent'yymsp[-5].minor.yy220 parameters.", &decl.first->beginLoc());
					YYERROR;
				} else {
					bool good_sort = true;
					it = decl.second->begin();
					BOOST_FOREACH(SortSymbol const* sort, *yymsp[-1].minor.yy507) {
						if (*it != sort) {
							// check to see if it'yymsp[-5].minor.yy220 a subsort, which is also permissable
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
						ref_ptr<ConstantSymbol> sym = new AttributeSymbol(decl.first->str(), yymsp[-5].minor.yy220, c, decl.second);
						yygotominor.yy465->push_back(sym);
						CONSTANT_DECL(sym, decl.first->beginLoc());

					}
				}
			}
		}
	  yy_destructor(yypParser,87,&yymsp[-6].minor);
  yy_destructor(yypParser,63,&yymsp[-4].minor);
  yy_destructor(yypParser,82,&yymsp[-2].minor);
  yy_destructor(yypParser,83,&yymsp[0].minor);
}
#line 5690 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 355: /* constant_dcl_lst ::= IDENTIFIER */
#line 2147 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy410 = new IdentifierDeclList();
		yygotominor.yy410->push_back(IdentifierDecl(yymsp[0].minor.yy0, NULL));
	}
#line 5698 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 356: /* constant_dcl_lst ::= IDENTIFIER PAREN_L sort_lst PAREN_R */
#line 2152 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy410 = new IdentifierDeclList();
		yygotominor.yy410->push_back(IdentifierDecl(yymsp[-3].minor.yy0, yymsp[-1].minor.yy507));
	  yy_destructor(yypParser,82,&yymsp[-2].minor);
  yy_destructor(yypParser,83,&yymsp[0].minor);
}
#line 5708 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 357: /* constant_dcl_lst ::= constant_dcl_lst COMMA IDENTIFIER */
#line 2157 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy410 = yymsp[-2].minor.yy410;
		yygotominor.yy410->push_back(IdentifierDecl(yymsp[0].minor.yy0, NULL));
	  yy_destructor(yypParser,113,&yymsp[-1].minor);
}
#line 5717 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 358: /* constant_dcl_lst ::= constant_dcl_lst COMMA IDENTIFIER PAREN_L sort_lst PAREN_R */
#line 2162 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy410 = yymsp[-5].minor.yy410;
		yygotominor.yy410->push_back(IdentifierDecl(yymsp[-3].minor.yy0, yymsp[-1].minor.yy507));
	  yy_destructor(yypParser,113,&yymsp[-4].minor);
  yy_destructor(yypParser,82,&yymsp[-2].minor);
  yy_destructor(yypParser,83,&yymsp[0].minor);
}
#line 5728 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 359: /* constant_dcl_type ::= ABACTION */
#line 2169 "bcplus/parser/detail/lemon_parser.y"
{
		ref_ptr<const Token> tok_ptr = yymsp[0].minor.yy0;
		yygotominor.yy245 = ConstantSymbol::Type::ABACTION;
		if (!parser->lang()->support(Language::Feature::CONST_ABACTION)) {
			parser->_feature_error(Language::Feature::CONST_ABACTION, &yymsp[0].minor.yy0->beginLoc());
			YYERROR;
		}
	}
#line 5740 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 360: /* constant_dcl_type ::= ACTION */
#line 2178 "bcplus/parser/detail/lemon_parser.y"
{
		ref_ptr<const Token> tok_ptr = yymsp[0].minor.yy0;
		yygotominor.yy245 = ConstantSymbol::Type::ACTION;
		if (!parser->lang()->support(Language::Feature::CONST_ACTION)) {
			parser->_feature_error(Language::Feature::CONST_ACTION, &yymsp[0].minor.yy0->beginLoc());
			YYERROR;
		}
	}
#line 5752 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 361: /* constant_dcl_type ::= ADDITIVEACTION */
#line 2187 "bcplus/parser/detail/lemon_parser.y"
{
		ref_ptr<const Token> tok_ptr = yymsp[0].minor.yy0;
		yygotominor.yy245 = ConstantSymbol::Type::ADDITIVEACTION;
		if (!parser->lang()->support(Language::Feature::CONST_ADDITIVEACTION)) {
			parser->_feature_error(Language::Feature::CONST_ADDITIVEACTION, &yymsp[0].minor.yy0->beginLoc());
			YYERROR;
		}
	}
#line 5764 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 362: /* constant_dcl_type ::= ADDITIVEFLUENT */
#line 2196 "bcplus/parser/detail/lemon_parser.y"
{
		ref_ptr<const Token> tok_ptr = yymsp[0].minor.yy0;
		yygotominor.yy245 = ConstantSymbol::Type::ADDITIVEFLUENT;
		if (!parser->lang()->support(Language::Feature::CONST_ADDITIVEFLUENT)) {
			parser->_feature_error(Language::Feature::CONST_ADDITIVEFLUENT, &yymsp[0].minor.yy0->beginLoc());
			YYERROR;
		}
	}
#line 5776 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 363: /* constant_dcl_type ::= EXTERNALACTION */
#line 2205 "bcplus/parser/detail/lemon_parser.y"
{
		ref_ptr<const Token> tok_ptr = yymsp[0].minor.yy0;
		yygotominor.yy245 = ConstantSymbol::Type::EXTERNALACTION;
		if (!parser->lang()->support(Language::Feature::CONST_EXTERNALACTION)) {
			parser->_feature_error(Language::Feature::CONST_EXTERNALACTION, &yymsp[0].minor.yy0->beginLoc());
			YYERROR;
		}
	}
#line 5788 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 364: /* constant_dcl_type ::= EXTERNALFLUENT */
#line 2214 "bcplus/parser/detail/lemon_parser.y"
{
		ref_ptr<const Token> tok_ptr = yymsp[0].minor.yy0;
		yygotominor.yy245 = ConstantSymbol::Type::EXTERNALFLUENT;
		if (!parser->lang()->support(Language::Feature::CONST_EXTERNALFLUENT)) {
			parser->_feature_error(Language::Feature::CONST_EXTERNALFLUENT, &yymsp[0].minor.yy0->beginLoc());
			YYERROR;
		}
	}
#line 5800 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 365: /* constant_dcl_type ::= EXOGENOUSACTION */
#line 2223 "bcplus/parser/detail/lemon_parser.y"
{
		ref_ptr<const Token> tok_ptr = yymsp[0].minor.yy0;
		yygotominor.yy245 = ConstantSymbol::Type::EXOGENOUSACTION;
		if (!parser->lang()->support(Language::Feature::CONST_EXOGENOUSACTION)) {
			parser->_feature_error(Language::Feature::CONST_EXOGENOUSACTION, &yymsp[0].minor.yy0->beginLoc());
			YYERROR;
		}
	}
#line 5812 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 366: /* constant_dcl_type ::= INERTIALFLUENT */
#line 2232 "bcplus/parser/detail/lemon_parser.y"
{
		ref_ptr<const Token> tok_ptr = yymsp[0].minor.yy0;
		yygotominor.yy245 = ConstantSymbol::Type::INERTIALFLUENT;
		if (!parser->lang()->support(Language::Feature::CONST_INERTIALFLUENT)) {
			parser->_feature_error(Language::Feature::CONST_INERTIALFLUENT, &yymsp[0].minor.yy0->beginLoc());
			YYERROR;
		}
	}
#line 5824 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 367: /* constant_dcl_type ::= RIGID */
#line 2241 "bcplus/parser/detail/lemon_parser.y"
{
		ref_ptr<const Token> tok_ptr = yymsp[0].minor.yy0;
		yygotominor.yy245 = ConstantSymbol::Type::RIGID;
		if (!parser->lang()->support(Language::Feature::CONST_RIGID)) {
			parser->_feature_error(Language::Feature::CONST_RIGID, &yymsp[0].minor.yy0->beginLoc());
			YYERROR;
		}
	}
#line 5836 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 368: /* constant_dcl_type ::= SIMPLEFLUENT */
#line 2250 "bcplus/parser/detail/lemon_parser.y"
{
		ref_ptr<const Token> tok_ptr = yymsp[0].minor.yy0;
		yygotominor.yy245 = ConstantSymbol::Type::SIMPLEFLUENT;
		if (!parser->lang()->support(Language::Feature::CONST_SIMPLEFLUENT)) {
			parser->_feature_error(Language::Feature::CONST_SIMPLEFLUENT, &yymsp[0].minor.yy0->beginLoc());
			YYERROR;
		}
	}
#line 5848 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 369: /* constant_dcl_type ::= SDFLUENT */
#line 2260 "bcplus/parser/detail/lemon_parser.y"
{
		ref_ptr<const Token> tok_ptr = yymsp[0].minor.yy0;
		yygotominor.yy245 = ConstantSymbol::Type::SDFLUENT;
		if (!parser->lang()->support(Language::Feature::CONST_SDFLUENT)) {
			parser->_feature_error(Language::Feature::CONST_SDFLUENT, &yymsp[0].minor.yy0->beginLoc());
			YYERROR;
		}
	}
#line 5860 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 370: /* attrib_spec ::= ATTRIBUTE */
#line 2270 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy220 = NULL;
		ref_ptr<const Referenced> kw_ptr = yymsp[0].minor.yy0;
		if (!parser->lang()->support(Language::Feature::CONST_ATTRIBUTE)) {
			parser->_feature_error(Language::Feature::CONST_ATTRIBUTE, &yymsp[0].minor.yy0->beginLoc());
			YYERROR;
		} else {
			// grab the boolean sort and provide it
			yygotominor.yy220 = parser->symtab()->star(parser->symtab()->bsort(SymbolTable::BuiltinSort::BOOLEAN));
		}
	}
#line 5875 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 371: /* attrib_spec ::= ATTRIBUTE PAREN_L sort PAREN_R */
#line 2283 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy220 = NULL;
		ref_ptr<const Referenced> kw_ptr = yymsp[-3].minor.yy0, s_ptr = yymsp[-1].minor.yy521;
		if (!parser->lang()->support(Language::Feature::CONST_ATTRIBUTE)) {
			parser->_feature_error(Language::Feature::CONST_ATTRIBUTE, &yymsp[-3].minor.yy0->beginLoc());
			YYERROR;
		} else {
			yygotominor.yy220 = parser->symtab()->star(yymsp[-1].minor.yy521);
		}
	  yy_destructor(yypParser,82,&yymsp[-2].minor);
  yy_destructor(yypParser,83,&yymsp[0].minor);
}
#line 5891 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 372: /* attrib_spec ::= ATTRIBUTE PAREN_L REAL BRACKET_L num_range BRACKET_R PAREN_R */
#line 2295 "bcplus/parser/detail/lemon_parser.y"
{
			yygotominor.yy220 = NULL;
			Term const* min = yymsp[-2].minor.yy205->min();
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
			Term const* max = yymsp[-2].minor.yy205->max();
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
			ref_ptr<const Referenced> nr_ptr = yymsp[-2].minor.yy205;
			ref_ptr<const Referenced> kw_ptr = yymsp[-6].minor.yy0, s_ptr = s;
			if (!parser->lang()->support(Language::Feature::CONST_ATTRIBUTE)) {
				parser->_feature_error(Language::Feature::CONST_ATTRIBUTE, &yymsp[-6].minor.yy0->beginLoc());
				YYERROR;
			} else {
				yygotominor.yy220 = parser->symtab()->star(s);
			}
		  yy_destructor(yypParser,82,&yymsp[-5].minor);
  yy_destructor(yypParser,65,&yymsp[-4].minor);
  yy_destructor(yypParser,77,&yymsp[-3].minor);
  yy_destructor(yypParser,78,&yymsp[-1].minor);
  yy_destructor(yypParser,83,&yymsp[0].minor);
}
#line 5962 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 373: /* attrib_spec ::= ATTRIBUTE PAREN_L INTEGER_TYPE BRACKET_L num_range BRACKET_R PAREN_R */
#line 2358 "bcplus/parser/detail/lemon_parser.y"
{
			yygotominor.yy220 = NULL;
			Term const* min = yymsp[-2].minor.yy205->min();
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
			Term const* max = yymsp[-2].minor.yy205->max();
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
			std::string temp = "integer["+preMin+*minos->base()+".."+preMax+*maxos->base()+"]";
			ReferencedString const* domainString = new ReferencedString(temp);
			SortSymbol* s = parser->symtab()->resolveOrCreate(new SortSymbol(domainString));
			ref_ptr<const Referenced> nr_ptr = yymsp[-2].minor.yy205;
			ref_ptr<const Referenced> kw_ptr = yymsp[-6].minor.yy0, s_ptr = s;
			if (!parser->lang()->support(Language::Feature::CONST_ATTRIBUTE)) {
				parser->_feature_error(Language::Feature::CONST_ATTRIBUTE, &yymsp[-6].minor.yy0->beginLoc());
				YYERROR;
			} else {
				yygotominor.yy220 = parser->symtab()->star(s);
			}
		  yy_destructor(yypParser,82,&yymsp[-5].minor);
  yy_destructor(yypParser,66,&yymsp[-4].minor);
  yy_destructor(yypParser,77,&yymsp[-3].minor);
  yy_destructor(yypParser,78,&yymsp[-1].minor);
  yy_destructor(yypParser,83,&yymsp[0].minor);
}
#line 6033 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 374: /* stmt_object_def ::= COLON_DASH OBJECTS object_bnd_lst PERIOD */
#line 2440 "bcplus/parser/detail/lemon_parser.y"
{
		ref_ptr<const Token> cd_ptr = yymsp[-3].minor.yy0;
		ref_ptr<const Token> p_ptr = yymsp[0].minor.yy0;
		ref_ptr<const Token> kw_ptr = yymsp[-2].minor.yy0;
		ref_ptr<ObjectDeclaration::ElementList> l_ptr = yymsp[-1].minor.yy486;

		if (!parser->lang()->support(Language::Feature::DECL_OBJECT)) {
			yygotominor.yy288 = NULL;
			parser->_feature_error(Language::Feature::DECL_OBJECT, &yymsp[-2].minor.yy0->beginLoc());
			YYERROR;
		} else {
			yygotominor.yy288 = new ObjectDeclaration(yymsp[-1].minor.yy486, yymsp[-3].minor.yy0->beginLoc(), yymsp[0].minor.yy0->endLoc());

			// Go ahead and add them to the symbol table
			BOOST_FOREACH(ObjectDeclaration::Element* bnd, *yymsp[-1].minor.yy486) {
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
#line 6068 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 375: /* object_bnd_lst ::= object_bnd */
#line 2473 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy486 = new ObjectDeclaration::ElementList();
		yygotominor.yy486->push_back(yymsp[0].minor.yy278);
	}
#line 6076 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 376: /* object_bnd_lst ::= object_bnd_lst SEMICOLON object_bnd */
#line 2479 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy486 = yymsp[-2].minor.yy486;
		yygotominor.yy486->push_back(yymsp[0].minor.yy278);
	  yy_destructor(yypParser,104,&yymsp[-1].minor);
}
#line 6085 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 377: /* object_bnd ::= object_lst DBL_COLON sort_id */
#line 2485 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy278 = new ObjectDeclaration::Element(yymsp[0].minor.yy521, yymsp[-2].minor.yy13);
	  yy_destructor(yypParser,87,&yymsp[-1].minor);
}
#line 6093 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 378: /* object_lst ::= object_spec */
#line 2490 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy13 = yymsp[0].minor.yy13;
	}
#line 6100 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 379: /* object_lst ::= object_lst COMMA object_spec */
#line 2494 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy13 = yymsp[-2].minor.yy13;
		yygotominor.yy13->splice(yygotominor.yy13->end(), *yymsp[0].minor.yy13);
		delete yymsp[0].minor.yy13;
	  yy_destructor(yypParser,113,&yymsp[-1].minor);
}
#line 6110 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 380: /* object_spec ::= IDENTIFIER */
#line 2503 "bcplus/parser/detail/lemon_parser.y"
{
		ref_ptr<const Token> id_ptr = yymsp[0].minor.yy0;
		yygotominor.yy13 = NULL;
		ref_ptr<const Symbol> o = parser->symtab()->resolveOrCreate(new ObjectSymbol(yymsp[0].minor.yy0->str()));
		if (!o) {
			parser->_parse_error("Detected a conflicting definition of \"" + Symbol::genName(*yymsp[0].minor.yy0->str(),0) + "\".", &yymsp[0].minor.yy0->beginLoc());
			YYERROR;
		} else {
			yygotominor.yy13 = new ObjectDeclaration::Element::ObjectList();
			yygotominor.yy13->push_back(o);
		}
	}
#line 6126 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 381: /* object_spec ::= IDENTIFIER PAREN_L sort_lst PAREN_R */
#line 2516 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy13 = NULL;
		ref_ptr<ObjectSymbol::SortList> lst_ptr = yymsp[-1].minor.yy507;
		ref_ptr<const Token> id_ptr = yymsp[-3].minor.yy0;
		ref_ptr<ObjectSymbol> o = parser->symtab()->resolveOrCreate(new ObjectSymbol(yymsp[-3].minor.yy0->str(), yymsp[-1].minor.yy507));
		if (!o) {
			parser->_parse_error("Detected a conflicting definition of \"" + Symbol::genName(*yymsp[-3].minor.yy0->str(),yymsp[-1].minor.yy507->size()) + "\".", &yymsp[-3].minor.yy0->beginLoc());
			YYERROR;
		} else {
			yygotominor.yy13 = new  ObjectDeclaration::Element::ObjectList();
			yygotominor.yy13->push_back(o.get());
		}
	  yy_destructor(yypParser,82,&yymsp[-2].minor);
  yy_destructor(yypParser,83,&yymsp[0].minor);
}
#line 6145 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 382: /* object_spec ::= INTEGER */
#line 2531 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy13 = NULL;
		ref_ptr<const Token> id_ptr = yymsp[0].minor.yy0;
		ref_ptr<const ObjectSymbol> o = parser->symtab()->resolveOrCreate(new ObjectSymbol(yymsp[0].minor.yy0->str()));
		if (!o) {
			parser->_parse_error("Detected a conflicting definition of \"" + Symbol::genName(*yymsp[0].minor.yy0->str(),0) + "\".", &yymsp[0].minor.yy0->beginLoc());
			YYERROR;
		} else {
			yygotominor.yy13 = new ObjectDeclaration::Element::ObjectList();
			yygotominor.yy13->push_back(o.get());
		}
	}
#line 6161 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 383: /* object_spec ::= FLOAT */
#line 2545 "bcplus/parser/detail/lemon_parser.y"
{
			yygotominor.yy13 = NULL;
			ref_ptr<const Token> id_ptr = yymsp[0].minor.yy0;
			ref_ptr<const ObjectSymbol> o = parser->symtab()->resolveOrCreate(new ObjectSymbol(yymsp[0].minor.yy0->str()));
			if (!o) {
				parser->_parse_error("Detected a conflicting definition of \"" + Symbol::genName(*yymsp[0].minor.yy0->str(),0) + "\".", &yymsp[0].minor.yy0->beginLoc());
				YYERROR;
			} else {
				yygotominor.yy13 = new ObjectDeclaration::Element::ObjectList();
				yygotominor.yy13->push_back(o.get());
			}
		}
#line 6177 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 384: /* object_spec ::= num_range */
#line 2559 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy13 = new ObjectDeclaration::Element::ObjectList();
		ref_ptr<const Referenced> nr_ptr = yymsp[0].minor.yy205;

		// iterate over the range and add it to the list
		ref_ptr<const Symbol> o = parser->symtab()->resolveOrCreate(parser->_newRangeSymbol( yymsp[0].minor.yy205->min(), yymsp[0].minor.yy205->max()));
		if (!o) {
			parser->_parse_error("INTERNAL ERROR: Could not create object symbol.", &yymsp[0].minor.yy205->beginLoc());
			YYERROR;
		} else {
			yygotominor.yy13->push_back(o.get());
		}
	}
#line 6194 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 385: /* stmt_variable_def ::= COLON_DASH VARIABLES variable_bnd_lst PERIOD */
#line 2588 "bcplus/parser/detail/lemon_parser.y"
{
		ref_ptr<const Token> cd_ptr = yymsp[-3].minor.yy0;
		ref_ptr<const Token> p_ptr = yymsp[0].minor.yy0;
		ref_ptr<const Token> kw_ptr = yymsp[-2].minor.yy0;
		ref_ptr<VariableDeclaration::ElementList> l_ptr = yymsp[-1].minor.yy445;

		if (!parser->lang()->support(Language::Feature::DECL_VARIABLE)) {
			yygotominor.yy267 = NULL;
			parser->_feature_error(Language::Feature::DECL_VARIABLE, &yymsp[-2].minor.yy0->beginLoc());
			YYERROR;
		} else {

			VariableSymbol* v2;

			// Go ahead and add them to the symbol table
			BOOST_FOREACH(ref_ptr<VariableSymbol>& v, *yymsp[-1].minor.yy445) {
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

			yygotominor.yy267 = new VariableDeclaration(yymsp[-1].minor.yy445, yymsp[-3].minor.yy0->beginLoc(), yymsp[0].minor.yy0->endLoc());


		}
	}
#line 6232 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 386: /* variable_bnd_lst ::= variable_bnd */
#line 2624 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy445 = yymsp[0].minor.yy445;
	}
#line 6239 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 387: /* variable_bnd_lst ::= variable_bnd_lst SEMICOLON variable_bnd */
#line 2629 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy445 = yymsp[-2].minor.yy445;
		yygotominor.yy445->splice(yygotominor.yy445->end(), *yymsp[0].minor.yy445);
		delete yymsp[0].minor.yy445;
	  yy_destructor(yypParser,104,&yymsp[-1].minor);
}
#line 6249 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 388: /* variable_bnd ::= variable_lst DBL_COLON sort */
#line 2636 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy445 = new VariableDeclaration::ElementList();

		BOOST_FOREACH(Token const* tok, *yymsp[-2].minor.yy400) {
			yygotominor.yy445->push_back(new VariableSymbol(tok->str(), yymsp[0].minor.yy521));
		}



		delete yymsp[-2].minor.yy400;
	  yy_destructor(yypParser,87,&yymsp[-1].minor);
}
#line 6265 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 389: /* variable_bnd ::= variable_lst */
#line 2649 "bcplus/parser/detail/lemon_parser.y"
{
		std::string temp = "tempVarSort";
		ReferencedString const* domainString = new ReferencedString(temp);
		SortSymbol* s = parser->symtab()->resolveOrCreate(new SortSymbol(domainString));
		yygotominor.yy445 = new VariableDeclaration::ElementList();

		BOOST_FOREACH(Token const* tok, *yymsp[0].minor.yy400) {
			yygotominor.yy445->push_back(new VariableSymbol(tok->str(), s));
		}
		delete yymsp[0].minor.yy400;
	}
#line 6280 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 390: /* variable_lst ::= IDENTIFIER */
#line 2662 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy400 = new TokenList();
		yygotominor.yy400->push_back(yymsp[0].minor.yy0);
	}
#line 6288 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 391: /* variable_lst ::= variable_lst COMMA IDENTIFIER */
#line 2667 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy400 = yymsp[-2].minor.yy400;
		yygotominor.yy400->push_back(yymsp[0].minor.yy0);
	  yy_destructor(yypParser,113,&yymsp[-1].minor);
}
#line 6297 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 392: /* stmt_sort_def ::= COLON_DASH SORTS sort_bnd_lst PERIOD */
#line 2688 "bcplus/parser/detail/lemon_parser.y"
{
		ref_ptr<const Token> cd_ptr = yymsp[-3].minor.yy0;
		ref_ptr<const Token> p_ptr = yymsp[0].minor.yy0;
		ref_ptr<const Token> kw_ptr = yymsp[-2].minor.yy0;
		ref_ptr<SortDeclaration::ElementList> l_ptr = yymsp[-1].minor.yy71;

		if (!parser->lang()->support(Language::Feature::DECL_SORT)) {
			yygotominor.yy429 = NULL;
			parser->_feature_error(Language::Feature::DECL_SORT, &yymsp[-2].minor.yy0->beginLoc());
			YYERROR;
		} else {
			yygotominor.yy429 = new SortDeclaration(yymsp[-1].minor.yy71, yymsp[-3].minor.yy0->beginLoc(), yymsp[0].minor.yy0->endLoc());
		}
	}
#line 6315 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 393: /* sort_bnd_lst ::= sort_bnd */
      case 395: /* sort_bnd ::= sort_dcl_lst */ yytestcase(yyruleno==395);
#line 2704 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy71 = yymsp[0].minor.yy71;
	}
#line 6323 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 394: /* sort_bnd_lst ::= sort_bnd_lst SEMICOLON sort_bnd */
#line 2709 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy71 = yymsp[-2].minor.yy71;
		yygotominor.yy71->splice(yygotominor.yy71->end(), *yymsp[0].minor.yy71);
		delete yymsp[0].minor.yy71;
	  yy_destructor(yypParser,104,&yymsp[-1].minor);
}
#line 6333 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 396: /* sort_bnd ::= sort_bnd DBL_LTHAN sort_bnd */
#line 2721 "bcplus/parser/detail/lemon_parser.y"
{
		BOOST_FOREACH(SortSymbol* sym, *yymsp[-2].minor.yy71) {
			BOOST_FOREACH(SortSymbol* sym2, *yymsp[0].minor.yy71) {
				sym2->addSubSort(sym);
			}
		}
		yygotominor.yy71 = yymsp[-2].minor.yy71;
		yygotominor.yy71->splice(yymsp[-2].minor.yy71->end(), *yymsp[0].minor.yy71);
		delete yymsp[0].minor.yy71;

	  yy_destructor(yypParser,111,&yymsp[-1].minor);
}
#line 6349 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 397: /* sort_bnd ::= sort_bnd DBL_GTHAN sort_bnd */
#line 2733 "bcplus/parser/detail/lemon_parser.y"
{
		BOOST_FOREACH(SortSymbol* sym, *yymsp[-2].minor.yy71) {
			BOOST_FOREACH(SortSymbol* sym2, *yymsp[0].minor.yy71) {
				sym->addSubSort(sym2);
			}
		}
		yygotominor.yy71 = yymsp[-2].minor.yy71;
		yygotominor.yy71->splice(yymsp[-2].minor.yy71->end(), *yymsp[0].minor.yy71);
		delete yymsp[0].minor.yy71;
	  yy_destructor(yypParser,110,&yymsp[-1].minor);
}
#line 6364 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 398: /* sort_bnd ::= PAREN_L sort_bnd PAREN_R */
#line 2744 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy71 = yymsp[-1].minor.yy71;
	  yy_destructor(yypParser,82,&yymsp[-2].minor);
  yy_destructor(yypParser,83,&yymsp[0].minor);
}
#line 6373 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 399: /* sort_dcl_lst ::= IDENTIFIER */
#line 2749 "bcplus/parser/detail/lemon_parser.y"
{
		ref_ptr<SortSymbol> s = parser->symtab()->resolveOrCreate(new SortSymbol(yymsp[0].minor.yy0->str()));
		if (!s) {
			yygotominor.yy71 = NULL;
			parser->_parse_error("Detected conflicting definition of sort symbol \"" + Symbol::genName(*yymsp[0].minor.yy0->str(),0) + "\".", &yymsp[0].minor.yy0->beginLoc());
			YYERROR;
		} else {
			yygotominor.yy71 = new SortDeclaration::ElementList();
			yygotominor.yy71->push_back(s);
		}

		delete yymsp[0].minor.yy0;
	}
#line 6390 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 400: /* sort_dcl_lst ::= sort_dcl_lst COMMA IDENTIFIER */
#line 2763 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy71 = yymsp[-2].minor.yy71;
		ref_ptr<SortSymbol> s = parser->symtab()->resolveOrCreate(new SortSymbol(yymsp[0].minor.yy0->str()));
		if (!s) {
			yymsp[-2].minor.yy71 = NULL;
			parser->_parse_error("Detected conflicting definition of sort symbol \"" + Symbol::genName(*yymsp[0].minor.yy0->str(),0) + "\".", &yymsp[0].minor.yy0->beginLoc());
			YYERROR;
		} else {
			yymsp[-2].minor.yy71->push_back(s);
		}

		delete yymsp[0].minor.yy0;

	  yy_destructor(yypParser,113,&yymsp[-1].minor);
}
#line 6409 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 401: /* stmt_show ::= COLON_DASH SHOW show_lst PERIOD */
#line 2790 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy248 = NULL;
		ref_ptr<const Token> cd_ptr = yymsp[-3].minor.yy0, kw_ptr = yymsp[-2].minor.yy0, p_ptr = yymsp[0].minor.yy0;
		ref_ptr<ShowStatement::ElementList> lst_ptr = yymsp[-1].minor.yy235;

		if (!parser->lang()->support(Language::Feature::DECL_SHOW)) {
			parser->_feature_error(Language::Feature::DECL_SHOW, &yymsp[-2].minor.yy0->beginLoc());
			YYERROR;
		} else {
			yygotominor.yy248 = new ShowStatement(yymsp[-1].minor.yy235, yymsp[-3].minor.yy0->beginLoc(), yymsp[0].minor.yy0->endLoc());
		}
	}
#line 6425 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 402: /* stmt_show ::= COLON_DASH SHOW ALL PERIOD */
#line 2804 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy248 = NULL;
		ref_ptr<const Token> cd_ptr = yymsp[-3].minor.yy0, kw_ptr = yymsp[-2].minor.yy0, p_ptr = yymsp[0].minor.yy0, all_ptr = yymsp[-1].minor.yy0;

		if (!parser->lang()->support(Language::Feature::DECL_SHOW)) {
			parser->_feature_error(Language::Feature::DECL_SHOW, &yymsp[-2].minor.yy0->beginLoc());
			YYERROR;
		} else if (!parser->lang()->support(Language::Feature::DECL_SHOW_ALL)) {
			parser->_feature_error(Language::Feature::DECL_SHOW_ALL, &yymsp[-1].minor.yy0->beginLoc());
			YYERROR;
		} else {
			yygotominor.yy248 = new ShowAllStatement(yymsp[-3].minor.yy0->beginLoc(), yymsp[0].minor.yy0->endLoc());
		}
	}
#line 6443 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 403: /* stmt_hide ::= COLON_DASH HIDE show_lst PERIOD */
#line 2821 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy248 = NULL;
		ref_ptr<const Token> cd_ptr = yymsp[-3].minor.yy0, kw_ptr = yymsp[-2].minor.yy0, p_ptr = yymsp[0].minor.yy0;
		ref_ptr<HideStatement::ElementList> lst_ptr = yymsp[-1].minor.yy235;

		if (!parser->lang()->support(Language::Feature::DECL_HIDE)) {
			parser->_feature_error(Language::Feature::DECL_HIDE, &yymsp[-2].minor.yy0->beginLoc());
			YYERROR;
		} else {
			yygotominor.yy248 = new HideStatement(yymsp[-1].minor.yy235, yymsp[-3].minor.yy0->beginLoc(), yymsp[0].minor.yy0->endLoc());
		}
	}
#line 6459 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 404: /* stmt_hide ::= COLON_DASH HIDE ALL PERIOD */
#line 2835 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy248 = NULL;
		ref_ptr<const Token> cd_ptr = yymsp[-3].minor.yy0, kw_ptr = yymsp[-2].minor.yy0, p_ptr = yymsp[0].minor.yy0, all_ptr = yymsp[-1].minor.yy0;

		if (!parser->lang()->support(Language::Feature::DECL_HIDE)) {
			parser->_feature_error(Language::Feature::DECL_HIDE, &yymsp[-2].minor.yy0->beginLoc());
			YYERROR;
		} else if (!parser->lang()->support(Language::Feature::DECL_HIDE_ALL)) {
			parser->_feature_error(Language::Feature::DECL_HIDE_ALL, &yymsp[-1].minor.yy0->beginLoc());
			YYERROR;
		} else {
			yygotominor.yy248 = new HideAllStatement(yymsp[-3].minor.yy0->beginLoc(), yymsp[0].minor.yy0->endLoc());
		}
	}
#line 6477 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 405: /* show_lst ::= show_elem */
#line 2853 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy235 = new ShowStatement::ElementList();
		yygotominor.yy235->push_back(yymsp[0].minor.yy426);
	}
#line 6485 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 406: /* show_lst ::= show_lst COMMA show_elem */
#line 2858 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy235 = yymsp[-2].minor.yy235;
		yygotominor.yy235->push_back(yymsp[0].minor.yy426);
	  yy_destructor(yypParser,113,&yymsp[-1].minor);
}
#line 6494 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 407: /* show_lst ::= show_lst SEMICOLON show_elem */
#line 2863 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy235 = yymsp[-2].minor.yy235;
		yygotominor.yy235->push_back(yymsp[0].minor.yy426);
	  yy_destructor(yypParser,104,&yymsp[-1].minor);
}
#line 6503 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 409: /* stmt_noconcurrency ::= NOCONCURRENCY PERIOD */
#line 2891 "bcplus/parser/detail/lemon_parser.y"
{ NC_STATEMENT(yygotominor.yy505, yymsp[-1].minor.yy0, yymsp[0].minor.yy0, Language::Feature::NOCONCURRENCY, NCStatement); }
#line 6508 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 410: /* stmt_strong_noconcurrency ::= STRONG_NOCONCURRENCY PERIOD */
#line 2892 "bcplus/parser/detail/lemon_parser.y"
{ NC_STATEMENT(yygotominor.yy10, yymsp[-1].minor.yy0, yymsp[0].minor.yy0, Language::Feature::STRONG_NOCONCURRENCY, StrongNCStatement); }
#line 6513 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 411: /* stmt_maxafvalue ::= COLON_DASH MAXAFVALUE EQ term_int_eval PERIOD */
#line 2918 "bcplus/parser/detail/lemon_parser.y"
{ VALUE_DECL(yygotominor.yy248, yymsp[-4].minor.yy0, yymsp[-3].minor.yy0, yymsp[-1].minor.yy289, yymsp[0].minor.yy0, Language::Feature::DECL_MAXAFVALUE, MaxAFValueStatement);   yy_destructor(yypParser,92,&yymsp[-2].minor);
}
#line 6519 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 412: /* stmt_maxafvalue ::= COLON_DASH MAXAFVALUE DBL_COLON term_int_eval PERIOD */
#line 2919 "bcplus/parser/detail/lemon_parser.y"
{ VALUE_DECL(yygotominor.yy248, yymsp[-4].minor.yy0, yymsp[-3].minor.yy0, yymsp[-1].minor.yy289, yymsp[0].minor.yy0, Language::Feature::DECL_MAXAFVALUE, MaxAFValueStatement);   yy_destructor(yypParser,87,&yymsp[-2].minor);
}
#line 6525 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 413: /* stmt_maxadditive ::= COLON_DASH MAXADDITIVE EQ term_int_eval PERIOD */
#line 2920 "bcplus/parser/detail/lemon_parser.y"
{ VALUE_DECL(yygotominor.yy248, yymsp[-4].minor.yy0, yymsp[-3].minor.yy0, yymsp[-1].minor.yy289, yymsp[0].minor.yy0, Language::Feature::DECL_MAXADDITIVE, MaxAdditiveStatement);   yy_destructor(yypParser,92,&yymsp[-2].minor);
}
#line 6531 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 414: /* stmt_maxadditive ::= COLON_DASH MAXADDITIVE DBL_COLON term_int_eval PERIOD */
#line 2921 "bcplus/parser/detail/lemon_parser.y"
{ VALUE_DECL(yygotominor.yy248, yymsp[-4].minor.yy0, yymsp[-3].minor.yy0, yymsp[-1].minor.yy289, yymsp[0].minor.yy0, Language::Feature::DECL_MAXADDITIVE, MaxAdditiveStatement);   yy_destructor(yypParser,87,&yymsp[-2].minor);
}
#line 6537 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 415: /* stmt_query ::= COLON_DASH QUERY query_lst PERIOD */
#line 2946 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy490 = NULL;
		ref_ptr<const Referenced> cd_ptr = yymsp[-3].minor.yy0, kw_ptr = yymsp[-2].minor.yy0, data_l_ptr = yymsp[-1].minor.yy373.l, p_ptr = yymsp[0].minor.yy0;
		ref_ptr<const Referenced> data_maxstep_ptr = yymsp[-1].minor.yy373.maxstep, data_label_ptr = yymsp[-1].minor.yy373.label;

		ref_ptr<const ReferencedString> label;
		if (yymsp[-1].minor.yy373.label) label = yymsp[-1].minor.yy373.label->str();
		else label = new ReferencedString("0");

		int min = -1, max = -1;
		if (yymsp[-1].minor.yy373.maxstep) {
			min = yymsp[-1].minor.yy373.maxstep->min();
			max = yymsp[-1].minor.yy373.maxstep->max();
		}

		if (!parser->lang()->support(Language::Feature::DECL_QUERY)) {
			parser->_feature_error(Language::Feature::DECL_QUERY, &yymsp[-2].minor.yy0->beginLoc());
			YYERROR;
		} else {
			bool good = true;

			// resolve the query label
			ref_ptr<QuerySymbol> sym = new QuerySymbol(label, min, max);
			if (!parser->symtab()->create(sym)) {
				parser->_parse_error("Could not create query, the label \"" + *label + "\" already exists.", (yymsp[-1].minor.yy373.label ? &yymsp[-1].minor.yy373.label->beginLoc() : &yymsp[-2].minor.yy0->beginLoc()));
				good = false;
				YYERROR;
			}


			if (good) yygotominor.yy490 = new QueryStatement(sym, yymsp[-1].minor.yy373.l, yymsp[-3].minor.yy0->beginLoc(), yymsp[0].minor.yy0->endLoc());
		}
	}
#line 6574 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 416: /* query_lst ::= formula_temporal */
#line 2982 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy373.l = new QueryStatement::FormulaList();
		yygotominor.yy373.maxstep = NULL;
		yygotominor.yy373.label = NULL;

		yygotominor.yy373.l->push_back(yymsp[0].minor.yy297);
	}
#line 6585 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 417: /* query_lst ::= query_maxstep_decl */
#line 2991 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy373.l = new QueryStatement::FormulaList();
		yygotominor.yy373.maxstep = yymsp[0].minor.yy21;
		yygotominor.yy373.label = NULL;
	}
#line 6594 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 418: /* query_lst ::= query_label_decl */
#line 2998 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy373.l = new QueryStatement::FormulaList();
		yygotominor.yy373.maxstep = NULL;
		yygotominor.yy373.label = yymsp[0].minor.yy75;
	}
#line 6603 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 419: /* query_lst ::= query_lst SEMICOLON formula_temporal */
#line 3005 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy373 = yymsp[-2].minor.yy373;
		yymsp[-2].minor.yy373.l->push_back(yymsp[0].minor.yy297);
	  yy_destructor(yypParser,104,&yymsp[-1].minor);
}
#line 6612 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 420: /* query_lst ::= query_lst SEMICOLON query_maxstep_decl */
#line 3011 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy373 = yymsp[-2].minor.yy373;

		if (yygotominor.yy373.maxstep) {
			parser->_parse_error("Encountered multiple maxstep definitions within a query.", &yymsp[0].minor.yy21->beginLoc());
			delete yymsp[0].minor.yy21;
			YYERROR;
		} else {
			yygotominor.yy373.maxstep = yymsp[0].minor.yy21;
		}
	  yy_destructor(yypParser,104,&yymsp[-1].minor);
}
#line 6628 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 421: /* query_lst ::= query_lst SEMICOLON query_label_decl */
#line 3024 "bcplus/parser/detail/lemon_parser.y"
{
		yygotominor.yy373 = yymsp[-2].minor.yy373;
		if (yygotominor.yy373.label) {
			parser->_parse_error("Encountered multiple maxstep definitions within a query.", &yymsp[0].minor.yy75->beginLoc());
			delete yymsp[0].minor.yy75;
			YYERROR;

		} else {
			yygotominor.yy373.label = yymsp[0].minor.yy75;
		}
	  yy_destructor(yypParser,104,&yymsp[-1].minor);
}
#line 6644 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 422: /* query_maxstep_decl ::= MAXSTEP DBL_COLON INTEGER */
#line 3050 "bcplus/parser/detail/lemon_parser.y"
{
	yygotominor.yy21 = NULL;
	ref_ptr<const Referenced> kw_ptr = yymsp[-2].minor.yy0, i_ptr = yymsp[0].minor.yy0;


	if (!parser->lang()->support(Language::Feature::QUERY_MAXSTEP)) {
		parser->_feature_error(Language::Feature::QUERY_MAXSTEP, &yymsp[-2].minor.yy0->beginLoc());
		YYERROR;
	} else {

		int max = -1;
		try {
			max = boost::lexical_cast<int>(*yymsp[0].minor.yy0->str());
			yygotominor.yy21 = new NumberRangeEval(-1, max, yymsp[0].minor.yy0->beginLoc(), yymsp[0].minor.yy0->endLoc());
		} catch (boost::bad_lexical_cast const& e) {
			parser->_parse_error("INTERNAL ERROR: An error occurred extracting an integer from \"" + *yymsp[0].minor.yy0->str() + "\".", &yymsp[0].minor.yy0->beginLoc());
			YYERROR;
		}
	}
  yy_destructor(yypParser,87,&yymsp[-1].minor);
}
#line 6669 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 423: /* query_maxstep_decl ::= MAXSTEP DBL_COLON num_range_eval */
#line 3071 "bcplus/parser/detail/lemon_parser.y"
{
	yygotominor.yy21 = NULL;
	ref_ptr<const Referenced> kw_ptr = yymsp[-2].minor.yy0, nr_ptr = yymsp[0].minor.yy21;

	if (!parser->lang()->support(Language::Feature::QUERY_MAXSTEP)) {
		parser->_feature_error(Language::Feature::QUERY_MAXSTEP, &yymsp[-2].minor.yy0->beginLoc());
		YYERROR;
	} else {
		yygotominor.yy21 = yymsp[0].minor.yy21;
		nr_ptr.release();
	}
  yy_destructor(yypParser,87,&yymsp[-1].minor);
}
#line 6686 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 424: /* query_label_decl ::= LABEL DBL_COLON INTEGER */
      case 425: /* query_label_decl ::= LABEL DBL_COLON IDENTIFIER */ yytestcase(yyruleno==425);
#line 3085 "bcplus/parser/detail/lemon_parser.y"
{ QUERY_DECL(yygotominor.yy75, yymsp[-2].minor.yy0, yymsp[0].minor.yy0, Language::Feature::QUERY_LABEL);   yy_destructor(yypParser,87,&yymsp[-1].minor);
}
#line 6693 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 426: /* clause_if ::= IF formula */
#line 3120 "bcplus/parser/detail/lemon_parser.y"
{ CLAUSE(yygotominor.yy297, yymsp[-1].minor.yy0, yymsp[0].minor.yy297, Language::Feature::CLAUSE_IF); 		}
#line 6698 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 427: /* clause_if ::= */
      case 429: /* clause_after ::= */ yytestcase(yyruleno==429);
      case 431: /* clause_ifcons ::= */ yytestcase(yyruleno==431);
      case 435: /* clause_where ::= */ yytestcase(yyruleno==435);
#line 3121 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy297 = NULL; }
#line 6706 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 428: /* clause_after ::= AFTER formula */
#line 3122 "bcplus/parser/detail/lemon_parser.y"
{ CLAUSE(yygotominor.yy297, yymsp[-1].minor.yy0, yymsp[0].minor.yy297, Language::Feature::CLAUSE_AFTER);	}
#line 6711 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 430: /* clause_ifcons ::= IFCONS formula */
#line 3124 "bcplus/parser/detail/lemon_parser.y"
{ CLAUSE(yygotominor.yy297, yymsp[-1].minor.yy0, yymsp[0].minor.yy297, Language::Feature::CLAUSE_IFCONS); 	}
#line 6716 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 432: /* clause_unless ::= UNLESS atomic_formula_anon */
#line 3126 "bcplus/parser/detail/lemon_parser.y"
{ CLAUSE(yygotominor.yy426, yymsp[-1].minor.yy0, yymsp[0].minor.yy426, Language::Feature::CLAUSE_UNLESS); 	}
#line 6721 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 433: /* clause_unless ::= */
#line 3127 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy426 = NULL; }
#line 6726 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 434: /* clause_where ::= WHERE formula_no_const */
#line 3128 "bcplus/parser/detail/lemon_parser.y"
{ CLAUSE(yygotominor.yy297, yymsp[-1].minor.yy0, yymsp[0].minor.yy297, Language::Feature::CLAUSE_WHERE); 	}
#line 6731 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 436: /* rate_decl ::= DERIVATIVE OF constant IS term IF MODE EQ INTEGER PERIOD */
#line 3139 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy541 = new RateDeclaration(yymsp[-7].minor.yy257,yymsp[-5].minor.yy115,yymsp[-1].minor.yy0->str());   yy_destructor(yypParser,46,&yymsp[-9].minor);
  yy_destructor(yypParser,63,&yymsp[-8].minor);
  yy_destructor(yypParser,48,&yymsp[-6].minor);
  yy_destructor(yypParser,47,&yymsp[-4].minor);
  yy_destructor(yypParser,49,&yymsp[-3].minor);
  yy_destructor(yypParser,92,&yymsp[-2].minor);
  yy_destructor(yypParser,84,&yymsp[0].minor);
}
#line 6743 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 437: /* alwayst_stmt ::= ALWAYST formula IF MODE EQ INTEGER PERIOD */
#line 3150 "bcplus/parser/detail/lemon_parser.y"
{ yygotominor.yy180 = new ForallTStatement(yymsp[-5].minor.yy297,yymsp[-1].minor.yy0->str());   yy_destructor(yypParser,32,&yymsp[-6].minor);
  yy_destructor(yypParser,47,&yymsp[-4].minor);
  yy_destructor(yypParser,49,&yymsp[-3].minor);
  yy_destructor(yypParser,92,&yymsp[-2].minor);
  yy_destructor(yypParser,84,&yymsp[0].minor);
}
#line 6753 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 438: /* stmt_law ::= law_basic */
      case 439: /* stmt_law ::= law_caused */ yytestcase(yyruleno==439);
      case 440: /* stmt_law ::= law_pcaused */ yytestcase(yyruleno==440);
      case 441: /* stmt_law ::= law_impl */ yytestcase(yyruleno==441);
      case 442: /* stmt_law ::= law_causes */ yytestcase(yyruleno==442);
      case 443: /* stmt_law ::= law_increments */ yytestcase(yyruleno==443);
      case 444: /* stmt_law ::= law_decrements */ yytestcase(yyruleno==444);
      case 445: /* stmt_law ::= law_mcause */ yytestcase(yyruleno==445);
      case 446: /* stmt_law ::= law_always */ yytestcase(yyruleno==446);
      case 447: /* stmt_law ::= law_constraint */ yytestcase(yyruleno==447);
      case 448: /* stmt_law ::= law_impossible */ yytestcase(yyruleno==448);
      case 449: /* stmt_law ::= law_never */ yytestcase(yyruleno==449);
      case 450: /* stmt_law ::= law_default */ yytestcase(yyruleno==450);
      case 451: /* stmt_law ::= law_exogenous */ yytestcase(yyruleno==451);
      case 452: /* stmt_law ::= law_inertial */ yytestcase(yyruleno==452);
      case 453: /* stmt_law ::= law_nonexecutable */ yytestcase(yyruleno==453);
      case 454: /* stmt_law ::= law_rigid */ yytestcase(yyruleno==454);
      case 455: /* stmt_law ::= law_observed */ yytestcase(yyruleno==455);
      case 456: /* stmt_law ::= law_temporal_constraint */ yytestcase(yyruleno==456);
#line 3198 "bcplus/parser/detail/lemon_parser.y"
{yygotominor.yy248 = yymsp[0].minor.yy248;}
#line 6776 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 457: /* law_basic ::= head_formula clause_if clause_ifcons clause_after clause_unless clause_where PERIOD */
#line 3319 "bcplus/parser/detail/lemon_parser.y"
{
		if (yymsp[-5].minor.yy297 || yymsp[-4].minor.yy297 || yymsp[-3].minor.yy297 || yymsp[-2].minor.yy426 || yymsp[-1].minor.yy297) {
			LAW_BASIC_FORM(yygotominor.yy248, NULL, yymsp[-6].minor.yy297, yymsp[-5].minor.yy297, yymsp[-4].minor.yy297, yymsp[-3].minor.yy297,
				yymsp[-2].minor.yy426, yymsp[-1].minor.yy297, yymsp[0].minor.yy0, Language::Feature::LAW_BASIC_S,
				Language::Feature::LAW_BASIC_D, BasicLaw);
		} else {
			LAW_BASIC_FORM(yygotominor.yy248, NULL, yymsp[-6].minor.yy297, yymsp[-5].minor.yy297, yymsp[-4].minor.yy297, yymsp[-3].minor.yy297,
				yymsp[-2].minor.yy426, yymsp[-1].minor.yy297, yymsp[0].minor.yy0, Language::Feature::LAW_BASIC_FACT,
				Language::Feature::LAW_BASIC_FACT, BasicLaw);
		}
	}
#line 6791 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 458: /* law_caused ::= CAUSED head_formula clause_if clause_ifcons clause_after clause_unless clause_where PERIOD */
#line 3331 "bcplus/parser/detail/lemon_parser.y"
{ LAW_BASIC_FORM(yygotominor.yy248, yymsp[-7].minor.yy0, yymsp[-6].minor.yy297, yymsp[-5].minor.yy297, yymsp[-4].minor.yy297, yymsp[-3].minor.yy297,
																																														yymsp[-2].minor.yy426, yymsp[-1].minor.yy297, yymsp[0].minor.yy0, Language::Feature::LAW_CAUSED_S,
																																															Language::Feature::LAW_CAUSED_D, CausedLaw); }
#line 6798 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 459: /* law_pcaused ::= POSSIBLY_CAUSED head_formula clause_if clause_ifcons clause_after clause_unless clause_where PERIOD */
#line 3335 "bcplus/parser/detail/lemon_parser.y"
{ LAW_BASIC_FORM(yygotominor.yy248, yymsp[-7].minor.yy0, yymsp[-6].minor.yy297, yymsp[-5].minor.yy297, yymsp[-4].minor.yy297, yymsp[-3].minor.yy297,
																																														yymsp[-2].minor.yy426, yymsp[-1].minor.yy297, yymsp[0].minor.yy0, Language::Feature::LAW_PCAUSED_S,
																																															Language::Feature::LAW_PCAUSED_D, PossiblyCausedLaw); }
#line 6805 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 460: /* law_impl ::= head_formula ARROW_LDASH formula clause_where PERIOD */
#line 3339 "bcplus/parser/detail/lemon_parser.y"
{ LAW_IMPL_FORM(yygotominor.yy248, yymsp[-4].minor.yy297, yymsp[-3].minor.yy0, yymsp[-2].minor.yy297, yymsp[-1].minor.yy297, yymsp[0].minor.yy0,
																																														Language::Feature::LAW_IMPL, ImplicationLaw); }
#line 6811 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 461: /* law_impl ::= ARROW_LDASH formula clause_where PERIOD */
#line 3342 "bcplus/parser/detail/lemon_parser.y"
{ LAW_IMPL_FORM(yygotominor.yy248, NULL, yymsp[-3].minor.yy0, yymsp[-2].minor.yy297, yymsp[-1].minor.yy297, yymsp[0].minor.yy0,
																																														Language::Feature::LAW_IMPL, ImplicationLaw); }
#line 6817 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 462: /* law_causes ::= atomic_formula CAUSES head_formula clause_if clause_unless clause_where PERIOD */
#line 3345 "bcplus/parser/detail/lemon_parser.y"
{ LAW_DYNAMIC_FORM(yygotominor.yy248, yymsp[-6].minor.yy426, yymsp[-5].minor.yy0, yymsp[-4].minor.yy297, yymsp[-3].minor.yy297, yymsp[-2].minor.yy426, yymsp[-1].minor.yy297, yymsp[0].minor.yy0,
																																														Language::Feature::LAW_CAUSES, CausesLaw); }
#line 6823 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 463: /* law_increments ::= atomic_formula INCREMENTS constant BY term clause_if clause_unless clause_where PERIOD */
#line 3349 "bcplus/parser/detail/lemon_parser.y"
{ LAW_INCREMENTAL_FORM(yygotominor.yy248, yymsp[-8].minor.yy426, yymsp[-7].minor.yy0, yymsp[-6].minor.yy257, yymsp[-4].minor.yy115, yymsp[-3].minor.yy297, yymsp[-2].minor.yy426, yymsp[-1].minor.yy297, yymsp[0].minor.yy0,
																																														Language::Feature::LAW_INCREMENTS, IncrementsLaw);   yy_destructor(yypParser,35,&yymsp[-5].minor);
}
#line 6830 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 464: /* law_decrements ::= atomic_formula DECREMENTS constant BY term clause_if clause_unless clause_where PERIOD */
#line 3352 "bcplus/parser/detail/lemon_parser.y"
{ LAW_INCREMENTAL_FORM(yygotominor.yy248, yymsp[-8].minor.yy426, yymsp[-7].minor.yy0, yymsp[-6].minor.yy257, yymsp[-4].minor.yy115, yymsp[-3].minor.yy297, yymsp[-2].minor.yy426, yymsp[-1].minor.yy297, yymsp[0].minor.yy0,
																																														Language::Feature::LAW_DECREMENTS, DecrementsLaw);   yy_destructor(yypParser,35,&yymsp[-5].minor);
}
#line 6837 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 465: /* law_mcause ::= atomic_formula MAY_CAUSE head_formula clause_if clause_unless clause_where PERIOD */
#line 3356 "bcplus/parser/detail/lemon_parser.y"
{ LAW_DYNAMIC_FORM(yygotominor.yy248, yymsp[-6].minor.yy426, yymsp[-5].minor.yy0, yymsp[-4].minor.yy297, yymsp[-3].minor.yy297, yymsp[-2].minor.yy426, yymsp[-1].minor.yy297, yymsp[0].minor.yy0,
																																														Language::Feature::LAW_MCAUSE, MayCauseLaw); }
#line 6843 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 466: /* law_always ::= ALWAYS formula clause_after clause_unless clause_where PERIOD */
#line 3360 "bcplus/parser/detail/lemon_parser.y"
{ LAW_CONSTRAINT_FORM(yygotominor.yy248, yymsp[-5].minor.yy0, yymsp[-4].minor.yy297, yymsp[-3].minor.yy297, yymsp[-2].minor.yy426, yymsp[-1].minor.yy297, yymsp[0].minor.yy0,
																																														Language::Feature::LAW_ALWAYS_S,
																																															Language::Feature::LAW_ALWAYS_D, AlwaysLaw); }
#line 6850 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 467: /* law_constraint ::= CONSTRAINT formula clause_after clause_unless clause_where PERIOD */
#line 3364 "bcplus/parser/detail/lemon_parser.y"
{ LAW_CONSTRAINT_FORM(yygotominor.yy248, yymsp[-5].minor.yy0, yymsp[-4].minor.yy297, yymsp[-3].minor.yy297, yymsp[-2].minor.yy426, yymsp[-1].minor.yy297, yymsp[0].minor.yy0,
																																														Language::Feature::LAW_CONSTRAINT_S,
																																															Language::Feature::LAW_CONSTRAINT_D, ConstraintLaw); }
#line 6857 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 468: /* law_impossible ::= IMPOSSIBLE formula clause_after clause_unless clause_where PERIOD */
#line 3368 "bcplus/parser/detail/lemon_parser.y"
{ LAW_CONSTRAINT_FORM(yygotominor.yy248, yymsp[-5].minor.yy0, yymsp[-4].minor.yy297, yymsp[-3].minor.yy297, yymsp[-2].minor.yy426, yymsp[-1].minor.yy297, yymsp[0].minor.yy0,
																																														Language::Feature::LAW_IMPOSSIBLE_S,
																																															Language::Feature::LAW_IMPOSSIBLE_D, ImpossibleLaw); }
#line 6864 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 469: /* law_never ::= NEVER formula clause_after clause_unless clause_where PERIOD */
#line 3372 "bcplus/parser/detail/lemon_parser.y"
{ LAW_CONSTRAINT_FORM(yygotominor.yy248, yymsp[-5].minor.yy0, yymsp[-4].minor.yy297, yymsp[-3].minor.yy297, yymsp[-2].minor.yy426, yymsp[-1].minor.yy297, yymsp[0].minor.yy0,
																																														Language::Feature::LAW_NEVER_S,
																																															Language::Feature::LAW_NEVER_D, NeverLaw); }
#line 6871 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 470: /* law_default ::= DEFAULT atomic_head_formula clause_if clause_ifcons clause_after clause_unless clause_where PERIOD */
#line 3376 "bcplus/parser/detail/lemon_parser.y"
{ LAW_BASIC_FORM(yygotominor.yy248, yymsp[-7].minor.yy0, yymsp[-6].minor.yy426, yymsp[-5].minor.yy297, yymsp[-4].minor.yy297, yymsp[-3].minor.yy297,
																																														yymsp[-2].minor.yy426, yymsp[-1].minor.yy297, yymsp[0].minor.yy0, Language::Feature::LAW_DEFAULT_S,
																																															Language::Feature::LAW_DEFAULT_D, DefaultLaw); }
#line 6878 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 471: /* law_exogenous ::= EXOGENOUS constant clause_if clause_ifcons clause_after clause_unless clause_where PERIOD */
#line 3380 "bcplus/parser/detail/lemon_parser.y"
{ LAW_BASIC_FORM(yygotominor.yy248, yymsp[-7].minor.yy0, yymsp[-6].minor.yy257, yymsp[-5].minor.yy297, yymsp[-4].minor.yy297, yymsp[-3].minor.yy297,
																																														yymsp[-2].minor.yy426, yymsp[-1].minor.yy297, yymsp[0].minor.yy0, Language::Feature::LAW_EXOGENOUS_S,
																																															Language::Feature::LAW_EXOGENOUS_D, ExogenousLaw); }
#line 6885 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 472: /* law_inertial ::= INERTIAL constant clause_if clause_ifcons clause_after clause_unless clause_where PERIOD */
#line 3384 "bcplus/parser/detail/lemon_parser.y"
{ LAW_BASIC_FORM(yygotominor.yy248, yymsp[-7].minor.yy0, yymsp[-6].minor.yy257, yymsp[-5].minor.yy297, yymsp[-4].minor.yy297, yymsp[-3].minor.yy297,
																																														yymsp[-2].minor.yy426, yymsp[-1].minor.yy297, yymsp[0].minor.yy0, Language::Feature::LAW_INERTIAL_S,
																																															Language::Feature::LAW_INERTIAL_D, InertialLaw); }
#line 6892 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 473: /* law_nonexecutable ::= NONEXECUTABLE formula clause_if clause_unless clause_where PERIOD */
#line 3388 "bcplus/parser/detail/lemon_parser.y"
{ LAW_DYNAMIC_CONSTRAINT_FORM(yygotominor.yy248, yymsp[-5].minor.yy0, yymsp[-4].minor.yy297, yymsp[-3].minor.yy297, yymsp[-2].minor.yy426, yymsp[-1].minor.yy297,
																																														yymsp[0].minor.yy0, Language::Feature::LAW_NONEXECUTABLE, NonexecutableLaw); }
#line 6898 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 474: /* law_rigid ::= RIGID constant clause_where PERIOD */
#line 3392 "bcplus/parser/detail/lemon_parser.y"
{ LAW_SIMPLE_FORM(yygotominor.yy248, yymsp[-3].minor.yy0, yymsp[-2].minor.yy257, yymsp[-1].minor.yy297, yymsp[0].minor.yy0,
																																														Language::Feature::LAW_RIGID, RigidLaw); }
#line 6904 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 475: /* law_observed ::= OBSERVED atomic_head_formula AT term_int_eval PERIOD */
#line 3397 "bcplus/parser/detail/lemon_parser.y"
{
			LAW_SIMPLE_FORM(yygotominor.yy248, yymsp[-4].minor.yy0, yymsp[-3].minor.yy426, yymsp[-1].minor.yy289, yymsp[0].minor.yy0, Language::Feature::LAW_OBSERVED, ObservedLaw);
		  yy_destructor(yypParser,76,&yymsp[-2].minor);
}
#line 6912 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 476: /* law_temporal_constraint ::= CONSTRAINT formula AT term_int_eval PERIOD */
#line 3402 "bcplus/parser/detail/lemon_parser.y"
{
			LAW_SIMPLE_FORM(yygotominor.yy248, yymsp[-4].minor.yy0, yymsp[-3].minor.yy297, yymsp[-1].minor.yy289, yymsp[0].minor.yy0, Language::Feature::LAW_TEMPORAL_CONSTRAINT, TemporalConstraintLaw);
		  yy_destructor(yypParser,76,&yymsp[-2].minor);
}
#line 6920 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 477: /* stmt_code_blk ::= ASP_GR */
#line 3425 "bcplus/parser/detail/lemon_parser.y"
{ CODE_BLK(yygotominor.yy248, yymsp[0].minor.yy0, Language::Feature::CODE_ASP_GR, ASPBlock);	}
#line 6925 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 478: /* stmt_code_blk ::= ASP_CP */
#line 3426 "bcplus/parser/detail/lemon_parser.y"
{ CODE_BLK(yygotominor.yy248, yymsp[0].minor.yy0, Language::Feature::CODE_ASP_CP, ASPBlock);	}
#line 6930 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 479: /* stmt_code_blk ::= F2LP_GR */
#line 3427 "bcplus/parser/detail/lemon_parser.y"
{ CODE_BLK(yygotominor.yy248, yymsp[0].minor.yy0, Language::Feature::CODE_F2LP_GR, F2LPBlock);	}
#line 6935 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 480: /* stmt_code_blk ::= F2LP_CP */
#line 3428 "bcplus/parser/detail/lemon_parser.y"
{ CODE_BLK(yygotominor.yy248, yymsp[0].minor.yy0, Language::Feature::CODE_F2LP_CP, F2LPBlock); }
#line 6940 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 481: /* stmt_code_blk ::= LUA_GR */
#line 3429 "bcplus/parser/detail/lemon_parser.y"
{ CODE_BLK(yygotominor.yy248, yymsp[0].minor.yy0, Language::Feature::CODE_LUA_GR, LUABlock);   }
#line 6945 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 482: /* stmt_code_blk ::= LUA_CP */
#line 3430 "bcplus/parser/detail/lemon_parser.y"
{ CODE_BLK(yygotominor.yy248, yymsp[0].minor.yy0, Language::Feature::CODE_LUA_CP, LUABlock);   }
#line 6950 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 483: /* stmt_code_blk ::= PYTHON_GR */
#line 3431 "bcplus/parser/detail/lemon_parser.y"
{ CODE_BLK(yygotominor.yy248, yymsp[0].minor.yy0, Language::Feature::CODE_PYTHON_GR, PYTHONBlock);   }
#line 6955 "bcplus/parser/detail/lemon_parser.c"
        break;
      case 484: /* stmt_code_blk ::= PYTHON_CP */
#line 3432 "bcplus/parser/detail/lemon_parser.y"
{ CODE_BLK(yygotominor.yy248, yymsp[0].minor.yy0, Language::Feature::CODE_PYTHON_CP, PYTHONBlock);   }
#line 6960 "bcplus/parser/detail/lemon_parser.c"
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
#line 214 "bcplus/parser/detail/lemon_parser.y"
 parser->_parse_error("Syntax error.");	
#line 7026 "bcplus/parser/detail/lemon_parser.c"
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
