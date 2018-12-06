/*******************************************************************\

Module: Lower expressions to arithmetic and logic expressions

Author: Michael Tautschnig

\*******************************************************************/

#ifndef CPROVER_SOLVERS_LOWERING_EXPR_LOWERING_H
#define CPROVER_SOLVERS_LOWERING_EXPR_LOWERING_H

#include <util/expr.h>

class byte_extract_exprt;
class namespacet;
class popcount_exprt;

exprt lower_byte_extract(const byte_extract_exprt &src, const namespacet &ns);

exprt lower_byte_operators(const exprt &src, const namespacet &ns);

bool has_byte_operator(const exprt &src);

/// Lower a popcount_exprt to arithmetic and logic expressions
/// \param expr  Input expression to be translated
/// \param ns  Namespace for type lookups
/// \return Semantically equivalent expression
exprt lower_popcount(const popcount_exprt &expr, const namespacet &ns);

#endif /* CPROVER_SOLVERS_LOWERING_EXPR_LOWERING_H */
