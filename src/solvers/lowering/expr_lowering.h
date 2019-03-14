/*******************************************************************\

Module: Lower expressions to arithmetic and logic expressions

Author: Michael Tautschnig

\*******************************************************************/

#ifndef CPROVER_SOLVERS_LOWERING_EXPR_LOWERING_H
#define CPROVER_SOLVERS_LOWERING_EXPR_LOWERING_H

#include <util/expr.h>

class byte_extract_exprt;
class byte_update_exprt;
class namespacet;
class popcount_exprt;

/// Rewrite a byte extract expression to more fundamental operations.
/// \param src: Byte extract expression
/// \param ns: Namespace
/// \return Semantically equivalent expression such that the top-level
///   expression no longer is a \ref byte_extract_exprt or
///   \ref byte_update_exprt. Use \ref lower_byte_operators to also remove all
///   byte operators from any operands of \p src.
exprt lower_byte_extract(const byte_extract_exprt &src, const namespacet &ns);

/// Rewrite a byte update expression to more fundamental operations.
/// \param src: Byte update expression
/// \param ns: Namespace
/// \return Semantically equivalent expression such that the top-level
///   expression no longer is a \ref byte_extract_exprt or
///   \ref byte_update_exprt. Use \ref lower_byte_operators to also remove all
///   byte operators from any operands of \p src.
exprt lower_byte_update(const byte_update_exprt &src, const namespacet &ns);

/// Rewrite an expression possibly containing byte-extract or -update
/// expressions to more fundamental operations.
/// \param src: Input expression
/// \param ns: Namespace
/// \return Semantically equivalent expression that does not contain any \ref
///   byte_extract_exprt or \ref byte_update_exprt.
exprt lower_byte_operators(const exprt &src, const namespacet &ns);

bool has_byte_operator(const exprt &src);

/// Lower a popcount_exprt to arithmetic and logic expressions
/// \param expr: Input expression to be translated
/// \param ns: Namespace for type lookups
/// \return Semantically equivalent expression
exprt lower_popcount(const popcount_exprt &expr, const namespacet &ns);

#endif /* CPROVER_SOLVERS_LOWERING_EXPR_LOWERING_H */
