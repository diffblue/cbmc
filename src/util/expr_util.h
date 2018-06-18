/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_EXPR_UTIL_H
#define CPROVER_UTIL_EXPR_UTIL_H

/*! \file util/expr_util.h
 * \brief Deprecated expression utility functions
 *
 * \author Daniel Kroening <kroening@kroening.com>
 * \date   Sun Jul 31 21:54:44 BST 2011
*/

#include "irep.h"

#include <functional>

class exprt;
class symbol_exprt;
class update_exprt;
class with_exprt;
class if_exprt;
class symbolt;
class typet;
class namespacet;

/// Creates a type with size (in bytes) equal to the size argument.
/// Makes use of sizeof() in the argument to avoid unnecessary use of byte
/// arrays.
/// \param size: An expression describing the size (in bytes) of the desired
///              type.
/// \param ns : A namespace for symbol type lookups.
/// \return A type with size given by the argument \a size.
///         If \a size is of the form n*sizeof(T) (or sizeof(T)*n), then this
///         type will be T[n]. If \a size is of the form sizeof(T), then this
///         type will be T. Otherwise, the type will be unsigned char[size].
typet type_from_size(const exprt &size, const namespacet &ns);

/// Returns true iff the argument is (syntactically) an lvalue.
bool is_lvalue(const exprt &expr);

/// splits an expression with >=3 operands into nested binary expressions
exprt make_binary(const exprt &);

/// converts an update expr into a (possibly nested) with expression
with_exprt make_with_expr(const update_exprt &);

/// converts a scalar/float expression to C/C++ Booleans
exprt is_not_zero(const exprt &, const namespacet &ns);

/// negate a Boolean expression, possibly removing a not_exprt,
/// and swapping false and true
exprt boolean_negate(const exprt &);

/// returns true if the expression has a subexpression that satisfies pred
bool has_subexpr(const exprt &, const std::function<bool(const exprt &)> &pred);

/// returns true if the expression has a subexpression with given ID
bool has_subexpr(const exprt &, const irep_idt &);

/// returns true if any of the contained types satisfies pred
/// \param type: a type
/// \param pred: a predicate
/// \param ns: namespace for symbol type lookups
/// \return true if one of the subtype of `type` satisfies predicate `pred`.
///         The meaning of "subtype" is in the algebraic datatype sense:
///         for example, the subtypes of a struct are the types of its
///         components, the subtype of a pointer is the type it points to,
///         etc...
///         For instance in the type `t` defined by
///         `{ int a; char[] b; double * c; { bool d} e}`, `int`, `char`,
///         `double` and `bool` are subtypes of `t`.
bool has_subtype(
  const typet &type,
  const std::function<bool(const typet &)> &pred,
  const namespacet &ns);

/// returns true if any of the contained types is id
bool has_subtype(const typet &, const irep_idt &id, const namespacet &);

/// lift up an if_exprt one level
if_exprt lift_if(const exprt &, std::size_t operand_number);

/// find the expression nested inside typecasts, if any
const exprt &skip_typecast(const exprt &expr);

#endif // CPROVER_UTIL_EXPR_UTIL_H
