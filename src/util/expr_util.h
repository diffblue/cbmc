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

class constant_exprt;
class exprt;
class update_exprt;
class with_exprt;
class if_exprt;
class typet;
class namespacet;

/// Returns true iff the argument is one of the following:
/// * a symbol
/// * a dereference
/// * an array element
/// * a struct member
bool is_assignable(const exprt &);

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
///   The meaning of "subtype" is in the algebraic datatype sense: for example,
///   the subtypes of a struct are the types of its components, the subtype of
///   a pointer is the type it points to, etc...
///   For instance in the type `t` defined by
///     `{ int a; char[] b; double * c; { bool d} e}`, `int`, `char`,
///   `double` and `bool` are subtypes of `t`.
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

/// Determine whether an expression is constant.  A literal constant is
/// constant, but so are, e.g., sums over constants or addresses of objects.
/// An implementation derive from this class to refine what it considers
/// constant in a particular context by overriding is_constant and/or
/// is_constant_address_of.
class is_constantt
{
public:
  /// returns true iff the expression can be considered constant
  bool operator()(const exprt &e) const
  {
    return is_constant(e);
  }

protected:
  virtual bool is_constant(const exprt &) const;
  virtual bool is_constant_address_of(const exprt &) const;
};

/// returns true_exprt if given true and false_exprt otherwise
constant_exprt make_boolean_expr(bool);

/// Conjunction of two expressions. If the second is already an `and_exprt`
/// add to its operands instead of creating a new expression. If one is `true`,
/// return the other expression. If one is `false` returns `false`.
exprt make_and(exprt a, exprt b);

/// Returns true if \p expr has a pointer type and a value NULL; it also returns
/// true when \p expr has value zero and NULL_is_zero is true; returns false in
/// all other cases.
bool is_null_pointer(const constant_exprt &expr);

#endif // CPROVER_UTIL_EXPR_UTIL_H
