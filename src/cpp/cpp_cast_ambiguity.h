/*******************************************************************\

Module: C++ Language Parsing and Type Checking: cast ambiguity

Author: Michael Tautschnig (with Kiro)

\*******************************************************************/

/// \file
/// Markers the C++ parser leaves on a `( name )` that may be a cast or a
/// parenthesized expression, for the type checker to resolve.
///
/// N5008 [expr.cast]/1 with [dcl.ambig.res]: `(x) - y` is a cast of `-y` if
/// x names a type, and the subtraction `x - y` otherwise; likewise for `+`,
/// `*` and `&`, and `(x)(y)` is a cast of `(y)` or the call `x(y)`.  Which
/// it is depends on name lookup, which the parser does not do.  It parses a
/// cast, marks it as ambiguous and marks the operator nodes above it whose
/// grouping may change.  cpp_typecheckt::resolve_cast_ambiguity looks the
/// name up and, if it does not name a type, regroups the operators of the
/// region as a parse with x as an operand would have grouped them: `(T)(x) -
/// y` is `((T)x) - y` and `(x) - y * z` is `x - (y * z)`.  The same applies
/// to `a<b>(c)` with an unqualified name a the parser has not seen declared:
/// the call of a template-id, or `(a < b) > (c)` if a denotes an object
/// ([temp.names]/3).

#ifndef CPROVER_CPP_CPP_CAST_AMBIGUITY_H
#define CPROVER_CPP_CPP_CAST_AMBIGUITY_H

#include <util/irep.h>

/// On an `explicit-typecast` node: the cast is ambiguous.  The value is
/// `unary` when the operand is the unary `+`, `-`, `*` or `&` whose token
/// follows the `)`, and `call` when the operand starts with a parenthesized
/// expression (an argument list if the name is not a type).
inline const irep_idt &ID_C_ambiguous_cast()
{
  static const irep_idt id{"#ambiguous_cast"};
  return id;
}

/// On an ambiguous cast and on the operator nodes (binary, prefix, cast)
/// that have such a node as an operand: the node belongs to the region that
/// the type checker regroups.
inline const irep_idt &ID_C_cast_ambiguity()
{
  static const irep_idt id{"#cast_ambiguity"};
  return id;
}

/// On a parenthesized expression that contains a region: the root of a
/// region of its own, which is an operand of any enclosing one.
inline const irep_idt &ID_C_cast_ambiguity_root()
{
  static const irep_idt id{"#cast_ambiguity_root"};
  return id;
}

/// On the parenthesized expression (or the cast) at the start of the
/// operand of a `call` ambiguous cast: the tokens that would be the
/// argument list.  The value is `split` when the expression is an
/// unparenthesized comma expression whose operands are the arguments, and
/// `single` otherwise.
inline const irep_idt &ID_C_cast_ambiguity_group()
{
  static const irep_idt id{"#cast_ambiguity_group"};
  return id;
}

/// On a call `name<arguments>(...)` of an unqualified name the parser has
/// not seen declared: the call of a template-id, or two comparisons
/// `name < argument > (...)` if the name is not a template ([temp.names]/3).
/// Also a member of the region (`#cast_ambiguity`).
inline const irep_idt &ID_C_ambiguous_template_id()
{
  static const irep_idt id{"#ambiguous_template_id"};
  return id;
}

/// On a comma expression in parentheses.
inline const irep_idt &ID_C_parenthesized_comma()
{
  static const irep_idt id{"#parenthesized_comma"};
  return id;
}

#endif // CPROVER_CPP_CPP_CAST_AMBIGUITY_H
