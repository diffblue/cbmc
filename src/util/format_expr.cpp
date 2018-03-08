/*******************************************************************\

Module: Expression Pretty Printing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Expression Pretty Printing

#include "arith_tools.h"
#include "expr.h"
#include "expr_iterator.h"
#include "fixedbv.h"
#include "format_expr.h"
#include "format_type.h"
#include "ieee_float.h"
#include "invariant.h"
#include "mp_arith.h"
#include "rational.h"
#include "rational_tools.h"
#include "std_expr.h"
#include "string2int.h"

#include <stack>
#include <ostream>

/// We use the precendences that most readers expect
/// (i.e., the ones you learn in primary school),
/// and stay clear of the surprising ones that C has.
static bool bracket_subexpression(
  const exprt &sub_expr,
  const exprt &expr)
{
  // no need for parentheses whenever the subexpression
  // doesn't have operands
  if(!sub_expr.has_operands())
    return false;

  // * and / bind stronger than + and -
  if(
    (sub_expr.id() == ID_mult || sub_expr.id() == ID_div) &&
    (expr.id() == ID_plus || expr.id() == ID_minus))
    return false;

  // ==, !=, <, <=, >, >= bind stronger than && and ||
  if(
    (sub_expr.id() == ID_equal || sub_expr.id() == ID_notequal ||
     sub_expr.id() == ID_lt || sub_expr.id() == ID_gt ||
     sub_expr.id() == ID_le || sub_expr.id() == ID_ge) &&
    (expr.id() == ID_and || expr.id() == ID_or))
    return false;

  return true;
}

/// This formats a multi-ary expression,
/// adding parentheses where indicated by \ref bracket_subexpression
static std::ostream &format_rec(
  std::ostream &os,
  const multi_ary_exprt &src)
{
  bool first = true;

  for(const auto &op : src.operands())
  {
    if(first)
      first = false;
    else
      os << ' ' << src.id() << ' ';

    const bool need_parentheses = bracket_subexpression(op, src);

    if(need_parentheses)
      os << '(';

    os << format(op);

    if(need_parentheses)
      os << ')';
  }

  return os;
}

/// This formats a binary expression,
/// which we do as for multi-ary expressions
static std::ostream &format_rec(
  std::ostream &os,
  const binary_exprt &src)
{
  return format_rec(os, to_multi_ary_expr(src));
}

/// This formats a unary expression,
/// adding parentheses very aggressively.
static std::ostream &format_rec(
  std::ostream &os,
  const unary_exprt &src)
{
  if(src.id() == ID_not)
    os << '!';
  else if(src.id() == ID_unary_minus)
    os << '-';
  else
    return os << src.pretty();

  if(src.op0().has_operands())
    return os << '(' << format(src.op0()) << ')';
  else
    return os << format(src.op0());
}

/// This formats a constant
static std::ostream &format_rec(
  std::ostream &os,
  const constant_exprt &src)
{
  auto type = src.type().id();

  if(type == ID_bool)
  {
    if(src.is_true())
      return os << "true";
    else if(src.is_false())
      return os << "false";
    else
      return os << src.pretty();
  }
  else if(type == ID_unsignedbv || type == ID_signedbv)
    return os << *numeric_cast<mp_integer>(src);
  else if(type == ID_integer)
    return os << src.get_value();
  else if(type == ID_floatbv)
    return os << ieee_floatt(src);
  else
    return os << src.pretty();
}

// The below generates a string in a generic syntax
// that is inspired by C/C++/Java, and is meant for debugging
// purposes.
std::ostream &format_rec(
  std::ostream &os,
  const exprt &expr)
{
  const auto &id = expr.id();

  if(id == ID_plus || id == ID_mult || id == ID_and || id == ID_or)
    return format_rec(os, to_multi_ary_expr(expr));
  else if(
    id == ID_lt || id == ID_gt || id == ID_ge || id == ID_le ||
    id == ID_minus || id == ID_implies || id == ID_equal || id == ID_notequal)
    return format_rec(os, to_binary_expr(expr));
  else if(id == ID_not || id == ID_unary_minus)
    return format_rec(os, to_unary_expr(expr));
  else if(id == ID_constant)
    return format_rec(os, to_constant_expr(expr));
  else if(id == ID_typecast)
    return os << "cast(" << format(to_typecast_expr(expr).op()) << ", "
              << format(expr.type()) << ')';
  else if(id == ID_member)
    return os << format(to_member_expr(expr).op()) << '.'
              << to_member_expr(expr).get_component_name();
  else if(id == ID_symbol)
    return os << to_symbol_expr(expr).get_identifier();
  else if(id == ID_forall || id == ID_exists)
    return os << id << ' ' << format(to_quantifier_expr(expr).symbol()) << " : "
              << format(to_quantifier_expr(expr).symbol().type()) << " . "
              << format(to_quantifier_expr(expr).where());
  else if(id == ID_let)
    return os << "LET " << format(to_let_expr(expr).symbol()) << " = "
              << format(to_let_expr(expr).value()) << " IN "
              << format(to_let_expr(expr).where());
  else if(id == ID_array || id == ID_struct)
  {
    os << "{ ";

    bool first = true;

    for(const auto &op : expr.operands())
    {
      if(first)
        first = false;
      else
        os << ", ";

      os << format(op);
    }

    return os << '}';
  }
  else if(id == ID_if)
  {
    const auto &if_expr = to_if_expr(expr);
    return os << format(if_expr.cond()) << '?' << format(if_expr.true_case())
              << ':' << format(if_expr.false_case());
  }
  else
  {
    if(!expr.has_operands())
      return os << id;

    os << id << '(';
    bool first = true;

    for(const auto &op : expr.operands())
    {
      if(first)
        first = false;
      else
        os << ", ";

      os << format(op);
    }

    return os << ')';
  }
}
