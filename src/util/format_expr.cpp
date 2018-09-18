/*******************************************************************\

Module: Expression Pretty Printing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Expression Pretty Printing

#include "format_expr.h"

#include "arith_tools.h"
#include "expr.h"
#include "expr_iterator.h"
#include "fixedbv.h"
#include "format_type.h"
#include "ieee_float.h"
#include "invariant.h"
#include "mp_arith.h"
#include "rational.h"
#include "rational_tools.h"
#include "std_code.h"
#include "std_expr.h"
#include "string2int.h"
#include "string_utils.h"

#include <ostream>
#include <stack>

/// We use the precendences that most readers expect
/// (i.e., the ones you learn in primary school),
/// and stay clear of the surprising ones that C has.
static bool bracket_subexpression(const exprt &sub_expr, const exprt &expr)
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
static std::ostream &format_rec(std::ostream &os, const multi_ary_exprt &src)
{
  bool first = true;

  std::string operator_str;

  if(src.id() == ID_and)
    operator_str = u8"\u2227"; // wedge, U+2227
  else if(src.id() == ID_or)
    operator_str = u8"\u2228"; // vee, U+2228
  else if(src.id() == ID_xor)
    operator_str = u8"\u2295"; // + in circle, U+2295
  else if(src.id() == ID_le)
    operator_str = u8"\u2264"; // <=, U+2264
  else if(src.id() == ID_ge)
    operator_str = u8"\u2265"; // >=, U+2265
  else if(src.id() == ID_notequal)
    operator_str = u8"\u2260"; // /=, U+2260
  else if(src.id() == ID_implies)
    operator_str = u8"\u21d2"; // =>, U+21D2
  else if(src.id() == ID_equal)
  {
    if(!src.operands().empty() && src.op0().type().id() == ID_bool)
      operator_str = u8"\u21d4"; // <=>, U+21D4
    else
      operator_str = "=";
  }
  else
    operator_str = id2string(src.id());

  for(const auto &op : src.operands())
  {
    if(first)
      first = false;
    else
      os << ' ' << operator_str << ' ';

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
static std::ostream &format_rec(std::ostream &os, const binary_exprt &src)
{
  return format_rec(os, to_multi_ary_expr(src));
}

/// This formats a unary expression,
/// adding parentheses very aggressively.
static std::ostream &format_rec(std::ostream &os, const unary_exprt &src)
{
  if(src.id() == ID_not)
    os << u8"\u00ac"; // neg, U+00AC
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
static std::ostream &format_rec(std::ostream &os, const constant_exprt &src)
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
  else if(type == ID_unsignedbv || type == ID_signedbv || type == ID_c_bool)
    return os << *numeric_cast<mp_integer>(src);
  else if(type == ID_integer)
    return os << src.get_value();
  else if(type == ID_string)
    return os << '"' << escape(id2string(src.get_value())) << '"';
  else if(type == ID_floatbv)
    return os << ieee_floatt(src);
  else if(type == ID_pointer && src.is_zero())
    return os << src.get_value();
  else
    return os << src.pretty();
}

std::ostream &fallback_format_rec(std::ostream &os, const exprt &expr)
{
  os << expr.id();

  for(const auto &s : expr.get_named_sub())
    if(s.first != ID_type)
      os << ' ' << s.first << "=\"" << s.second.id() << '"';

  if(expr.has_operands())
  {
    os << '(';
    bool first = true;

    for(const auto &op : expr.operands())
    {
      if(first)
        first = false;
      else
        os << ", ";

      os << format(op);
    }

    os << ')';
  }

  return os;
}

// The below generates a string in a generic syntax
// that is inspired by C/C++/Java, and is meant for debugging
// purposes.
std::ostream &format_rec(std::ostream &os, const exprt &expr)
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
  else if(id == ID_index)
  {
    const auto &index_expr = to_index_expr(expr);
    return os << format(index_expr.array()) << '[' << format(index_expr.index())
              << ']';
  }
  else if(id == ID_type)
    return format_rec(os, expr.type());
  else if(id == ID_forall)
    return os << u8"\u2200 " << format(to_quantifier_expr(expr).symbol())
              << " : " << format(to_quantifier_expr(expr).symbol().type())
              << " . " << format(to_quantifier_expr(expr).where());
  else if(id == ID_exists)
    return os << u8"\u2203 " << format(to_quantifier_expr(expr).symbol())
              << " : " << format(to_quantifier_expr(expr).symbol().type())
              << " . " << format(to_quantifier_expr(expr).where());
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
  else if(id == ID_code)
  {
    const auto &code = to_code(expr);
    const irep_idt &statement = code.get_statement();

    if(statement == ID_assign)
      return os << format(to_code_assign(code).lhs()) << " = "
                << format(to_code_assign(code).rhs()) << ';';
    else if(statement == ID_block)
    {
      os << '{';
      for(const auto &s : to_code_block(code).operands())
        os << ' ' << format(s);
      return os << " }";
    }
    else
      return fallback_format_rec(os, expr);
  }
  else
    return fallback_format_rec(os, expr);
}
