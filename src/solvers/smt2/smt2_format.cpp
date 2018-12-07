/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "smt2_format.h"

#include <util/arith_tools.h>
#include <util/std_expr.h>
#include <util/std_types.h>

std::ostream &smt2_format_rec(std::ostream &out, const typet &type)
{
  if(type.id() == ID_unsignedbv)
    out << "(_ BitVec " << to_unsignedbv_type(type).get_width() << ')';
  else if(type.id() == ID_bool)
    out << "Bool";
  else if(type.id() == ID_integer)
    out << "Int";
  else if(type.id() == ID_real)
    out << "Real";
  else if(type.id() == ID_array)
  {
    const auto &array_type = to_array_type(type);
    out << "(Array " << smt2_format(array_type.size().type()) << ' '
        << smt2_format(array_type.subtype()) << ')';
  }
  else if(type.id() == ID_floatbv)
  {
    const auto &floatbv_type = to_floatbv_type(type);
    // the width of the mantissa needs to be increased by one to
    // include the hidden bit
    out << "(_ FloatingPoint " << floatbv_type.get_e() << ' '
        << floatbv_type.get_f() + 1 << ')';
  }
  else
    out << "? " << type.id();

  return out;
}

std::ostream &smt2_format_rec(std::ostream &out, const exprt &expr)
{
  if(expr.id() == ID_constant)
  {
    const auto &value = to_constant_expr(expr).get_value();

    const typet &expr_type = expr.type();

    if(expr_type.id() == ID_unsignedbv)
    {
      const std::size_t width = to_unsignedbv_type(expr_type).get_width();

      const auto value = numeric_cast_v<mp_integer>(expr);

      out << "(_ bv" << value << " " << width << ")";
    }
    else if(expr_type.id() == ID_bool)
    {
      if(expr.is_true())
        out << "true";
      else if(expr.is_false())
        out << "false";
      else
        DATA_INVARIANT(false, "unknown Boolean constant");
    }
    else if(expr_type.id() == ID_integer)
    {
      out << value;
    }
    else if(expr_type.id() == ID_string)
    {
      out << '"';

      for(const auto &c : value)
      {
        // " is the only escape sequence
        if(c == '"')
          out << '"' << '"';
        else
          out << c;
      }

      out << '"';
    }
    else if(expr_type.id() == ID_floatbv)
    {
      out << value;
    }
    else
      DATA_INVARIANT(false, "unhandled constant: " + expr_type.id_string());
  }
  else if(expr.id() == ID_symbol)
  {
    const auto &identifier = to_symbol_expr(expr).get_identifier();
    if(expr.get_bool("#quoted"))
    {
      out << '|';
      out << identifier;
      out << '|';
    }
    else
      out << identifier;
  }
  else if(expr.id() == ID_with && expr.type().id() == ID_array)
  {
    const auto &with_expr = to_with_expr(expr);
    out << "(store " << smt2_format(with_expr.old()) << ' '
        << smt2_format(with_expr.where()) << ' '
        << smt2_format(with_expr.new_value()) << ')';
  }
  else if(expr.id() == ID_array_list)
  {
    const auto &array_list_expr = to_multi_ary_expr(expr);

    for(std::size_t i = 0; i < array_list_expr.operands().size(); i += 2)
      out << "(store ";

    out << "((as const " << smt2_format(expr.type()) << ")) "
        << smt2_format(from_integer(0, expr.type().subtype())) << ')';

    for(std::size_t i = 0; i < array_list_expr.operands().size(); i += 2)
    {
      DATA_INVARIANT(
        i < array_list_expr.operands().size() - 1,
        "array_list has even number of operands");
      out << ' ' << smt2_format(array_list_expr.operands()[i]) << ' '
          << smt2_format(array_list_expr.operands()[i + 1]) << ')';
    }
  }
  else
    out << "? " << expr.id();

  return out;
}
