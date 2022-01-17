/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "smt2_format.h"

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/ieee_float.h>

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
        << smt2_format(array_type.element_type()) << ')';
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
    const auto &constant_expr = to_constant_expr(expr);
    const auto &value = constant_expr.get_value();
    const typet &expr_type = expr.type();

    if(expr_type.id() == ID_unsignedbv)
    {
      const std::size_t width = to_unsignedbv_type(expr_type).get_width();

      const auto int_value = numeric_cast_v<mp_integer>(constant_expr);

      out << "(_ bv" << int_value << " " << width << ")";
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
      // negative numbers need to be encoded using a unary minus expression
      auto int_value = numeric_cast_v<mp_integer>(constant_expr);
      if(int_value < 0)
        out << "(- " << -int_value << ')';
      else
        out << int_value;
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
      const ieee_floatt v = ieee_floatt(constant_expr);
      const size_t e = v.spec.e;
      const size_t f = v.spec.f + 1; // SMT-LIB counts the hidden bit

      if(v.is_NaN())
      {
        out << "(_ NaN " << e << " " << f << ")";
      }
      else if(v.is_infinity())
      {
        if(v.get_sign())
          out << "(_ -oo " << e << " " << f << ")";
        else
          out << "(_ +oo " << e << " " << f << ")";
      }
      else
      {
        // Zero, normal or subnormal

        mp_integer binary = v.pack();
        std::string binaryString(integer2binary(v.pack(), v.spec.width()));

        out << "(fp "
            << "#b" << binaryString.substr(0, 1) << " "
            << "#b" << binaryString.substr(1, e) << " "
            << "#b" << binaryString.substr(1 + e, f - 1) << ")";
      }
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
