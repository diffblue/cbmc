/*******************************************************************\

Module: Algebraic Numbers

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// Algebraic numbers

#include "algebraic_number.h"

#include "mathematical_types.h"
#include "rational_tools.h"

constant_exprt algebraic_numbert::as_expr() const
{
  if(coefficients.size() == 2 && coefficients.back().is_one())
  {
    // root of x - c
    auto c = from_rational(-coefficients.front());
    c.type() = real_typet{};
    return c;
  }
  else
  {
    std::ostringstream oss;
    oss << *this;
    return constant_exprt{oss.str(), real_typet{}};
  }
}

std::ostream &operator<<(std::ostream &out, const algebraic_numbert &a)
{
  out << "x ∈ ℝ.(";

  const auto &coefficients = a.get_coefficients();

  bool need_plus = false;
  for(std::size_t d = coefficients.size(); d > 0; --d)
  {
    if(coefficients[d - 1].is_zero())
      continue;
    if(need_plus)
      out << " + ";
    if(d == 1)
      out << coefficients[d - 1];
    else
    {
      if(!coefficients[d - 1].is_one())
        out << coefficients[d - 1] << "*";
      out << "x^" << d - 1;
    }
    need_plus = true;
  }

  if(!need_plus)
    out << "0";
  out << " = 0)";

  return out;
}
