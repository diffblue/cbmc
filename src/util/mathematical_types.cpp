/*******************************************************************\

Module: Mathematical types

Author: Daniel Kroening, kroening@kroening.com
        Maria Svorenova, maria.svorenova@diffblue.com

\*******************************************************************/

/// \file
/// Mathematical types

#include "mathematical_types.h"

#include "std_expr.h"

/// Returns true if the type is a rational, real, integer, natural, complex,
/// unsignedbv, signedbv, floatbv or fixedbv.
bool is_number(const typet &type)
{
  const irep_idt &id = type.id();
  return id == ID_rational || id == ID_real || id == ID_integer ||
         id == ID_natural || id == ID_complex || id == ID_unsignedbv ||
         id == ID_signedbv || id == ID_floatbv || id == ID_fixedbv;
}

constant_exprt integer_typet::zero_expr() const
{
  return constant_exprt{ID_0, *this};
}

constant_exprt integer_typet::one_expr() const
{
  return constant_exprt{ID_1, *this};
}

constant_exprt natural_typet::zero_expr() const
{
  return constant_exprt{ID_0, *this};
}

constant_exprt natural_typet::one_expr() const
{
  return constant_exprt{ID_1, *this};
}

constant_exprt rational_typet::zero_expr() const
{
  return constant_exprt{ID_0, *this};
}

constant_exprt rational_typet::one_expr() const
{
  return constant_exprt{ID_1, *this};
}

constant_exprt real_typet::zero_expr() const
{
  return constant_exprt{ID_0, *this};
}

constant_exprt real_typet::one_expr() const
{
  return constant_exprt{ID_1, *this};
}

bool range_typet::includes(const mp_integer &singleton) const
{
  return get_from() <= singleton && singleton <= get_to();
}

constant_exprt range_typet::one_expr() const
{
  PRECONDITION(includes(1));
  return constant_exprt{ID_1, *this};
}

constant_exprt range_typet::zero_expr() const
{
  PRECONDITION(includes(0));
  return constant_exprt{ID_0, *this};
}

void range_typet::set_from(const mp_integer &from)
{
  set(ID_from, integer2string(from));
}

void range_typet::set_to(const mp_integer &to)
{
  set(ID_to, integer2string(to));
}

mp_integer range_typet::get_from() const
{
  return string2integer(get_string(ID_from));
}

mp_integer range_typet::get_to() const
{
  return string2integer(get_string(ID_to));
}
