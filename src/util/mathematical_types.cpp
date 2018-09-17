/*******************************************************************\

Module: Mathematical types

Author: Daniel Kroening, kroening@kroening.com
        Maria Svorenova, maria.svorenova@diffblue.com

\*******************************************************************/

/// \file
/// Mathematical types

#include "mathematical_types.h"

/// Returns true if the type is a rational, real, integer, natural, complex,
/// unsignedbv, signedbv, floatbv or fixedbv.
bool is_number(const typet &type)
{
  const irep_idt &id = type.id();
  return id == ID_rational || id == ID_real || id == ID_integer ||
         id == ID_natural || id == ID_complex || id == ID_unsignedbv ||
         id == ID_signedbv || id == ID_floatbv || id == ID_fixedbv;
}
