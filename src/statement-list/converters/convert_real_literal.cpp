/*******************************************************************\

Module: Statement List Language Conversion

Author: Matthias Weiss, matthias.weiss@diffblue.com

\*******************************************************************/

/// \file
/// Statement List Language Conversion

#include "convert_real_literal.h"

#include <util/ieee_float.h>
#include <util/std_expr.h>

constant_exprt convert_real_literal(const std::string &src)
{
  floatbv_typet type = ieee_float_spect::single_precision().to_type();
  type.set(ID_statement_list_type, ID_statement_list_real);

  return constant_exprt(src, type);
}
