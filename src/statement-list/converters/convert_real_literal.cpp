/*******************************************************************\

Module: Statement List Language Conversion

Author: Matthias Weiss, matthias.weiss@diffblue.com

\*******************************************************************/

/// \file
/// Statement List Language Conversion

#include "convert_real_literal.h"
#include "statement_list_types.h"

#include <util/ieee_float.h>
#include <util/std_expr.h>

constant_exprt convert_real_literal(const std::string &src)
{
  ieee_floatt real{get_real_type()};
  real.from_float(std::stof(src));
  return real.to_expr();
}
