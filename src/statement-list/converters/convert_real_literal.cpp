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
  return constant_exprt(src, get_real_type());
}
