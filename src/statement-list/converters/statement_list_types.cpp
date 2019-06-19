/*******************************************************************\

Module: Statement List Type Helper

Author: Matthias Weiss, matthias.weiss@diffblue.com

\*******************************************************************/

/// \file
/// Statement List Type Helper

#include "statement_list_types.h"
#include <util/ieee_float.h>
#include <util/std_types.h>

signedbv_typet get_int_type()
{
  return signedbv_typet{STL_INT_WIDTH};
}
signedbv_typet get_dint_type()
{
  return signedbv_typet{STL_DINT_WIDTH};
}
floatbv_typet get_real_type()
{
  return ieee_float_spect::single_precision().to_type();
}
bool_typet get_bool_type()
{
  return bool_typet{};
}
