/*******************************************************************\

Module: Expression Pretty Printing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Expression Pretty Printing

#include "formatter.h"
#include "format_expr.h"
#include "format_type.h"

debug_formattert debug_formatter;
default_debug_formattert default_debug_formatter;

std::ostream &default_debug_formattert::format(
  std::ostream &out,
  const exprt &src)
{
  return out << ::format(src);
}

std::ostream &default_debug_formattert::format(
  std::ostream &out,
  const typet &src)
{
  return out << ::format(src);
}

std::ostream &default_debug_formattert::format(
  std::ostream &out,
  const source_locationt &src)
{
  return out << src;
}
