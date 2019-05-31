/*******************************************************************\

Module: Statement List Language Conversion

Author: Matthias Weiss, matthias.weiss@diffblue.com

\*******************************************************************/

/// \file
/// Statement List Language Conversion

#include "convert_bool_literal.h"

#include <algorithm>
#include <util/std_types.h>
// Needed for back_inserter in Visual Studio.
#include <iterator>

constant_exprt convert_bool_literal(const std::string &src)
{
  std::string copy;
  transform(begin(src), end(src), back_inserter(copy), ::tolower);

  bool_typet type;
  type.set(ID_statement_list_type, ID_statement_list_bool);

  return constant_exprt(copy, type);
}
