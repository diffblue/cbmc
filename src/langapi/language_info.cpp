/*******************************************************************\

Module: Language frontend info interface

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Language frontend info interface

#include "language_info.h"

#include <util/cprover_prefix.h>
#include <util/expr.h>
#include <util/prefix.h>
#include <util/std_types.h>
#include <util/symbol.h>
#include <util/symbol_table.h>

#include "language.h"

bool language_infot::from_expr(
  const exprt &expr,
  std::string &code,
  const namespacet &ns) const
{
  code = expr.pretty();
  return false;
}

bool language_infot::from_type(
  const typet &type,
  std::string &code,
  const namespacet &ns) const
{
  code = type.pretty();
  return false;
}

bool language_infot::type_to_name(
  const typet &type,
  std::string &name,
  const namespacet &ns) const
{
  // probably ansi-c/type2name could be used as better fallback if moved to
  // util/
  name = type.pretty();
  return false;
}

std::unique_ptr<languaget> language_infot::new_language() const
{
  return factory(*this);
}
