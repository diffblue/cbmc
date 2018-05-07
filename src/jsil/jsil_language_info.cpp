/*******************************************************************\

Module: Jsil Language

Author: Michael Tautschnig, tautschn@amazon.com

\*******************************************************************/

/// \file
/// Jsil Language

#include "jsil_language_info.h"

#include "expr2jsil.h"
#include "jsil_language.h"

std::set<std::string> jsil_language_infot::extensions() const
{
  return {"jsil"};
}

bool jsil_language_infot::from_expr(
  const exprt &expr,
  std::string &code,
  const namespacet &ns) const
{
  code = expr2jsil(expr, ns);
  return false;
}

bool jsil_language_infot::from_type(
  const typet &type,
  std::string &code,
  const namespacet &ns) const
{
  code = type2jsil(type, ns);
  return false;
}

std::unique_ptr<language_infot> new_jsil_language_info()
{
  return std::unique_ptr<language_infot>(
    new jsil_language_infot(new_jsil_language));
}
