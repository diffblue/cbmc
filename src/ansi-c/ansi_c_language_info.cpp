/*******************************************************************\

Module: C Language

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "ansi_c_language_info.h"

#include "expr2c.h"
#include "type2name.h"

#include "ansi_c_language.h"

std::set<std::string> ansi_c_language_infot::extensions() const
{
  return {"c", "i"};
}

bool ansi_c_language_infot::from_expr(
  const exprt &expr,
  std::string &code,
  const namespacet &ns) const
{
  code = expr2c(expr, ns);
  return false;
}

bool ansi_c_language_infot::from_type(
  const typet &type,
  std::string &code,
  const namespacet &ns) const
{
  code = type2c(type, ns);
  return false;
}

bool ansi_c_language_infot::type_to_name(
  const typet &type,
  std::string &name,
  const namespacet &ns) const
{
  name = type2name(type, ns);
  return false;
}

std::unique_ptr<language_infot> new_ansi_c_language_info()
{
  return std::unique_ptr<language_infot>(
    new ansi_c_language_infot(new_ansi_c_language));
}
