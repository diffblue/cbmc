/*******************************************************************\

Module: C++ Language

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "cpp_language_info.h"

#include "cpp_language.h"
#include "cpp_type2name.h"
#include "expr2cpp.h"

std::set<std::string> cpp_language_infot::extensions() const
{
  std::set<std::string> s;

  s.insert("cpp");
  s.insert("CPP");
  s.insert("cc");
  s.insert("c++");
  s.insert("ii");
  s.insert("cxx");

#ifndef _WIN32
  s.insert("C");
#endif

  return s;
}

bool cpp_language_infot::from_expr(
  const exprt &expr,
  std::string &code,
  const namespacet &ns) const
{
  code = expr2cpp(expr, ns);
  return false;
}

bool cpp_language_infot::from_type(
  const typet &type,
  std::string &code,
  const namespacet &ns) const
{
  code = type2cpp(type, ns);
  return false;
}

bool cpp_language_infot::type_to_name(
  const typet &type,
  std::string &name,
  const namespacet &ns) const
{
  name = cpp_type2name(type);
  return false;
}

std::unique_ptr<language_infot> new_cpp_language_info()
{
  return std::unique_ptr<language_infot>(
    new cpp_language_infot(new_cpp_language));
}
