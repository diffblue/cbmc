/*******************************************************************\

Module: Java Bytecode Language

Author: Diffblue Ltd

\*******************************************************************/

#include "java_bytecode_language_info.h"

#include "expr2java.h"
#include "java_bytecode_language.h"

std::set<std::string> java_bytecode_language_infot::extensions() const
{
  return {"class", "jar"};
}

bool java_bytecode_language_infot::from_expr(
  const exprt &expr,
  std::string &code,
  const namespacet &ns) const
{
  code = expr2java(expr, ns);
  return false;
}

bool java_bytecode_language_infot::from_type(
  const typet &type,
  std::string &code,
  const namespacet &ns) const
{
  code = type2java(type, ns);
  return false;
}

std::unique_ptr<language_infot> new_java_bytecode_language_info()
{
  return std::unique_ptr<language_infot>(
    new java_bytecode_language_infot(new_java_bytecode_language));
}
