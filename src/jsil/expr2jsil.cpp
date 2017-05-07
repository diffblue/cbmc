/*******************************************************************\

Module: Jsil Language

Author: Michael Tautschnig, tautschn@amazon.com

\*******************************************************************/

/// \file
/// Jsil Language

#include "expr2jsil.h"

#include <ansi-c/expr2c_class.h>

class expr2jsilt:public expr2ct
{
public:
  explicit expr2jsilt(const namespacet &_ns):expr2ct(_ns) { }

protected:
};

std::string expr2jsil(const exprt &expr, const namespacet &ns)
{
  expr2jsilt expr2jsil(ns);
  expr2jsil.get_shorthands(expr);
  return expr2jsil.convert(expr);
}

std::string type2jsil(const typet &type, const namespacet &ns)
{
  expr2jsilt expr2jsil(ns);
  return expr2jsil.convert(type);
}
