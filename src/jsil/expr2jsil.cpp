/*******************************************************************\

Module: Jsil Language

Author: Michael Tautschnig, tautschn@amazon.com

\*******************************************************************/

#include <ansi-c/expr2c_class.h>

#include "expr2jsil.h"

class expr2jsilt:public expr2ct
{
public:
  explicit expr2jsilt(const namespacet &_ns):expr2ct(_ns) { }

  virtual std::string convert(const exprt &src)
  {
    return expr2ct::convert(src);
  }

  virtual std::string convert(const typet &src)
  {
    return expr2ct::convert(src);
  }

protected:
};

/*******************************************************************\

Function: expr2jsil

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string expr2jsil(const exprt &expr, const namespacet &ns)
{
  expr2jsilt expr2jsil(ns);
  expr2jsil.get_shorthands(expr);
  return expr2jsil.convert(expr);
}

/*******************************************************************\

Function: type2jsil

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string type2jsil(const typet &type, const namespacet &ns)
{
  expr2jsilt expr2jsil(ns);
  return expr2jsil.convert(type);
}
