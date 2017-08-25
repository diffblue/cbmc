
/*******************************************************************\

Module: Jsil Language

Author: Michael Tautschnig, tautschn@amazon.com

\*******************************************************************/

#ifndef CPROVER_JSIL_EXPR2JSIL_CLASS_H
#define CPROVER_JSIL_EXPR2JSIL_CLASS_H

#include <ansi-c/expr2c_class.h>

class expr2jsilt:public expr2ct
{
public:
  explicit expr2jsilt(const namespacet &_ns):expr2ct(_ns) { }

protected:
};

#endif
