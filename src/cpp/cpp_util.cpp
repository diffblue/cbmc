/*******************************************************************\

Module:

Author:

\*******************************************************************/

#include <util/expr.h>
#include <util/symbol.h>

#include "cpp_util.h"

exprt cpp_symbol_expr(const symbolt &symbol)
{
  exprt tmp(ID_symbol, symbol.type);
  tmp.set(ID_identifier, symbol.name);

  if(symbol.is_lvalue)
    tmp.set(ID_C_lvalue, true);

  return tmp;
}
