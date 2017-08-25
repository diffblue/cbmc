/*******************************************************************\

Module:

Author:

\*******************************************************************/

#include "cpp_util.h"

#include <util/expr.h>
#include <util/symbol.h>

exprt cpp_symbol_expr(const symbolt &symbol)
{
  exprt tmp(ID_symbol, symbol.type);
  tmp.set(ID_identifier, symbol.name);

  if(symbol.is_lvalue)
    tmp.set(ID_C_lvalue, true);

  return tmp;
}
