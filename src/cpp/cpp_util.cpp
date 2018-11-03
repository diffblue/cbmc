/*******************************************************************\

Module:

Author:

\*******************************************************************/

#include "cpp_util.h"

#include <util/std_expr.h>
#include <util/symbol.h>

symbol_exprt cpp_symbol_expr(const symbolt &symbol)
{
  symbol_exprt tmp(symbol.name, symbol.type);

  if(symbol.is_lvalue)
    tmp.set(ID_C_lvalue, true);

  return tmp;
}
