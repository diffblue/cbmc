/*******************************************************************\

Module:

Author:

\*******************************************************************/

#include <expr.h>
#include <symbol.h>

#include "cpp_util.h"

/*******************************************************************\

Function: cpp_symbol_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt cpp_symbol_expr(const symbolt &symbol)
{
  exprt tmp(ID_symbol, symbol.type);
  tmp.set(ID_identifier, symbol.name);

  if(symbol.lvalue)
    tmp.set(ID_C_lvalue, true);

  return tmp;
}

