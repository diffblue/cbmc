/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "namespace_utils.h"
#include "symbol.h"
#include <goto-programs/remove_returns.h>

/*******************************************************************\

  Function: namespace_utils_baset::does_symbol_match

  Purpose:
    Checks whether an exprt is actually a symbolt matching a predicate

  Inputs:
    lvalue:
      An exprt to be tested
    predicate:
      The predicate to test for

  Outputs:
    Whether the exprt was actually a symbolt matching a predicate

\*******************************************************************/

bool namespace_utils_baset::does_symbol_match(
  const exprt &lvalue,
  std::function<bool(symbolt)> predicate) const
{
  if(lvalue.id()!=ID_symbol)
    return false;
  const symbolt *symbol;
  if(lookup(lvalue.get(ID_identifier), symbol))
    return false;
  return predicate(*symbol);
}

/*******************************************************************\

  Function: namespace_utils_baset::is_parameter

  Purpose:
    Checks whether an exprt is actually a parameter symbol

  Inputs:
    lvalue:
      An exprt to be tested

  Outputs:
    Whether the exprt was actually a parameter symbol

\*******************************************************************/

bool namespace_utils_baset::is_parameter(const exprt &lvalue) const
{
  return does_symbol_match(
    lvalue,
    [] (symbolt symbol) { return symbol.is_parameter; });
}

/*******************************************************************\

  Function: namespace_utils_baset::is_static

  Purpose:
    Checks whether an exprt is actually a static symbol

  Inputs:
    lvalue:
      An exprt to be tested

  Outputs:
    Whether the exprt was actually a static symbol

\*******************************************************************/

bool namespace_utils_baset::is_static(const exprt &lvalue) const
{
  // TODO: Also check for static member accesses
  return does_symbol_match(
    lvalue,
    [] (symbolt symbol) { return symbol.is_static_lifetime; });
}

/*******************************************************************\

  Function: namespace_utils_baset::is_auxiliary_variable

  Purpose:
    Checks whether an exprt is actually an auxiliary variable symbol

  Inputs:
    lvalue:
      An exprt to be tested

  Outputs:
    Whether the exprt was actually an auxiliary variable symbol

\*******************************************************************/

bool namespace_utils_baset::is_auxiliary_variable(const exprt &lvalue) const
{
  return does_symbol_match(
    lvalue,
    [] (symbolt symbol) { return symbol.is_auxiliary; });
}

/*******************************************************************\

  Function: namespace_utils_baset::is_return_value_auxiliary

  Purpose:
    Checks whether an exprt is actually an auxiliary return value symbol

  Inputs:
    lvalue:
      An exprt to be tested

  Outputs:
    Whether the exprt was actually an auxiliary return value symbol

\*******************************************************************/

bool namespace_utils_baset::is_return_value_auxiliary(const exprt &lvalue) const
{
  return
    does_symbol_match(
      lvalue,
      [] (symbolt symbol)
      {
        return
          symbol.is_static_lifetime
            && symbol.is_auxiliary
            && symbol.is_file_local
            && symbol.is_thread_local;
      })
    && as_string(lvalue.get(ID_identifier)).find(RETURN_VALUE_SUFFIX)
      != std::string::npos;
}
