/*******************************************************************\

Module: Modified expression replacement for constant propagator

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Modified expression replacement for constant propagator

#include "replace_symbol_ext.h"

#include <util/std_types.h>
#include <util/std_expr.h>

/// does not replace object in address_of expressions
bool replace_symbol_extt::replace(exprt &dest) const
{
  bool result=true; // nothing changed

  // first look at type

  if(have_to_replace(dest.type()))
    if(!replace_symbolt::replace(dest.type()))
      result=false;

  // now do expression itself

  if(!have_to_replace(dest))
    return result;

  if(dest.id()==ID_symbol)
  {
    expr_mapt::const_iterator it=
      expr_map.find(dest.get(ID_identifier));

    if(it!=expr_map.end())
    {
      dest=it->second;
      return false;
    }
  }

  Forall_operands(it, dest)
    if(!replace(*it))
      result=false;

  const irept &c_sizeof_type=dest.find(ID_C_c_sizeof_type);

  if(c_sizeof_type.is_not_nil() &&
     !replace_symbolt::replace(
       static_cast<typet&>(dest.add(ID_C_c_sizeof_type))))
    result=false;

  const irept &va_arg_type=dest.find(ID_C_va_arg_type);

  if(va_arg_type.is_not_nil() &&
     !replace_symbolt::replace(
       static_cast<typet&>(dest.add(ID_C_va_arg_type))))
    result=false;

  return result;
}
