/*******************************************************************\

Module: ANSI-C Linking

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// ANSI-C Linking

#include "casting_replace_symbol.h"

#include <util/pointer_expr.h>
#include <util/std_code.h>
#include <util/std_expr.h>

bool casting_replace_symbolt::replace(exprt &dest) const
{
  bool result = true; // unchanged

  // first look at type

  const exprt &const_dest(dest);
  if(have_to_replace(const_dest.type()))
    if(!replace_symbolt::replace(dest.type()))
      result = false;

  // now do expression itself

  if(!have_to_replace(dest))
    return result;

  if(dest.id() == ID_side_effect)
  {
    if(auto call = expr_try_dynamic_cast<side_effect_expr_function_callt>(dest))
    {
      if(!have_to_replace(call->function()))
        return replace_symbolt::replace(dest);

      exprt before = dest;
      code_typet type = to_code_type(call->function().type());

      result &= replace_symbolt::replace(call->function());

      // maybe add type casts here?
      for(auto &arg : call->arguments())
        result &= replace_symbolt::replace(arg);

      if(
        type.return_type() !=
        to_code_type(call->function().type()).return_type())
      {
        call->type() = to_code_type(call->function().type()).return_type();
        dest = typecast_exprt(*call, type.return_type());
        result = true;
      }

      return result;
    }
  }
  else if(dest.id() == ID_address_of)
  {
    pointer_typet ptr_type = to_pointer_type(dest.type());

    result &= replace_symbolt::replace(dest);

    address_of_exprt address_of = to_address_of_expr(dest);
    if(address_of.object().type() != ptr_type.base_type())
    {
      to_pointer_type(address_of.type()).base_type() =
        address_of.object().type();
      dest = typecast_exprt{address_of, std::move(ptr_type)};
      result = true;
    }

    return result;
  }

  return replace_symbolt::replace(dest);
}

bool casting_replace_symbolt::replace_symbol_expr(symbol_exprt &s) const
{
  expr_mapt::const_iterator it = expr_map.find(s.get_identifier());

  if(it == expr_map.end())
    return true;

  const exprt &e = it->second;

  source_locationt previous_source_location{s.source_location()};
  DATA_INVARIANT_WITH_DIAGNOSTICS(
    previous_source_location.is_not_nil(),
    "front-ends should construct symbol expressions with source locations",
    s.pretty());
  if(e.type().id() != ID_array && e.type().id() != ID_code)
  {
    typet type = s.type();
    static_cast<exprt &>(s) = typecast_exprt::conditional_cast(e, type);
  }
  else
    static_cast<exprt &>(s) = e;
  s.add_source_location() = std::move(previous_source_location);

  return false;
}
