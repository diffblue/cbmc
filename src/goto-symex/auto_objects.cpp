/*******************************************************************\

Module: Symbolic Execution of ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution of ANSI-C

#include "goto_symex.h"

#include <util/pointer_expr.h>
#include <util/prefix.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

exprt goto_symext::make_auto_object(const typet &type, statet &state)
{
  dynamic_counter++;

  // produce auto-object symbol
  symbolt symbol;

  symbol.base_name="auto_object"+std::to_string(dynamic_counter);
  symbol.name="symex::"+id2string(symbol.base_name);
  symbol.is_lvalue=true;
  symbol.type=type;
  symbol.mode=ID_C;

  state.symbol_table.add(symbol);

  return symbol_exprt(symbol.name, symbol.type);
}

void goto_symext::initialize_auto_object(const exprt &expr, statet &state)
{
  const typet &type=ns.follow(expr.type());

  if(type.id()==ID_struct)
  {
    const struct_typet &struct_type=to_struct_type(type);

    for(const auto &comp : struct_type.components())
    {
      member_exprt member_expr(expr, comp.get_name(), comp.type());

      initialize_auto_object(member_expr, state);
    }
  }
  else if(type.id()==ID_pointer)
  {
    const pointer_typet &pointer_type=to_pointer_type(type);
    const typet &base_type = pointer_type.base_type();

    // we don't like function pointers and
    // we don't like void *
    if(base_type.id() != ID_code && base_type.id() != ID_empty)
    {
      // could be NULL nondeterministically

      address_of_exprt address_of_expr(
        make_auto_object(base_type, state), pointer_type);

      if_exprt rhs(
        side_effect_expr_nondett(bool_typet(), expr.source_location()),
        null_pointer_exprt(pointer_type),
        address_of_expr);

      symex_assign(state, expr, rhs);
    }
  }
}

void goto_symext::trigger_auto_object(const exprt &expr, statet &state)
{
  expr.visit_pre([&state, this](const exprt &e) {
    if(is_ssa_expr(e))
    {
      const ssa_exprt &ssa_expr = to_ssa_expr(e);
      const irep_idt &obj_identifier = ssa_expr.get_object_name();

      if(obj_identifier != statet::guard_identifier())
      {
        const symbolt &symbol = ns.lookup(obj_identifier);

        if(has_prefix(id2string(symbol.base_name), "auto_object"))
        {
          // done already?
          if(!state.get_level2().current_names.has_key(
               ssa_expr.get_identifier()))
          {
            initialize_auto_object(e, state);
          }
        }
      }
    }
  });
}
