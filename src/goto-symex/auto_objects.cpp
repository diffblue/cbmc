/*******************************************************************\

Module: Symbolic Execution of ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution of ANSI-C

#include <util/fresh_symbol.h>
#include <util/pointer_expr.h>
#include <util/std_code.h>
#include <util/std_expr.h>

#include "goto_symex.h"

exprt goto_symext::make_auto_object(const typet &type, statet &state)
{
  // produce auto-object symbol
  symbolt &symbol = get_fresh_aux_symbol(
    type,
    "symex",
    "auto_object",
    state.source.pc->source_location(),
    ID_C,
    state.symbol_table);
  symbol.is_thread_local = false;
  symbol.is_file_local = false;

  return symbol.symbol_expr();
}

void goto_symext::initialize_auto_object(const exprt &expr, statet &state)
{
  DATA_INVARIANT(
    expr.type().id() != ID_struct,
    "no L2-renamed expression expected, all struct-like types should be tags");

  if(
    auto struct_tag_type = type_try_dynamic_cast<struct_tag_typet>(expr.type()))
  {
    const struct_typet &struct_type = ns.follow_tag(*struct_tag_type);

    for(const auto &comp : struct_type.components())
    {
      member_exprt member_expr(expr, comp.get_name(), comp.type());

      initialize_auto_object(member_expr, state);
    }
  }
  else if(auto pointer_type = type_try_dynamic_cast<pointer_typet>(expr.type()))
  {
    const typet &base_type = pointer_type->base_type();

    // we don't like function pointers and
    // we don't like void *
    if(base_type.id() != ID_code && base_type.id() != ID_empty)
    {
      // could be NULL nondeterministically

      address_of_exprt address_of_expr(
        make_auto_object(base_type, state), *pointer_type);

      if_exprt rhs(
        side_effect_expr_nondett(bool_typet(), expr.source_location()),
        null_pointer_exprt(*pointer_type),
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

        if(symbol.base_name.starts_with("symex::auto_object"))
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
