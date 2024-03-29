/*******************************************************************\

Module: Function Entering and Exiting

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Function Entering and Exiting

#include "function.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/cprover_prefix.h>
#include <util/pointer_expr.h>
#include <util/string_constant.h>

#include <goto-programs/goto_model.h>

code_function_callt function_to_call(
  symbol_table_baset &symbol_table,
  const irep_idt &id,
  const irep_idt &argument)
{
  // already there?

  symbol_table_baset::symbolst::const_iterator s_it =
    symbol_table.symbols.find(id);

  if(s_it==symbol_table.symbols.end())
  {
    // This has to be dead code: a symbol table must contain all functions that
    // appear in goto_functions.
    UNREACHABLE;
#if 0

    // not there
    auto p = pointer_type(char_type());
    p.base_type().set(ID_C_constant, true);

    const code_typet function_type({code_typet::parametert(p)}, empty_typet());

    symbolt new_symbol{id, function_type, irep_idt{}};
    new_symbol.base_name=id;

    symbol_table.insert(std::move(new_symbol));

    s_it=symbol_table.symbols.find(id);
    DATA_INVARIANT(s_it != symbol_table.symbols.end(), "symbol not found");
#endif
  }

  // signature is expected to be
  // (type *) -> ...
  if(s_it->second.type.id()!=ID_code ||
     to_code_type(s_it->second.type).parameters().size()!=1 ||
     to_code_type(s_it->second.type).parameters()[0].type().id()!=ID_pointer)
  {
    std::string error = "function '" + id2string(id) + "' has wrong signature";
    throw error;
  }

  string_constantt function_id_string(argument);

  code_function_callt call(
    symbol_exprt(s_it->second.name, s_it->second.type),
    {typecast_exprt(
      address_of_exprt(
        index_exprt(function_id_string, from_integer(0, c_index_type()))),
      to_code_type(s_it->second.type).parameters()[0].type())});

  return call;
}

void function_enter(
  goto_modelt &goto_model,
  const irep_idt &id)
{
  for(auto &gf_entry : goto_model.goto_functions.function_map)
  {
    // don't instrument our internal functions
    if(gf_entry.first.starts_with(CPROVER_PREFIX))
      continue;

    // don't instrument the function to be called,
    // or otherwise this will be recursive
    if(gf_entry.first == id)
      continue;

    // patch in a call to `id' at the entry point
    goto_programt &body = gf_entry.second.body;

    body.insert_before(
      body.instructions.begin(),
      goto_programt::make_function_call(
        function_to_call(goto_model.symbol_table, id, gf_entry.first)));
  }
}

void function_exit(
  goto_modelt &goto_model,
  const irep_idt &id)
{
  for(auto &gf_entry : goto_model.goto_functions.function_map)
  {
    // don't instrument our internal functions
    if(gf_entry.first.starts_with(CPROVER_PREFIX))
      continue;

    // don't instrument the function to be called,
    // or otherwise this will be recursive
    if(gf_entry.first == id)
      continue;

    // patch in a call to `id' at the exit points
    goto_programt &body = gf_entry.second.body;

    // make sure we have END_OF_FUNCTION
    if(body.instructions.empty() ||
       !body.instructions.back().is_end_function())
    {
      body.add(goto_programt::make_end_function());
    }

    Forall_goto_program_instructions(i_it, body)
    {
      if(i_it->is_set_return_value())
      {
        goto_programt::instructiont call = goto_programt::make_function_call(
          function_to_call(goto_model.symbol_table, id, gf_entry.first));
        body.insert_before_swap(i_it, call);

        // move on
        i_it++;
      }
    }

    // exiting without return
    goto_programt::targett last=body.instructions.end();
    last--;
    DATA_INVARIANT(last->is_end_function(), "must be end of function");

    // is there already a return?
    bool has_set_return_value = false;

    if(last!=body.instructions.begin())
    {
      goto_programt::targett before_last=last;
      --before_last;
      if(before_last->is_set_return_value())
        has_set_return_value = true;
    }

    if(!has_set_return_value)
    {
      goto_programt::instructiont call = goto_programt::make_function_call(
        function_to_call(goto_model.symbol_table, id, gf_entry.first));
      body.insert_before_swap(last, call);
    }
  }
}
