/*******************************************************************\

Module: Stack depth checks

Author: Daniel Kroening, Michael Tautschnig

Date: November 2011

\*******************************************************************/

/// \file
/// Stack depth checks

#include "stack_depth.h"

#include <util/arith_tools.h>
#include <util/bitvector_types.h>

#include <goto-programs/goto_convert_functions.h>
#include <goto-programs/goto_model.h>

#include <linking/static_lifetime_init.h>

static symbol_exprt add_stack_depth_symbol(
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  const irep_idt identifier="$stack_depth";
  unsignedbv_typet type(sizeof(std::size_t)*8);

  symbolt new_symbol;
  new_symbol.name=identifier;
  new_symbol.base_name=identifier;
  new_symbol.pretty_name=identifier;
  new_symbol.type=type;
  new_symbol.is_static_lifetime=true;
  new_symbol.value=from_integer(0, type);
  new_symbol.mode=ID_C;
  new_symbol.is_thread_local=true;
  new_symbol.is_lvalue=true;

  bool failed = goto_model.symbol_table.add(new_symbol);
  CHECK_RETURN(!failed);

  if(goto_model.goto_functions.function_map.erase(INITIALIZE_FUNCTION) != 0)
  {
    static_lifetime_init(
      goto_model.symbol_table,
      goto_model.symbol_table.lookup_ref(INITIALIZE_FUNCTION).location);
    goto_convert(
      INITIALIZE_FUNCTION,
      goto_model.symbol_table,
      goto_model.goto_functions,
      message_handler);
    goto_model.goto_functions.update();
  }

  return new_symbol.symbol_expr();
}

static void stack_depth(
  goto_programt &goto_program,
  const symbol_exprt &symbol,
  const std::size_t i_depth,
  const exprt &max_depth)
{
  assert(!goto_program.instructions.empty());

  goto_programt::targett first=goto_program.instructions.begin();

  binary_relation_exprt guard(symbol, ID_le, max_depth);
  goto_programt::targett assert_ins = goto_program.insert_before(
    first, goto_programt::make_assertion(guard, first->source_location()));

  assert_ins->source_location_nonconst().set_comment(
    "Stack depth exceeds " + std::to_string(i_depth));
  assert_ins->source_location_nonconst().set_property_class("stack-depth");

  goto_program.insert_before(
    first,
    goto_programt::make_assignment(
      code_assignt(symbol, plus_exprt(symbol, from_integer(1, symbol.type()))),
      first->source_location()));

  goto_programt::targett last=--goto_program.instructions.end();
  assert(last->is_end_function());

  goto_programt::instructiont minus_ins = goto_programt::make_assignment(
    code_assignt(symbol, minus_exprt(symbol, from_integer(1, symbol.type()))),
    last->source_location());

  goto_program.insert_before_swap(last, minus_ins);
}

void stack_depth(
  goto_modelt &goto_model,
  const std::size_t depth,
  message_handlert &message_handler)
{
  const symbol_exprt sym = add_stack_depth_symbol(goto_model, message_handler);

  const exprt depth_expr(from_integer(depth, sym.type()));

  for(auto &gf_entry : goto_model.goto_functions.function_map)
  {
    if(
      gf_entry.second.body_available() &&
      gf_entry.first != INITIALIZE_FUNCTION &&
      gf_entry.first != goto_functionst::entry_point())
    {
      stack_depth(gf_entry.second.body, sym, depth, depth_expr);
    }
  }

  // update counters etc.
  goto_model.goto_functions.update();
}
