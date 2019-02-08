/*******************************************************************\

Module: Stack depth checks

Author: Daniel Kroening, Michael Tautschnig

Date: November 2011

\*******************************************************************/

/// \file
/// Stack depth checks

#include "stack_depth.h"

#include <util/arith_tools.h>

#include <goto-programs/goto_model.h>

#include <linking/static_lifetime_init.h>

symbol_exprt add_stack_depth_symbol(symbol_tablet &symbol_table)
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

  symbol_table.insert(std::move(new_symbol));

  return symbol_exprt(identifier, type);
}

void stack_depth(
  goto_programt &goto_program,
  const symbol_exprt &symbol,
  const std::size_t i_depth,
  const exprt &max_depth)
{
  assert(!goto_program.instructions.empty());

  goto_programt::targett first=goto_program.instructions.begin();

  binary_relation_exprt guard(symbol, ID_le, max_depth);
  goto_programt::targett assert_ins = goto_program.insert_before(
    first, goto_programt::make_assertion(guard, first->source_location));

  assert_ins->source_location.set_comment(
    "Stack depth exceeds "+std::to_string(i_depth));
  assert_ins->source_location.set_property_class("stack-depth");

  goto_program.insert_before(
    first,
    goto_programt::make_assignment(
      code_assignt(symbol, plus_exprt(symbol, from_integer(1, symbol.type()))),
      first->source_location));

  goto_programt::targett last=--goto_program.instructions.end();
  assert(last->is_end_function());

  goto_programt::instructiont minus_ins = goto_programt::make_assignment(
    code_assignt(symbol, minus_exprt(symbol, from_integer(1, symbol.type()))),
    last->source_location);

  goto_program.insert_before_swap(last, minus_ins);
}

void stack_depth(
  goto_modelt &goto_model,
  const std::size_t depth)
{
  const symbol_exprt sym=
    add_stack_depth_symbol(goto_model.symbol_table);

  const exprt depth_expr(from_integer(depth, sym.type()));

  Forall_goto_functions(f_it, goto_model.goto_functions)
    if(f_it->second.body_available() &&
        f_it->first != INITIALIZE_FUNCTION &&
        f_it->first!=goto_functionst::entry_point())
      stack_depth(f_it->second.body, sym, depth, depth_expr);

  // initialize depth to 0
  goto_functionst::function_mapt::iterator i_it =
    goto_model.goto_functions.function_map.find(INITIALIZE_FUNCTION);
  DATA_INVARIANT(
    i_it!=goto_model.goto_functions.function_map.end(),
    INITIALIZE_FUNCTION " must exist");

  goto_programt &init=i_it->second.body;
  goto_programt::targett first=init.instructions.begin();
  init.insert_before(
    first,
    goto_programt::make_assignment(
      code_assignt(sym, from_integer(0, sym.type()))));
  // no suitable value for source location -- omitted

  // update counters etc.
  goto_model.goto_functions.update();
}
