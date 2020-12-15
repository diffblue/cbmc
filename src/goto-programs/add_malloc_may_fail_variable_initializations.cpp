/// \file
/// \author Diffblue Ltd.

#include "add_malloc_may_fail_variable_initializations.h"

#include "goto_model.h"

#include <linking/static_lifetime_init.h>

#include <util/arith_tools.h>
#include <util/config.h>
#include <util/irep.h>

template <typename T>
code_assignt make_integer_assignment(
  const symbol_table_baset &symbol_table,
  const irep_idt &symbol_name,
  T &&value)
{
  const auto &symbol = symbol_table.lookup_ref(symbol_name).symbol_expr();
  return code_assignt{symbol, from_integer(value, symbol.type())};
}

void add_malloc_may_fail_variable_initializations(goto_modelt &goto_model)
{
  const auto malloc_may_fail_id = irep_idt{CPROVER_PREFIX "malloc_may_fail"};
  const auto malloc_failure_mode_id =
    irep_idt{CPROVER_PREFIX "malloc_failure_mode"};
  if(!goto_model.symbol_table.has_symbol(malloc_may_fail_id))
  {
    // if malloc_may_fail isn't in the symbol table (i.e. builtin library not
    // loaded) then we don't generate initialisation code for it.
    return;
  }

  INVARIANT(
    goto_model.symbol_table.has_symbol(malloc_failure_mode_id),
    "if malloc_may_fail is in the symbol table then so should "
    "malloc_failure_mode");

  auto const initialize_function_name = INITIALIZE_FUNCTION;
  PRECONDITION(
    goto_model.get_goto_functions().function_map.count(
      initialize_function_name) == 1);
  auto &initialize_function =
    goto_model.goto_functions.function_map.find(initialize_function_name)
      ->second;
  const auto initialize_function_end =
    --initialize_function.body.instructions.end();

  initialize_function.body.insert_before(
    initialize_function_end,
    goto_programt::make_assignment(make_integer_assignment(
      goto_model.symbol_table,
      malloc_may_fail_id,
      config.ansi_c.malloc_may_fail)));

  initialize_function.body.insert_before(
    initialize_function_end,
    goto_programt::make_assignment(make_integer_assignment(
      goto_model.symbol_table,
      malloc_failure_mode_id,
      config.ansi_c.malloc_failure_mode)));
}
