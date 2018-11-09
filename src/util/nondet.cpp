/*******************************************************************\

Module: Non-deterministic object init and choice for CBMC

 Author: Diffblue Ltd.

\*******************************************************************/

#include "nondet.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/fresh_symbol.h>
#include <util/symbol.h>

/// Gets a fresh nondet choice in range (min_value, max_value). GOTO generated
/// resembles:
/// ```
/// int_type name_prefix::nondet_int = NONDET(int_type)
/// ASSUME(name_prefix::nondet_int >= min_value)
/// ASSUME(name_prefix::nondet_int <= max_value)
/// ```
/// \param min_value: Minimum value (inclusive) of returned int.
/// \param max_value: Maximum value (inclusive) of returned int.
/// \param name_prefix: Prefix for the fresh symbol name generated (should be
///   function id)
/// \param int_type: The type of the int used to non-deterministically choose
///   one of the switch cases.
/// \param source_location: The location to mark the generated int with.
/// \param symbol_table: The global symbol table.
/// \param instructions [out]: Output instructions are written to
///   'instructions'. These declare, nondet-initialise and range-constrain (with
///   assume statements) a fresh integer.
/// \return Returns a symbol expression for the resulting integer.
symbol_exprt generate_nondet_int(
  const mp_integer &min_value,
  const mp_integer &max_value,
  const std::string &name_prefix,
  const typet &int_type,
  const irep_idt &mode,
  const source_locationt &source_location,
  symbol_table_baset &symbol_table,
  code_blockt &instructions)
{
  PRECONDITION(min_value < max_value);

  // Declare a symbol for the non deterministic integer.
  const symbol_exprt &nondet_symbol =
    get_fresh_aux_symbol(
      int_type, name_prefix, "nondet_int", source_location, mode, symbol_table)
      .symbol_expr();
  instructions.add(code_declt(nondet_symbol));

  // Assign the symbol any non deterministic integer value.
  //   int_type name_prefix::nondet_int = NONDET(int_type)
  instructions.add(
    code_assignt(nondet_symbol, side_effect_expr_nondett(int_type)));

  // Constrain the non deterministic integer with a lower bound of `min_value`.
  //   ASSUME(name_prefix::nondet_int >= min_value)
  instructions.add(
    code_assumet(
      binary_predicate_exprt(
        nondet_symbol, ID_ge, from_integer(min_value, int_type))));

  // Constrain the non deterministic integer with an upper bound of `max_value`.
  //   ASSUME(name_prefix::nondet_int <= max_value)
  instructions.add(
    code_assumet(
      binary_predicate_exprt(
        nondet_symbol, ID_le, from_integer(max_value, int_type))));

  return nondet_symbol;
}

/// Pick nondeterministically between imperative actions 'switch_cases'.
/// \param name_prefix: Name prefix for fresh symbols (should be function id)
/// \param switch_cases: List of codet objects to execute in each switch case.
/// \param int_type: The type of the int used to non-deterministically choose
///   one of the switch cases.
/// \param source_location: The location to mark the generated int with.
/// \param symbol_table: The global symbol table.
/// \return Returns a nondet-switch choosing between switch_cases. The resulting
///   switch block has no default case.
code_blockt generate_nondet_switch(
  const irep_idt &name_prefix,
  const alternate_casest &switch_cases,
  const typet &int_type,
  const irep_idt &mode,
  const source_locationt &source_location,
  symbol_table_baset &symbol_table)
{
  PRECONDITION(!switch_cases.empty());

  if(switch_cases.size() == 1)
    return code_blockt({switch_cases[0]});

  code_blockt result_block;

  const symbol_exprt &switch_value = generate_nondet_int(
    0,
    switch_cases.size() - 1,
    id2string(name_prefix),
    int_type,
    mode,
    source_location,
    symbol_table,
    result_block);

  code_blockt switch_block;
  size_t case_number = 0;
  for(const auto &switch_case : switch_cases)
  {
    code_blockt this_block;
    this_block.add(switch_case);
    this_block.add(code_breakt());
    code_switch_caset this_case(
      from_integer(case_number, switch_value.type()), this_block);
    switch_block.add(std::move(this_case));
    ++case_number;
  }

  code_switcht result_switch(switch_value, switch_block);
  result_block.add(std::move(result_switch));
  return result_block;
}
