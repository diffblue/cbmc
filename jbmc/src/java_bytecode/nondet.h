/*******************************************************************\

Module: Non-deterministic object init and choice for JBMC

Author: Diffblue Ltd.

\*******************************************************************/

#ifndef CPROVER_JAVA_BYTECODE_NONDET_H
#define CPROVER_JAVA_BYTECODE_NONDET_H

#include <util/std_code.h>

class allocate_objectst;
class symbol_table_baset;

using allocate_local_symbolt =
  std::function<symbol_exprt(const typet &type, std::string)>;

/// Same as \ref generate_nondet_int(
///   const mp_integer &min_value,
///   const mp_integer &max_value,
///   const std::string &name_prefix,
///   const typet &int_type,
///   const irep_idt &mode,
///   const source_locationt &source_location,
///   symbol_table_baset &symbol_table,
///   code_blockt &instructions)
/// except the minimum and maximum values are represented as exprts.
symbol_exprt generate_nondet_int(
  const exprt &min_value_expr,
  const exprt &max_value_expr,
  const std::string &basename_prefix,
  const source_locationt &source_location,
  allocate_objectst &allocate_objects,
  code_blockt &instructions);

symbol_exprt generate_nondet_int(
  const exprt &min_value_expr,
  const exprt &max_value_expr,
  const std::string &basename_prefix,
  const source_locationt &source_location,
  const allocate_local_symbolt &alocate_local_symbol,
  code_blockt &instructions);

/// Gets a fresh nondet choice in range (min_value, max_value). GOTO generated
/// resembles:
/// ```
/// int_type name_prefix::nondet_int = NONDET(int_type)
/// ASSUME(name_prefix::nondet_int >= min_value)
/// ASSUME(name_prefix::nondet_int <= max_value)
/// ```
/// \param min_value: Minimum value (inclusive) of returned int.
/// \param max_value: Maximum value (inclusive) of returned int.
/// \param basename_prefix: Basename prefix for the fresh symbol name generated.
/// \param int_type: The type of the int used to non-deterministically choose
///   one of the switch cases.
/// \param allocate_objects: Handles allocation of new objects.
/// \param source_location: The location to mark the generated int with.
/// \param [out] instructions: Output instructions are written to
///   'instructions'. These declare, nondet-initialise and range-constrain (with
///   assume statements) a fresh integer.
/// \return Returns a symbol expression for the resulting integer.
symbol_exprt generate_nondet_int(
  const mp_integer &min_value,
  const mp_integer &max_value,
  const std::string &basename_prefix,
  const typet &int_type,
  const source_locationt &source_location,
  allocate_objectst &allocate_objects,
  code_blockt &instructions);

typedef std::vector<codet> alternate_casest;

/// Pick nondeterministically between imperative actions 'switch_cases'.
/// \param name_prefix: Name prefix for fresh symbols (should be function id)
/// \param switch_cases: List of codet objects to execute in each switch case.
/// \param int_type: The type of the int used to non-deterministically choose
///   one of the switch cases.
/// \param mode: Mode (language) of the symbol to be generated.
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
  symbol_table_baset &symbol_table);

#endif // CPROVER_JAVA_BYTECODE_NONDET_H
