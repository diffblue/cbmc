/*******************************************************************\

 Module: Non-deterministic object init and choice for JBMC

 Author: Diffblue Ltd.

\*******************************************************************/

#ifndef CPROVER_JAVA_BYTECODE_NONDET_H
#define CPROVER_JAVA_BYTECODE_NONDET_H

#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

symbol_exprt generate_nondet_int(
  const mp_integer &min_value,
  const mp_integer &max_value,
  const std::string &name_prefix,
  const typet &int_type,
  const irep_idt &mode,
  const source_locationt &source_location,
  symbol_table_baset &symbol_table,
  code_blockt &instructions);

typedef std::vector<codet> alternate_casest;

code_blockt generate_nondet_switch(
  const irep_idt &name_prefix,
  const alternate_casest &switch_cases,
  const typet &int_type,
  const irep_idt &mode,
  const source_locationt &source_location,
  symbol_table_baset &symbol_table);

#endif // CPROVER_JAVA_BYTECODE_NONDET_H
