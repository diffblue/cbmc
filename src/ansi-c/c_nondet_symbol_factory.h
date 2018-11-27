/*******************************************************************\

Module: C Nondet Symbol Factory

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// C Nondet Symbol Factory

#ifndef CPROVER_ANSI_C_C_NONDET_SYMBOL_FACTORY_H
#define CPROVER_ANSI_C_C_NONDET_SYMBOL_FACTORY_H

#include "c_object_factory_parameters.h"

#include <util/std_code.h>
#include <util/symbol_table.h>

symbol_exprt c_nondet_symbol_factory(
  code_blockt &init_code,
  symbol_tablet &symbol_table,
  const irep_idt base_name,
  const typet &type,
  const source_locationt &,
  const c_object_factory_parameterst &object_factory_parameters);

#endif // CPROVER_ANSI_C_C_NONDET_SYMBOL_FACTORY_H
