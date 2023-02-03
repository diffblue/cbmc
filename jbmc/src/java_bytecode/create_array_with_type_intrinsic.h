/*******************************************************************\

Module: Implementation of CProver.createArrayWithType intrinsic

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// Implementation of CProver.createArrayWithType intrinsic

#ifndef CPROVER_JAVA_BYTECODE_CREATE_ARRAY_WITH_TYPE_INTRINSIC_H
#define CPROVER_JAVA_BYTECODE_CREATE_ARRAY_WITH_TYPE_INTRINSIC_H

#include <util/std_code_base.h>

class message_handlert;
class symbol_table_baset;

irep_idt get_create_array_with_type_name();

codet create_array_with_type_body(
  const irep_idt &function_id,
  symbol_table_baset &symbol_table,
  message_handlert &message_handler);

#endif
