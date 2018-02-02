/*******************************************************************\

Module: Java Static Initializers

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

#ifndef CPROVER_JAVA_BYTECODE_JAVA_STATIC_INITIALIZERS_H
#define CPROVER_JAVA_BYTECODE_JAVA_STATIC_INITIALIZERS_H

#include <util/symbol_table.h>
#include <util/std_code.h>

irep_idt clinit_wrapper_name(const irep_idt &class_name);

bool is_clinit_wrapper_function(const irep_idt &function_id);

void create_static_initializer_wrappers(symbol_tablet &symbol_table);

codet get_clinit_wrapper_body(
  const irep_idt &function_id, const symbol_tablet &symbol_table);

#endif
