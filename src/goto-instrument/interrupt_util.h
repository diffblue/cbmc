/*******************************************************************\

Module: Interrupt Instrumentation 

Author: Daniel Kroening, Lihao Liang

Date: June 2016

\*******************************************************************/

#ifndef CPROVER_INTERRUPT_UTIL_H
#define CPROVER_INTERRUPT_UTIL_H

#include "rw_set.h"

#define CPROVER_ISR_ARRAY_ID "__CPROVER_ISR_ARRAY"

typedef hash_map_cont<unsigned int, irep_idt> isr_mapt;
typedef hash_map_cont<irep_idt, rw_set_function_rect, irep_id_hash> 
  isr_rw_set_mapt;

symbol_exprt get_isr(
  const symbol_tablet &symbol_table,
  const irep_idt &interrupt_handler);

bool potential_race_on_read(
  const rw_set_baset &code_rw_set,
  const rw_set_baset &isr_rw_set);

 bool potential_race_on_write(
  const rw_set_baset &code_rw_set,
  const rw_set_baset &isr_rw_set);
 
void insert_function_before_instruction(
  goto_programt &goto_program,
  goto_programt::targett &i_it,
  const symbol_exprt &function);

void insert_function_after_instruction(
  goto_programt &goto_program,
  goto_programt::targett &i_it,
  const symbol_exprt &function);

void build_isr_map(
  const namespacet &ns, 
  isr_mapt &isr_map);

#endif
