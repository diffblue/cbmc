/*******************************************************************\

Module: Interrupt Instrumentation

Author: Daniel Kroening, Lihao Liang

Date: June 2016

\*******************************************************************/

#include <ansi-c/string_constant.h>
#include "interrupt_util.h"

/*******************************************************************\

Function: get_isr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

symbol_exprt get_isr(
  const symbol_tablet &symbol_table,
  const irep_idt &interrupt_handler)
{
  std::list<symbol_exprt> matches;

  forall_symbol_base_map(m_it, symbol_table.symbol_base_map, interrupt_handler)
  {
    // look it up
    symbol_tablet::symbolst::const_iterator s_it=
      symbol_table.symbols.find(m_it->second);

    if(s_it==symbol_table.symbols.end())
      continue;

    if(s_it->second.type.id()==ID_code)
      matches.push_back(s_it->second.symbol_expr());
  }

  if(matches.empty())
    throw "interrupt handler `"+id2string(interrupt_handler)+"' not found";

  if(matches.size()>=2)
    throw "interrupt handler `"+id2string(interrupt_handler)+"' is ambiguous";

  symbol_exprt isr=matches.front();

  if(!to_code_type(isr.type()).parameters().empty())
    throw "interrupt handler `"+id2string(interrupt_handler)+
          "' must not have parameters";

  return isr;
}

/*******************************************************************\

Function: poential_race_on_read

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool potential_race_on_read(
  const rw_set_baset &code_rw_set,
  const rw_set_baset &isr_rw_set)
{
  // R/W race?
  forall_rw_set_r_entries(e_it, code_rw_set)
  {
    if(isr_rw_set.has_w_entry(e_it->first))
      return true;
  }

  return false;
}

/*******************************************************************\

Function: poential_race_on_write

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool potential_race_on_write(
  const rw_set_baset &code_rw_set,
  const rw_set_baset &isr_rw_set)
{
  // W/R or W/W?
  forall_rw_set_w_entries(e_it, code_rw_set)
  {
    if(isr_rw_set.has_r_entry(e_it->first))
      return true;

    if(isr_rw_set.has_w_entry(e_it->first))
      return true;
  }

  return false;
}

/*******************************************************************\

Function: insert_function_before_instruction

  Inputs:

 Outputs:

 Purpose: insert function call before instruction

\*******************************************************************/

void insert_function_before_instruction(
  goto_programt &goto_program,
  goto_programt::targett &i_it,
  const symbol_exprt &function)
{
  goto_programt::instructiont &instruction=*i_it;
  goto_programt::instructiont original_instruction;
  original_instruction.swap(instruction);

  const source_locationt &source_location=
    original_instruction.source_location;

  code_function_callt function_call;
  function_call.add_source_location()=source_location;
  function_call.function()=function;

  goto_programt::targett t_call=i_it;
  goto_programt::targett t_orig=goto_program.insert_after(t_call);

  t_call->make_function_call(function_call);
  t_call->source_location=source_location;
  t_call->function=original_instruction.function;

  t_orig->swap(original_instruction);

  i_it=t_orig; // the for loop already counts us up
}

/*******************************************************************\

Function: insert_function_after_instruction

  Inputs:

 Outputs:

 Purpose: insert function call after instruction

\*******************************************************************/

void insert_function_after_instruction(
  goto_programt &goto_program,
  goto_programt::targett &i_it,
  const symbol_exprt &function)
{
  goto_programt::targett t_orig=i_it;
  t_orig++;

  goto_programt::targett t_call=goto_program.insert_after(i_it);

  const source_locationt &source_location=i_it->source_location;

  code_function_callt function_call;
  function_call.add_source_location()=source_location;
  function_call.function()=function;

  t_call->make_function_call(function_call);
  t_call->source_location=source_location;
  t_call->function=i_it->function;

  i_it=t_call; // the for loop already counts us up
}

/*******************************************************************\

Function: build_isr_map

  Inputs:

 Outputs:

 Purpose: retrieve a list of interrupt handlers from source code
\*******************************************************************/

void build_isr_map(const namespacet &ns, isr_mapt &isr_map)
{
  const symbolt &threads=ns.lookup(CPROVER_ISR_ARRAY);
  const array_exprt &thread_array_expr=to_array_expr(threads.value);
  unsigned int i=0;

  forall_operands(thread_it, thread_array_expr)
  {
    const irep_idt &thread_name=
      to_string_constant(thread_it->op0().op0()).get_value();
    isr_map[i]=thread_name;
    i++;
  }
}
