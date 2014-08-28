/*******************************************************************\

Module: Count effective lines of code

Author: Michael Tautschnig

Date: December 2012

\*******************************************************************/

#include <iostream>

#include <util/prefix.h>

#include "count_eloc.h"

/*******************************************************************\

Function: count_eloc

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

unsigned count_eloc(const goto_programt &goto_program)
{
  hash_set_cont<irep_idt, irep_id_hash> lines;

  forall_goto_program_instructions(it, goto_program)
    if(it->source_location.is_not_nil() &&
        !has_prefix(id2string(it->source_location.get_file()), "<built-in-"))
      lines.insert(it->source_location.get_line());

  return lines.size();
}

/*******************************************************************\

Function: count_eloc

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void count_eloc(const goto_functionst &goto_functions)
{
  unsigned eloc=0;
  forall_goto_functions(f_it, goto_functions)
    eloc+=count_eloc(f_it->second.body);

  std::cout << "Effective lines of code: " << eloc << std::endl;
}

