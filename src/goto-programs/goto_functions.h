/*******************************************************************\

Module: Goto Programs with Functions

Author: Daniel Kroening

Date: June 2003

\*******************************************************************/

#ifndef CPROVER_GOTO_FUNCTIONS_H
#define CPROVER_GOTO_FUNCTIONS_H

#include <iostream>

#include <std_types.h>

#include "goto_program.h"
#include "goto_functions_template.h"

class goto_functionst:public goto_functions_templatet<goto_programt>
{
public:
};

#define Forall_goto_functions(it, functions) \
  for(goto_functionst::function_mapt::iterator it=(functions).function_map.begin(); \
      it!=(functions).function_map.end(); it++)
 
#define forall_goto_functions(it, functions) \
  for(goto_functionst::function_mapt::const_iterator it=(functions).function_map.begin(); \
      it!=(functions).function_map.end(); it++)

void get_local_identifiers(
  const goto_function_templatet<goto_programt> &goto_function,
  std::set<irep_idt> &dest);

#endif
