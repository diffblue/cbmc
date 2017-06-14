/*******************************************************************\

Module: Goto Programs with Functions

Author: Daniel Kroening

Date: June 2003

\*******************************************************************/

/// \file
/// Goto Programs with Functions

#ifndef CPROVER_GOTO_PROGRAMS_GOTO_FUNCTIONS_H
#define CPROVER_GOTO_PROGRAMS_GOTO_FUNCTIONS_H

#include "goto_program.h"
#include "goto_functions_template.h"

class goto_functionst:public goto_functions_templatet<goto_programt>
{
public:
  goto_functionst()=default;

  // Copying is unavailable as base class copy is deleted
  // MSVC is unable to automatically determine this
  goto_functionst(const goto_functionst &)=delete;
  goto_functionst &operator=(const goto_functionst &)=delete;

  // Move operations need to be explicitly enabled as they are deleted with the
  // copy operations
  // default for move operations isn't available on Windows yet, so define
  //  explicitly (see https://msdn.microsoft.com/en-us/library/hh567368.aspx
  //  under "Defaulted and Deleted Functions")

  goto_functionst(goto_functionst &&other):
    goto_functions_templatet(std::move(other))
  {
  }

  goto_functionst &operator=(goto_functionst &&other)
  {
    goto_functions_templatet::operator=(std::move(other));
    return *this;
  }
};

#define Forall_goto_functions(it, functions) \
  for(goto_functionst::function_mapt::iterator \
      it=(functions).function_map.begin(); \
      it!=(functions).function_map.end(); it++)

#define forall_goto_functions(it, functions) \
  for(goto_functionst::function_mapt::const_iterator \
      it=(functions).function_map.begin(); \
      it!=(functions).function_map.end(); it++)

void get_local_identifiers(
  const goto_function_templatet<goto_programt> &goto_function,
  std::set<irep_idt> &dest);

#endif // CPROVER_GOTO_PROGRAMS_GOTO_FUNCTIONS_H
