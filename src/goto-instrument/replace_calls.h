/*******************************************************************\

Module: Replace calls

Author: Daniel Poetzl

\*******************************************************************/

/// \file
/// Replace calls to given functions with calls to other given
/// functions

#ifndef CPROVER_GOTO_PROGRAMS_REPLACE_CALLS_H
#define CPROVER_GOTO_PROGRAMS_REPLACE_CALLS_H

#include <goto-programs/goto_model.h>

class replace_callst
{
public:
  typedef std::list<std::string> replacement_listt;
  typedef std::map<irep_idt, irep_idt> replacement_mapt;

  void operator()(
    goto_modelt &goto_model,
    const replacement_listt &replacement_list) const;

  void operator()(
    goto_modelt &goto_model,
    const replacement_mapt &replacement_map) const;

protected:
  void operator()(
    goto_programt &goto_program,
    const goto_functionst &goto_functions,
    const namespacet &ns,
    const replacement_mapt &replacement_map) const;

  replacement_mapt
  parse_replacement_list(const replacement_listt &replacement_list) const;

  void check_replacement_map(
    const replacement_mapt &replacement_map,
    const goto_functionst &goto_functions,
    const namespacet &ns) const;
};

#define OPT_REPLACE_CALLS "(replace-calls):"

#define HELP_REPLACE_CALLS                                                     \
  " --replace-calls f:g           replace calls to f with calls to g\n"

#endif // CPROVER_GOTO_PROGRAMS_REPLACE_CALLS_H
