/*******************************************************************\

Module: Compute objects assigned to in a function

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Compute objects assigned to in a function.

#ifndef CPROVER_GOTO_INSTRUMENT_FUNCTION_ASSIGNS_H
#define CPROVER_GOTO_INSTRUMENT_FUNCTION_ASSIGNS_H

#include <goto-programs/goto_program.h>

#include <map>

class goto_functionst;
class local_may_aliast;

class function_assignst
{
public:
  explicit function_assignst(const goto_functionst &_goto_functions)
    : goto_functions(_goto_functions)
  {
  }

  typedef std::set<exprt> assignst;

  void get_assigns(
    const local_may_aliast &local_may_alias,
    const goto_programt::const_targett,
    assignst &);

  void get_assigns_function(const exprt &, assignst &);

  void operator()(const exprt &function, assignst &assigns)
  {
    get_assigns_function(function, assigns);
  }

protected:
  const goto_functionst &goto_functions;

  typedef std::map<irep_idt, assignst> function_mapt;
  function_mapt function_map;
};

#endif // CPROVER_GOTO_INSTRUMENT_FUNCTION_ASSIGNS_H
