/*******************************************************************\

Module: Modifies

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Modifies

#ifndef CPROVER_GOTO_INSTRUMENT_FUNCTION_MODIFIES_H
#define CPROVER_GOTO_INSTRUMENT_FUNCTION_MODIFIES_H

#include <goto-programs/goto_functions.h>
#include <analyses/local_may_alias.h>

class function_modifiest
{
public:
  explicit function_modifiest(const goto_functionst &_goto_functions):
    goto_functions(_goto_functions)
  {
  }

  typedef std::set<exprt> modifiest;

  void get_modifies(
    const local_may_aliast &local_may_alias,
    const goto_programt::const_targett,
    modifiest &);

  void get_modifies_function(
    const exprt &,
    modifiest &);

  void operator()(const exprt &function, modifiest &modifies)
  {
    get_modifies_function(function, modifies);
  }

protected:
  const goto_functionst &goto_functions;

  typedef std::map<irep_idt, modifiest> function_mapt;
  function_mapt function_map;
};

#endif // CPROVER_GOTO_INSTRUMENT_FUNCTION_MODIFIES_H
