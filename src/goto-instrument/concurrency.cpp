/*******************************************************************\

Module: Encoding for Threaded Goto Programs

Author: Daniel Kroening

Date: October 2012

\*******************************************************************/

#include "concurrency.h"
#include "is_threaded.h"

class concurrency_instrumentationt
{
public:
  concurrency_instrumentationt(
    value_setst &_value_sets, 
    contextt &_context):
    value_sets(_value_sets),
    context(_context)
  {
  }
  
  void operator()(goto_functionst &goto_functions)
  {
    instrument(goto_functions);
  }

protected:
  value_setst &value_sets;
  contextt &context;
  
  void instrument(goto_functionst &goto_functions);
  void instrument(goto_programt &goto_program);
};

/*******************************************************************\

Function: concurrency_instrumentationt::instrument

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void concurrency_instrumentationt::instrument(
  goto_programt &goto_program)
{
}

/*******************************************************************\

Function: concurrency_instrumentationt::instrument

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void concurrency_instrumentationt::instrument(
  goto_functionst &goto_functions)
{
  namespacet ns(context);
  is_threadedt is_threaded(ns, goto_functions);

  for(goto_functionst::function_mapt::iterator
      f_it=goto_functions.function_map.begin();
      f_it!=goto_functions.function_map.end();
      f_it++)
    instrument(f_it->second.body);
}

/*******************************************************************\

Function: concurrency

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void concurrency(
  value_setst &value_sets,
  class contextt &context,
  goto_functionst &goto_functions)
{
  concurrency_instrumentationt concurrency_instrumentation(value_sets, context);
  concurrency_instrumentation(goto_functions);
}
