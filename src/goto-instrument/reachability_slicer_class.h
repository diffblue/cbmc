/*******************************************************************\

Module: Goto Program Slicing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAM_SLICER_CLASS_H
#define CPROVER_GOTO_PROGRAM_SLICER_CLASS_H

#include <goto-programs/goto_functions.h>
#include <goto-programs/cfg.h>

#include <analyses/is_threaded.h>

/*******************************************************************\

   Class: reachability_slicert

 Purpose:

\*******************************************************************/

class reachability_slicert
{
public:
  void operator()(goto_functionst &goto_functions)
  {
    cfg(goto_functions);
    is_threadedt is_threaded(goto_functions);
    fixedpoint_assertions(is_threaded);
    slice(goto_functions);
  }

protected:
  struct slicer_entryt
  {
    slicer_entryt():reaches_assertion(false)
    {
    }

    bool reaches_assertion;
  };

  typedef cfg_baset<slicer_entryt> cfgt;
  cfgt cfg;

  typedef std::stack<cfgt::iterator> queuet;

  void fixedpoint_assertions(const is_threadedt &is_threaded);

  void slice(goto_functionst &goto_functions);
};

#endif
