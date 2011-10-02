/*******************************************************************\

Module: Goto Program Slicing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAM_SLICER_CLASS_H
#define CPROVER_GOTO_PROGRAM_SLICER_CLASS_H

#include "goto_functions.h"
#include "cfg.h"

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
    fixedpoints();
    slice(goto_functions);
  }

  void operator()(goto_programt &goto_program)
  {
    cfg(goto_program);
    fixedpoints();
    slice(goto_program);
  }

protected:
  struct slicer_entryt
  {
    slicer_entryt():reaches_assertion(false), threaded(false)
    {
    }

    bool reaches_assertion, threaded;
  };

  typedef cfg_baset<slicer_entryt> cfgt;
  cfgt cfg;

  typedef std::stack<cfgt::iterator> queuet;

  void fixedpoint_assertions();
  void fixedpoint_threads();

  void fixedpoints()
  {
    // do threads first
    fixedpoint_threads();
    fixedpoint_assertions();
  }

  void slice(goto_programt &goto_program);
  void slice(goto_functionst &goto_functions);
};

#endif
