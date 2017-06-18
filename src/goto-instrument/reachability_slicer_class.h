/*******************************************************************\

Module: Goto Program Slicing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Goto Program Slicing

#ifndef CPROVER_GOTO_INSTRUMENT_REACHABILITY_SLICER_CLASS_H
#define CPROVER_GOTO_INSTRUMENT_REACHABILITY_SLICER_CLASS_H

#include <goto-programs/goto_functions.h>
#include <goto-programs/cfg.h>

#include <analyses/is_threaded.h>

class slicing_criteriont;

class reachability_slicert
{
public:
  void operator()(
    goto_functionst &goto_functions,
    slicing_criteriont &criterion)
  {
    cfg(goto_functions);
    is_threadedt is_threaded(goto_functions);
    fixedpoint_assertions(is_threaded, criterion);
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

  using cfgt = cfg_baset<reachability_slicert::slicer_entryt>;
  cfgt cfg;

  using queuet = std::stack<cfgt::entryt>;

  void fixedpoint_assertions(
    const is_threadedt &is_threaded,
    slicing_criteriont &criterion);

  void slice(goto_functionst &goto_functions);
};

#endif // CPROVER_GOTO_INSTRUMENT_REACHABILITY_SLICER_CLASS_H
