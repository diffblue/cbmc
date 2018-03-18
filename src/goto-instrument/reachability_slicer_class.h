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
    slicing_criteriont &criterion,
    bool include_forward_reachability)
  {
    cfg(goto_functions);
    is_threadedt is_threaded(goto_functions);
    fixedpoint_to_assertions(is_threaded, criterion);
    if(include_forward_reachability)
      fixedpoint_from_assertions(is_threaded, criterion);
    slice(goto_functions);
  }

protected:
  struct slicer_entryt
  {
    slicer_entryt() : reaches_assertion(false), reachable_from_assertion(false)
    {
    }

    bool reaches_assertion;
    bool reachable_from_assertion;
  };

  typedef cfg_baset<slicer_entryt> cfgt;
  cfgt cfg;

  typedef std::stack<cfgt::entryt> queuet;

  void fixedpoint_to_assertions(
    const is_threadedt &is_threaded,
    slicing_criteriont &criterion);

  void fixedpoint_from_assertions(
    const is_threadedt &is_threaded,
    slicing_criteriont &criterion);

  void slice(goto_functionst &goto_functions);

private:
  std::vector<cfgt::node_indext>
  get_sources(const is_threadedt &is_threaded, slicing_criteriont &criterion);
};

#endif // CPROVER_GOTO_INSTRUMENT_REACHABILITY_SLICER_CLASS_H
