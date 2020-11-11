/*******************************************************************\

Module: Variable sensitivity domain

Author: Martin Brain, martin.brain@cs.ox.ac.uk

Date: August 2020

\*******************************************************************/

/// \file
/// An abstract interpreter, based on the default recursive-interprocedural
/// that uses variable sensitivity domain's three-way-merge operation on
/// returning from a function call.  This gives some of the precision of
/// context-sensitive analysis but at a fraction of the cost.  The really
/// key thing is that it distinguishes between variables that are modified in
/// the function (or things called from it) and those that appear modified
/// because they have different values at different call sites.  This is
/// especially important for preserving the value of (unmodified) global
/// variables.

#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_THREE_WAY_MERGE_ABSTRACT_INTERPRETER_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_THREE_WAY_MERGE_ABSTRACT_INTERPRETER_H

#include <analyses/ai.h>

class ai_three_way_merget : public ai_recursive_interproceduralt
{
public:
  ai_three_way_merget(
    std::unique_ptr<ai_history_factory_baset> &&hf,
    std::unique_ptr<ai_domain_factory_baset> &&df,
    std::unique_ptr<ai_storage_baset> &&st)
    : ai_recursive_interproceduralt(std::move(hf), std::move(df), std::move(st))
  {
  }

protected:
  // Like ai_recursive_interproceduralt we hook the handling of function calls.
  // Much of this is the same as ai_recursive_interproceduralt's handling but
  // on function return the three-way merge is used.
  bool visit_edge_function_call(
    const irep_idt &calling_function_id,
    trace_ptrt p_call,
    locationt l_return,
    const irep_idt &callee_function_id,
    working_sett &working_set,
    const goto_programt &callee,
    const goto_functionst &goto_functions,
    const namespacet &ns) override;
};

#endif
