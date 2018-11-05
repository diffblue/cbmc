/*******************************************************************\

Module: Over-approximate Concurrency for Threaded Goto Programs

Author: Daniel Kroening

Date: October 2012

\*******************************************************************/

/// \file
/// Over-approximate Concurrency for Threaded Goto Programs

#include "is_threaded.h"

#include "ai.h"

class is_threaded_domaint:public ai_domain_baset
{
public:
  bool reachable;
  bool is_threaded;

  is_threaded_domaint():
    reachable(false),
    is_threaded(false)
  {
    // this is bottom
  }

  bool merge(
    const is_threaded_domaint &src,
    locationt,
    locationt)
  {
    INVARIANT(src.reachable,
              "Abstract states are only merged at reachable locations");

    bool old_reachable=reachable;
    bool old_is_threaded=is_threaded;

    reachable=true;
    is_threaded|=src.is_threaded;

    return old_reachable!=reachable ||
           old_is_threaded!=is_threaded;
  }

  void transform(
    const irep_idt &,
    locationt from,
    const irep_idt &,
    locationt,
    ai_baset &,
    const namespacet &) final override
  {
    INVARIANT(reachable,
              "Transformers are only applied at reachable locations");

    if(from->is_start_thread())
      is_threaded=true;
  }

  void make_bottom() final override
  {
    reachable=false;
    is_threaded=false;
  }

  void make_top() final override
  {
    reachable=true;
    is_threaded=true;
  }

  void make_entry() final override
  {
    reachable=true;
    is_threaded=false;
  }

  bool is_bottom() const override final
  {
    DATA_INVARIANT(reachable || !is_threaded,
                   "A location cannot be threaded if it is not reachable.");

    return !reachable;
  }

  bool is_top() const override final
  {
    return reachable && is_threaded;
  }
};

void is_threadedt::compute(const goto_functionst &goto_functions)
{
  // the analysis doesn't actually use the namespace, fake one
  symbol_tablet symbol_table;
  const namespacet ns(symbol_table);

  ait<is_threaded_domaint> is_threaded_analysis;

  is_threaded_analysis(goto_functions, ns);

  forall_goto_functions(f_it, goto_functions)
    forall_goto_program_instructions(i_it, f_it->second.body)
      if(is_threaded_analysis[i_it].is_threaded)
        is_threaded_set.insert(i_it);
}
