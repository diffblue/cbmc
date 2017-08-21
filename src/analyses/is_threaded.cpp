/*******************************************************************\

Module: Over-approximate Concurrency for Threaded Goto Programs

Author: Daniel Kroening

Date: October 2012

\*******************************************************************/

/// \file
/// Over-approximate Concurrency for Threaded Goto Programs

#include "ai.h"
#include "is_threaded.h"

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
    locationt from,
    locationt to)
  {
    assert(src.reachable);

    bool old_reachable=reachable;
    bool old_is_threaded=is_threaded;

    reachable=true;
    is_threaded|=src.is_threaded;

    return old_reachable!=reachable ||
           old_is_threaded!=is_threaded;
  }

  virtual std::vector<symbol_exprt> get_modified_symbols(const is_threaded_domaint &other) const
  {
    return std::vector<symbol_exprt>();
  }

  void transform(
    locationt from,
    locationt to,
    ai_baset &ai,
    const namespacet &ns) final override
  {
    assert(reachable);

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
    assert(reachable || !is_threaded);

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
