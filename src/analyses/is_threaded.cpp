/*******************************************************************\

Module: Over-approximate Concurrency for Threaded Goto Programs

Author: Daniel Kroening

Date: October 2012

\*******************************************************************/

#include "ai.h"
#include "is_threaded.h"

class is_threaded_domaint:public ai_domain_baset
{
public:
  bool reachable;
  bool has_spawn;
  bool is_threaded;

  inline is_threaded_domaint():
    reachable(false),
    has_spawn(false),
    is_threaded(false)
  {
    // this is bottom
  }

  inline bool merge(
    const is_threaded_domaint &src,
    locationt from,
    locationt to)
  {
    bool old_reachable=reachable;
    if(src.reachable)
      reachable=true;

    bool old_h_s=has_spawn;
    if(src.has_spawn &&
       (from->is_end_function() ||
        from->function==to->function))
      has_spawn=true;

    bool old_i_t=is_threaded;
    if(has_spawn ||
       (src.is_threaded &&
       !from->is_end_function()))
      is_threaded=true;

    return old_reachable!=reachable ||
           old_i_t!=is_threaded ||
           old_h_s!=has_spawn;
  }

  void transform(
    locationt from,
    locationt to,
    ai_baset &ai,
    const namespacet &ns) final
  {
    if(!reachable)
      return;
    if(from->is_start_thread() ||
       to->is_end_thread())
    {
      has_spawn=true;
      is_threaded=true;
    }
  }

  void make_bottom() final
  {
    reachable=has_spawn=is_threaded=false;
  }

  void make_top() final
  {
    reachable=has_spawn=is_threaded=true;
  }

  void make_entry() final
  {
    reachable=true;
    has_spawn=is_threaded=false;
  }
};

/*******************************************************************\

Function: is_threadedt::compute

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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
