/*******************************************************************\

Module: Fence inference: Main

Author: Vincent Nimal

\*******************************************************************/

#include <util/i2string.h>
#include <util/cprover_prefix.h>
#include <util/expr_util.h>
#include <util/message.h>

#include <goto-programs/remove_skip.h>
#include <goto-instrument/wmm/goto2graph.h>
#include <goto-instrument/rw_set.h>

#include "fence_inserter.h"
#include "fence_user_def.h"
#include "fence_assert.h"
#include "fencer.h"

/*******************************************************************\

Function: fencer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void fence_weak_memory(
  memory_modelt model,
  value_setst &value_sets,
  symbol_tablet &symbol_table,
  goto_functionst &goto_functions,
  bool SCC,
  instrumentation_strategyt event_strategy,
  unsigned unwinding_bound,
  bool no_cfg_kill,
  bool no_dependencies,
  loop_strategyt duplicate_body,
  unsigned input_max_var,
  unsigned input_max_po_trans,
  bool render_po,
  bool render_file,
  bool render_function,
  bool cav11_option,
  bool hide_internals,
  bool print_graph,
  infer_modet mode,
  message_handlert& message_handler,
  bool ignore_arrays)
{
  messaget message(message_handler);

  message.status() << "--------" << messaget::eom;

  // all access to shared variables is pushed into assignments
  Forall_goto_functions(f_it, goto_functions)
    if(f_it->first!=CPROVER_PREFIX "initialize" &&
      f_it->first!=goto_functionst::entry_point())
      introduce_temporaries(value_sets, symbol_table, f_it->first,
        f_it->second.body,
#ifdef LOCAL_MAY
        f_it->second,
#endif
        message);
  message.status() << "Temporary variables added" << messaget::eom;

  unsigned max_thds = 0;
  instrumentert instrumenter(symbol_table, goto_functions, message);
  max_thds=instrumenter.goto2graph_cfg(value_sets, model,
    no_dependencies, duplicate_body);
  ++max_thds;
  message.status() << "Abstract event graph computed" << messaget::eom;

  // collects cycles, directly or by SCCs
  if(input_max_var!=0 || input_max_po_trans!=0)
    instrumenter.set_parameters_collection(input_max_var,input_max_po_trans,
      ignore_arrays);
  else
    instrumenter.set_parameters_collection(max_thds, 0, ignore_arrays);

  if(SCC)
  {
    instrumenter.collect_cycles_by_SCCs(model);
    message.statistics() << "cycles collected: " << messaget::eom;
    unsigned interesting_scc = 0;
    unsigned total_cycles = 0;
    for(unsigned i=0; i<instrumenter.num_sccs; i++)
      if(instrumenter.egraph_SCCs[i].size()>=4)
      {
        message.statistics() << "SCC #" << i << ": "
          <<instrumenter.set_of_cycles_per_SCC[interesting_scc++].size()
          <<" cycles found" << messaget::eom;
        total_cycles += instrumenter
          .set_of_cycles_per_SCC[interesting_scc++].size();
      }

    /* if no cycle, no need to instrument */
    if(total_cycles == 0)
    {
      message.result() << "program safe -- no need to place additional fences"
        <<messaget::eom;

      // prints the whole abstract graph
      if(print_graph)
        instrumenter.egraph.print_graph();

      return;
    }
  }
  else
  {
    instrumenter.collect_cycles(model);
    message.statistics() << "cycles collected: "
      << instrumenter.set_of_cycles.size()
      << " cycles found" << messaget::eom;

    /* if no cycle, no need to instrument */
    if(instrumenter.set_of_cycles.size() == 0)
    {
      message.result() 
        << "program safe -- no need to place additional fences"
        << messaget::eom;
      instrumenter.print_map_function_graph();

      // prints the whole abstract graph
      if(print_graph)
        instrumenter.egraph.print_graph();

      return;
    }
  }

  /* selection of the cycles */
  if(!no_cfg_kill)
    instrumenter.cfg_cycles_filter();

  /* selects method, infers fences then outputs them */ 
  switch(mode) {
    case INFER:
    {
      fence_insertert fence_inserter(instrumenter, model);
      fence_inserter.compute();
      fence_inserter.print_to_file_3();
      break;
    }
    case USER_DEF:
    {
      fence_user_def_insertert fence_inserter(instrumenter, model);
      fence_inserter.compute();
      fence_inserter.print_to_file_3();
      break;
    }
    case USER_ASSERT:
    {
      fence_assert_insertert fence_inserter(instrumenter, model);
      fence_inserter.compute();
      fence_inserter.print_to_file_3();
      break;
    }
  }

  // additional outputs
#if 0
  instrumenter.set_rendering_options(render_po, render_file, render_function);
  instrumenter.print_outputs(model, hide_internals);
#endif

  /* TODO: insert the fences into the actual code or call script directly 
     from here*/

  /* removes potential skips */
  Forall_goto_functions(f_it, goto_functions)
    remove_skip(f_it->second.body);

  // update counters etc.
  goto_functions.update();

  // prints the whole abstract graph
  if(print_graph)
    instrumenter.egraph.print_graph();

  // for debug only
#if 0
  instrumenter.print_map_function_graph();
#endif
}

