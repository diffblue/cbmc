/*******************************************************************\

Module:

Author: Vincent Nimal

\*******************************************************************/

#include <util/i2string.h>
#include <util/cprover_prefix.h>
#include <util/expr_util.h>
#include <util/namespace.h>
#include <util/message.h>

#include <goto-programs/remove_skip.h>
#include <goto-instrument/rw_set.h>
#include <goto-instrument/wmm/instrumenter_pensieve.h>

#include "pensieve.h"

/*******************************************************************\

Function: fencer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void fence_pensieve(
  value_setst &value_sets,
  symbol_tablet &symbol_table,
  goto_functionst &goto_functions,
  unsigned unwinding_bound,
  unsigned input_max_po_trans,
  bool render_po,
  bool render_file,
  bool render_function,
  bool naive_mode,
  message_handlert& message_handler)
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
  
  instrumenter_pensievet instrumenter(symbol_table, goto_functions, message);
  max_thds=instrumenter.goto2graph_cfg(value_sets, Power, true, no_loop);
  message.status() << "Abstract event graph computed" << messaget::eom;

  if(input_max_po_trans!=0)
    instrumenter.set_parameters_collection(0,input_max_po_trans);
  else
    instrumenter.set_parameters_collection(max_thds);

  /* necessary for correct printings */
  namespacet ns(symbol_table); 

  if(naive_mode)
    instrumenter.collect_pairs_naive(ns);
  else
    instrumenter.collect_pairs(ns);

  /* removes potential skips */
  Forall_goto_functions(f_it, goto_functions)
    remove_skip(f_it->second.body);

  // update counters etc.
  goto_functions.update();
}

