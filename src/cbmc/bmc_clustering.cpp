/*******************************************************************\

Module: Clustering Symbolic Execution of ANSI-C

Author: 

\*******************************************************************/

#include <limits>

#include <goto-symex/slice.h>
#include <util/time_stopping.h>
#include <util/string2int.h>
#include <util/source_location.h>
#include <util/string_utils.h>
#include <util/message.h>
#include <util/json.h>
#include <util/cprover_prefix.h>

#include <langapi/mode.h>
#include <langapi/language_util.h>

#include <ansi-c/ansi_c_language.h>

#include <stdlib.h>     /* srand, rand */
#include <time.h>       /* time */

#include <goto-symex/build_goto_trace.h>
#include <iostream>
#include "bmc_clustering.h"

/*******************************************************************\

Function: bmc_clusteringt::step

  Inputs:

 Outputs:

 Purpose: run goto-symex^2 loop

\*******************************************************************/

safety_checkert::resultt bmc_clusteringt::step(
  const goto_functionst &goto_functions)
{
  symex().total_vccs=0;
  symex().remaining_vccs=0;

  setup_clustering_unwind();

  bool restored_state=false;
  while(!symex_state.call_stack().empty())
  {
    if(!restored_state)
    {
      symex()(
        symex_state,
        goto_functions,
        goto_functions.function_map.at(goto_functions.entry_point()).body);
    }
    restored_state=false;

    if(symex_state.call_stack().empty())
    {
      if(symex().learning_symex)
      {
        symex().backtrack_learn(symex_state);
        //symex().print_learnt_map();
      }

      if(!symex().states.empty())
      {
        pick_up_a_new_state();
        restored_state=true;
        continue;
      }
      else break;
    }

    if(symex().learning_symex)
      symex().add_latest_learnt_info(symex_state, goto_functions);

    if(symex_state.source.pc->type==ASSERT)
    {
      if(violated_assert())
      {
        goto_tracet &goto_trace=safety_checkert::error_trace;
        build_goto_trace(equation, prop_conv, ns, goto_trace);
        std::cout << "\n" << "Counterexample:" << "\n";
        show_goto_trace(std::cout, ns, goto_trace);
        result() << "VERIFICATION FAILED" << eom;
        result() << "#Visited states: "
          << (symex().recorded_states-symex().states.size())
          << eom;
        return safety_checkert::resultt::UNSAFE;
      }
    }
    else
    {
      goto_symext::statet state=symex_state;
      // depth-first
      if(symex_state.locations.back().goto_branch
        ==symex_targett::sourcet::EMPTY)
      {
        if(reachable_if())
        {
          state.locations.back().goto_branch=symex_targett::sourcet::IF;
          symex().states.push_back(state);
          ++symex().recorded_states;
          equations.push_back(equation);
          symex().add_goto_if_assumption(symex_state, goto_functions);
          continue;
        }

        else // if(reachable_else())
        {
          state.locations.back().goto_branch=symex_targett::sourcet::ELSE;
          symex().add_goto_else_assumption(symex_state, goto_functions);
          continue;
        }
        UNREACHABLE;
      }
      else
      {
        if(reachable_else())
        {
          state.locations.back().goto_branch=symex_targett::sourcet::ELSE;
          symex().add_goto_else_assumption(symex_state, goto_functions);
          continue;
        }
        if(!symex().states.empty())
        {
          pick_up_a_new_state();
          restored_state=true;
        }
        else break;
      }
    }
    continue;
  }

  report_success();

  result() << "#Visited states: "
    << (symex().recorded_states-symex().states.size())
    << eom;
  return safety_checkert::resultt::SAFE;
}

/*******************************************************************\

Function: bmc_incrementalt::run

  Inputs:

 Outputs:

 Purpose: run incremental BMC loop

\*******************************************************************/

safety_checkert::resultt bmc_clusteringt::run(
  const goto_functionst &goto_functions)
{
  safety_checkert::resultt result;

  absolute_timet sat_start=current_time();

  result=step(goto_functions);

  if(options.get_bool_option("show-vcc"))
    show_vcc();

  absolute_timet sat_stop=current_time();
  status() << "Runtime: " << (sat_stop-sat_start) << "s" << eom;

  return result;
}

decision_proceduret::resultt bmc_clusteringt::run_and_clear_decision_procedure()
{
  prop_conv.set_all_frozen();

  // each time a different solver is created
  prop_convt &prop_conv2=cbmc_solvers.get_solver().release()->prop_conv();

  decision_proceduret::resultt result=run_decision_procedure(prop_conv2);

  return result;
}

bool bmc_clusteringt::violated_assert()
{
#if 0
  std::cout << "\n[(goto-symex^2)]: assert\n";
  std::cout << symex_state.source.pc->source_location << "\n";
  std::cout << from_expr(symex_state.source.pc->code) << "\n";
#endif

  std::size_t num=equation.SSA_steps.size();
  clear(equation);

  symex().mock_step(symex_state, goto_functions);

  if(num==equation.SSA_steps.size())
    return false;

  decision_proceduret::resultt result=run_and_clear_decision_procedure();

  if(result==decision_proceduret::resultt::D_SATISFIABLE)
    return true;

  return false;
}

void bmc_clusteringt::clear(symex_target_equationt &equation)
{
  for(auto &x : equation.SSA_steps)
    if(x.is_assert())
      x.ignore=true;
}

bool bmc_clusteringt::reachable_if()
{
#if 0
  std::cout << "\n[(goto-symex^2)]: reachable if\n";
  std::cout << "[source]: " << symex_state.source.pc->source_location << "\n";
  std::cout << "[type]: " << symex_state.source.pc->type << "\n";
  std::cout << "[guard]:" << from_expr(symex_state.source.pc->guard) << "\n";
#endif

  // make a snapshot
  goto_symext::statet backup_state=symex_state;
  auto tmp=equation;

  std::size_t num=equation.SSA_steps.size();
  clear(equation);
  symex().mock_goto_if_condition(symex_state, goto_functions);
  if(num==equation.SSA_steps.size())
    return false;
  decision_proceduret::resultt result=run_and_clear_decision_procedure();

  // recover the analysis
  symex_state=backup_state;
  equation=tmp;

  --symex().total_vccs;
  --symex().remaining_vccs;

  return (result==decision_proceduret::resultt::D_SATISFIABLE);
}

bool bmc_clusteringt::reachable_else()
{
#if 0
  std::cout << "\n[(goto-symex^2)]: reachable else\n";
  std::cout << "[source]: " << symex_state.source.pc->source_location << "\n";
  std::cout << "[type]: " << symex_state.source.pc->type << "\n";
  std::cout << "[guard]:" << from_expr(symex_state.source.pc->guard) << "\n";
#endif

  // make a snapshot
  goto_symext::statet backup_state=symex_state;
  auto tmp=equation;

  std::size_t num=equation.SSA_steps.size();
  clear(equation);
  symex().mock_goto_else_condition(symex_state, goto_functions);
  if(num==equation.SSA_steps.size())
    return false;
  decision_proceduret::resultt result=run_and_clear_decision_procedure();

  // recover
  symex_state=backup_state;
  equation=tmp;

  --symex().total_vccs;
  --symex().remaining_vccs;

  return (result==decision_proceduret::resultt::D_SATISFIABLE);
}

decision_proceduret::resultt
bmc_clusteringt::run_decision_procedure(prop_convt &prop_conv)
{
  status() << "Passing problem to "
           << prop_conv.decision_procedure_text() << eom;

  prop_conv.set_message_handler(get_message_handler());

  // stop the time
  absolute_timet sat_start=current_time();

  do_conversion(prop_conv);

  status() << "Running " << prop_conv.decision_procedure_text() << eom;


  decision_proceduret::resultt dec_result=prop_conv.dec_solve();
  // output runtime

  {
    absolute_timet sat_stop=current_time();
    status() << "Runtime decision procedure: "
             << (sat_stop-sat_start) << "s" << eom;
  }

  return dec_result;
}

void bmc_clusteringt::do_conversion(prop_convt &prop_conv)
{
  // convert HDL (hook for hw-cbmc)
  do_unwind_module();

  status() << "converting SSA" << eom;

  // convert SSA
  equation.convert(prop_conv);

  // the 'extra constraints'
  if(!bmc_constraints.empty())
  {
    status() << "converting constraints" << eom;

    forall_expr_list(it, bmc_constraints)
      prop_conv.set_to_true(*it);
  }
}

void bmc_clusteringt::setup_clustering_unwind()
{
  const std::string &set=options.get_option("unwindset");
  std::vector<std::string> unwindset_loops;
  split_string(set, ',', unwindset_loops, true, true);

  for(auto &val : unwindset_loops)
  {
    unsigned thread_nr=0;
    bool thread_nr_set=false;

    if(!val.empty() &&
       isdigit(val[0]) &&
       val.find(":")!=std::string::npos)
    {
      std::string nr=val.substr(0, val.find(":"));
      thread_nr=unsafe_string2unsigned(nr);
      thread_nr_set=true;
      val.erase(0, nr.size()+1);
    }

    if(val.rfind(":")!=std::string::npos)
    {
      std::string id=val.substr(0, val.rfind(":"));
      long uw=unsafe_string2int(val.substr(val.rfind(":")+1));

      if(thread_nr_set)
        symex().set_unwind_thread_loop_limit(thread_nr, id, uw);
      else
        symex().set_unwind_loop_limit(id, uw);
    }
  }

  if(options.get_option("unwind")!="")
    symex().set_unwind_limit(options.get_unsigned_int_option("unwind"));
}

void bmc_clusteringt::pick_up_a_new_state()
{
  if(symex_method=="fifo")
  {
    // fifo
    symex_state=symex().states.front();
    symex().states.erase(symex().states.begin());
    equation=equations.front();
    equations.erase(equations.begin());
  }
  else
  {
    // dfs
    symex_state=symex().states.back();
    symex().states.pop_back();
    equation=equations.back();
    equations.pop_back();
  }

  symex().create_a_cluster(symex_state, equation);
}
