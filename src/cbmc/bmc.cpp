/*******************************************************************\

Module: Symbolic Execution of ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution of ANSI-C

#include "bmc.h"

#include <chrono>
#include <exception>
#include <fstream>
#include <iostream>
#include <memory>

#include <util/exit_codes.h>
#include <util/string2int.h>
#include <util/source_location.h>
#include <util/string_utils.h>
#include <util/memory_info.h>
#include <util/message.h>
#include <util/json.h>
#include <util/cprover_prefix.h>

#include <langapi/mode.h>
#include <langapi/language_util.h>

#include <goto-programs/goto_model.h>
#include <goto-programs/xml_goto_trace.h>
#include <goto-programs/json_goto_trace.h>
#include <goto-programs/graphml_witness.h>

#include <goto-symex/build_goto_trace.h>
#include <goto-symex/slice.h>
#include <goto-symex/slice_by_trace.h>
#include <goto-symex/memory_model_sc.h>
#include <goto-symex/memory_model_tso.h>
#include <goto-symex/memory_model_pso.h>

#include "cbmc_solvers.h"
#include "counterexample_beautification.h"
#include "fault_localization.h"

void bmct::do_unwind_module()
{
  // this is a hook for hw-cbmc
}

/// Hook used by CEGIS to selectively freeze variables
/// in the SAT solver after the SSA formula is added to the solver.
/// Freezing variables is necessary to make use of incremental
/// solving with MiniSat SimpSolver.
/// Potentially a useful hook for other applications using
/// incremental solving.
void bmct::freeze_program_variables()
{
  // this is a hook for cegis
}

void bmct::error_trace()
{
  status() << "Building error trace" << eom;

  goto_tracet &goto_trace=safety_checkert::error_trace;
  build_goto_trace(equation, prop_conv, ns, goto_trace);

  switch(ui)
  {
  case ui_message_handlert::uit::PLAIN:
    result() << "Counterexample:" << eom;
    show_goto_trace(result(), ns, goto_trace);
    result() << eom;
    break;

  case ui_message_handlert::uit::XML_UI:
    {
      xmlt xml;
      convert(ns, goto_trace, xml);
      status() << xml;
    }
    break;

  case ui_message_handlert::uit::JSON_UI:
    {
      json_objectt json;
      json_arrayt &result_array=json["results"].make_array();
      json_objectt &json_result=result_array.push_back().make_object();
      const goto_trace_stept &step=goto_trace.steps.back();
      json_result["property"]=
        json_stringt(id2string(step.pc->source_location.get_property_id()));
      json_result["description"]=
        json_stringt(id2string(step.pc->source_location.get_comment()));
      json_result["status"]=json_stringt("failed");
      jsont &json_trace=json_result["trace"];
      convert(ns, goto_trace, json_trace, trace_options());
      status() << json_result;
    }
    break;
  }
}

/// outputs witnesses in graphml format
void bmct::output_graphml(resultt result)
{
  const std::string graphml=options.get_option("graphml-witness");
  if(graphml.empty())
    return;

  graphml_witnesst graphml_witness(ns);
  if(result==resultt::UNSAFE)
    graphml_witness(safety_checkert::error_trace);
  else if(result==resultt::SAFE)
    graphml_witness(equation);
  else
    return;

  if(graphml=="-")
    write_graphml(graphml_witness.graph(), std::cout);
  else
  {
    std::ofstream out(graphml);
    write_graphml(graphml_witness.graph(), out);
  }
}

void bmct::do_conversion()
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

    for(const auto &constraint : bmc_constraints)
      prop_conv.set_to_true(constraint);
  }
  // hook for cegis to freeze synthesis program vars
  freeze_program_variables();
}

decision_proceduret::resultt
bmct::run_decision_procedure(prop_convt &prop_conv)
{
  status() << "Passing problem to "
           << prop_conv.decision_procedure_text() << eom;

  prop_conv.set_message_handler(get_message_handler());

  auto solver_start = std::chrono::steady_clock::now();

  do_conversion();

  status() << "Running " << prop_conv.decision_procedure_text() << eom;

  decision_proceduret::resultt dec_result=prop_conv.dec_solve();

  {
    auto solver_stop = std::chrono::steady_clock::now();
    status() << "Runtime decision procedure: "
             << std::chrono::duration<double>(solver_stop-solver_start).count()
             << "s" << eom;
  }

  return dec_result;
}

void bmct::report_success()
{
  result() << "VERIFICATION SUCCESSFUL" << eom;

  switch(ui)
  {
  case ui_message_handlert::uit::PLAIN:
    break;

  case ui_message_handlert::uit::XML_UI:
    {
      xmlt xml("cprover-status");
      xml.data="SUCCESS";
      result() << xml;
    }
    break;

  case ui_message_handlert::uit::JSON_UI:
    {
      json_objectt json_result;
      json_result["cProverStatus"]=json_stringt("success");
      result() << json_result;
    }
    break;
  }
}

void bmct::report_failure()
{
  result() << "VERIFICATION FAILED" << eom;

  switch(ui)
  {
  case ui_message_handlert::uit::PLAIN:
    break;

  case ui_message_handlert::uit::XML_UI:
    {
      xmlt xml("cprover-status");
      xml.data="FAILURE";
      result() << xml;
    }
    break;

  case ui_message_handlert::uit::JSON_UI:
    {
      json_objectt json_result;
      json_result["cProverStatus"]=json_stringt("failure");
      result() << json_result;
    }
    break;
  }
}

void bmct::show_program()
{
  unsigned count=1;

  std::cout << "\n" << "Program constraints:" << "\n";

  for(const auto &step : equation.SSA_steps)
  {
    std::cout << "// " << step.source.pc->location_number << " ";
    std::cout << step.source.pc->source_location.as_string() << "\n";

    if(step.is_assignment())
    {
      std::string string_value=
        from_expr(ns, "", step.cond_expr);
      std::cout << "(" << count << ") " << string_value << "\n";

      if(!step.guard.is_true())
      {
        std::string string_value=
          from_expr(ns, "", step.guard);
        std::cout << std::string(std::to_string(count).size()+3, ' ');
        std::cout << "guard: " << string_value << "\n";
      }

      count++;
    }
    else if(step.is_assert())
    {
      std::string string_value=
        from_expr(ns, "", step.cond_expr);
      std::cout << "(" << count << ") ASSERT("
                << string_value <<") " << "\n";

      if(!step.guard.is_true())
      {
        std::string string_value=
          from_expr(ns, "", step.guard);
        std::cout << std::string(std::to_string(count).size()+3, ' ');
        std::cout << "guard: " << string_value << "\n";
      }

      count++;
    }
    else if(step.is_assume())
    {
      std::string string_value=
        from_expr(ns, "", step.cond_expr);
      std::cout << "(" << count << ") ASSUME("
                << string_value <<") " << "\n";

      if(!step.guard.is_true())
      {
        std::string string_value=
          from_expr(ns, "", step.guard);
        std::cout << std::string(std::to_string(count).size()+3, ' ');
        std::cout << "guard: " << string_value << "\n";
      }

      count++;
    }
    else if(step.is_constraint())
    {
      std::string string_value=
        from_expr(ns, "", step.cond_expr);
      std::cout << "(" << count << ") CONSTRAINT("
                << string_value <<") " << "\n";

      count++;
    }
    else if(step.is_shared_read() || step.is_shared_write())
    {
      std::string string_value=
        from_expr(ns, "", step.ssa_lhs);
      std::cout << "(" << count << ") SHARED_"
                << (step.is_shared_write()?"WRITE":"READ")
                << "(" << string_value <<")\n";

      if(!step.guard.is_true())
      {
        std::string string_value=
          from_expr(ns, "", step.guard);
        std::cout << std::string(std::to_string(count).size()+3, ' ');
        std::cout << "guard: " << string_value << "\n";
      }

      count++;
    }
  }
}


void bmct::get_memory_model()
{
  const std::string mm=options.get_option("mm");

  if(mm.empty() || mm=="sc")
    memory_model=util_make_unique<memory_model_sct>(ns);
  else if(mm=="tso")
    memory_model=util_make_unique<memory_model_tsot>(ns);
  else if(mm=="pso")
    memory_model=util_make_unique<memory_model_psot>(ns);
  else
  {
    error() << "Invalid memory model " << mm
            << " -- use one of sc, tso, pso" << eom;
    throw "invalid memory model";
  }
}

void bmct::setup()
{
  get_memory_model();
  symex.options=options;

  {
    const symbolt *init_symbol;
    if(!ns.lookup(CPROVER_PREFIX "initialize", init_symbol))
      symex.language_mode=init_symbol->mode;
  }

  status() << "Starting Bounded Model Checking" << eom;

  symex.last_source_location.make_nil();

    setup_unwind();
}

safety_checkert::resultt bmct::execute(const goto_functionst &goto_functions)
{
  try
  {
    perform_symbolic_execution(goto_functions);

    // add a partial ordering, if required
    if(equation.has_threads())
    {
      memory_model->set_message_handler(get_message_handler());
      (*memory_model)(equation);
    }

  statistics() << "size of program expression: "
               << equation.SSA_steps.size()
               << " steps" << eom;

    slice();

    // coverage report
    std::string cov_out=options.get_option("symex-coverage-report");
    if(!cov_out.empty() &&
       symex.output_coverage_report(goto_functions, cov_out))
    {
      error() << "Failed to write symex coverage report" << eom;
      return safety_checkert::resultt::ERROR;
    }

    if(options.get_bool_option("show-vcc"))
    {
      show_vcc();
      return safety_checkert::resultt::SAFE; // to indicate non-error
    }

    if(!options.get_list_option("cover").empty())
    {
      const optionst::value_listt criteria=
        options.get_list_option("cover");
      return cover(goto_functions, criteria)?
        safety_checkert::resultt::ERROR:safety_checkert::resultt::SAFE;
    }

    if(options.get_option("localize-faults")!="")
    {
      fault_localizationt fault_localization(
        goto_functions, *this, options);
      return fault_localization();
    }

    // any properties to check at all?
    if(!options.get_bool_option("program-only") &&
       symex.remaining_vccs==0)
    {
      report_success();
      output_graphml(resultt::SAFE);
      return safety_checkert::resultt::SAFE;
    }

    if(options.get_bool_option("program-only"))
    {
      show_program();
      return safety_checkert::resultt::SAFE;
    }

    return decide(goto_functions, prop_conv);
  }

  catch(const std::string &error_str)
  {
    messaget message(get_message_handler());
    message.error().source_location=symex.last_source_location;
    message.error() << error_str << messaget::eom;

    return safety_checkert::resultt::ERROR;
  }

  catch(const char *error_str)
  {
    messaget message(get_message_handler());
    message.error().source_location=symex.last_source_location;
    message.error() << error_str << messaget::eom;

    return safety_checkert::resultt::ERROR;
  }

  catch(const std::bad_alloc &)
  {
    error() << "Out of memory" << eom;
    return safety_checkert::resultt::ERROR;
  }
}

void bmct::slice()
{
  if(options.get_option("slice-by-trace")!="")
  {
    symex_slice_by_tracet symex_slice_by_trace(ns);

    symex_slice_by_trace.slice_by_trace
    (options.get_option("slice-by-trace"),
        equation);
  }
  // any properties to check at all?
  if(equation.has_threads())
  {
    // we should build a thread-aware SSA slicer
    statistics() << "no slicing due to threads" << eom;
  }
  else
  {
    if(options.get_bool_option("slice-formula"))
    {
      ::slice(equation);
      statistics() << "slicing removed "
                   << equation.count_ignored_SSA_steps()
                   << " assignments"<<eom;
    }
    else
    {
      if(options.get_list_option("cover").empty())
      {
        simple_slice(equation);
        statistics() << "simple slicing removed "
                     << equation.count_ignored_SSA_steps()
                     << " assignments"<<eom;
      }
    }
  }
  statistics() << "Generated "
               << symex.total_vccs<<" VCC(s), "
               << symex.remaining_vccs
               << " remaining after simplification" << eom;
}

safety_checkert::resultt bmct::run(
  const goto_functionst &goto_functions)
{
  setup();

  return execute(goto_functions);
}

safety_checkert::resultt bmct::decide(
  const goto_functionst &goto_functions,
  prop_convt &prop_conv)
{
  prop_conv.set_message_handler(get_message_handler());

  if(options.get_bool_option("stop-on-fail"))
    return stop_on_fail(prop_conv);
  else
    return all_properties(goto_functions, prop_conv);
}

void bmct::show()
{
  if(options.get_bool_option("show-vcc"))
  {
    show_vcc();
  }

  if(options.get_bool_option("program-only"))
  {
    show_program();
  }
}

safety_checkert::resultt bmct::stop_on_fail(prop_convt &prop_conv)
{
  switch(run_decision_procedure(prop_conv))
  {
  case decision_proceduret::resultt::D_UNSATISFIABLE:
    report_success();
    output_graphml(resultt::SAFE);
    return resultt::SAFE;

  case decision_proceduret::resultt::D_SATISFIABLE:
    if(options.get_bool_option("trace"))
    {
      if(options.get_bool_option("beautify"))
        counterexample_beautificationt()(
          dynamic_cast<bv_cbmct &>(prop_conv), equation, ns);

      error_trace();
      output_graphml(resultt::UNSAFE);
    }

    report_failure();
    return resultt::UNSAFE;

  default:
    if(options.get_bool_option("dimacs") ||
       options.get_option("outfile")!="")
      return resultt::SAFE;

    error() << "decision procedure failed" << eom;

    return resultt::ERROR;
  }
}

void bmct::setup_unwind()
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
        symex.set_unwind_thread_loop_limit(thread_nr, id, uw);
      else
        symex.set_unwind_loop_limit(id, uw);
    }
  }

  if(options.get_option("unwind")!="")
    symex.set_unwind_limit(options.get_unsigned_int_option("unwind"));
}

int bmct::do_language_agnostic_bmc(
  const optionst &opts,
  const goto_modelt &goto_model,
  const ui_message_handlert::uit &ui,
  messaget &message,
  std::function<void(bmct &, const goto_modelt &)> frontend_configure_bmc)
{
  message_handlert &mh = message.get_message_handler();
  safety_checkert::resultt result;
  goto_symext::branch_worklistt worklist;
  try
  {
    {
      cbmc_solverst solvers(
        opts, goto_model.symbol_table, message.get_message_handler());
      solvers.set_ui(ui);
      std::unique_ptr<cbmc_solverst::solvert> cbmc_solver;
      cbmc_solver = solvers.get_solver();
      prop_convt &pc = cbmc_solver->prop_conv();
      bmct bmc(opts, goto_model.symbol_table, mh, pc, worklist);
      bmc.set_ui(ui);
      frontend_configure_bmc(bmc, goto_model);
      result = bmc.run(goto_model.goto_functions);
    }
    INVARIANT(
      opts.get_bool_option("paths") || worklist.empty(),
      "the worklist should be empty after doing full-program "
      "model checking, but the worklist contains " +
        std::to_string(worklist.size()) + " unexplored branches.");

    // When model checking, the bmc.run() above will already have explored
    // the entire program, and result contains the verification result. The
    // worklist (containing paths that have not yet been explored) is thus
    // empty, and we don't enter this loop.
    //
    // When doing path exploration, there will be some saved paths left to
    // explore in the worklist. We thus need to run the above code again,
    // once for each saved path in the worklist, to continue symbolically
    // execute the program. Note that the code in the loop is similar to
    // the code above except that we construct a path_explorert rather than
    // a bmct, which allows us to execute from a saved state rather than
    // from the entry point. See the path_explorert documentation, and the
    // difference between the implementations of perform_symbolic_exection()
    // in bmct and path_explorert, for more information.

    while(!worklist.empty())
    {
      message.status() << "___________________________\n"
                       << "Starting new path (" << worklist.size()
                       << " to go)\n"
                       << message.eom;
      cbmc_solverst solvers(
        opts, goto_model.symbol_table, message.get_message_handler());
      solvers.set_ui(ui);
      std::unique_ptr<cbmc_solverst::solvert> cbmc_solver;
      cbmc_solver = solvers.get_solver();
      prop_convt &pc = cbmc_solver->prop_conv();
      goto_symext::branch_pointt &resume = worklist.front();
      path_explorert pe(
        opts,
        goto_model.symbol_table,
        mh,
        pc,
        resume.equation,
        resume.state,
        worklist);
      frontend_configure_bmc(pe, goto_model);
      result &= pe.run(goto_model.goto_functions);
      worklist.pop_front();
    }
  }
  catch(const char *error_msg)
  {
    message.error() << error_msg << message.eom;
    return CPROVER_EXIT_EXCEPTION;
  }
  catch(const std::string &error_msg)
  {
    message.error() << error_msg << message.eom;
    return CPROVER_EXIT_EXCEPTION;
  }
  catch(...)
  {
    message.error() << "unable to get solver" << message.eom;
    throw std::current_exception();
  }

  switch(result)
  {
  case safety_checkert::resultt::SAFE:
    return CPROVER_EXIT_VERIFICATION_SAFE;
  case safety_checkert::resultt::UNSAFE:
    return CPROVER_EXIT_VERIFICATION_UNSAFE;
  case safety_checkert::resultt::ERROR:
    return CPROVER_EXIT_INTERNAL_ERROR;
  }
  UNREACHABLE;
}

void bmct::perform_symbolic_execution(const goto_functionst &goto_functions)
{
  symex.symex_from_entry_point_of(goto_functions, symex_symbol_table);
  INVARIANT(
    options.get_bool_option("paths") || branch_worklist.empty(),
    "Branch points were saved even though we should have been "
    "executing the entire program and merging paths");
}

void path_explorert::perform_symbolic_execution(
  const goto_functionst &goto_functions)
{
  symex.resume_symex_from_saved_state(
    goto_functions, saved_state, &equation, symex_symbol_table);
}
