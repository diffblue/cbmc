/*******************************************************************\

Module: Symbolic Execution of ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution of ANSI-C

#include "bmc.h"

#include <chrono>
#include <iostream>

#include <util/exception_utils.h>
#include <util/exit_codes.h>

#include <langapi/language_util.h>

#include <goto-symex/show_program.h>
#include <goto-symex/show_vcc.h>

#include <linking/static_lifetime_init.h>

#include <goto-checker/bmc_util.h>
#include <goto-checker/report_util.h>
#include <goto-checker/solver_factory.h>

#include "counterexample_beautification.h"
#include "fault_localization.h"

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

decision_proceduret::resultt bmct::run_decision_procedure()
{
  status() << "Passing problem to "
           << prop_conv.decision_procedure_text() << eom;

  prop_conv.set_message_handler(get_message_handler());

  auto solver_start = std::chrono::steady_clock::now();

  convert_symex_target_equation(equation, prop_conv, get_message_handler());

  // hook for cegis to freeze synthesis program vars
  freeze_program_variables();

  status() << "Running " << prop_conv.decision_procedure_text() << eom;

  decision_proceduret::resultt dec_result=prop_conv.dec_solve();

  {
    auto solver_stop = std::chrono::steady_clock::now();
    statistics()
      << "Runtime decision procedure: "
      << std::chrono::duration<double>(solver_stop - solver_start).count()
      << "s" << eom;
  }

  return dec_result;
}

safety_checkert::resultt bmct::execute(
  abstract_goto_modelt &goto_model)
{
  try
  {
    auto get_goto_function = [&goto_model](const irep_idt &id) ->
      const goto_functionst::goto_functiont &
    {
      return goto_model.get_goto_function(id);
    };

    perform_symbolic_execution(get_goto_function);

    // Borrow a reference to the goto functions map. This reference, or
    // iterators pointing into it, must not be stored by this function or its
    // callees, as goto_model.get_goto_function (as used by symex)
    // will have side-effects on it.
    const goto_functionst &goto_functions =
      goto_model.get_goto_functions();

    // This provides the driver program the opportunity to do things like a
    // symbol-table or goto-functions dump instead of actually running the
    // checker, like show-vcc except driver-program specific.
    // In particular clients that use symex-driven program loading need to print
    // GOTO functions after symex, as function bodies are not produced until
    // symex first requests them.
    if(driver_callback_after_symex && driver_callback_after_symex())
      return safety_checkert::resultt::SAFE; // to indicate non-error

    if(equation.has_threads())
    {
      // When doing path exploration in a concurrent setting, we should avoid
      // model-checking the program until we reach the end of a path.
      if(symex.should_pause_symex)
        return safety_checkert::resultt::PAUSED;

      // add a partial ordering, if required
      memory_model->set_message_handler(get_message_handler());
      (*memory_model)(equation);
    }

    statistics() << "size of program expression: "
                 << equation.SSA_steps.size()
                 << " steps" << eom;

    slice(symex, equation, ns, options, ui_message_handler);

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
      show_vcc(options, ui_message_handler, equation);
      return safety_checkert::resultt::SAFE; // to indicate non-error
    }

    if(!options.get_list_option("cover").empty())
    {
      return cover(goto_functions)?
        safety_checkert::resultt::ERROR:safety_checkert::resultt::SAFE;
    }

    if(options.get_option("localize-faults")!="")
    {
      fault_localizationt fault_localization(
        goto_functions, *this, options);
      return fault_localization();
    }

    // any properties to check at all?
    if(
      !options.get_bool_option("program-only") &&
      symex.get_remaining_vccs() == 0)
    {
      if(options.is_set("paths"))
        return safety_checkert::resultt::PAUSED;
      report_success(ui_message_handler);
      output_graphml(equation, ns, options);
      return safety_checkert::resultt::SAFE;
    }

    if(options.get_bool_option("program-only"))
    {
      show_program(ns, equation);
      return safety_checkert::resultt::SAFE;
    }

    if(!options.is_set("paths") || symex.path_segment_vccs > 0)
      return decide(goto_functions);

    return safety_checkert::resultt::PAUSED;
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


safety_checkert::resultt bmct::run(
  abstract_goto_modelt &goto_model)
{
  memory_model = get_memory_model(options, ns);
  setup_symex(symex, ns, options, ui_message_handler);

  return execute(goto_model);
}

safety_checkert::resultt bmct::decide(const goto_functionst &goto_functions)
{
  prop_conv.set_message_handler(get_message_handler());

  if(options.get_bool_option("stop-on-fail"))
    return stop_on_fail();
  else
    return all_properties(goto_functions);
}

safety_checkert::resultt bmct::stop_on_fail()
{
  switch(run_decision_procedure())
  {
  case decision_proceduret::resultt::D_UNSATISFIABLE:
    report_success(ui_message_handler);
    output_graphml(equation, ns, options);
    return resultt::SAFE;

  case decision_proceduret::resultt::D_SATISFIABLE:
    if(options.get_bool_option("trace"))
    {
      if(options.get_bool_option("beautify"))
        counterexample_beautificationt()(
          dynamic_cast<boolbvt &>(prop_conv), equation);

      build_error_trace(
        error_trace, ns, equation, prop_conv, ui_message_handler);
      output_error_trace(error_trace, ns, trace_options(), ui_message_handler);
      output_graphml(error_trace, ns, options);
    }

    report_failure(ui_message_handler);
    return resultt::UNSAFE;

  default:
    if(options.get_bool_option("dimacs") ||
       options.get_option("outfile")!="")
      return resultt::SAFE;

    error() << "decision procedure failed" << eom;

    return resultt::ERROR;
  }

  UNREACHABLE;
}

/// Perform core BMC, using an abstract model to supply GOTO function bodies
/// (perhaps created on demand).
/// \param opts: command-line options affecting BMC
/// \param model: provides goto function bodies and the symbol table, perhaps
///   creating those function bodies on demand.
/// \param ui: user-interface mode (plain text, XML output, JSON output, ...)
/// \param driver_configure_bmc: function provided by the driver program,
///   which applies driver-specific configuration to a bmct before running.
/// \param callback_after_symex: optional callback to be run after symex.
///   See class member `bmct::driver_callback_after_symex` for details.
int bmct::do_language_agnostic_bmc(
  const optionst &opts,
  abstract_goto_modelt &model,
  ui_message_handlert &ui,
  std::function<void(bmct &, const symbol_tablet &)> driver_configure_bmc,
  std::function<bool(void)> callback_after_symex)
{
  safety_checkert::resultt final_result = safety_checkert::resultt::SAFE;
  safety_checkert::resultt tmp_result = safety_checkert::resultt::SAFE;
  const symbol_tablet &symbol_table = model.get_symbol_table();
  messaget message(ui);
  std::unique_ptr<path_storaget> worklist;
  std::string strategy = opts.get_option("exploration-strategy");
  worklist = get_path_strategy(strategy);
  try
  {
    {
      solver_factoryt solvers(
        opts,
        symbol_table,
        ui,
        ui.get_ui() == ui_message_handlert::uit::XML_UI);
      std::unique_ptr<solver_factoryt::solvert> cbmc_solver =
        solvers.get_solver();
      prop_convt &pc = cbmc_solver->prop_conv();
      bmct bmc(opts, symbol_table, ui, pc, *worklist, callback_after_symex);
      if(driver_configure_bmc)
        driver_configure_bmc(bmc, symbol_table);
      tmp_result = bmc.run(model);

      if(
        tmp_result == safety_checkert::resultt::UNSAFE &&
        opts.get_bool_option("stop-on-fail") && opts.is_set("paths"))
      {
        worklist->clear();
        return CPROVER_EXIT_VERIFICATION_UNSAFE;
      }

      if(tmp_result != safety_checkert::resultt::PAUSED)
        final_result = tmp_result;
    }
    INVARIANT(
      opts.get_bool_option("paths") || worklist->empty(),
      "the worklist should be empty after doing full-program "
      "model checking, but the worklist contains " +
        std::to_string(worklist->size()) + " unexplored branches.");

    // When model checking, the bmc.run() above will already have explored
    // the entire program, and final_result contains the verification result.
    // The worklist (containing paths that have not yet been explored) is thus
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

    while(!worklist->empty())
    {
      solver_factoryt solvers(
        opts,
        symbol_table,
        ui,
        ui.get_ui() == ui_message_handlert::uit::XML_UI);
      std::unique_ptr<solver_factoryt::solvert> cbmc_solver =
        solvers.get_solver();
      prop_convt &pc = cbmc_solver->prop_conv();
      path_storaget::patht &resume = worklist->peek();
      path_explorert pe(
        opts,
        symbol_table,
        ui,
        pc,
        resume.equation,
        resume.state,
        *worklist,
        callback_after_symex);
      if(driver_configure_bmc)
        driver_configure_bmc(pe, symbol_table);
      tmp_result = pe.run(model);

      if(
        tmp_result == safety_checkert::resultt::UNSAFE &&
        opts.get_bool_option("stop-on-fail") && opts.is_set("paths"))
      {
        worklist->clear();
        return CPROVER_EXIT_VERIFICATION_UNSAFE;
      }

      if(tmp_result != safety_checkert::resultt::PAUSED)
        final_result &= tmp_result;
      worklist->pop();
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
  catch(std::runtime_error &e)
  {
    message.error() << e.what() << message.eom;
    return CPROVER_EXIT_EXCEPTION;
  }

  switch(final_result)
  {
  case safety_checkert::resultt::SAFE:
    if(opts.is_set("paths"))
      report_success(ui);
    return CPROVER_EXIT_VERIFICATION_SAFE;
  case safety_checkert::resultt::UNSAFE:
    if(opts.is_set("paths"))
      report_failure(ui);
    return CPROVER_EXIT_VERIFICATION_UNSAFE;
  case safety_checkert::resultt::ERROR:
    return CPROVER_EXIT_INTERNAL_ERROR;
  case safety_checkert::resultt::PAUSED:
    UNREACHABLE;
  }
  UNREACHABLE;
}

void bmct::perform_symbolic_execution(
  goto_symext::get_goto_functiont get_goto_function)
{
  symex.symex_from_entry_point_of(get_goto_function, symex_symbol_table);

  if(options.get_bool_option("validate-ssa-equation"))
  {
    symex.validate(validation_modet::INVARIANT);
  }

  INVARIANT(
    options.get_bool_option("paths") || path_storage.empty(),
    "Branch points were saved even though we should have been "
    "executing the entire program and merging paths");
}

void path_explorert::perform_symbolic_execution(
  goto_symext::get_goto_functiont get_goto_function)
{
  symex.resume_symex_from_saved_state(
    get_goto_function, saved_state, &equation, symex_symbol_table);
}
