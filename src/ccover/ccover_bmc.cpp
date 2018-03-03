/*******************************************************************\

Module: Bounded Model Checking for Test Suite Generation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Bounded Model Checking for Test Suite Generation

#include "ccover_bmc.h"

#include <util/exit_codes.h>
#include <util/string2int.h>
#include <util/string_utils.h>

#include <langapi/language_util.h>

#include <goto-symex/memory_model_pso.h>
#include <goto-symex/path_storage.h>
#include <goto-symex/slice.h>
#include <goto-symex/slice_by_trace.h>

#include <cbmc/cbmc_solvers.h>

#include <linking/static_lifetime_init.h>

void ccover_bmct::do_conversion()
{
  status() << "converting SSA" << eom;

  // convert SSA
  equation.convert(prop_conv);
}

void ccover_bmct::get_memory_model()
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

void ccover_bmct::setup()
{
  get_memory_model();

  {
    const symbolt *init_symbol;
    if(!ns.lookup(INITIALIZE_FUNCTION, init_symbol))
      symex.language_mode=init_symbol->mode;
  }

  status() << "Starting Bounded Model Checking" << eom;

  symex.last_source_location.make_nil();

  symex.unwindset.parse_unwind(options.get_option("unwind"));
  symex.unwindset.parse_unwindset(options.get_option("unwindset"));
}

void ccover_bmct::run(abstract_goto_modelt &goto_model)
{
  setup();

  auto get_goto_function = [&goto_model](const irep_idt &id) ->
    const goto_functionst::goto_functiont &
  {
    return goto_model.get_goto_function(id);
  };

  // perform symbolic execution
  symex.symex_from_entry_point_of(get_goto_function, symex_symbol_table);

  // Borrow a reference to the goto functions map. This reference, or
  // iterators pointing into it, must not be stored by this function or its
  // callees, as goto_model.get_goto_function (as used by symex)
  // will have side-effects on it.
  const goto_functionst &goto_functions =
    goto_model.get_goto_functions();

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

//  const optionst::value_listt criteria=
//    options.get_list_option("cover");

  cover(goto_functions);
}

void ccover_bmct::slice()
{
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
                   << " assignments" << eom;
    }
    else
    {
      if(options.get_list_option("cover").empty())
      {
        simple_slice(equation);
        statistics() << "simple slicing removed "
                     << equation.count_ignored_SSA_steps()
                     << " assignments" << eom;
      }
    }
  }

  statistics() << "Generated "
               << symex.total_vccs<<" VCC(s), "
               << symex.remaining_vccs
               << " remaining after simplification" << eom;
}

/// Perform core BMC, using an abstract model to supply GOTO function bodies
/// (perhaps created on demand).
/// \param opts: command-line options affecting BMC
/// \param model: provides goto function bodies and the symbol table, perhaps
//    creating those function bodies on demand.
/// \param ui: user-interface mode (plain text, XML output, JSON output, ...)
/// \param message_handler: used for logging
int ccover_bmct::do_bmc(
  const optionst &opts,
  abstract_goto_modelt &model,
  const ui_message_handlert::uit &ui,
  message_handlert &message_handler)
{
  const symbol_tablet &symbol_table = model.get_symbol_table();
   messaget message(message_handler);

  path_strategy_choosert path_strategy_chooser;
  std::unique_ptr<path_storaget> path_storage=
    path_strategy_chooser.get("lifo");

  try
  {
    cbmc_solverst solvers(opts, symbol_table, message_handler);
    solvers.set_ui(ui);
    std::unique_ptr<cbmc_solverst::solvert> cbmc_solver;
    cbmc_solver = solvers.get_solver();
    prop_convt &pc = cbmc_solver->prop_conv();
    ccover_bmct bmc(opts, symbol_table, message_handler, pc, *path_storage);
    bmc.set_ui(ui);
    bmc.run(model);
    return CPROVER_EXIT_SUCCESS;
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
  catch(const std::bad_alloc &)
  {
    message.error() << "Out of memory" << eom;
    return CPROVER_EXIT_INTERNAL_OUT_OF_MEMORY;
  }
  catch(...)
  {
    message.error() << "unable to get solver" << message.eom;
    return CPROVER_EXIT_EXCEPTION;
  }
}
