/*******************************************************************\

Module: CPROVER Command Line Option Processing

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// cprover Command Line Options Processing

#include "cprover_parse_options.h"

#include <util/config.h>
#include <util/cout_message.h>
#include <util/exit_codes.h>
#include <util/options.h>
#include <util/signal_catcher.h>
#include <util/ui_message.h>
#include <util/unicode.h>
#include <util/version.h>

#include <goto-programs/adjust_float_expressions.h>
#include <goto-programs/goto_inline.h>
#include <goto-programs/initialize_goto_model.h>
#include <goto-programs/loop_ids.h>
#include <goto-programs/remove_function_pointers.h>
#include <goto-programs/set_properties.h>
#include <goto-programs/show_goto_functions.h>
#include <goto-programs/show_properties.h>

#include <ansi-c/ansi_c_language.h>
#include <ansi-c/gcc_version.h>
#include <langapi/mode.h>

#include "c_safety_checks.h"
#include "format_hooks.h"
#include "help_formatter.h"
#include "instrument_contracts.h"
#include "instrument_given_invariants.h"
#include "state_encoding.h"

#include <fstream>
#include <iostream>

static void show_goto_functions(const goto_modelt &goto_model)
{
  // sort alphabetically
  const auto sorted = goto_model.goto_functions.sorted();

  const namespacet ns(goto_model.symbol_table);
  for(const auto &fun : sorted)
  {
    const symbolt &symbol = ns.lookup(fun->first);
    const bool has_body = fun->second.body_available();

    if(has_body)
    {
      std::cout << "^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n\n";

      std::cout << symbol.display_name() << " /* " << symbol.name << " */\n";
      fun->second.body.output(ns, symbol.name, std::cout);
    }
  }
}

static void show_functions_with_loops(const goto_modelt &goto_model)
{
  // sort alphabetically
  const auto sorted = goto_model.goto_functions.sorted();

  const namespacet ns(goto_model.symbol_table);
  for(const auto &fun : sorted)
  {
    const symbolt &symbol = ns.lookup(fun->first);

    if(symbol.is_file_local)
      continue;

    bool has_loop = false;
    for(auto &instruction : fun->second.body.instructions)
      if(instruction.is_backwards_goto())
        has_loop = true;

    if(has_loop)
      std::cout << symbol.display_name() << '\n';
  }
}

int cprover_parse_optionst::main()
{
  try
  {
    install_signal_catcher();

    cmdlinet cmdline;

    if(cmdline.parse(argc, argv, CPROVER_OPTIONS))
    {
      std::cerr << "Usage error!" << '\n';
      return CPROVER_EXIT_USAGE_ERROR;
    }

    if(cmdline.isset("version"))
    {
      std::cout << CBMC_VERSION << '\n';
      return CPROVER_EXIT_SUCCESS;
    }

    if(cmdline.isset('?') || cmdline.isset("help") || cmdline.isset('h'))
    {
      help();
      return CPROVER_EXIT_SUCCESS;
    }

    register_language(new_ansi_c_language);
    format_hooks();

    if(cmdline.args.empty())
    {
      std::cerr << "Please provide a program to verify\n";
      return CPROVER_EXIT_INCORRECT_TASK;
    }

    config.set(cmdline);

    // configure gcc, if required
    if(config.ansi_c.preprocessor == configt::ansi_ct::preprocessort::GCC)
    {
      gcc_versiont gcc_version;
      gcc_version.get("gcc");
      configure_gcc(gcc_version);
    }

    console_message_handlert message_handler;
    null_message_handlert null_message_handler;

    optionst options;
    auto goto_model =
      initialize_goto_model(cmdline.args, message_handler, options);

    auto &remove_function_pointers_message_handler =
      cmdline.isset("verbose")
        ? static_cast<message_handlert &>(message_handler)
        : static_cast<message_handlert &>(null_message_handler);

    remove_function_pointers(
      remove_function_pointers_message_handler, goto_model, false);

    adjust_float_expressions(goto_model);
    instrument_given_invariants(goto_model);

    bool perform_inlining;

    if(cmdline.isset("smt2"))
    {
      perform_inlining = !cmdline.isset("no-inline");
    }
    else
    {
      perform_inlining = cmdline.isset("inline");
    }

    if(!perform_inlining)
      instrument_contracts(goto_model);

    if(!cmdline.isset("no-safety"))
      c_safety_checks(goto_model);

    if(cmdline.isset("no-assertions"))
      no_assertions(goto_model);

    label_properties(goto_model);

    // bool perform_inlining = false;
    bool variable_encoding = cmdline.isset("variables");

    if(perform_inlining || variable_encoding)
    {
      std::cout << "Performing inlining\n";
      goto_inline(goto_model, message_handler, false);
    }

    goto_model.goto_functions.compute_target_numbers();
    goto_model.goto_functions.compute_location_numbers();

    if(cmdline.isset("show-goto-functions"))
    {
      show_goto_functions(goto_model);
      return CPROVER_EXIT_SUCCESS;
    }

    // show loop ids?
    if(cmdline.isset("show-loops"))
    {
      show_loop_ids(ui_message_handlert::uit::PLAIN, goto_model);
      return CPROVER_EXIT_SUCCESS;
    }

    if(cmdline.isset("show-functions-with-loops"))
    {
      show_functions_with_loops(goto_model);
      return CPROVER_EXIT_SUCCESS;
    }

    if(cmdline.isset("validate-goto-model"))
    {
      goto_model.validate();
    }

    if(cmdline.isset("show-properties"))
    {
      ui_message_handlert ui_message_handler(cmdline, "cprover");
      show_properties(goto_model, ui_message_handler);
      return CPROVER_EXIT_SUCCESS;
    }

// gcc produces a spurious warning on optionalt<irep_idt>.
// This will likely go away once we use std::optional<irep_idt>.
// To make clang ignore the pragma, we need to guard it with an ifdef.
#pragma GCC diagnostic push
#ifndef __clang__
#  pragma GCC diagnostic ignored "-Wmaybe-uninitialized"
#endif
    optionalt<irep_idt> contract = cmdline.isset("contract")
                                     ? irep_idt(cmdline.get_value("contract"))
                                     : optionalt<irep_idt>{};
#pragma GCC diagnostic pop

    if(cmdline.isset("smt2") || cmdline.isset("text") || variable_encoding)
    {
      auto format = cmdline.isset("smt2") ? state_encoding_formatt::SMT2
                                          : state_encoding_formatt::ASCII;

      if(cmdline.isset("outfile"))
      {
        auto file_name = cmdline.get_value("outfile");
#ifdef _WIN32
        std::ofstream out(widen(file_name));
#else
        std::ofstream out(file_name);
#endif
        if(!out)
        {
          std::cerr << "failed to open " << file_name << '\n';
          return CPROVER_EXIT_PARSE_ERROR;
        }

        if(variable_encoding)
          ::variable_encoding(goto_model, format, out);
        else
          state_encoding(goto_model, format, perform_inlining, contract, out);

        std::cout << "formula written to " << file_name << '\n';
      }
      else
      {
        if(variable_encoding)
          ::variable_encoding(goto_model, format, std::cout);
        else
          state_encoding(
            goto_model, format, perform_inlining, contract, std::cout);
      }

      if(!cmdline.isset("solve"))
        return CPROVER_EXIT_SUCCESS;
    }

    solver_optionst solver_options;

    if(cmdline.isset("unwind"))
    {
      solver_options.loop_limit = std::stoull(cmdline.get_value("unwind"));
    }
    else
      solver_options.loop_limit = 1;

    solver_options.trace = cmdline.isset("trace");
    solver_options.verbose = cmdline.isset("verbose");

    // solve
    auto result = state_encoding_solver(
      goto_model, perform_inlining, contract, solver_options);

    switch(result)
    {
    case solver_resultt::ALL_PASS:
      return CPROVER_EXIT_SUCCESS;

    case solver_resultt::SOME_FAIL:
      return CPROVER_EXIT_VERIFICATION_UNSAFE;

    case solver_resultt::ERROR:
      return CPROVER_EXIT_INTERNAL_ERROR;
    }
  }
  catch(const cprover_exception_baset &e)
  {
    std::cerr << "error: " << e.what() << '\n';
    return CPROVER_EXIT_EXCEPTION;
  }

  UNREACHABLE; // to silence a gcc warning
}

/// display command line help
void cprover_parse_optionst::help()
{
  std::cout << '\n';

  std::cout
    << u8"* * CPROVER " << CBMC_VERSION << " (" << (sizeof(void *) * 8)
    << "-bit)"
    << " * *\n"
    << "* *                       Copyright 2022                       * *\n";

  // clang-format off
  std::cout << help_formatter(
    "\n"
    "Usage:                     \tPurpose:\n"
    "\n"
    " {bcprover} [{y-?}] [{y-h}] [{y--help}] \t show this help\n"
    " {bcprover} {usource-file.c}    \t convert a given C program\n"
    "\n"
    "Other options:\n"
    " {y--inline} \t perform function call inlining before"
    " generating the formula\n"
    " {y--no-safety} \t disable safety checks\n"
    " {y--contract} {ufunction} \t check contract of given function\n"
    " {y--outfile} {ufile-name} \t set output file for formula\n"
    " {y--smt2} \t output formula in SMT-LIB2 format\n"
    " {y--text} \t output formula in text format\n"
    "\n");
}
