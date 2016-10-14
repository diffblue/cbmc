/*******************************************************************\

Module: GOTO-DIFF Command Line Option Processing

Author: Peter Schrammel

\*******************************************************************/

#include <fstream>
#include <cstdlib> // exit()
#include <iostream>
#include <memory>

#include <util/string2int.h>
#include <util/config.h>
#include <util/expr_util.h>
#include <util/language.h>
#include <util/i2string.h>

#include <goto-programs/goto_convert_functions.h>
#include <goto-programs/remove_function_pointers.h>
#include <goto-programs/remove_returns.h>
#include <goto-programs/remove_vector.h>
#include <goto-programs/remove_complex.h>
#include <goto-programs/remove_asm.h>
#include <goto-programs/remove_unused_functions.h>
#include <goto-programs/goto_inline.h>
#include <goto-programs/show_properties.h>
#include <goto-programs/set_properties.h>
#include <goto-programs/read_goto_binary.h>
#include <goto-programs/string_abstraction.h>
#include <goto-programs/string_instrumentation.h>
#include <goto-programs/loop_ids.h>
#include <goto-programs/link_to_library.h>

#include <pointer-analysis/add_failed_symbols.h>

#include <analyses/goto_check.h>

#include <langapi/mode.h>

#include <cbmc/version.h>

#include "goto_diff_parse_options.h"
#include "goto_diff.h"
#include "syntactic_diff.h"
#include "unified_diff.h"
#include "change_impact.h"

/*******************************************************************\

Function: goto_diff_parse_optionst::goto_diff_parse_optionst

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

goto_diff_parse_optionst::goto_diff_parse_optionst(int argc, const char **argv):
  parse_options_baset(GOTO_DIFF_OPTIONS, argc, argv),
  language_uit("GOTO_DIFF " CBMC_VERSION, cmdline)
{
}

/*******************************************************************\

Function: goto_diff_parse_optionst::goto_diff_parse_optionst

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

::goto_diff_parse_optionst::goto_diff_parse_optionst(
  int argc,
  const char **argv,
  const std::string &extra_options):
  parse_options_baset(GOTO_DIFF_OPTIONS+extra_options, argc, argv),
  language_uit("GOTO_DIFF " CBMC_VERSION, cmdline)
{
}

/*******************************************************************\

Function: goto_diff_parse_optionst::eval_verbosity

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_diff_parse_optionst::eval_verbosity()
{
  // this is our default verbosity
  unsigned int v=messaget::M_STATISTICS;

  if(cmdline.isset("verbosity"))
  {
    v=unsafe_string2unsigned(cmdline.get_value("verbosity"));
    if(v>10) v=10;
  }

  ui_message_handler.set_verbosity(v);
}

/*******************************************************************\

Function: goto_diff_parse_optionst::get_command_line_options

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_diff_parse_optionst::get_command_line_options(optionst &options)
{
  if(config.set(cmdline))
  {
    usage_error();
    exit(1);
  }

  if(cmdline.isset("program-only"))
    options.set_option("program-only", true);

  if(cmdline.isset("show-vcc"))
    options.set_option("show-vcc", true);

  if(cmdline.isset("cover"))
    options.set_option("cover", cmdline.get_value("cover"));

  if(cmdline.isset("mm"))
    options.set_option("mm", cmdline.get_value("mm"));

  if(cmdline.isset("c89"))
    config.ansi_c.set_c89();

  if(cmdline.isset("c99"))
    config.ansi_c.set_c99();

  if(cmdline.isset("c11"))
    config.ansi_c.set_c11();

  if(cmdline.isset("cpp98"))
    config.cpp.set_cpp98();

  if(cmdline.isset("cpp03"))
    config.cpp.set_cpp03();

  if(cmdline.isset("cpp11"))
    config.cpp.set_cpp11();

  if(cmdline.isset("no-simplify"))
    options.set_option("simplify", false);
  else
    options.set_option("simplify", true);

  if(cmdline.isset("all-claims") || // will go away
     cmdline.isset("all-properties")) // use this one
    options.set_option("all-properties", true);
  else
    options.set_option("all-properties", false);

  if(cmdline.isset("unwind"))
    options.set_option("unwind", cmdline.get_value("unwind"));

  if(cmdline.isset("depth"))
    options.set_option("depth", cmdline.get_value("depth"));

  if(cmdline.isset("debug-level"))
    options.set_option("debug-level", cmdline.get_value("debug-level"));

  if(cmdline.isset("slice-by-trace"))
    options.set_option("slice-by-trace", cmdline.get_value("slice-by-trace"));

  if(cmdline.isset("unwindset"))
    options.set_option("unwindset", cmdline.get_value("unwindset"));

  // constant propagation
  if(cmdline.isset("no-propagation"))
    options.set_option("propagation", false);
  else
    options.set_option("propagation", true);

  // check array bounds
  if(cmdline.isset("bounds-check"))
    options.set_option("bounds-check", true);
  else
    options.set_option("bounds-check", false);

  // check division by zero
  if(cmdline.isset("div-by-zero-check"))
    options.set_option("div-by-zero-check", true);
  else
    options.set_option("div-by-zero-check", false);

  // check overflow/underflow
  if(cmdline.isset("signed-overflow-check"))
    options.set_option("signed-overflow-check", true);
  else
    options.set_option("signed-overflow-check", false);

  // check overflow/underflow
  if(cmdline.isset("unsigned-overflow-check"))
    options.set_option("unsigned-overflow-check", true);
  else
    options.set_option("unsigned-overflow-check", false);

  // check overflow/underflow
  if(cmdline.isset("float-overflow-check"))
    options.set_option("float-overflow-check", true);
  else
    options.set_option("float-overflow-check", false);

  // check for NaN (not a number)
  if(cmdline.isset("nan-check"))
    options.set_option("nan-check", true);
  else
    options.set_option("nan-check", false);

  // check pointers
  if(cmdline.isset("pointer-check"))
    options.set_option("pointer-check", true);
  else
    options.set_option("pointer-check", false);

  // check for memory leaks
  if(cmdline.isset("memory-leak-check"))
    options.set_option("memory-leak-check", true);
  else
    options.set_option("memory-leak-check", false);

  // check assertions
  if(cmdline.isset("no-assertions"))
    options.set_option("assertions", false);
  else
    options.set_option("assertions", true);

  // use assumptions
  if(cmdline.isset("no-assumptions"))
    options.set_option("assumptions", false);
  else
    options.set_option("assumptions", true);

  // magic error label
  if(cmdline.isset("error-label"))
    options.set_option("error-label", cmdline.get_values("error-label"));

  // generate unwinding assertions
  if(cmdline.isset("cover"))
    options.set_option("unwinding-assertions", false);
  else
    options.set_option("unwinding-assertions",
      cmdline.isset("unwinding-assertions"));

  // generate unwinding assumptions otherwise
  options.set_option("partial-loops",
   cmdline.isset("partial-loops"));

  if(options.get_bool_option("partial-loops") &&
     options.get_bool_option("unwinding-assertions"))
  {
    error() << "--partial-loops and --unwinding-assertions must not be given together" << eom;
    exit(1);
  }
}

/*******************************************************************\

Function: goto_diff_parse_optionst::doit

  Inputs:

 Outputs:

 Purpose: invoke main modules

\*******************************************************************/

int goto_diff_parse_optionst::doit()
{
  if(cmdline.isset("version"))
  {
    std::cout << CBMC_VERSION << std::endl;
    return 0;
  }

  //
  // command line options
  //

  optionst options;
  get_command_line_options(options);
  eval_verbosity();

  //
  // Print a banner
  //
  status() << "GOTO_DIFF version " CBMC_VERSION " "
           << sizeof(void *)*8 << "-bit "
           << config.this_architecture() << " "
           << config.this_operating_system() << eom;

  register_languages();

  goto_modelt goto_model1, goto_model2;

  int get_goto_programs_ret=
    get_goto_programs(options, goto_model1, goto_model2);

  if(get_goto_programs_ret!=-1)
    return get_goto_programs_ret;

  if(cmdline.isset("show-goto-functions"))
  {
    //ENHANCE: make UI specific
    std::cout << "*******************************************************\n";
    namespacet ns1(goto_model1.symbol_table);
    goto_model1.goto_functions.output(ns1, std::cout);
    std::cout << "*******************************************************\n";
    namespacet ns2(goto_model1.symbol_table);
    goto_model2.goto_functions.output(ns2, std::cout);
    return 0;
  }

  if(cmdline.isset("change-impact"))
  {
    change_impact(goto_model1, goto_model2);
    return 0;
  }

  if(cmdline.isset("unified") ||
     cmdline.isset('u'))
  {
    unified_difft u(goto_model1, goto_model2);
    u();
    u.output(std::cout);

    return 0;
  }

  std::unique_ptr<goto_difft> goto_diff;
  goto_diff = std::unique_ptr<goto_difft>(
    new syntactic_difft(goto_model1, goto_model2,get_message_handler()));
  goto_diff->set_ui(get_ui());

  (*goto_diff)();

  goto_diff->output_functions(std::cout);

  return 0;
}

/*******************************************************************\

Function: goto_diff_parse_optionst::get_goto_programs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int goto_diff_parse_optionst::get_goto_programs(
  const optionst &options,
  goto_modelt &goto_model1,
  goto_modelt &goto_model2)
{
  if(cmdline.args.size()!=2)
  {
    error() << "Please provide two programs to compare" << eom;
    return 6;
  }

  status() << "Reading GOTO program from `" << cmdline.args[0] << "'" << eom;

  if(read_goto_binary(cmdline.args[0],
                      goto_model1.symbol_table, goto_model1.goto_functions,
                      get_message_handler()))
    throw 0;

  status() << "Reading GOTO program from `" << cmdline.args[1] << "'" << eom;

  if(read_goto_binary(cmdline.args[1],
                      goto_model2.symbol_table, goto_model2.goto_functions,
                      get_message_handler()))
    throw 0;

  config.set(cmdline);
  config.set_from_symbol_table(goto_model2.symbol_table);

  return -1; // no error, continue
}

/*******************************************************************\

Function: goto_diff_parse_optionst::process_goto_program

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool goto_diff_parse_optionst::process_goto_program(
  const optionst &options,
  goto_modelt &goto_model)
{
  symbol_tablet &symbol_table = goto_model.symbol_table;
  goto_functionst &goto_functions = goto_model.goto_functions;

  try
  {
    namespacet ns(symbol_table);

    // Remove inline assembler; this needs to happen before
    // adding the library.
    remove_asm(symbol_table, goto_functions);

    // add the library
    status() << "Adding CPROVER library ("
             << config.ansi_c.arch << ")" << eom;
    link_to_library(symbol_table, goto_functions, ui_message_handler);

    // remove function pointers
    status() << "Function Pointer Removal" << eom;
    remove_function_pointers(symbol_table, goto_functions,
      cmdline.isset("pointer-check"));

    // do partial inlining
    status() << "Partial Inlining" << eom;
    goto_partial_inline(goto_functions, ns, ui_message_handler);

    // remove returns, gcc vectors, complex
    remove_returns(symbol_table, goto_functions);
    remove_vector(symbol_table, goto_functions);
    remove_complex(symbol_table, goto_functions);

    // add generic checks
    status() << "Generic Property Instrumentation" << eom;
    goto_check(ns, options, goto_functions);

    // add failed symbols
    // needs to be done before pointer analysis
    add_failed_symbols(symbol_table);

    // recalculate numbers, etc.
    goto_functions.update();

    // add loop ids
    goto_functions.compute_loop_numbers();

    // show it?
    if(cmdline.isset("show-loops"))
    {
      show_loop_ids(get_ui(), goto_functions);
      return true;
    }

    // show it?
    if(cmdline.isset("show-goto-functions"))
    {
      goto_functions.output(ns, std::cout);
      return true;
    }
  }

  catch(const char *e)
  {
    error() << e << eom;
    return true;
  }

  catch(const std::string e)
  {
    error() << e << eom;
    return true;
  }

  catch(int)
  {
    return true;
  }

  catch(std::bad_alloc)
  {
    error() << "Out of memory" << eom;
    return true;
  }

  return false;
}

/*******************************************************************\

Function: goto_diff_parse_optionst::help

  Inputs:

 Outputs:

 Purpose: display command line help

\*******************************************************************/

void goto_diff_parse_optionst::help()
{
  std::cout <<
    "\n"
    "* *           GOTO_DIFF " CBMC_VERSION " - Copyright (C) 2016            * *\n"
    "* *            Daniel Kroening, Peter Schrammel             * *\n"
    "* *                 kroening@kroening.com                   * *\n"
    "\n"
    "Usage:                       Purpose:\n"
    "\n"
    " goto_diff [-?] [-h] [--help]      show help\n"
    " goto_diff old new                 goto binaries to be compared\n"
    "\n"
    "Diff options:\n"
    " --show-functions             show functions (default)\n"
    " --syntactic                  do syntactic diff (default)\n"
    " -u | --unified               output unified diff\n"
    " --change-impact              output unified diff with dependencies\n"
    "\n"
    "Other options:\n"
    " --version                    show version and exit\n"
    " --json-ui                    use JSON-formatted output\n"
    "\n";
}
