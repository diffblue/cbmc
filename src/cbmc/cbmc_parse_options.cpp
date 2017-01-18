/*******************************************************************\

Module: CBMC Command Line Option Processing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <fstream>
#include <cstdlib> // exit()
#include <iostream>
#include <memory>

#include <util/string2int.h>
#include <util/config.h>
#include <util/expr_util.h>
#include <util/language.h>
#include <util/unicode.h>
#include <util/memory_info.h>

#include <ansi-c/c_preprocess.h>

#include <goto-programs/goto_convert_functions.h>
#include <goto-programs/remove_function_pointers.h>
#include <goto-programs/remove_virtual_functions.h>
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
#include <goto-programs/remove_skip.h>
#include <goto-programs/show_goto_functions.h>

#include <goto-instrument/full_slicer.h>
#include <goto-instrument/nondet_static.h>
#include <goto-instrument/cover.h>

#include <pointer-analysis/add_failed_symbols.h>

#include <langapi/mode.h>

#include "cbmc_solvers.h"
#include "cbmc_parse_options.h"
#include "bmc.h"
#include "version.h"
#include "xml_interface.h"

/*******************************************************************\

Function: cbmc_parse_optionst::cbmc_parse_optionst

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

cbmc_parse_optionst::cbmc_parse_optionst(int argc, const char **argv):
  parse_options_baset(CBMC_OPTIONS, argc, argv),
  xml_interfacet(cmdline),
  language_uit(cmdline, ui_message_handler),
  ui_message_handler(cmdline, "CBMC " CBMC_VERSION)
{
}

/*******************************************************************\

Function: cbmc_parse_optionst::cbmc_parse_optionst

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

::cbmc_parse_optionst::cbmc_parse_optionst(
  int argc,
  const char **argv,
  const std::string &extra_options):
  parse_options_baset(CBMC_OPTIONS+extra_options, argc, argv),
  xml_interfacet(cmdline),
  language_uit(cmdline, ui_message_handler),
  ui_message_handler(cmdline, "CBMC " CBMC_VERSION)
{
}

/*******************************************************************\

Function: cbmc_parse_optionst::eval_verbosity

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cbmc_parse_optionst::eval_verbosity()
{
  // this is our default verbosity
  unsigned int v=messaget::M_STATISTICS;

  if(cmdline.isset("verbosity"))
  {
    v=unsafe_string2unsigned(cmdline.get_value("verbosity"));
    if(v>10)
      v=10;
  }

  ui_message_handler.set_verbosity(v);
}

/*******************************************************************\

Function: cbmc_parse_optionst::get_command_line_options

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cbmc_parse_optionst::get_command_line_options(optionst &options)
{
  if(config.set(cmdline))
  {
    usage_error();
    exit(1); // should contemplate EX_USAGE from sysexits.h
  }

  if(cmdline.isset("program-only"))
    options.set_option("program-only", true);

  if(cmdline.isset("show-vcc"))
    options.set_option("show-vcc", true);

  if(cmdline.isset("cover"))
    options.set_option("cover", cmdline.get_values("cover"));

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

  if(cmdline.isset("stop-on-fail") ||
     cmdline.isset("dimacs") ||
     cmdline.isset("outfile"))
    options.set_option("stop-on-fail", true);
  else
    options.set_option("stop-on-fail", false);

  if(cmdline.isset("trace") ||
     cmdline.isset("stop-on-fail"))
    options.set_option("trace", true);

  if(cmdline.isset("localize-faults"))
    options.set_option("localize-faults", true);
  if(cmdline.isset("localize-faults-method"))
  {
    options.set_option(
      "localize-faults-method",
      cmdline.get_value("localize-faults-method"));
  }

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

  // all checks supported by goto_check
  GOTO_CHECK_PARSE_OPTIONS(cmdline, options);

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
  {
    options.set_option(
      "unwinding-assertions",
      cmdline.isset("unwinding-assertions"));
  }

  // generate unwinding assumptions otherwise
  options.set_option(
    "partial-loops",
    cmdline.isset("partial-loops"));

  if(options.get_bool_option("partial-loops") &&
     options.get_bool_option("unwinding-assertions"))
  {
    error() << "--partial-loops and --unwinding-assertions "
            << "must not be given together" << eom;
    exit(1); // should contemplate EX_USAGE from sysexits.h
  }

  // remove unused equations
  options.set_option(
    "slice-formula",
    cmdline.isset("slice-formula"));

  // simplify if conditions and branches
  if(cmdline.isset("no-simplify-if"))
    options.set_option("simplify-if", false);
  else
    options.set_option("simplify-if", true);

  if(cmdline.isset("arrays-uf-always"))
    options.set_option("arrays-uf", "always");
  else if(cmdline.isset("arrays-uf-never"))
    options.set_option("arrays-uf", "never");
  else
    options.set_option("arrays-uf", "auto");

  if(cmdline.isset("dimacs"))
    options.set_option("dimacs", true);

  if(cmdline.isset("refine-arrays"))
  {
    options.set_option("refine", true);
    options.set_option("refine-arrays", true);
  }

  if(cmdline.isset("refine-arithmetic"))
  {
    options.set_option("refine", true);
    options.set_option("refine-arithmetic", true);
  }

  if(cmdline.isset("refine"))
  {
    options.set_option("refine", true);
    options.set_option("refine-arrays", true);
    options.set_option("refine-arithmetic", true);
  }

  if(cmdline.isset("max-node-refinement"))
    options.set_option(
      "max-node-refinement",
      cmdline.get_value("max-node-refinement"));

  if(cmdline.isset("aig"))
    options.set_option("aig", true);

  // SMT Options
  bool version_set=false;

  if(cmdline.isset("smt1"))
  {
    options.set_option("smt1", true);
    options.set_option("smt2", false);
    version_set=true;
  }

  if(cmdline.isset("smt2"))
  {
    // If both are given, smt2 takes precedence
    options.set_option("smt1", false);
    options.set_option("smt2", true);
    version_set=true;
  }

  if(cmdline.isset("fpa"))
    options.set_option("fpa", true);


  bool solver_set=false;

  if(cmdline.isset("boolector"))
  {
    options.set_option("boolector", true), solver_set=true;
    if(!version_set)
      options.set_option("smt2", true), version_set=true;
  }

  if(cmdline.isset("mathsat"))
  {
    options.set_option("mathsat", true), solver_set=true;
    if(!version_set)
      options.set_option("smt2", true), version_set=true;
  }

  if(cmdline.isset("cvc3"))
  {
    options.set_option("cvc3", true), solver_set=true;
    if(!version_set)
      options.set_option("smt1", true), version_set=true;
  }

  if(cmdline.isset("cvc4"))
  {
    options.set_option("cvc4", true), solver_set=true;
    if(!version_set)
      options.set_option("smt2", true), version_set=true;
  }

  if(cmdline.isset("yices"))
  {
    options.set_option("yices", true), solver_set=true;
    if(!version_set)
      options.set_option("smt2", true), version_set=true;
  }

  if(cmdline.isset("z3"))
  {
    options.set_option("z3", true), solver_set=true;
    if(!version_set)
      options.set_option("smt2", true), version_set=true;
  }

  if(cmdline.isset("opensmt"))
  {
    options.set_option("opensmt", true), solver_set=true;
    if(!version_set)
      options.set_option("smt1", true), version_set=true;
  }

  if(version_set && !solver_set)
  {
    if(cmdline.isset("outfile"))
    {
      // outfile and no solver should give standard compliant SMT-LIB
      options.set_option("generic", true), solver_set=true;
    }
    else
    {
      if(options.get_bool_option("smt1"))
      {
        options.set_option("boolector", true), solver_set=true;
      }
      else
      {
        assert(options.get_bool_option("smt2"));
        options.set_option("z3", true), solver_set=true;
      }
    }
  }
  // Either have solver and standard version set, or neither.
  assert(version_set==solver_set);

  if(cmdline.isset("beautify"))
    options.set_option("beautify", true);

  if(cmdline.isset("no-sat-preprocessor"))
    options.set_option("sat-preprocessor", false);
  else
    options.set_option("sat-preprocessor", true);

  options.set_option(
    "pretty-names",
    !cmdline.isset("no-pretty-names"));

  if(cmdline.isset("outfile"))
    options.set_option("outfile", cmdline.get_value("outfile"));

  if(cmdline.isset("graphml-witness"))
  {
    options.set_option("graphml-witness", cmdline.get_value("graphml-witness"));
    options.set_option("stop-on-fail", true);
    options.set_option("trace", true);
  }
}

/*******************************************************************\

Function: cbmc_parse_optionst::doit

  Inputs:

 Outputs:

 Purpose: invoke main modules

\*******************************************************************/

int cbmc_parse_optionst::doit()
{
  if(cmdline.isset("version"))
  {
    std::cout << CBMC_VERSION << std::endl;
    return 0; // should contemplate EX_OK from sysexits.h
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
  status() << "CBMC version " CBMC_VERSION " "
           << sizeof(void *)*8 << "-bit "
           << config.this_architecture() << " "
           << config.this_operating_system() << eom;

  //
  // Unwinding of transition systems is done by hw-cbmc.
  //

  if(cmdline.isset("module") ||
     cmdline.isset("gen-interface"))
  {
    error() << "This version of CBMC has no support for "
               " hardware modules. Please use hw-cbmc." << eom;
    return 1; // should contemplate EX_USAGE from sysexits.h
  }

  register_languages();

  if(cmdline.isset("test-preprocessor"))
    return test_c_preprocessor(ui_message_handler)?8:0;

  if(cmdline.isset("preprocess"))
  {
    preprocessing();
    return 0; // should contemplate EX_OK from sysexits.h
  }

  goto_functionst goto_functions;

  // get solver
  cbmc_solverst cbmc_solvers(options, symbol_table, ui_message_handler);
  cbmc_solvers.set_ui(get_ui());

  std::unique_ptr<cbmc_solverst::solvert> cbmc_solver;

  try
  {
    cbmc_solver=cbmc_solvers.get_solver();
  }

  catch(const char *error_msg)
  {
    error() << error_msg << eom;
    return 1; // should contemplate EX_SOFTWARE from sysexits.h
  }

  prop_convt &prop_conv=cbmc_solver->prop_conv();

  bmct bmc(options, symbol_table, ui_message_handler, prop_conv);

  int get_goto_program_ret=
    get_goto_program(options, bmc, goto_functions);

  if(get_goto_program_ret!=-1)
    return get_goto_program_ret;

  label_properties(goto_functions);

  if(cmdline.isset("show-claims") || // will go away
     cmdline.isset("show-properties")) // use this one
  {
    const namespacet ns(symbol_table);
    show_properties(ns, get_ui(), goto_functions);
    return 0; // should contemplate EX_OK from sysexits.h
  }

  // may replace --show-properties
  if(cmdline.isset("show-reachable-properties"))
  {
    const namespacet ns(symbol_table);

    // Entry point will have been set before and function pointers removed
    status() << "Removing Unused Functions" << eom;
    remove_unused_functions(goto_functions, ui_message_handler);

    show_properties(ns, get_ui(), goto_functions);
    return 0; // should contemplate EX_OK from sysexits.h
  }

  if(set_properties(goto_functions))
    return 7; // should contemplate EX_USAGE from sysexits.h

  // do actual BMC
  return do_bmc(bmc, goto_functions);
}

/*******************************************************************\

Function: cbmc_parse_optionst::set_properties

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool cbmc_parse_optionst::set_properties(goto_functionst &goto_functions)
{
  try
  {
    if(cmdline.isset("claim")) // will go away
      ::set_properties(goto_functions, cmdline.get_values("claim"));

    if(cmdline.isset("property")) // use this one
      ::set_properties(goto_functions, cmdline.get_values("property"));
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

  return false;
}

/*******************************************************************\

Function: cbmc_parse_optionst::get_goto_program

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int cbmc_parse_optionst::get_goto_program(
  const optionst &options,
  bmct &bmc, // for get_modules
  goto_functionst &goto_functions)
{
  if(cmdline.args.empty())
  {
    error() << "Please provide a program to verify" << eom;
    return 6;
  }

  try
  {
    if(cmdline.isset("show-parse-tree"))
    {
      if(cmdline.args.size()!=1 ||
         is_goto_binary(cmdline.args[0]))
      {
        error() << "Please give exactly one source file" << eom;
        return 6;
      }

      std::string filename=cmdline.args[0];

      #ifdef _MSC_VER
      std::ifstream infile(widen(filename));
      #else
      std::ifstream infile(filename);
      #endif

      if(!infile)
      {
        error() << "failed to open input file `"
                << filename << "'" << eom;
        return 6;
      }

      languaget *language=get_language_from_filename(filename);

      if(language==NULL)
      {
        error() << "failed to figure out type of file `"
                <<  filename << "'" << eom;
        return 6;
      }

      language->set_message_handler(get_message_handler());

      status("Parsing", filename);

      if(language->parse(infile, filename))
      {
        error() << "PARSING ERROR" << eom;
        return 6;
      }

      language->show_parse(std::cout);
      return 0;
    }

    cmdlinet::argst binaries;
    binaries.reserve(cmdline.args.size());

    for(cmdlinet::argst::iterator
        it=cmdline.args.begin();
        it!=cmdline.args.end();
        ) // no ++it
    {
      if(is_goto_binary(*it))
      {
        binaries.push_back(*it);
        it=cmdline.args.erase(it);
        continue;
      }

      ++it;
    }

    if(!cmdline.args.empty())
    {
      if(parse())
        return 6;
      if(typecheck())
        return 6;
      int get_modules_ret=get_modules(bmc);
      if(get_modules_ret!=-1)
        return get_modules_ret;
      if(binaries.empty() && final())
        return 6;

      // we no longer need any parse trees or language files
      clear_parse();
    }

    for(const auto &bin : binaries)
    {
      status() << "Reading GOTO program from file " << eom;

      if(read_object_and_link(
        bin,
        symbol_table,
        goto_functions,
        get_message_handler()))
      {
        return 6;
      }
    }

    if(!binaries.empty())
      config.set_from_symbol_table(symbol_table);

    if(cmdline.isset("show-symbol-table"))
    {
      show_symbol_table();
      return 0;
    }

    status() << "Generating GOTO Program" << eom;

    goto_convert(symbol_table, goto_functions, ui_message_handler);

    if(process_goto_program(options, goto_functions))
      return 6;

    // show it?
    if(cmdline.isset("show-loops"))
    {
      show_loop_ids(get_ui(), goto_functions);
      return 0;
    }

    // show it?
    if(cmdline.isset("show-goto-functions"))
    {
      namespacet ns(symbol_table);
      show_goto_functions(ns, get_ui(), goto_functions);
      return 0;
    }
  }

  catch(const char *e)
  {
    error() << e << eom;
    return 6;
  }

  catch(const std::string e)
  {
    error() << e << eom;
    return 6;
  }

  catch(int)
  {
    return 6;
  }

  catch(std::bad_alloc)
  {
    error() << "Out of memory" << eom;
    return 6;
  }

  return -1; // no error, continue
}

/*******************************************************************\

Function: cbmc_parse_optionst::preprocessing

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cbmc_parse_optionst::preprocessing()
{
  try
  {
    if(cmdline.args.size()!=1)
    {
      error() << "Please provide one program to preprocess" << eom;
      return;
    }

    std::string filename=cmdline.args[0];

    std::ifstream infile(filename);

    if(!infile)
    {
      error() << "failed to open input file" << eom;
      return;
    }

    languaget *ptr=get_language_from_filename(filename);

    if(ptr==NULL)
    {
      error() << "failed to figure out type of file" << eom;
      return;
    }

    ptr->set_message_handler(get_message_handler());

    std::unique_ptr<languaget> language(ptr);

    if(language->preprocess(infile, filename, std::cout))
      error() << "PREPROCESSING ERROR" << eom;
  }

  catch(const char *e)
  {
    error() << e << eom;
  }

  catch(const std::string e)
  {
    error() << e << eom;
  }

  catch(int)
  {
  }

  catch(std::bad_alloc)
  {
    error() << "Out of memory" << eom;
  }
}

/*******************************************************************\

Function: cbmc_parse_optionst::process_goto_program

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool cbmc_parse_optionst::process_goto_program(
  const optionst &options,
  goto_functionst &goto_functions)
{
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

    if(cmdline.isset("string-abstraction"))
      string_instrumentation(
        symbol_table, get_message_handler(), goto_functions);

    // remove function pointers
    status() << "Removal of function pointers and virtual functions" << eom;
    remove_function_pointers(
      symbol_table,
      goto_functions,
      cmdline.isset("pointer-check"));
    remove_virtual_functions(symbol_table, goto_functions);

    // full slice?
    if(cmdline.isset("full-slice"))
    {
      status() << "Performing a full slice" << eom;
      full_slicer(goto_functions, ns);
    }

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

    // ignore default/user-specified initialization
    // of variables with static lifetime
    if(cmdline.isset("nondet-static"))
    {
      status() << "Adding nondeterministic initialization "
                  "of static/global variables" << eom;
      nondet_static(ns, goto_functions);
    }

    if(cmdline.isset("string-abstraction"))
    {
      status() << "String Abstraction" << eom;
      string_abstraction(
        symbol_table,
        get_message_handler(),
        goto_functions);
    }

    // add failed symbols
    // needs to be done before pointer analysis
    add_failed_symbols(symbol_table);

    // recalculate numbers, etc.
    goto_functions.update();

    // add loop ids
    goto_functions.compute_loop_numbers();

    // instrument cover goals

    if(cmdline.isset("cover"))
    {
      std::list<std::string> criteria_strings=
        cmdline.get_values("cover");

      std::set<coverage_criteriont> criteria;

      for(const auto &criterion_string : criteria_strings)
      {
        coverage_criteriont c;

        if(criterion_string=="assertion" || criterion_string=="assertions")
          c=coverage_criteriont::ASSERTION;
        else if(criterion_string=="path" || criterion_string=="paths")
          c=coverage_criteriont::PATH;
        else if(criterion_string=="branch" || criterion_string=="branches")
          c=coverage_criteriont::BRANCH;
        else if(criterion_string=="location" || criterion_string=="locations")
          c=coverage_criteriont::LOCATION;
        else if(criterion_string=="decision" || criterion_string=="decisions")
          c=coverage_criteriont::DECISION;
        else if(criterion_string=="condition" || criterion_string=="conditions")
          c=coverage_criteriont::CONDITION;
        else if(criterion_string=="mcdc")
          c=coverage_criteriont::MCDC;
        else if(criterion_string=="cover")
          c=coverage_criteriont::COVER;
        else
        {
          error() << "unknown coverage criterion" << eom;
          return true;
        }

        criteria.insert(c);
      }

      status() << "Instrumenting coverage goals" << eom;

      for(const auto &criterion : criteria)
        instrument_cover_goals(symbol_table, goto_functions, criterion);

      goto_functions.update();
    }

    // remove skips
    remove_skip(goto_functions);
    goto_functions.update();
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

Function: cbmc_parse_optionst::do_bmc

  Inputs:

 Outputs:

 Purpose: invoke main modules

\*******************************************************************/

int cbmc_parse_optionst::do_bmc(
  bmct &bmc,
  const goto_functionst &goto_functions)
{
  bmc.set_ui(get_ui());

  // do actual BMC
  bool result=(bmc.run(goto_functions)==safety_checkert::SAFE);

  // let's log some more statistics
  debug() << "Memory consumption:" << messaget::endl;
  memory_info(debug());
  debug() << eom;

  // We return '0' if the property holds,
  // and '10' if it is violated.
  return result?0:10;
}

/*******************************************************************\

Function: cbmc_parse_optionst::help

  Inputs:

 Outputs:

 Purpose: display command line help

\*******************************************************************/

void cbmc_parse_optionst::help()
{
  std::cout <<
    "\n"
    "* *   CBMC " CBMC_VERSION " - Copyright (C) 2001-2016 ";

  std::cout << "(" << (sizeof(void *)*8) << "-bit version)";

  std::cout << "   * *\n";

  std::cout <<
    "* *              Daniel Kroening, Edmund Clarke             * *\n"
    "* * Carnegie Mellon University, Computer Science Department * *\n"
    "* *                 kroening@kroening.com                   * *\n"
    "* *        Protected in part by U.S. patent 7,225,417       * *\n"
    "\n"
    "Usage:                       Purpose:\n"
    "\n"
    " cbmc [-?] [-h] [--help]      show help\n"
    " cbmc file.c ...              source file names\n"
    "\n"
    "Analysis options:\n"
    " --show-properties            show the properties, but don't run analysis\n" // NOLINT(*)
    " --property id                only check one specific property\n"
    " --stop-on-fail               stop analysis once a failed property is detected\n" // NOLINT(*)
    " --trace                      give a counterexample trace for failed properties\n" //NOLINT(*)
    "\n"
    "C/C++ frontend options:\n"
    " -I path                      set include path (C/C++)\n"
    " -D macro                     define preprocessor macro (C/C++)\n"
    " --preprocess                 stop after preprocessing\n"
    " --16, --32, --64             set width of int\n"
    " --LP64, --ILP64, --LLP64,\n"
    "   --ILP32, --LP32            set width of int, long and pointers\n"
    " --little-endian              allow little-endian word-byte conversions\n"
    " --big-endian                 allow big-endian word-byte conversions\n"
    " --unsigned-char              make \"char\" unsigned by default\n"
    " --mm model                   set memory model (default: sc)\n"
    " --arch                       set architecture (default: "
                                   << configt::this_architecture() << ")\n"
    " --os                         set operating system (default: "
                                   << configt::this_operating_system() << ")\n"
    " --c89/99/11                  set C language standard (default: "
                                   << (configt::ansi_ct::default_c_standard()==
                                       configt::ansi_ct::c_standardt::C89?"c89":
                                       configt::ansi_ct::default_c_standard()==
                                       configt::ansi_ct::c_standardt::C99?"c99":
                                       configt::ansi_ct::default_c_standard()==
                                       configt::ansi_ct::c_standardt::C11?"c11":"") << ")\n" // NOLINT(*)
    " --cpp98/03/11                set C++ language standard (default: "
                                   << (configt::cppt::default_cpp_standard()==
                                       configt::cppt::cpp_standardt::CPP98?"cpp98": // NOLINT(*)
                                       configt::cppt::default_cpp_standard()==
                                       configt::cppt::cpp_standardt::CPP03?"cpp03": // NOLINT(*)
                                       configt::cppt::default_cpp_standard()==
                                       configt::cppt::cpp_standardt::CPP11?"cpp11":"") << ")\n" // NOLINT(*)
    #ifdef _WIN32
    " --gcc                        use GCC as preprocessor\n"
    #endif
    " --no-arch                    don't set up an architecture\n"
    " --no-library                 disable built-in abstract C library\n"
    " --round-to-nearest           rounding towards nearest even (default)\n"
    " --round-to-plus-inf          rounding towards plus infinity\n"
    " --round-to-minus-inf         rounding towards minus infinity\n"
    " --round-to-zero              rounding towards zero\n"
    " --function name              set main function name\n"
    "\n"
    "Program representations:\n"
    " --show-parse-tree            show parse tree\n"
    " --show-symbol-table          show symbol table\n"
    HELP_SHOW_GOTO_FUNCTIONS
    "\n"
    "Program instrumentation options:\n"
    GOTO_CHECK_HELP
    " --no-assertions              ignore user assertions\n"
    " --no-assumptions             ignore user assumptions\n"
    " --error-label label          check that label is unreachable\n"
    " --cover CC                   create test-suite with coverage criterion CC\n" // NOLINT(*)
    " --mm MM                      memory consistency model for concurrent programs\n" // NOLINT(*)
    "\n"
    "Java Bytecode frontend options:\n"
    " --classpath dir/jar          set the classpath\n"
    " --main-class class-name      set the name of the main class\n"
    "\n"
    "Semantic transformations:\n"
    " --nondet-static              add nondeterministic initialization of variables with static lifetime\n" // NOLINT(*)
    "\n"
    "BMC options:\n"
    " --program-only               only show program expression\n"
    " --show-loops                 show the loops in the program\n"
    " --depth nr                   limit search depth\n"
    " --unwind nr                  unwind nr times\n"
    " --unwindset L:B,...          unwind loop L with a bound of B\n"
    "                              (use --show-loops to get the loop IDs)\n"
    " --show-vcc                   show the verification conditions\n"
    " --slice-formula              remove assignments unrelated to property\n"
    " --unwinding-assertions       generate unwinding assertions\n"
    " --partial-loops              permit paths with partial loops\n"
    " --no-pretty-names            do not simplify identifiers\n"
    " --graphml-witness filename   write the witness in GraphML format to filename\n" // NOLINT(*)
    "\n"
    "Backend options:\n"
    " --dimacs                     generate CNF in DIMACS format\n"
    " --beautify                   beautify the counterexample (greedy heuristic)\n" // NOLINT(*)
    " --localize-faults            localize faults (experimental)\n"
    " --smt1                       use default SMT1 solver (obsolete)\n"
    " --smt2                       use default SMT2 solver (Z3)\n"
    " --boolector                  use Boolector\n"
    " --mathsat                    use MathSAT\n"
    " --cvc4                       use CVC4\n"
    " --yices                      use Yices\n"
    " --z3                         use Z3\n"
    " --refine                     use refinement procedure (experimental)\n"
    " --outfile filename           output formula to given file\n"
    " --arrays-uf-never            never turn arrays into uninterpreted functions\n" // NOLINT(*)
    " --arrays-uf-always           always turn arrays into uninterpreted functions\n" // NOLINT(*)
    "\n"
    "Other options:\n"
    " --version                    show version and exit\n"
    " --xml-ui                     use XML-formatted output\n"
    " --xml-interface              bi-directional XML interface\n"
    " --json-ui                    use JSON-formatted output\n"
    "\n";
}
