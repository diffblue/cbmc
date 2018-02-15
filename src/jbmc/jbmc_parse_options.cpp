/*******************************************************************\

Module: JBMC Command Line Option Processing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// JBMC Command Line Option Processing

#include "jbmc_parse_options.h"

#include <fstream>
#include <cstdlib> // exit()
#include <iostream>
#include <memory>

#include <util/string2int.h>
#include <util/config.h>
#include <util/unicode.h>
#include <util/memory_info.h>
#include <util/invariant.h>

#include <langapi/language.h>

#include <ansi-c/ansi_c_language.h>

#include <goto-programs/convert_nondet.h>
#include <goto-programs/lazy_goto_model.h>
#include <goto-programs/instrument_preconditions.h>
#include <goto-programs/goto_convert_functions.h>
#include <goto-programs/goto_inline.h>
#include <goto-programs/loop_ids.h>
#include <goto-programs/remove_virtual_functions.h>
#include <goto-programs/remove_instanceof.h>
#include <goto-programs/remove_returns.h>
#include <goto-programs/remove_exceptions.h>
#include <goto-programs/remove_asm.h>
#include <goto-programs/remove_unused_functions.h>
#include <goto-programs/remove_skip.h>
#include <goto-programs/replace_java_nondet.h>
#include <goto-programs/set_properties.h>
#include <goto-programs/show_goto_functions.h>
#include <goto-programs/show_symbol_table.h>
#include <goto-programs/show_properties.h>

#include <goto-symex/adjust_float_expressions.h>

#include <goto-instrument/full_slicer.h>
#include <goto-instrument/nondet_static.h>
#include <goto-instrument/cover.h>

#include <pointer-analysis/add_failed_symbols.h>

#include <langapi/mode.h>

#include <java_bytecode/java_bytecode_language.h>
#include <java_bytecode/java_enum_static_init_unwind_handler.h>

#include <cbmc/cbmc_solvers.h>
#include <cbmc/bmc.h>
#include <cbmc/version.h>

jbmc_parse_optionst::jbmc_parse_optionst(int argc, const char **argv):
  parse_options_baset(JBMC_OPTIONS, argc, argv),
  messaget(ui_message_handler),
  ui_message_handler(cmdline, "JBMC " CBMC_VERSION)
{
}

::jbmc_parse_optionst::jbmc_parse_optionst(
  int argc,
  const char **argv,
  const std::string &extra_options):
  parse_options_baset(JBMC_OPTIONS+extra_options, argc, argv),
  messaget(ui_message_handler),
  ui_message_handler(cmdline, "JBMC " CBMC_VERSION)
{
}

void jbmc_parse_optionst::eval_verbosity()
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

void jbmc_parse_optionst::get_command_line_options(optionst &options)
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
    parse_cover_options(cmdline, options);

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
  PARSE_OPTIONS_GOTO_CHECK(cmdline, options);

  // unwind loops in java enum static initialization
  if(cmdline.isset("java-unwind-enum-static"))
    options.set_option("java-unwind-enum-static", true);

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

  if(cmdline.isset("refine-strings"))
  {
    options.set_option("refine-strings", true);
    options.set_option("string-printable", cmdline.isset("string-printable"));
    if(cmdline.isset("string-max-length"))
      options.set_option(
        "string-max-length", cmdline.get_value("string-max-length"));
  }

  if(cmdline.isset("max-node-refinement"))
    options.set_option(
      "max-node-refinement",
      cmdline.get_value("max-node-refinement"));

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
        INVARIANT(options.get_bool_option("smt2"), "smt2 set");
        options.set_option("z3", true), solver_set=true;
      }
    }
  }

  // Either have solver and standard version set, or neither.
  INVARIANT(version_set==solver_set, "solver and version set");

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

  if(cmdline.isset("symex-coverage-report"))
    options.set_option(
      "symex-coverage-report",
      cmdline.get_value("symex-coverage-report"));

  PARSE_OPTIONS_GOTO_TRACE(cmdline, options);
}

/// invoke main modules
int jbmc_parse_optionst::doit()
{
  if(cmdline.isset("version"))
  {
    std::cout << CBMC_VERSION << '\n';
    return 0; // should contemplate EX_OK from sysexits.h
  }

  //
  // command line options
  //

  optionst options;
  try
  {
    get_command_line_options(options);
  }

  catch(const char *error_msg)
  {
    error() << error_msg << eom;
    return 6; // should contemplate EX_SOFTWARE from sysexits.h
  }

  catch(const std::string &error_msg)
  {
    error() << error_msg << eom;
    return 6; // should contemplate EX_SOFTWARE from sysexits.h
  }

  eval_verbosity();

  //
  // Print a banner
  //
  status() << "JBMC version " CBMC_VERSION " "
           << sizeof(void *)*8 << "-bit "
           << config.this_architecture() << " "
           << config.this_operating_system() << eom;

  register_language(new_ansi_c_language);
  register_language(new_java_bytecode_language);

  if(cmdline.isset("show-parse-tree"))
  {
    if(cmdline.args.size()!=1)
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

    std::unique_ptr<languaget> language=
      get_language_from_filename(filename);

    if(language==nullptr)
    {
      error() << "failed to figure out type of file `"
              <<  filename << "'" << eom;
      return 6;
    }

    language->get_language_options(cmdline);
    language->set_message_handler(get_message_handler());

    status() << "Parsing " << filename << eom;

    if(language->parse(infile, filename))
    {
      error() << "PARSING ERROR" << eom;
      return 6;
    }

    language->show_parse(std::cout);
    return 0;
  }

  std::unique_ptr<goto_modelt> goto_model_ptr;
  int get_goto_program_ret=get_goto_program(goto_model_ptr, options);
  if(get_goto_program_ret!=-1)
    return get_goto_program_ret;

  goto_modelt &goto_model = *goto_model_ptr;

  if(cmdline.isset("show-properties"))
  {
    show_properties(goto_model, ui_message_handler.get_ui());
    return 0; // should contemplate EX_OK from sysexits.h
  }

  if(set_properties(goto_model))
    return 7; // should contemplate EX_USAGE from sysexits.h

  // get solver
  cbmc_solverst jbmc_solvers(
    options,
    goto_model.symbol_table,
    get_message_handler());

  jbmc_solvers.set_ui(ui_message_handler.get_ui());

  std::unique_ptr<cbmc_solverst::solvert> jbmc_solver;

  try
  {
    jbmc_solver=jbmc_solvers.get_solver();
  }

  catch(const char *error_msg)
  {
    error() << error_msg << eom;
    return 1; // should contemplate EX_SOFTWARE from sysexits.h
  }

  prop_convt &prop_conv=jbmc_solver->prop_conv();

  bmct bmc(
    options,
    goto_model.symbol_table,
    get_message_handler(),
    prop_conv);

  // unwinds <clinit> loops to number of enum elements
  if(options.get_bool_option("java-unwind-enum-static"))
  {
    bmc.add_loop_unwind_handler(
      [&goto_model]
      (const irep_idt &function_id,
       unsigned loop_number,
       unsigned unwind,
       unsigned &max_unwind) { // NOLINT (*)
        return java_enum_static_init_unwind_handler(
          function_id,
          loop_number,
          unwind,
          max_unwind,
          goto_model.symbol_table);
      });
  }

  // do actual BMC
  return do_bmc(bmc, goto_model);
}

bool jbmc_parse_optionst::set_properties(goto_modelt &goto_model)
{
  try
  {
    if(cmdline.isset("property"))
      ::set_properties(goto_model, cmdline.get_values("property"));
  }

  catch(const char *e)
  {
    error() << e << eom;
    return true;
  }

  catch(const std::string &e)
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

int jbmc_parse_optionst::get_goto_program(
  std::unique_ptr<goto_modelt> &goto_model,
  const optionst &options)
{
  if(cmdline.args.empty())
  {
    error() << "Please provide a program to verify" << eom;
    return 6;
  }

  try
  {
    lazy_goto_modelt lazy_goto_model=lazy_goto_modelt::from_handler_object(
      *this, options, get_message_handler());
    lazy_goto_model.initialize(cmdline);

    // Add failed symbols for any symbol created prior to loading any
    // particular function:
    add_failed_symbols(lazy_goto_model.symbol_table);

    status() << "Generating GOTO Program" << messaget::eom;
    lazy_goto_model.load_all_functions();

    // Show the symbol table before process_goto_functions mangles return
    // values, etc
    if(cmdline.isset("show-symbol-table"))
    {
      show_symbol_table(
        lazy_goto_model.symbol_table, ui_message_handler.get_ui());
      return 0;
    }

    // Move the model out of the local lazy_goto_model
    // and into the caller's goto_model
    goto_model=lazy_goto_modelt::process_whole_model_and_freeze(
      std::move(lazy_goto_model));
    if(goto_model == nullptr)
      return 6;

    // show it?
    if(cmdline.isset("show-loops"))
    {
      show_loop_ids(ui_message_handler.get_ui(), *goto_model);
      return 0;
    }

    // show it?
    if(
      cmdline.isset("show-goto-functions") ||
      cmdline.isset("list-goto-functions"))
    {
      show_goto_functions(
        *goto_model,
        get_message_handler(),
        ui_message_handler.get_ui(),
        cmdline.isset("list-goto-functions"));
      return 0;
    }

    status() << config.object_bits_info() << eom;
  }

  catch(const char *e)
  {
    error() << e << eom;
    return 6;
  }

  catch(const std::string &e)
  {
    error() << e << eom;
    return 6;
  }

  catch(int)
  {
    return 6;
  }

  catch(const std::bad_alloc &)
  {
    error() << "Out of memory" << eom;
    return 6;
  }

  return -1; // no error, continue
}

void jbmc_parse_optionst::process_goto_function(
  goto_model_functiont &function,
  const can_produce_functiont &available_functions,
  const optionst &options)
{
  journalling_symbol_tablet &symbol_table = function.get_symbol_table();
  namespacet ns(symbol_table);
  goto_functionst::goto_functiont &goto_function = function.get_goto_function();
  try
  {
    // Removal of RTTI inspection:
    remove_instanceof(goto_function, symbol_table);
    // Java virtual functions -> explicit dispatch tables:
    remove_virtual_functions(function);

    auto function_is_stub =
      [&symbol_table, &available_functions](const irep_idt &id) { // NOLINT(*)
        return symbol_table.lookup_ref(id).value.is_nil() &&
               !available_functions.can_produce_function(id);
      };

    remove_returns(function, function_is_stub);

    replace_java_nondet(function);

    // Similar removal of java nondet statements:
    // TODO Should really get this from java_bytecode_language somehow, but we
    // don't have an instance of that here.
    object_factory_parameterst factory_params;
    factory_params.max_nondet_array_length=
      cmdline.isset("java-max-input-array-length")
        ? std::stoul(cmdline.get_value("java-max-input-array-length"))
        : MAX_NONDET_ARRAY_LENGTH_DEFAULT;
    factory_params.max_nondet_string_length=
      cmdline.isset("string-max-input-length")
        ? std::stoul(cmdline.get_value("string-max-input-length"))
        : MAX_NONDET_STRING_LENGTH;
    factory_params.max_nondet_tree_depth=
      cmdline.isset("java-max-input-tree-depth")
        ? std::stoul(cmdline.get_value("java-max-input-tree-depth"))
        : MAX_NONDET_TREE_DEPTH;

    convert_nondet(
      function,
      get_message_handler(),
      factory_params);

    // add generic checks
    goto_check(ns, options, ID_java, function.get_goto_function());

    // checks don't know about adjusted float expressions
    adjust_float_expressions(goto_function, ns);

    // add failed symbols for anything created relating to this particular
    // function (note this means subseqent passes mustn't create more!):
    journalling_symbol_tablet::changesett new_symbols =
      symbol_table.get_inserted();
    for(const irep_idt &new_symbol_name : new_symbols)
    {
      add_failed_symbol_if_needed(
        symbol_table.lookup_ref(new_symbol_name),
        symbol_table);
    }

    // update the function member in each instruction
    function.update_instructions_function();
  }

  catch(const char *e)
  {
    error() << e << eom;
    throw;
  }

  catch(const std::string &e)
  {
    error() << e << eom;
    throw;
  }

  catch(const std::bad_alloc &)
  {
    error() << "Out of memory" << eom;
    throw;
  }
}

bool jbmc_parse_optionst::process_goto_functions(
  goto_modelt &goto_model,
  const optionst &options)
{
  try
  {
    status() << "Running GOTO functions transformation passes" << eom;
    // remove catch and throw (introduces instanceof but request it is removed)
    remove_exceptions(
      goto_model, remove_exceptions_typest::REMOVE_ADDED_INSTANCEOF);

    // instrument library preconditions
    instrument_preconditions(goto_model);

    // ignore default/user-specified initialization
    // of variables with static lifetime
    if(cmdline.isset("nondet-static"))
    {
      status() << "Adding nondeterministic initialization "
                  "of static/global variables" << eom;
      nondet_static(goto_model);
    }

    // recalculate numbers, etc.
    goto_model.goto_functions.update();

    if(cmdline.isset("drop-unused-functions"))
    {
      // Entry point will have been set before and function pointers removed
      status() << "Removing unused functions" << eom;
      remove_unused_functions(goto_model, get_message_handler());
    }

    // remove skips such that trivial GOTOs are deleted and not considered
    // for coverage annotation:
    remove_skip(goto_model);

    // instrument cover goals
    if(cmdline.isset("cover"))
    {
      if(instrument_cover_goals(options, goto_model, get_message_handler()))
        return true;
    }

    // label the assertions
    // This must be done after adding assertions and
    // before using the argument of the "property" option.
    // Do not re-label after using the property slicer because
    // this would cause the property identifiers to change.
    label_properties(goto_model);

    // full slice?
    if(cmdline.isset("full-slice"))
    {
      status() << "Performing a full slice" << eom;
      if(cmdline.isset("property"))
        property_slicer(goto_model, cmdline.get_values("property"));
      else
        full_slicer(goto_model);
    }

    // remove any skips introduced since coverage instrumentation
    remove_skip(goto_model);
    goto_model.goto_functions.update();
  }

  catch(const char *e)
  {
    error() << e << eom;
    return true;
  }

  catch(const std::string &e)
  {
    error() << e << eom;
    return true;
  }

  catch(int)
  {
    return true;
  }

  catch(const std::bad_alloc &)
  {
    error() << "Out of memory" << eom;
    return true;
  }

  return false;
}

/// invoke main modules
int jbmc_parse_optionst::do_bmc(bmct &bmc, goto_modelt &goto_model)
{
  bmc.set_ui(ui_message_handler.get_ui());

  int result=6;

  // do actual BMC
  switch(bmc.run(goto_model.goto_functions))
  {
    case safety_checkert::resultt::SAFE:
      result=0;
      break;
    case safety_checkert::resultt::UNSAFE:
      result=10;
      break;
    case safety_checkert::resultt::ERROR:
      result=6;
      break;
  }

  // let's log some more statistics
  debug() << "Memory consumption:" << messaget::endl;
  memory_info(debug());
  debug() << eom;

  return result;
}

/// display command line help
void jbmc_parse_optionst::help()
{
  std::cout <<
    "\n"
    "* *   JBMC " CBMC_VERSION " - Copyright (C) 2001-2017 ";

  std::cout << "(" << (sizeof(void *)*8) << "-bit version)";

  std::cout << "   * *\n";

  std::cout <<
    "* *              Daniel Kroening, Edmund Clarke             * *\n"
    "* * Carnegie Mellon University, Computer Science Department * *\n"
    "* *                 kroening@kroening.com                   * *\n"
    "\n"
    "Usage:                       Purpose:\n"
    "\n"
    " jbmc [-?] [-h] [--help]      show help\n"
    " jbmc class                   name of class to be checked\n"
    "\n"
    "Analysis options:\n"
    " --show-properties            show the properties, but don't run analysis\n" // NOLINT(*)
    " --symex-coverage-report f    generate a Cobertura XML coverage report in f\n" // NOLINT(*)
    " --property id                only check one specific property\n"
    " --stop-on-fail               stop analysis once a failed property is detected\n" // NOLINT(*)
    " --trace                      give a counterexample trace for failed properties\n" //NOLINT(*)
    "\n"
    HELP_FUNCTIONS
    "\n"
    "Program representations:\n"
    " --show-parse-tree            show parse tree\n"
    " --show-symbol-table          show symbol table\n"
    HELP_SHOW_GOTO_FUNCTIONS
    " --drop-unused-functions      drop functions trivially unreachable from main function\n" // NOLINT(*)
    "\n"
    "Program instrumentation options:\n"
    HELP_GOTO_CHECK
    " --no-assertions              ignore user assertions\n"
    " --no-assumptions             ignore user assumptions\n"
    " --error-label label          check that label is unreachable\n"
    " --cover CC                   create test-suite with coverage criterion CC\n" // NOLINT(*)
    " --mm MM                      memory consistency model for concurrent programs\n" // NOLINT(*)
    "\n"
    "Java Bytecode frontend options:\n"
    " --classpath dir/jar          set the classpath\n"
    " --main-class class-name      set the name of the main class\n"
    JAVA_BYTECODE_LANGUAGE_OPTIONS_HELP
    // This one is handled by jbmc_parse_options not by the Java frontend,
    // hence its presence here:
    " --java-unwind-enum-static    try to unwind loops in static initialization of enums\n" // NOLINT(*)
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
    " --object-bits n              number of bits used for object addresses\n"
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
    " --refine-strings             use string refinement (experimental)\n"
    " --string-printable           add constraint that strings are printable (experimental)\n" // NOLINT(*)
    " --string-max-length          add constraint on the length of strings\n" // NOLINT(*)
    " --string-max-input-length    add constraint on the length of input strings\n" // NOLINT(*)
    " --outfile filename           output formula to given file\n"
    " --arrays-uf-never            never turn arrays into uninterpreted functions\n" // NOLINT(*)
    " --arrays-uf-always           always turn arrays into uninterpreted functions\n" // NOLINT(*)
    "\n"
    "Other options:\n"
    " --version                    show version and exit\n"
    " --xml-ui                     use XML-formatted output\n"
    " --json-ui                    use JSON-formatted output\n"
    HELP_GOTO_TRACE
    " --verbosity #                verbosity level\n"
    HELP_TIMESTAMP
    "\n";
}
