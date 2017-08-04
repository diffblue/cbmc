/*******************************************************************\

Module: CBMC Command Line Option Processing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// CBMC Command Line Option Processing

#include "cbmc_parse_options.h"

#include <fstream>
#include <cstdlib> // exit()
#include <iostream>
#include <memory>

#include <util/string2int.h>
#include <util/config.h>
#include <util/language.h>
#include <util/unicode.h>
#include <util/memory_info.h>
#include <util/invariant.h>

#include <ansi-c/c_preprocess.h>

#include <goto-programs/goto_convert_functions.h>
#include <goto-programs/remove_function_pointers.h>
#include <goto-programs/remove_virtual_functions.h>
#include <goto-programs/remove_instanceof.h>
#include <goto-programs/remove_returns.h>
#include <goto-programs/remove_exceptions.h>
#include <goto-programs/remove_vector.h>
#include <goto-programs/remove_complex.h>
#include <goto-programs/remove_asm.h>
#include <goto-programs/remove_unused_functions.h>
#include <goto-programs/remove_static_init_loops.h>
#include <goto-programs/mm_io.h>
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
#include <goto-programs/replace_java_nondet.h>
#include <goto-programs/convert_nondet.h>

#include <goto-symex/rewrite_union.h>
#include <goto-symex/adjust_float_expressions.h>

#include <goto-instrument/full_slicer.h>
#include <goto-instrument/nondet_static.h>
#include <goto-instrument/cover.h>

#include <pointer-analysis/add_failed_symbols.h>

#include <langapi/mode.h>

#include "java_bytecode/java_bytecode_language.h"

#include "cbmc_solvers.h"
#include "bmc.h"
#include "version.h"
#include "xml_interface.h"

cbmc_parse_optionst::cbmc_parse_optionst(int argc, const char **argv):
  parse_options_baset(CBMC_OPTIONS, argc, argv),
  xml_interfacet(cmdline),
  language_uit(cmdline, ui_message_handler),
  ui_message_handler(cmdline, "CBMC " CBMC_VERSION)
{
}

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
    options.set_option("string-non-empty", cmdline.isset("string-non-empty"));
    options.set_option("string-printable", cmdline.isset("string-printable"));
    if(cmdline.isset("string-max-length"))
      options.set_option(
        "string-max-length", cmdline.get_value("string-max-length"));
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

  if(cmdline.isset("symex-coverage-report"))
    options.set_option(
      "symex-coverage-report",
      cmdline.get_value("symex-coverage-report"));
}

/// invoke main modules
int cbmc_parse_optionst::doit()
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

  catch(const std::string error_msg)
  {
    error() << error_msg << eom;
    return 6; // should contemplate EX_SOFTWARE from sysexits.h
  }

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

  expr_listt bmc_constraints;

  int get_goto_program_ret=
    get_goto_program(options, bmc_constraints, goto_functions);

  if(get_goto_program_ret!=-1)
    return get_goto_program_ret;

  if(cmdline.isset("show-claims") || // will go away
     cmdline.isset("show-properties")) // use this one
  {
    const namespacet ns(symbol_table);
    show_properties(ns, get_ui(), goto_functions);
    return 0; // should contemplate EX_OK from sysexits.h
  }

  if(set_properties(goto_functions))
    return 7; // should contemplate EX_USAGE from sysexits.h

  // unwinds <clinit> loops to number of enum elements
  // side effect: add this as explicit unwind to unwind set
  if(options.get_bool_option("java-unwind-enum-static"))
    remove_static_init_loops(
      symbol_table,
      goto_functions,
      options,
      ui_message_handler);

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

  // do actual BMC
  return do_bmc(bmc, goto_functions);
}

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

int cbmc_parse_optionst::get_goto_program(
  const optionst &options,
  expr_listt &bmc_constraints, // for get_modules
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
      language->get_language_options(cmdline);

      if(language==nullptr)
      {
        error() << "failed to figure out type of file `"
                <<  filename << "'" << eom;
        return 6;
      }

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
      int get_modules_ret=get_modules(bmc_constraints);
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

    status() << config.object_bits_info() << eom;
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
    ptr->get_language_options(cmdline);

    if(ptr==nullptr)
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
    link_to_library(symbol_table, goto_functions, ui_message_handler);

    if(cmdline.isset("string-abstraction"))
      string_instrumentation(
        symbol_table, get_message_handler(), goto_functions);

    // remove function pointers
    status() << "Removal of function pointers and virtual functions" << eom;
    remove_function_pointers(
      get_message_handler(),
      symbol_table,
      goto_functions,
      cmdline.isset("pointer-check"));
    // Java virtual functions -> explicit dispatch tables:
    remove_virtual_functions(symbol_table, goto_functions);
    // remove catch and throw
    remove_exceptions(symbol_table, goto_functions);
    // Similar removal of RTTI inspection:
    remove_instanceof(symbol_table, goto_functions);

    mm_io(symbol_table, goto_functions);

    // do partial inlining
    status() << "Partial Inlining" << eom;
    goto_partial_inline(goto_functions, ns, ui_message_handler);

    // remove returns, gcc vectors, complex
    remove_returns(symbol_table, goto_functions);
    remove_vector(symbol_table, goto_functions);
    remove_complex(symbol_table, goto_functions);
    rewrite_union(goto_functions, ns);

    // Similar removal of java nondet statements:
    // TODO Should really get this from java_bytecode_language somehow, but we
    // don't have an instance of that here.
    const auto max_nondet_array_length=
      cmdline.isset("java-max-input-array-length")
        ? std::stoi(cmdline.get_value("java-max-input-array-length"))
        : MAX_NONDET_ARRAY_LENGTH_DEFAULT;
    replace_java_nondet(goto_functions);
    convert_nondet(
      goto_functions,
      symbol_table,
      ui_message_handler,
      max_nondet_array_length);

    // add generic checks
    status() << "Generic Property Instrumentation" << eom;
    goto_check(ns, options, goto_functions);

    // checks don't know about adjusted float expressions
    adjust_float_expressions(goto_functions, ns);

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

    if(cmdline.isset("drop-unused-functions"))
    {
      // Entry point will have been set before and function pointers removed
      status() << "Removing unused functions" << eom;
      remove_unused_functions(goto_functions, ui_message_handler);
    }

    // remove skips such that trivial GOTOs are deleted and not considered
    // for coverage annotation:
    remove_skip(goto_functions);

    // instrument cover goals
    if(cmdline.isset("cover"))
    {
      if(instrument_cover_goals(
           cmdline,
           symbol_table,
           goto_functions,
           get_message_handler()))
        return true;
    }

    // label the assertions
    // This must be done after adding assertions and
    // before using the argument of the "property" option.
    // Do not re-label after using the property slicer because
    // this would cause the property identifiers to change.
    label_properties(goto_functions);

    // full slice?
    if(cmdline.isset("full-slice"))
    {
      status() << "Performing a full slice" << eom;
      if(cmdline.isset("property"))
        property_slicer(goto_functions, ns, cmdline.get_values("property"));
      else
        full_slicer(goto_functions, ns);
    }

    // remove any skips introduced since coverage instrumentation
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

/// invoke main modules
int cbmc_parse_optionst::do_bmc(
  bmct &bmc,
  const goto_functionst &goto_functions)
{
  bmc.set_ui(get_ui());

  int result=6;

  // do actual BMC
  switch(bmc.run(goto_functions))
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
void cbmc_parse_optionst::help()
{
  std::cout <<
    "\n"
    "* *   CBMC " CBMC_VERSION " - Copyright (C) 2001-2017 ";

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
    " --symex-coverage-report f    generate a Cobertura XML coverage report in f\n" // NOLINT(*)
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
    // NOLINTNEXTLINE(whitespace/line_length)
    " --java-max-vla-length        limit the length of user-code-created arrays\n"
    // NOLINTNEXTLINE(whitespace/line_length)
    " --java-throw-runtime-exceptions Make implicit runtime exceptions explicit"
    " --java-cp-include-files      regexp or JSON list of files to load (with '@' prefix)\n"
    " --java-unwind-enum-static    try to unwind loops in static initialization of enums\n"
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
    " --string-non-empty           add constraint that strings are non empty (experimental)\n" // NOLINT(*)
    " --string-printable           add constraint that strings are printable (experimental)\n" // NOLINT(*)
    " --string-max-length          add constraint on the length of strings (experimental)\n" // NOLINT(*)
    " --outfile filename           output formula to given file\n"
    " --arrays-uf-never            never turn arrays into uninterpreted functions\n" // NOLINT(*)
    " --arrays-uf-always           always turn arrays into uninterpreted functions\n" // NOLINT(*)
    "\n"
    "Other options:\n"
    " --version                    show version and exit\n"
    " --xml-ui                     use XML-formatted output\n"
    " --xml-interface              bi-directional XML interface\n"
    " --json-ui                    use JSON-formatted output\n"
    " --verbosity #                verbosity level\n"
    "\n";
}
