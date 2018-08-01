/*******************************************************************\

Module: CBMC Command Line Option Processing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// CBMC Command Line Option Processing

#include "ccover_parse_options.h"

#include <fstream>
#include <cstdlib> // exit()
#include <iostream>
#include <memory>

#include <util/config.h>
#include <util/exit_codes.h>
#include <util/invariant.h>
#include <util/string2int.h>
#include <util/unicode.h>
#include <util/version.h>

#include <langapi/language.h>
#include <langapi/mode.h>

#include <ansi-c/c_preprocess.h>
#include <ansi-c/ansi_c_language.h>
#include <ansi-c/cprover_library.h>

#include <cpp/cpp_language.h>
#include <cpp/cprover_library.h>

#include <goto-programs/adjust_float_expressions.h>
#include <goto-programs/initialize_goto_model.h>
#include <goto-programs/instrument_preconditions.h>
#include <goto-programs/goto_convert_functions.h>
#include <goto-programs/goto_inline.h>
#include <goto-programs/link_to_library.h>
#include <goto-programs/loop_ids.h>
#include <goto-programs/mm_io.h>
#include <goto-programs/read_goto_binary.h>
#include <goto-programs/remove_function_pointers.h>
#include <goto-programs/remove_returns.h>
#include <goto-programs/remove_vector.h>
#include <goto-programs/remove_complex.h>
#include <goto-programs/remove_asm.h>
#include <goto-programs/remove_unused_functions.h>
#include <goto-programs/remove_skip.h>
#include <goto-programs/set_properties.h>
#include <goto-programs/show_goto_functions.h>
#include <goto-programs/show_symbol_table.h>
#include <goto-programs/show_properties.h>
#include <goto-programs/string_abstraction.h>
#include <goto-programs/string_instrumentation.h>

#include <goto-symex/rewrite_union.h>

#include <goto-instrument/full_slicer.h>
#include <goto-instrument/nondet_static.h>
#include <goto-instrument/cover.h>

#include <pointer-analysis/add_failed_symbols.h>

#include <langapi/mode.h>

ccover_parse_optionst::ccover_parse_optionst(int argc, const char **argv):
  parse_options_baset(CCOVER_OPTIONS, argc, argv),
  messaget(ui_message_handler),
  ui_message_handler(cmdline, std::string("ccover ") + CBMC_VERSION)
{
}

void ccover_parse_optionst::eval_verbosity()
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

void ccover_parse_optionst::get_command_line_options(optionst &options)
{
  if(config.set(cmdline))
  {
    usage_error();
    exit(CPROVER_EXIT_USAGE_ERROR);
  }

  if(cmdline.isset("paths"))
    options.set_option("paths", true);

  if(cmdline.isset("show-vcc"))
    options.set_option("show-vcc", true);

  if(cmdline.isset("cover"))
    parse_cover_options(cmdline, options);
  else // default criterion
    options.set_option("cover", std::list<std::string>({"location"}));

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

  if(cmdline.isset("trace"))
    options.set_option("trace", true);

  if(cmdline.isset("unwind"))
    options.set_option("unwind", cmdline.get_value("unwind"));

  if(cmdline.isset("depth"))
    options.set_option("depth", cmdline.get_value("depth"));

  if(cmdline.isset("debug-level"))
    options.set_option("debug-level", cmdline.get_value("debug-level"));

  if(cmdline.isset("unwindset"))
    options.set_option("unwindset", cmdline.get_value("unwindset"));

  // constant propagation
  if(cmdline.isset("no-propagation"))
    options.set_option("propagation", false);
  else
    options.set_option("propagation", true);

  // use assumptions
  if(cmdline.isset("no-assumptions"))
    options.set_option("assumptions", false);
  else
    options.set_option("assumptions", true);

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

  if(cmdline.isset("aig"))
    options.set_option("aig", true);

  if(cmdline.isset("fpa"))
    options.set_option("fpa", true);

  if(cmdline.isset("boolector"))
  {
    options.set_option("boolector", true);
    options.set_option("smt2", true);
  }

  if(cmdline.isset("mathsat"))
  {
    options.set_option("mathsat", true);
    options.set_option("smt2", true);
  }

  if(cmdline.isset("cvc4"))
  {
    options.set_option("cvc4", true);
    options.set_option("smt2", true);
  }

  if(cmdline.isset("yices"))
  {
    options.set_option("yices", true);
    options.set_option("smt2", true);
  }

  if(cmdline.isset("z3"))
  {
    options.set_option("z3", true);
    options.set_option("smt2", true);
  }

  if(cmdline.isset("beautify"))
    options.set_option("beautify", true);

  if(cmdline.isset("no-sat-preprocessor"))
    options.set_option("sat-preprocessor", false);
  else
    options.set_option("sat-preprocessor", true);

  if(cmdline.isset("outfile"))
    options.set_option("outfile", cmdline.get_value("outfile"));

  PARSE_OPTIONS_GOTO_TRACE(cmdline, options);
}

/// invoke main modules
int ccover_parse_optionst::doit()
{
  if(cmdline.isset("version"))
  {
    std::cout << CBMC_VERSION << '\n';
    return CPROVER_EXIT_SUCCESS;
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
    return CPROVER_EXIT_EXCEPTION;
  }

  catch(const std::string &error_msg)
  {
    error() << error_msg << eom;
    return CPROVER_EXIT_EXCEPTION;
  }

  eval_verbosity();

  //
  // Print a banner
  //
  status() << "CBMC version " << CBMC_VERSION << ' '
           << sizeof(void *)*8 << "-bit "
           << config.this_architecture() << ' '
           << config.this_operating_system() << eom;

  //
  // Unwinding of transition systems is done by hw-cbmc.
  //

  if(cmdline.isset("module") ||
     cmdline.isset("gen-interface"))
  {
    error() << "This version of CBMC has no support for "
               " hardware modules. Please use hw-cbmc." << eom;
    return CPROVER_EXIT_USAGE_ERROR;
  }

  register_language(new_ansi_c_language);
  register_language(new_cpp_language);

  if(cmdline.isset("test-preprocessor"))
    return test_c_preprocessor(get_message_handler())
             ? CPROVER_EXIT_PREPROCESSOR_TEST_FAILED
             : CPROVER_EXIT_SUCCESS;

  if(cmdline.isset("preprocess"))
  {
    preprocessing();
    return CPROVER_EXIT_SUCCESS;
  }

  if(cmdline.isset("show-parse-tree"))
  {
    if(cmdline.args.size()!=1 ||
       is_goto_binary(cmdline.args[0]))
    {
      error() << "Please give exactly one source file" << eom;
      return CPROVER_EXIT_INCORRECT_TASK;
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
      return CPROVER_EXIT_INCORRECT_TASK;
    }

    std::unique_ptr<languaget> language=
      get_language_from_filename(filename);

    if(language==nullptr)
    {
      error() << "failed to figure out type of file `"
              <<  filename << "'" << eom;
      return CPROVER_EXIT_INCORRECT_TASK;
    }

    language->get_language_options(cmdline);
    language->set_message_handler(get_message_handler());

    status() << "Parsing " << filename << eom;

    if(language->parse(infile, filename))
    {
      error() << "PARSING ERROR" << eom;
      return CPROVER_EXIT_INCORRECT_TASK;
    }

    language->show_parse(std::cout);
    return CPROVER_EXIT_SUCCESS;
  }

  int get_goto_program_ret=get_goto_program(options);

  if(get_goto_program_ret!=-1)
    return get_goto_program_ret;

  return ccover_bmct::do_bmc(
    options, goto_model, ui_message_handler.get_ui(), get_message_handler());
}

int ccover_parse_optionst::get_goto_program(
  const optionst &options)
{
  if(cmdline.args.empty())
  {
    error() << "Please provide a program to test" << eom;
    return CPROVER_EXIT_INCORRECT_TASK;
  }

  try
  {
    goto_model=initialize_goto_model(cmdline, get_message_handler());

    if(cmdline.isset("show-symbol-table"))
    {
      show_symbol_table(goto_model, ui_message_handler.get_ui());
      return CPROVER_EXIT_SUCCESS;
    }

    if(process_goto_program(options))
      return CPROVER_EXIT_INTERNAL_ERROR;

    // show it?
    if(cmdline.isset("show-loops"))
    {
      show_loop_ids(ui_message_handler.get_ui(), goto_model);
      return CPROVER_EXIT_SUCCESS;
    }

    // show it?
    if(
      cmdline.isset("show-goto-functions") ||
      cmdline.isset("list-goto-functions"))
    {
      show_goto_functions(
        goto_model,
        get_message_handler(),
        ui_message_handler.get_ui(),
        cmdline.isset("list-goto-functions"));
      return CPROVER_EXIT_SUCCESS;
    }

    status() << config.object_bits_info() << eom;
  }

  catch(const char *e)
  {
    error() << e << eom;
    return CPROVER_EXIT_EXCEPTION;
  }

  catch(const std::string &e)
  {
    error() << e << eom;
    return CPROVER_EXIT_EXCEPTION;
  }

  catch(int e)
  {
    error() << "Numeric exception : " << e << eom;
    return CPROVER_EXIT_EXCEPTION;
  }

  catch(const std::bad_alloc &)
  {
    error() << "Out of memory" << eom;
    return CPROVER_EXIT_INTERNAL_OUT_OF_MEMORY;
  }

  return -1; // no error, continue
}

void ccover_parse_optionst::preprocessing()
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

    std::unique_ptr<languaget> language=get_language_from_filename(filename);
    language->get_language_options(cmdline);

    if(language==nullptr)
    {
      error() << "failed to figure out type of file" << eom;
      return;
    }

    language->set_message_handler(get_message_handler());

    if(language->preprocess(infile, filename, std::cout))
      error() << "PREPROCESSING ERROR" << eom;
  }

  catch(const char *e)
  {
    error() << e << eom;
  }

  catch(const std::string &e)
  {
    error() << e << eom;
  }

  catch(int e)
  {
    error() << "Numeric exception : " << e << eom;
  }

  catch(const std::bad_alloc &)
  {
    error() << "Out of memory" << eom;
    exit(CPROVER_EXIT_INTERNAL_OUT_OF_MEMORY);
  }
}

bool ccover_parse_optionst::process_goto_program(
  const optionst &options)
{
  try
  {
    // Remove inline assembler; this needs to happen before
    // adding the library.
    remove_asm(goto_model);

    // add the library
    link_to_library(
      goto_model, get_message_handler(), cprover_cpp_library_factory);
    link_to_library(
      goto_model, get_message_handler(), cprover_c_library_factory);

    if(cmdline.isset("string-abstraction"))
      string_instrumentation(goto_model, get_message_handler());

    // remove function pointers
    status() << "Removal of function pointers and virtual functions" << eom;
    remove_function_pointers(
      get_message_handler(),
      goto_model,
      cmdline.isset("pointer-check"));

    mm_io(goto_model);

    // remove library preconditions
    remove_preconditions(goto_model);

    // remove returns, gcc vectors, complex
    remove_returns(goto_model);
    remove_vector(goto_model);
    remove_complex(goto_model);
    rewrite_union(goto_model);

    // checks don't know about adjusted float expressions
    adjust_float_expressions(goto_model);

    // ignore default/user-specified initialization
    // of variables with static lifetime
    if(cmdline.isset("nondet-static"))
    {
      status() << "Adding nondeterministic initialization "
                  "of static/global variables" << eom;
      nondet_static(goto_model);
    }

    if(cmdline.isset("string-abstraction"))
    {
      status() << "String Abstraction" << eom;
      string_abstraction(
        goto_model,
        get_message_handler());
    }

    // add failed symbols
    // needs to be done before pointer analysis
    add_failed_symbols(goto_model.symbol_table);

    // recalculate numbers, etc.
    goto_model.goto_functions.update();

    // add loop ids
    goto_model.goto_functions.compute_loop_numbers();

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

  catch(int e)
  {
    error() << "Numeric exception : " << e << eom;
    return true;
  }

  catch(const std::bad_alloc &)
  {
    error() << "Out of memory" << eom;
    exit(CPROVER_EXIT_INTERNAL_OUT_OF_MEMORY);
    return true;
  }

  return false;
}

/// display command line help
void ccover_parse_optionst::help()
{
  // clang-format off
  std::cout << '\n' << banner_string("ccover", CBMC_VERSION) << '\n';

  std::cout <<
    "* *                     Daniel Kroening                     * *\n"
    "* *    University of Oxford Computer, Science Department    * *\n"
    "* *                 kroening@kroening.com                   * *\n"
    "\n"
    "Usage:                       Purpose:\n"
    "\n"
    " ccover [-?] [-h] [--help]    show help\n"
    " cccover file.c ...           source file names\n"
    "\n"
    "Test suite generation options:\n"
    " --cover CC                   create test-suite with coverage criterion CC\n" // NOLINT(*)
    "                              criteria supported are location, branch,\n"
    "                              condition, decision, mcdc\n"
    "                              default: location\n"
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
    " --mm MM                      memory consistency model for concurrent programs\n" // NOLINT(*)
    " --round-to-nearest           rounding towards nearest even (default)\n"
    " --round-to-plus-inf          rounding towards plus infinity\n"
    " --round-to-minus-inf         rounding towards minus infinity\n"
    " --round-to-zero              rounding towards zero\n"
    HELP_FUNCTIONS
    "\n"
    "Program instrumentation options:\n"
    " --no-assumptions             ignore user assumptions\n"
    " --drop-unused-functions      drop functions trivially unreachable from main function\n" // NOLINT(*)
    "\n"
    "Semantic transformations:\n"
    // NOLINTNEXTLINE(whitespace/line_length)
    " --nondet-static              add nondeterministic initialization of variables with static lifetime\n"
    "\n"
    "BMC options:\n"
    HELP_BMC
    "\n"
    "Solver options:\n"
    " --object-bits n              number of bits used for object addresses\n"
    " --dimacs                     generate CNF in DIMACS format\n"
    " --beautify                   beautify the counterexample (greedy heuristic)\n" // NOLINT(*)
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
  // clang-format on
}
