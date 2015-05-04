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
#include <util/i2string.h>

#include <ansi-c/c_preprocess.h>

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
  language_uit("CBMC " CBMC_VERSION, cmdline)
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
  language_uit("CBMC " CBMC_VERSION, cmdline)
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
    if(v>10) v=10;
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
    exit(1);
  }

  if(cmdline.isset("program-only"))
    options.set_option("program-only", true);

  if(cmdline.isset("show-vcc"))
    options.set_option("show-vcc", true);

  if(cmdline.isset("cover-assertions"))
    options.set_option("cover-assertions", true);

  if(cmdline.isset("mm"))
    options.set_option("mm", cmdline.get_value("mm"));

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
  if(cmdline.isset("cover-assertions"))
    options.set_option("unwinding-assertions", false);
  else
    options.set_option("unwinding-assertions",
      !cmdline.isset("no-unwinding-assertions"));

  // generate unwinding assumptions otherwise
  options.set_option("partial-loops",
   cmdline.isset("partial-loops"));

  // remove unused equations
  options.set_option("slice-formula",
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

  if(cmdline.isset("refine"))
    options.set_option("refine", true);

  if(cmdline.isset("max-node-refinement"))
    options.set_option("max-node-refinement", cmdline.get_value("max-node-refinement"));

  if(cmdline.isset("aig"))
    options.set_option("aig", true);

  // SMT Options
  bool version_set = false;

  if(cmdline.isset("smt1"))
  {
    options.set_option("smt1", true);
    options.set_option("smt2", false);
    version_set = true;
  }

  if(cmdline.isset("smt2"))
  {
    options.set_option("smt1", false);// If both are given, smt2 takes precedence
    options.set_option("smt2", true);
    version_set = true;
  }

  if(cmdline.isset("fpa"))
    options.set_option("fpa", true);


  bool solver_set = false;

  if(cmdline.isset("boolector"))
  {
    options.set_option("boolector", true), solver_set = true;
    if(!version_set)
      options.set_option("smt2", true), version_set = true;
  }

  if(cmdline.isset("mathsat"))
  {
    options.set_option("mathsat", true), solver_set = true;
    if(!version_set)
      options.set_option("smt2", true), version_set = true;
  }

  if(cmdline.isset("cvc3"))
  {
    options.set_option("cvc3", true), solver_set = true;
    if(!version_set)
      options.set_option("smt1", true), version_set = true;
  }

  if(cmdline.isset("cvc4"))
  {
    options.set_option("cvc4", true), solver_set = true;
    if(!version_set)
      options.set_option("smt2", true), version_set = true;
  }

  if(cmdline.isset("yices"))
  {
    options.set_option("yices", true), solver_set = true;
    if(!version_set)
      options.set_option("smt2", true), version_set = true;
  }

  if(cmdline.isset("z3"))
  {
    options.set_option("z3", true), solver_set = true;
    if(!version_set)
      options.set_option("smt2", true), version_set = true;
  }

  if(cmdline.isset("opensmt"))
  {
    options.set_option("opensmt", true), solver_set = true;
    if(!version_set)
      options.set_option("smt1", true), version_set = true;
  }

  if(version_set && !solver_set)
  {
    if(cmdline.isset("outfile"))
    {
      // outfile and no solver should give standard compliant SMT-LIB
      options.set_option("generic", true), solver_set = true;
    }
    else
    {
      if(options.get_bool_option("smt1"))
      {
	options.set_option("boolector", true), solver_set = true;
      }
      else
      {
	assert(options.get_bool_option("smt2"));
	options.set_option("mathsat", true), solver_set = true;
      }
    }
  }
  // Either have solver and standard version set, or neither.
  assert(version_set == solver_set);

  if(cmdline.isset("beautify"))
    options.set_option("beautify", true);

  if(cmdline.isset("no-sat-preprocessor"))
    options.set_option("sat-preprocessor", false);
  else
    options.set_option("sat-preprocessor", true);

  options.set_option("pretty-names", 
                     !cmdline.isset("no-pretty-names"));

  if(cmdline.isset("outfile"))
    options.set_option("outfile", cmdline.get_value("outfile"));

  if(cmdline.isset("graphml-cex"))
    options.set_option("graphml-cex", cmdline.get_value("graphml-cex"));
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
    return 1;
  }
  
  register_languages();
  
  if(cmdline.isset("test-preprocessor"))
    return test_c_preprocessor(ui_message_handler)?8:0;
  
  if(cmdline.isset("preprocess"))
  {
    preprocessing();
    return 0;
  }

  goto_functionst goto_functions;
  bmct bmc(options, symbol_table, ui_message_handler);

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
    return 0;
  }

  if(cmdline.isset("show-reachable-properties")) // may replace --show-properties
  {
    const namespacet ns(symbol_table);
    
    // Entry point will have been set before and function pointers removed
    status() << "Removing Unused Functions" << eom;
    remove_unused_functions(goto_functions, ui_message_handler);
    
    show_properties(ns, get_ui(), goto_functions);
    return 0;
  }

  if(set_properties(goto_functions))
    return 7;

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
    if(cmdline.args.size()==1 &&
       is_goto_binary(cmdline.args[0]))
    {
      status() << "Reading GOTO program from file" << eom;

      if(read_goto_binary(cmdline.args[0],
           symbol_table, goto_functions, get_message_handler()))
        return 6;
        
      config.ansi_c.set_from_symbol_table(symbol_table);

      if(cmdline.isset("show-symbol-table"))
      {
        show_symbol_table();
        return 0;
      }
      
      irep_idt entry_point=goto_functions.entry_point();
      
      if(symbol_table.symbols.find(entry_point)==symbol_table.symbols.end())
      {
        error() << "The goto binary has no entry point; please complete linking" << eom;
        return 6;
      }
    }
    else if(cmdline.isset("show-parse-tree"))
    {
      if(cmdline.args.size()!=1)
      {
        error() << "Please give one source file only" << eom;
        return 6;
      }
      
      std::string filename=cmdline.args[0];
      
      #ifdef _MSC_VER
      std::ifstream infile(widen(filename).c_str());
      #else
      std::ifstream infile(filename.c_str());
      #endif
                
      if(!infile)
      {
        error() << "failed to open input file `" << filename << "'" << eom;
        return 6;
      }
                              
      languaget *language=get_language_from_filename(filename);
      
      if(language==NULL)
      {
        error() << "failed to figure out type of file `" <<  filename << "'" << eom;
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
    else
    {
      if(parse()) return 6;
      if(typecheck()) return 6;
      int get_modules_ret=get_modules(bmc);
      if(get_modules_ret!=-1) return get_modules_ret;
      if(final()) return 6;

      // we no longer need any parse trees or language files
      clear_parse();

      if(cmdline.isset("show-symbol-table"))
      {
        show_symbol_table();
        return 0;
      }

      irep_idt entry_point=goto_functions.entry_point();
      
      if(symbol_table.symbols.find(entry_point)==symbol_table.symbols.end())
      {
        error() << "No entry point; please provide a main function" << eom;
        return 6;
      }

      status() << "Generating GOTO Program" << eom;

      goto_convert(symbol_table, goto_functions, ui_message_handler);
    }

    if(process_goto_program(options, goto_functions))
      return 6;
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

    std::ifstream infile(filename.c_str());

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

    std::auto_ptr<languaget> language(ptr);
  
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
    status() << "Adding CPROVER library" << eom;
    link_to_library(symbol_table, goto_functions, ui_message_handler);

    if(cmdline.isset("string-abstraction"))
      string_instrumentation(
        symbol_table, get_message_handler(), goto_functions);

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
    
    if(cmdline.isset("string-abstraction"))
    {
      status() << "String Abstraction" << eom;
      string_abstraction(symbol_table,
        get_message_handler(), goto_functions);
    }

    // add failed symbols
    // needs to be done before pointer analysis
    add_failed_symbols(symbol_table);
    
    // recalculate numbers, etc.
    goto_functions.update();

    // add loop ids
    goto_functions.compute_loop_numbers();
    
    // if we aim to cover, replace
    // all assertions by false to prevent simplification
    
    if(cmdline.isset("cover-assertions"))
      make_assertions_false(goto_functions);

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
  bool result=bmc.run(goto_functions);

  // let's log some more statistics
  debug() << "Memory consumption:" << messaget::endl;
  memory_info(debug());
  debug() << eom;

  // We return '0' if the property holds,
  // and '10' if it is violated.
  return result?10:0;
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
    "* *   CBMC " CBMC_VERSION " - Copyright (C) 2001-2014 ";
    
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
    "Frontend options:\n"
    " -I path                      set include path (C/C++)\n"
    " -D macro                     define preprocessor macro (C/C++)\n"
    " --preprocess                 stop after preprocessing\n"
    " --16, --32, --64             set width of int\n"
    " --LP64, --ILP64, --LLP64,\n"
    "   --ILP32, --LP32            set width of int, long and pointers\n"
    " --little-endian              allow little-endian word-byte conversions\n"
    " --big-endian                 allow big-endian word-byte conversions\n"
    " --unsigned-char              make \"char\" unsigned by default\n"
    " --show-parse-tree            show parse tree\n"
    " --show-symbol-table          show symbol table\n"
    " --show-goto-functions        show goto program\n"
    " --mm model                   set memory model (default: sc)\n"
    " --arch                       set architecture (default: "
                                   << configt::this_architecture() << ")\n"
    " --os                         set operating system (default: "
                                   << configt::this_operating_system() << ")\n"
    #ifdef _WIN32
    " --gcc                        use GCC as preprocessor\n"
    #endif
    " --no-arch                    don't set up an architecture\n"
    " --no-library                 disable built-in abstract C library\n"
    " --round-to-nearest           IEEE floating point rounding mode (default)\n"
    " --round-to-plus-inf          IEEE floating point rounding mode\n"
    " --round-to-minus-inf         IEEE floating point rounding mode\n"
    " --round-to-zero              IEEE floating point rounding mode\n"
    "\n"
    "Program instrumentation options:\n"
    " --bounds-check               enable array bounds checks\n"
    " --div-by-zero-check          enable division by zero checks\n"
    " --pointer-check              enable pointer checks\n"
    " --memory-leak-check          enable memory leak checks\n"
    " --signed-overflow-check      enable arithmetic over- and underflow checks\n"
    " --unsigned-overflow-check    enable arithmetic over- and underflow checks\n"
    " --float-overflow-check       check floating-point for +/-Inf\n"
    " --nan-check                  check floating-point for NaN\n"
    " --all-properties             report status of all properties\n"
    " --show-properties            show the properties\n"
    " --show-loops                 show the loops in the program\n"
    " --no-assertions              ignore user assertions\n"
    " --no-assumptions             ignore user assumptions\n"
    " --error-label label          check that label is unreachable\n"
    " --cover-assertions           check which assertions are reachable\n"
    " --mm MM                      memory consistency model for concurrent programs\n"
    "\n"
    "BMC options:\n"
    " --function name              set main function name\n"
    " --property id                only check one specific property\n"
    " --program-only               only show program expression\n"
    " --depth nr                   limit search depth\n"
    " --unwind nr                  unwind nr times\n"
    " --unwindset L:B,...          unwind loop L with a bound of B\n"
    "                              (use --show-loops to get the loop IDs)\n"
    " --show-vcc                   show the verification conditions\n"
    " --slice-formula              remove assignments unrelated to property\n"
    " --no-unwinding-assertions    do not generate unwinding assertions\n"
    " --partial-loops              permit paths with partial loops\n"
    " --no-pretty-names            do not simplify identifiers\n"
    " --graphml-cex filename       write the counterexample in GraphML format to filename\n"
    "\n"
    "Backend options:\n"
    " --dimacs                     generate CNF in DIMACS format\n"
    " --beautify                   beautify the counterexample (greedy heuristic)\n"
    " --smt1                       output subgoals in SMT1 syntax (experimental)\n"
    " --smt2                       output subgoals in SMT2 syntax (experimental)\n"
    " --boolector                  use Boolector (experimental)\n"
    " --mathsat                    use MathSAT (experimental)\n"
    " --cvc3                       use CVC3 (experimental)\n"
    " --cvc4                       use CVC4 (experimental)\n"
    " --yices                      use Yices (experimental)\n"
    " --z3                         use Z3 (experimental)\n"
    " --opensmt                    use OpenSMT (experimental)\n"
    " --refine                     use refinement procedure (experimental)\n"
    " --outfile filename           output formula to given file\n"
    " --arrays-uf-never            never turn arrays into uninterpreted functions\n"
    " --arrays-uf-always           always turn arrays into uninterpreted functions\n"
    "\n"
    "Other options:\n"
    " --version                    show version and exit\n"
    " --xml-ui                     use XML-formatted output\n"
    " --xml-interface              bi-directional XML interface\n"
    "\n";
}
