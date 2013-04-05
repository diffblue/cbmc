/*******************************************************************\

Module: Main Module 

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <fstream>
#include <iostream>
#include <memory>
#include <cstdlib>

#include <config.h>
#include <expr_util.h>
#include <language.h>

#include <goto-programs/goto_convert_functions.h>
#include <goto-programs/remove_function_pointers.h>
#include <goto-programs/goto_inline.h>
#include <goto-programs/show_claims.h>
#include <goto-programs/set_claims.h>
#include <goto-programs/read_goto_binary.h>
#include <goto-programs/interpreter.h>
#include <goto-programs/string_abstraction.h>
#include <goto-programs/string_instrumentation.h>
#include <goto-programs/loop_ids.h>
#include <goto-programs/link_to_library.h>

#include <pointer-analysis/goto_program_dereference.h>
#include <pointer-analysis/add_failed_symbols.h>

#include <analyses/goto_check.h>

#include <langapi/mode.h>

#include "parseoptions.h"
#include "bmc.h"
#include "version.h"
#include "xml_interface.h"

/*******************************************************************\

Function: cbmc_parseoptionst::cbmc_parseoptionst

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

cbmc_parseoptionst::cbmc_parseoptionst(int argc, const char **argv):
  parseoptions_baset(CBMC_OPTIONS, argc, argv),
  xml_interfacet(cmdline),
  language_uit("CBMC " CBMC_VERSION, cmdline)
{
}
  
/*******************************************************************\

Function: cbmc_parseoptionst::cbmc_parseoptionst

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

::cbmc_parseoptionst::cbmc_parseoptionst(
  int argc,
  const char **argv,
  const std::string &extra_options):
  parseoptions_baset(CBMC_OPTIONS+extra_options, argc, argv),
  xml_interfacet(cmdline),
  language_uit("CBMC " CBMC_VERSION, cmdline)
{
}

/*******************************************************************\

Function: cbmc_parseoptionst::set_verbosity

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cbmc_parseoptionst::set_verbosity(messaget &message)
{
  int v=8;
  
  if(cmdline.isset("verbosity"))
  {
    v=atoi(cmdline.getval("verbosity"));
    if(v<0)
      v=0;
    else if(v>9)
      v=9;
  }
  
  message.set_verbosity(v);
}

/*******************************************************************\

Function: cbmc_parseoptionst::get_command_line_options

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cbmc_parseoptionst::get_command_line_options(optionst &options)
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

  if(cmdline.isset("no-simplify"))
    options.set_option("simplify", false);
  else
    options.set_option("simplify", true);

  if(cmdline.isset("all-claims"))
    options.set_option("all-claims", true);
  else
    options.set_option("all-claims", false);

  if(cmdline.isset("unwind"))
    options.set_option("unwind", cmdline.getval("unwind"));

  if(cmdline.isset("depth"))
    options.set_option("depth", cmdline.getval("depth"));

  if(cmdline.isset("debug-level"))
    options.set_option("debug-level", cmdline.getval("debug-level"));

  if(cmdline.isset("slice-by-trace"))
    options.set_option("slice-by-trace", cmdline.getval("slice-by-trace"));

  if(cmdline.isset("unwindset"))
    options.set_option("unwindset", cmdline.getval("unwindset"));

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
    options.set_option("error-label", cmdline.getval("error-label"));

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

  if(cmdline.isset("boolector"))
    options.set_option("boolector", true);

  if(cmdline.isset("mathsat"))
    options.set_option("mathsat", true);

  if(cmdline.isset("cvc"))
    options.set_option("cvc", true);

  if(cmdline.isset("smt1"))
    options.set_option("smt1", true);

  if(cmdline.isset("smt2"))
    options.set_option("smt2", true);

  if(cmdline.isset("fpa"))
    options.set_option("fpa", true);

  if(cmdline.isset("yices"))
    options.set_option("yices", true);

  if(cmdline.isset("z3"))
    options.set_option("z3", true);

  if(cmdline.isset("beautify"))
    options.set_option("beautify", true);

  options.set_option("pretty-names", 
                     !cmdline.isset("no-pretty-names"));

  if(cmdline.isset("outfile"))
    options.set_option("outfile", cmdline.getval("outfile"));
}

/*******************************************************************\

Function: cbmc_parseoptionst::doit

  Inputs:

 Outputs:

 Purpose: invoke main modules

\*******************************************************************/

int cbmc_parseoptionst::doit()
{
  if(cmdline.isset("version"))
  {
    std::cout << CBMC_VERSION << std::endl;
    return 0;
  }

  //
  // unwinding of transition systems
  //

  if(cmdline.isset("module") ||
     cmdline.isset("gen-interface"))

  {
    error("This version of CBMC has no support for "
          " hardware modules. Please use hw-cbmc.");
    return 1;
  }
  
  register_languages();

  //
  // command line options
  //

  optionst options;
  get_command_line_options(options);

  bmct bmc(options, symbol_table, ui_message_handler);
  set_verbosity(bmc);
  set_verbosity(*this);
  
  if(cmdline.isset("preprocess"))
  {
    preprocessing();
    return 0;
  }

  goto_functionst goto_functions;

  if(get_goto_program(options, bmc, goto_functions))
    return 6;
    
  label_claims(goto_functions);

  if(cmdline.isset("show-claims"))
  {
    const namespacet ns(symbol_table);
    show_claims(ns, get_ui(), goto_functions);
    return 0;
  }

  if(set_claims(goto_functions))
    return 7;

  // do actual BMC
  return do_bmc(bmc, goto_functions);
}

/*******************************************************************\

Function: cbmc_parseoptionst::set_claims

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool cbmc_parseoptionst::set_claims(goto_functionst &goto_functions)
{
  try
  {
    if(cmdline.isset("claim"))
      ::set_claims(goto_functions, cmdline.get_values("claim"));  
  }

  catch(const char *e)
  {
    error(e);
    return true;
  }

  catch(const std::string e)
  {
    error(e);
    return true;
  }
  
  catch(int)
  {
    return true;
  }
  
  return false;
}

/*******************************************************************\

Function: cbmc_parseoptionst::get_goto_program

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
  
bool cbmc_parseoptionst::get_goto_program(
  const optionst &options,
  bmct &bmc,
  goto_functionst &goto_functions)
{
  if(cmdline.args.size()==0)
  {
    error("Please provide a program to verify");
    return true;
  }

  try
  {
    if(cmdline.args.size()==1 &&
       is_goto_binary(cmdline.args[0]))
    {
      status("Reading GOTO program from file");

      if(read_goto_binary(cmdline.args[0],
           symbol_table, goto_functions, get_message_handler()))
        return true;
        
      config.ansi_c.set_from_symbol_table(symbol_table);

      if(cmdline.isset("show-symbol-table"))
      {
        show_symbol_table();
        return true;
      }
      
      if(symbol_table.symbols.find(ID_main)==symbol_table.symbols.end())
      {
        error("The goto binary has no entry point; please complete linking");
        return true;
      }
    }
    else
    {
      if(parse()) return true;
      if(typecheck()) return true;
      if(get_modules(bmc)) return true;    
      if(final()) return true;

      // we no longer need any parse trees or language files
      clear_parse();

      if(cmdline.isset("show-symbol-table"))
      {
        show_symbol_table();
        return true;
      }

      if(symbol_table.symbols.find(ID_main)==symbol_table.symbols.end())
      {
        error("No entry point; please provide a main function");
        return true;
      }

      status("Generating GOTO Program");

      goto_convert(symbol_table, goto_functions, ui_message_handler);
    }

    // finally add the library
    status("Adding CPROVER library");      
    link_to_library(symbol_table, goto_functions, ui_message_handler);

    if(process_goto_program(options, goto_functions))
      return true;
  }

  catch(const char *e)
  {
    error(e);
    return true;
  }

  catch(const std::string e)
  {
    error(e);
    return true;
  }
  
  catch(int)
  {
    return true;
  }
  
  catch(std::bad_alloc)
  {
    error("Out of memory");
    return true;
  }
  
  return false;
}

/*******************************************************************\

Function: cbmc_parseoptionst::preprocessing

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
  
void cbmc_parseoptionst::preprocessing()
{
  try
  {
    if(cmdline.args.size()!=1)
    {
      error("Please provide one program to preprocess");
      return;
    }

    std::string filename=cmdline.args[0];

    std::ifstream infile(filename.c_str());

    if(!infile)
    {
      error("failed to open input file");
      return;
    }

    languaget *ptr=get_language_from_filename(filename);

    if(ptr==NULL)
    {
      error("failed to figure out type of file");
      return;
    }

    std::auto_ptr<languaget> language(ptr);
  
    if(language->preprocess(
      infile, filename, std::cout, get_message_handler()))
      error("PREPROCESSING ERROR");
  }

  catch(const char *e)
  {
    error(e);
  }

  catch(const std::string e)
  {
    error(e);
  }
  
  catch(int)
  {
  }

  catch(std::bad_alloc)
  {
    error("Out of memory");
  }
}

/*******************************************************************\

Function: cbmc_parseoptionst::process_goto_program

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
  
bool cbmc_parseoptionst::process_goto_program(
  const optionst &options,
  goto_functionst &goto_functions)
{
  try
  {
    namespacet ns(symbol_table);

    if(cmdline.isset("string-abstraction"))
      string_instrumentation(
        symbol_table, get_message_handler(), goto_functions);

    status("Function Pointer Removal");
    remove_function_pointers(symbol_table, goto_functions,
      cmdline.isset("pointer-check"));

    status("Partial Inlining");
    // do partial inlining
    goto_partial_inline(goto_functions, ns, ui_message_handler);
    
    status("Generic Property Instrumentation");
    // add generic checks
    goto_check(ns, options, goto_functions);
    
    if(cmdline.isset("string-abstraction"))
    {
      status("String Abstraction");
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
    error(e);
    return true;
  }

  catch(const std::string e)
  {
    error(e);
    return true;
  }
  
  catch(int)
  {
    return true;
  }
  
  catch(std::bad_alloc)
  {
    error("Out of memory");
    return true;
  }
  
  return false;
}

/*******************************************************************\

Function: cbmc_parseoptionst::do_bmc

  Inputs:

 Outputs:

 Purpose: invoke main modules

\*******************************************************************/

int cbmc_parseoptionst::do_bmc(
  bmct &bmc,
  const goto_functionst &goto_functions)
{
  bmc.set_ui(get_ui());

  // do actual BMC
  if(bmc.run(goto_functions))
    return 10;

  return 0;
}

/*******************************************************************\

Function: cbmc_parseoptionst::help

  Inputs:

 Outputs:

 Purpose: display command line help

\*******************************************************************/

void cbmc_parseoptionst::help()
{
  std::cout <<
    "\n"
    "* *   CBMC " CBMC_VERSION " - Copyright (C) 2001-2011 ";
    
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
    " --show-symbol-table          show symbol table\n"
    " --show-goto-functions        show goto program\n"
    " --ppc-macos                  set MACOS/PPC architecture\n"
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
    " --signed-overflow-check      enable arithmetic over- and underflow checks\n"
    " --unsigned-overflow-check    enable arithmetic over- and underflow checks\n"
    " --nan-check                  check floating-point for NaN\n"
    " --all-claims                 report status of all claims\n"
    " --show-claims                only show claims\n"
    " --show-loops                 show the loops in the program\n"
    " --no-assertions              ignore user assertions\n"
    " --no-assumptions             ignore user assumptions\n"
    " --error-label label          check that label is unreachable\n"
    " --cover-assertions           check which assertions are reachable\n"
    "\n"
    "BMC options:\n"
    " --function name              set main function name\n"
    " --claim nr                   only check specific claim\n"
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
    "\n"
    "Backend options:\n"
    " --dimacs                     generate CNF in DIMACS format\n"
    " --beautify                   beautify the counterexample (greedy heuristic)\n"
    " --smt1                       output subgoals in SMT1 syntax (experimental)\n"
    " --smt2                       output subgoals in SMT2 syntax (experimental)\n"
    " --boolector                  use Boolector (experimental)\n"
    " --mathsat                    use MathSAT (experimental)\n"
    " --cvc                        use CVC3 (experimental)\n"
    " --yices                      use Yices (experimental)\n"
    " --z3                         use Z3 (experimental)\n"
    " --refine                     use refinement procedure (experimental)\n"
    " --outfile filename           output formula to given file\n"
    " --arrays-uf-never            never turn arrays into uninterpreted functions\n"
    " --arrays-uf-always           always turn arrays into uninterpreted functions\n"
    "\n"
    "Other options:\n"
    " --version                    show version and exit\n"
    " --xml-ui                     use XML-formatted output\n"
    " --xml-interface              stdio-XML interface\n"
    "\n";
}
