/*******************************************************************\

Module: Symex Command Line Options Processing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>
#include <fstream>

#include <util/config.h>
#include <util/language.h>
#include <util/options.h>
#include <util/memory_info.h>

#include <ansi-c/ansi_c_language.h>
#include <cpp/cpp_language.h>

#include <goto-programs/goto_convert_functions.h>
#include <goto-programs/show_properties.h>
#include <goto-programs/set_properties.h>
#include <goto-programs/read_goto_binary.h>
#include <goto-programs/loop_ids.h>
#include <goto-programs/link_to_library.h>
#include <goto-programs/goto_inline.h>

#include <analyses/goto_check.h>

#include <langapi/mode.h>

#include <cbmc/version.h>

#include "symex_parseoptions.h"

/*******************************************************************\

Function: symex_parseoptionst::symex_parseoptionst

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

symex_parseoptionst::symex_parseoptionst(int argc, const char **argv):
  parseoptions_baset(SYMEX_OPTIONS, argc, argv),
  language_uit("Symex " CBMC_VERSION, cmdline)
{
}
  
/*******************************************************************\

Function: symex_parseoptionst::eval_verbosity

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void symex_parseoptionst::eval_verbosity()
{
  // this is our default verbosity
  int v=messaget::M_STATISTICS;
  
  if(cmdline.isset("verbosity"))
  {
    v=atoi(cmdline.getval("verbosity"));
    if(v<0)
      v=0;
    else if(v>10)
      v=10;
  }
  
  set_verbosity(v);
}

/*******************************************************************\

Function: symex_parseoptionst::get_command_line_options

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void symex_parseoptionst::get_command_line_options(optionst &options)
{
  if(config.set(cmdline))
  {
    usage_error();
    exit(1);
  }

  if(cmdline.isset("unwind"))
    options.set_option("unwind", cmdline.getval("unwind"));

  if(cmdline.isset("depth"))
    options.set_option("depth", cmdline.getval("depth"));

  if(cmdline.isset("debug-level"))
    options.set_option("debug-level", cmdline.getval("debug-level"));

  if(cmdline.isset("unwindset"))
    options.set_option("unwindset", cmdline.getval("unwindset"));

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
    options.set_option("error-label", cmdline.getval("error-label"));
}

/*******************************************************************\

Function: symex_parseoptionst::doit

  Inputs:

 Outputs:

 Purpose: invoke main modules

\*******************************************************************/

int symex_parseoptionst::doit()
{
  if(cmdline.isset("version"))
  {
    std::cout << CBMC_VERSION << std::endl;
    return 0;
  }

  register_language(new_ansi_c_language);
  register_language(new_cpp_language);

  //
  // command line options
  //

  optionst options;
  get_command_line_options(options);

  eval_verbosity();

  goto_functionst goto_functions;

  if(get_goto_program(options, goto_functions))
    return 6;
    
  label_properties(goto_functions);

  if(cmdline.isset("show-properties"))
  {
    const namespacet ns(symbol_table);
    show_properties(ns, get_ui(), goto_functions);
    return 0;
  }

  if(set_properties(goto_functions))
    return 7;

  // do actual Symex
  return do_symex(goto_functions);
}

/*******************************************************************\

Function: symex_parseoptionst::set_properties

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool symex_parseoptionst::set_properties(goto_functionst &goto_functions)
{
  try
  {
    if(cmdline.isset("property"))
      ::set_properties(goto_functions, cmdline.get_values("property"));
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

Function: symex_parseoptionst::get_goto_program

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
  
bool symex_parseoptionst::get_goto_program(
  const optionst &options,
  goto_functionst &goto_functions)
{
  if(cmdline.args.size()==0)
  {
    error() << "Please provide a program to verify" << eom;
    return true;
  }

  try
  {
    if(cmdline.args.size()==1 &&
       is_goto_binary(cmdline.args[0]))
    {
      status() << "Reading GOTO program from file" << eom;

      if(read_goto_binary(cmdline.args[0],
           symbol_table, goto_functions, get_message_handler()))
        return true;
        
      config.ansi_c.set_from_symbol_table(symbol_table);

      if(cmdline.isset("show-symbol-table"))
      {
        show_symbol_table();
        return true;
      }
      
      irep_idt entry_point=goto_functions.entry_point();
      
      if(symbol_table.symbols.find(entry_point)==symbol_table.symbols.end())
      {
        error() << "The goto binary has no entry point; please complete linking" << eom;
        return true;
      }
    }
    else if(cmdline.isset("show-parse-tree"))
    {
      if(cmdline.args.size()!=1)
      {
        error() << "Please give one source file only" << eom;
        return true;
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
        return true;
      }
                              
      languaget *language=get_language_from_filename(filename);
                                                
      if(language==NULL)
      {
        error() << "failed to figure out type of file `" <<  filename << "'" << eom;
        return true;
      }
                                                                
      status("Parsing", filename);
  
      if(language->parse(infile, filename, get_message_handler()))
      {
        error() << "PARSING ERROR" << eom;
        return true;
      }
      
      language->show_parse(std::cout);
      return true;
    }
    else
    {
    
      if(parse()) return true;
      if(typecheck()) return true;
      if(final()) return true;

      // we no longer need any parse trees or language files
      clear_parse();

      if(cmdline.isset("show-symbol-table"))
      {
        show_symbol_table();
        return true;
      }

      irep_idt entry_point=goto_functions.entry_point();
      
      if(symbol_table.symbols.find(entry_point)==symbol_table.symbols.end())
      {
        error() << "No entry point; please provide a main function" << eom;
        return true;
      }

      status() << "Generating GOTO Program" << eom;

      goto_convert(symbol_table, goto_functions, ui_message_handler);
    }

    // finally add the library
    status() << "Adding CPROVER library" << eom;
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
    error() << "Out of memory" << eom;
    return true;
  }
  
  return false;
}

/*******************************************************************\

Function: symex_parseoptionst::process_goto_program

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
  
bool symex_parseoptionst::process_goto_program(
  const optionst &options,
  goto_functionst &goto_functions)
{
  try
  {
    namespacet ns(symbol_table);

    // do partial inlining
    status() << "Partial Inlining" << eom;
    goto_partial_inline(goto_functions, ns, ui_message_handler);
    
    // add generic checks
    status() << "Generic Property Instrumentation" << eom;
    goto_check(ns, options, goto_functions);
    
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
    error() << "Out of memory" << eom;
    return true;
  }
  
  return false;
}

/*******************************************************************\

Function: symex_parseoptionst::do_symex

  Inputs:

 Outputs:

 Purpose: invoke main modules

\*******************************************************************/

int symex_parseoptionst::do_symex(
  const goto_functionst &goto_functions)
{
  #if 0
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
  #endif
}

/*******************************************************************\

Function: symex_parseoptionst::help

  Inputs:

 Outputs:

 Purpose: display command line help

\*******************************************************************/

void symex_parseoptionst::help()
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
    " symex [-?] [-h] [--help]      show help\n"
    " symex file.c ...              source file names\n"
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
    " --memory-leak-check          enable memory leak checks\n"
    " --signed-overflow-check      enable arithmetic over- and underflow checks\n"
    " --unsigned-overflow-check    enable arithmetic over- and underflow checks\n"
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
    " --property nr                only check one specific property\n"
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
    "\n";
}
