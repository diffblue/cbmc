/*******************************************************************\

Module: Main Module 

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <fstream>
#include <memory>

#include <config.h>
#include <expr_util.h>

#include <goto-programs/goto_convert_functions.h>
#include <goto-programs/goto_function_pointers.h>
#include <goto-programs/goto_check.h>
#include <goto-programs/goto_inline.h>
#include <goto-programs/show_claims.h>
#include <goto-programs/set_claims.h>
#include <goto-programs/read_goto_binary.h>
#include <goto-programs/write_goto_binary.h>
#include <goto-programs/dump_c.h>
#include <goto-programs/interpreter.h>
#include <goto-programs/string_abstraction.h>
#include <goto-programs/string_instrumentation.h>
#include <goto-programs/loop_numbers.h>

#include <pointer-analysis/value_set_analysis.h>
#include <pointer-analysis/goto_program_dereference.h>
#include <pointer-analysis/add_failed_symbols.h>
#include <pointer-analysis/show_value_sets.h>

#include "parseoptions.h"
#include "version.h"
#include "document_claims.h"
#include "uninitialized.h"
#include "full_slicer.h"
#include "show_locations.h"
#include "points_to.h"
#include "alignment_checks.h"

/*******************************************************************\

Function: goto_instrument_parseoptionst::set_verbosity

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_instrument_parseoptionst::set_verbosity(messaget &message)
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

Function: goto_instrument_parseoptionst::doit

  Inputs:

 Outputs:

 Purpose: invoke main modules

\*******************************************************************/

int goto_instrument_parseoptionst::doit()
{
  if(cmdline.isset("version"))
  {
    std::cout << GOTO_INSTRUMENT_VERSION << std::endl;
    return 0;
  }
  
  if(cmdline.args.size()!=1 && cmdline.args.size()!=2)
  {
    help();
    return 0;
  }
  
  set_verbosity(*this);

  try
  {
    register_languages();

    goto_functionst goto_functions;

    get_goto_program(goto_functions);
    instrument_goto_program(goto_functions);

    if(cmdline.isset("show-value-sets"))
    {
      namespacet ns(context);

      status("Function Pointer Removal");
      remove_function_pointers(ns, goto_functions);

      status("Partial Inlining");
      goto_partial_inline(goto_functions, ns, ui_message_handler);
    
      status("Pointer Analysis");
      value_set_analysist value_set_analysis(ns);
      value_set_analysis(goto_functions);

      show_value_sets(get_ui(), goto_functions, value_set_analysis);
      return 0;
    }

    if(cmdline.isset("show-points-to"))
    {
      namespacet ns(context);

      status("Function Pointer Removal");
      remove_function_pointers(ns, goto_functions);

      status("Partial Inlining");
      goto_partial_inline(goto_functions, ns, ui_message_handler);
    
      status("Pointer Analysis");
      points_tot points_to;
      points_to(goto_functions);
      points_to.output(std::cout);
      return 0;
    }

    if(cmdline.isset("show-symbol-table"))
    {
      show_symbol_table();
      return 0;
    }

    if(cmdline.isset("show-uninitialized"))
    {
      show_uninitialized(context, goto_functions, std::cout);
      return 0;
    }

    if(cmdline.isset("interpreter"))
    {
      status("Starting interpeter");
      interpreter(context, goto_functions);
      return 0;
    }

    if(cmdline.isset("show-claims"))
    {
      const namespacet ns(context);
      show_claims(ns, get_ui(), goto_functions);
      return 0;
    }

    if(cmdline.isset("document-claims"))
    {
      const namespacet ns(context);
      document_claims(ns, goto_functions, std::cout);
      return 0;
    }

    if(cmdline.isset("show-loops"))
    {
      show_loop_numbers(get_ui(), goto_functions);
      return 0;
    }

    if(cmdline.isset("show-goto-functions"))
    {
      namespacet ns(context);
      goto_functions.output(ns, std::cout);
      return 0;
    }

    // experimental: print structs
    if(cmdline.isset("show-struct-alignment"))
    {
      print_struct_alignment_problems(context, std::cout);
      return 0;
    }
    // end of experiment

    if(cmdline.isset("show-locations"))
    {
      show_locations(get_ui(), goto_functions);
      return 0;
    }

    if(cmdline.isset("dump-c"))
    {
      namespacet ns(context);
      dump_c(goto_functions, ns, std::cout);
      return 0;
    }
    
    // write new binary?
    if(cmdline.args.size()==2)
    {
      status("Writing GOTO program to "+cmdline.args[1]);
      
      if(write_goto_binary(
        cmdline.args[1], context, goto_functions, get_message_handler()))
        return 1;
      else
        return 0;
    }

    help();
    return 0;
  }

  catch(const char *e)
  {
    error(e);
    return 11;
  }

  catch(const std::string e)
  {
    error(e);
    return 11;
  }
  
  catch(int)
  {
    return 11;
  }
  
  catch(std::bad_alloc)
  {
    error("Out of memory");
    return 11;
  }
}

/*******************************************************************\

Function: goto_instrument_parseoptionst::get_goto_program

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
  
void goto_instrument_parseoptionst::get_goto_program(
  goto_functionst &goto_functions)
{
  status("Reading GOTO program from "+cmdline.args[0]);

  if(read_goto_binary(cmdline.args[0],
    context, goto_functions, get_message_handler()))
    throw 0;

  config.ansi_c.set_from_context(context);
}

/*******************************************************************\

Function: goto_instrument_parseoptionst::instrument_goto_program

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
  
void goto_instrument_parseoptionst::instrument_goto_program(
  goto_functionst &goto_functions)
{
  optionst options;

  // use assumptions instead of assertions?
  if(cmdline.isset("assert-to-assume"))
    options.set_option("assert-to-assume", true);
  else
    options.set_option("assert-to-assume", false);

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

  namespacet ns(context);

  // add generic checks, if needed
  goto_check(ns, options, goto_functions);
  
  // check for uninitalized local varibles
  if(cmdline.isset("uninitialized-check"))
  {
    status("Adding checks for uninitialized local variables");
    add_uninitialized_locals_assertions(context, goto_functions);
  }
  
  if(cmdline.isset("string-abstraction"))
  {
    status("String Abstraction");
    string_abstraction(context,
      get_message_handler(), goto_functions);
  }

  if(cmdline.isset("pointer-check"))
  {
    status("Function Pointer Removal");
    remove_function_pointers(ns, goto_functions);

    // do partial inlining
    status("Partial Inlining");
    goto_partial_inline(goto_functions, ns, ui_message_handler);
    
    status("Pointer Analysis");
    value_set_analysist value_set_analysis(ns);
    value_set_analysis(goto_functions);

    // add pointer checks
    status("Adding Pointer Checks");
    pointer_checks(
      goto_functions, context, options, value_set_analysis);
  }

  // add failed symbols
  add_failed_symbols(context);
  
  // recalculate numbers, etc.
  goto_functions.update();

  // add loop ids
  goto_functions.compute_loop_numbers();
  
  // full slice?
  if(cmdline.isset("full-slice"))
  {
    status("Performing a full slice");
    full_slicer(goto_functions);
  }
}

/*******************************************************************\

Function: goto_instrument_parseoptionst::help

  Inputs:

 Outputs:

 Purpose: display command line help

\*******************************************************************/

void goto_instrument_parseoptionst::help()
{
  std::cout <<
    "\n"
    "* *       Goto-Instrument " GOTO_INSTRUMENT_VERSION " - Copyright (C) 2008-2009           * *\n"
    "* *                     Daniel Kroening                     * *\n"
    "* *                 kroening@kroening.com                   * *\n"
    "\n"
    "Usage:                       Purpose:\n"
    "\n"
    " goto-instrument [-?] [-h] [--help]  show help\n"
    " goto-instrument in out              perform instrumentation\n"
    "\n"
    "Main options:\n"
    " --show-loops                 show the loops in the program\n"
    " --show-claims                show claims\n"
    " --document-claims            generate claim documentation\n"
    " --show-symbol-table          show symbol table\n"
    " --show-goto-functions        show goto program\n"
    " --show-struct-alignment      show struct members that might be concurrently accessed\n"
    " --dump-c                     generate C source\n"
    " --interpreter                do concrete execution\n"
    "\n"
    "Instrumentation options:\n"
    " --no-assertions              ignore user assertions\n"
    " --bounds-check               add array bounds checks\n"
    " --div-by-zero-check          add division by zero checks\n"
    " --pointer-check              add pointer checks\n"
    " --signed-overflow-check      add arithmetic over- and underflow checks\n"
    " --unsigned-overflow-check    add arithmetic over- and underflow checks\n"
    " --nan-check                  add floating-point NaN checks\n"
    " --uninitialized-check        add checks for uninitialized locals (experimental)\n"
    " --error-label label          check that label is unreachable\n"
    "\n"
    "Other options:\n"
    " --version                    show version and exit\n"
    " --xml-ui                     use XML-formatted output\n"
    "\n";
}
