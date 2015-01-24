/*******************************************************************\

Module: Main Module 

Author:

\*******************************************************************/

#include <fstream>
#include <iostream>
#include <memory>

#include <util/config.h>
#include <util/string2int.h>

#include <goto-programs/remove_function_pointers.h>
#include <goto-programs/remove_skip.h>
#include <goto-programs/set_properties.h>
#include <goto-programs/goto_inline.h>
#include <goto-programs/read_goto_binary.h>
#include <goto-programs/write_goto_binary.h>
#include <goto-programs/link_to_library.h>
#include <goto-programs/remove_asm.h>

#ifdef POINTER_ANALYSIS_FI
#include <pointer-analysis/value_set_analysis_fi.h>
#else
#include <pointer-analysis/value_set_analysis.h>
#endif

#include <pointer-analysis/goto_program_dereference.h>
#include <pointer-analysis/add_failed_symbols.h>

#include <analyses/local_may_alias.h>
#include <analyses/goto_check.h>

#include <goto-instrument/rw_set.h>
#include <goto-instrument/wmm/weak_memory.h>

#include "propagate_const_function_pointers.h"
#include "version.h"
#include "musketeer_parseoptions.h"
#include "fencer.h"
#include "fence_shared.h"
#include "pensieve.h"
#include "replace_async.h"
#include "infer_mode.h"

/*******************************************************************\

Function: goto_fence_inserter_parseoptionst::set_verbosity

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_fence_inserter_parseoptionst::set_verbosity()
{
  unsigned int v=8; // default
  
  if(cmdline.isset("verbosity"))
  {
    v=unsafe_string2unsigned(cmdline.get_value("verbosity"));
    if(v>10) v=10;
  }

  ui_message_handler.set_verbosity(v);
}

/*******************************************************************\

Function: goto_fence_inserter_parseoptionst::doit

  Inputs:

 Outputs:

 Purpose: invoke main modules

\*******************************************************************/

int goto_fence_inserter_parseoptionst::doit()
{
  if(cmdline.isset("version"))
  {
    std::cout << GOTO_FENCE_INSERTER_VERSION << std::endl;
    return 0;
  }
  
  if(cmdline.args.size()!=1 && cmdline.args.size()!=2)
  {
    help();
    return 0;
  }
  
  set_verbosity();

  try
  {
    register_languages();

    goto_functionst goto_functions;

    get_goto_program(goto_functions);

    instrument_goto_program(goto_functions);
    
    // write new binary?
    if(cmdline.args.size()==2)
    {
      status() << "Writing GOTO program to " << cmdline.args[1] << eom;
      
      if(write_goto_binary(
        cmdline.args[1], symbol_table, goto_functions, get_message_handler()))
        return 1;
      else
        return 0;
    }

    //help();
    return 0;
  }

  catch(const char *e)
  {
    error() << e << eom;
    return 11;
  }

  catch(const std::string e)
  {
    error() << e << eom;
    return 11;
  }
  
  catch(int)
  {
    return 11;
  }
  
  catch(std::bad_alloc)
  {
    error() << "Out of memory" << eom;
    return 11;
  }
}

/*******************************************************************\

Function: goto_fence_inserter_parseoptionst::get_goto_program

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
  
void goto_fence_inserter_parseoptionst::get_goto_program(
  goto_functionst &goto_functions)
{
  status() << "Reading GOTO program from " << cmdline.args[0] << eom;

  if(read_goto_binary(cmdline.args[0],
    symbol_table, goto_functions, get_message_handler()))
    throw 0;

  config.ansi_c.set_from_symbol_table(symbol_table);
}

/*******************************************************************\

Function: goto_fence_inserter_parseoptionst::instrument_goto_program

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
  
void goto_fence_inserter_parseoptionst::instrument_goto_program(
  goto_functionst &goto_functions)
{
  optionst options;

  // unwind loops 
  if(cmdline.isset("unwind"))
  {
    status() << "Unwinding loops" << eom;
    options.set_option("unwind", cmdline.get_value("unwind"));
  }

  // we add the library, as some analyses benefit
  
  status() << "Adding CPROVER library" << eom;      
  link_to_library(symbol_table, goto_functions, ui_message_handler);

  namespacet ns(symbol_table);

  // add generic checks, if needed
  goto_check(ns, options, goto_functions);
 
  if( cmdline.isset("mm")
      || cmdline.isset("all-shared")
      || cmdline.isset("volatile") 
      || cmdline.isset("pensieve") 
      || cmdline.isset("naive") 
      || cmdline.isset("all-shared-aeg") )
  {
    if(cmdline.isset("remove-function-pointers")) {
      status() << "remove soundly function pointers" << eom;
      remove_function_pointers(symbol_table, goto_functions, 
        cmdline.isset("pointer-check"));
    }

    if(cmdline.isset("async")) {
      status() << "Replace pthread_creates by __CPROVER_ASYNC_0:" << eom;
      replace_async(ns, goto_functions);
      goto_functions.update();
    }

    // do partial inlining
    status() << "Partial Inlining" << eom;
    goto_partial_inline(goto_functions, ns, ui_message_handler);

    if( cmdline.isset("const-function-pointer-propagation") ) {
      /* propagate const pointers to functions */
      status() << "Propagate Constant Function Pointers" << eom;
      propagate_const_function_pointers(symbol_table, goto_functions, 
        get_message_handler());
    }

    //goto_functions.output(ns, std::cout);
    //return;
#if 0
    status() << "Function Pointer Removal" << eom;
    remove_function_pointers(symbol_table, goto_functions, 
      cmdline.isset("pointer-check"));
#endif

#if 0
    // do partial inlining
    status() << "Partial Inlining" << eom;
    goto_partial_inline(goto_functions, ns, ui_message_handler);
#endif

    status() << "Pointer Analysis" << eom;
#ifdef POINTER_ANALYSIS_FI
    value_set_analysis_fit value_set_analysis(ns);
#else
    value_set_analysist value_set_analysis(ns);
#endif

#ifndef LOCAL_MAY
    value_set_analysis(goto_functions);
#endif

    status() << "Removing asm code" << eom;
    remove_asm(symbol_table, goto_functions);
    goto_functions.update();

    if(cmdline.isset("all-shared")) {
      status() << "Shared variables accesses detection" << eom;
      fence_all_shared(get_message_handler(), value_set_analysis, symbol_table,
        goto_functions);
      // simple analysis, coupled with script to insert;
      // does not transform the goto-binary
      return;
    }
    if(cmdline.isset("all-shared-aeg")) {
      status() << "Shared variables accesses detection (CF)" << eom;
      fence_all_shared_aeg(get_message_handler(), value_set_analysis, 
        symbol_table, goto_functions);
      // simple analysis, coupled with script to insert;
      // does not transform the goto-binary
      return;
    }
    else if(cmdline.isset("volatile")) {
      status() << "Detection of variables declared volatile" << eom;

      fence_volatile(get_message_handler(), value_set_analysis, symbol_table, 
        goto_functions);
      // simple analysis, coupled with script to insert;
      // does not transform the goto-binary
      return;
    }
    else if(cmdline.isset("pensieve") || cmdline.isset("naive")) {
      status() << "Delay-set analysis" << eom;

      const unsigned unwind_loops =
        ( cmdline.isset("unwind") ? 
          unsafe_string2unsigned(cmdline.get_value("unwind")) : 0 );

      const unsigned max_po_trans =
        ( cmdline.isset("max-po-trans") ?
          unsafe_string2unsigned(cmdline.get_value("max-po-trans")) : 0 );

      fence_pensieve(         
        value_set_analysis,
        symbol_table,
        goto_functions,
        unwind_loops,
        max_po_trans,
        !cmdline.isset("no-po-rendering"),
        cmdline.isset("render-cluster-file"),
        cmdline.isset("render-cluster-function"),
        cmdline.isset("naive"),
        get_message_handler());
        // simple analysis, coupled with script to insert;
        // does not transform the goto-binary
        return;
    }
    else if(cmdline.isset("mm"))
    {
      std::string mm=cmdline.get_value("mm");
      memory_modelt model;

      status() << "Fence detection for " << mm 
        << " via critical cycles and ILP" << eom;

      // strategy of instrumentation
      instrumentation_strategyt inst_strategy;
      if(cmdline.isset("one-event-per-cycle"))
        inst_strategy=one_event_per_cycle;
      else if(cmdline.isset("minimum-interference"))
        inst_strategy=min_interference;
      else if(cmdline.isset("read-first"))
        inst_strategy=read_first;
      else if(cmdline.isset("write-first"))
        inst_strategy=write_first;
      else if(cmdline.isset("my-events"))
        inst_strategy=my_events;
      else
        /* default: instruments all unsafe pairs */
        inst_strategy=all;
      
      const unsigned unwind_loops = 
        ( cmdline.isset("unwind") ? 
          unsafe_string2unsigned(cmdline.get_value("unwind")) : 0 );

      const unsigned max_var =
        ( cmdline.isset("max-var") ?
          unsafe_string2unsigned(cmdline.get_value("max-var")) : 0 );

      const unsigned max_po_trans =
        ( cmdline.isset("max-po-trans") ?
          unsafe_string2unsigned(cmdline.get_value("max-po-trans")) : 0 );

      if(mm=="tso")
      {
        status() << "Adding weak memory (TSO) Instrumentation" << eom;
        model=TSO;
      }
      else if(mm=="pso")
      {
        status() << "Adding weak memory (PSO) Instrumentation" << eom;
        model=PSO;
      }
      else if(mm=="rmo")
      {
        status() << "Adding weak memory (RMO) Instrumentation" << eom;
        model=RMO;
      }
      else if(mm=="power")
      {
        status() << "Adding weak memory (Power) Instrumentation" << eom;
        model=Power;
      }
      else
      {
        status/*error*/() << "Unknown weak memory model" << eom;
        model=Unknown;
      }

      /* inference mode */
      infer_modet infer_mode=INFER;
      
      if(cmdline.isset("userdef"))
        infer_mode=USER_DEF;

      loop_strategyt loops=arrays_only;

      if(cmdline.isset("force-loop-duplication"))
        loops=all_loops;
      if(cmdline.isset("no-loop-duplication"))
        loops=no_loop;

      /*if(model!=Unknown)*/
        fence_weak_memory(
          model,
          value_set_analysis,
          symbol_table,
          goto_functions,
          cmdline.isset("scc"),
          inst_strategy,
          unwind_loops,
          !cmdline.isset("cfg-kill"),
          cmdline.isset("no-dependencies"),
          loops,
          max_var,
          max_po_trans,
          !cmdline.isset("no-po-rendering"),
          cmdline.isset("render-cluster-file"),
          cmdline.isset("render-cluster-function"),
          cmdline.isset("cav11"),
          cmdline.isset("hide-internals"),
          cmdline.isset("print-graph"),
          infer_mode,
          get_message_handler(),
          cmdline.isset("ignore-arrays"));
    }
  }  

  // add failed symbols
  add_failed_symbols(symbol_table);
  
  // recalculate numbers, etc.
  goto_functions.update();

  // add loop ids
  goto_functions.compute_loop_numbers();
  
  // label the assertions
  label_properties(goto_functions);
}

/*******************************************************************\

Function: goto_fence_inserter_parseoptionst::help

  Inputs:

 Outputs:

 Purpose: display command line help

\*******************************************************************/

void goto_fence_inserter_parseoptionst::help()
{
  std::cout <<
    "\n"
    "* *     musketeer " GOTO_FENCE_INSERTER_VERSION "     * *\n"
    "\n"
    "              ~__\n"
    "               |)\n"
    "              /|_____\n"
    "             / |\n"
    "              /|\n"
    "             / |\n"
    "\n"
    "Usage:                        Purpose:\n"
    "\n"
    " musketeer [-?] [-h] [--help] show help\n"
    "\n"
    "Main options:\n"
    "\n"
    " --mm <tso,pso,rmo,power>     detects all the fences to insert for a weak\n"
    "                              memory model\n"
    "\n"
    "Alternative methods:\n"
    "\n"
    " --all-shared                 detects and fences all the accesses to shared\n"
    "                              variables (context insensitive)\n"
    " --all-shared-aeg             detects all the accesses to shared variables\n"
    "                              (context sensitive)\n"
    " --volatile                   detects all the accesses to volatile variables\n"
    " --pensieve                   detects all the pairs to be delayed with\n"
    "                              Pensieve's criteria (context sensitive)\n"
    " --naive                      detects all the pairs to be delayed in a naive\n"
    "                              approach (context sensitive)\n"
    "\n"
    "Options:\n"
    "\n"
    " --remove-function-pointers   removes soundly function pointers based on\n"
    "                              their signatures\n"
    " --async                      replaces all the pthread_creates by CPROVER_ASYNC\n"
    " --const-function-pointer-propagation\n"
    "                              propagates the constant pointers to functions\n"
    " --scc                        detects cycles in parallel (one thread/SCC)\n"
    " --force-loop-duplication     duplicates the bodies of all the loops, and not\n"
    "                              only those with arrays accesses\n"
    " --no-loop-duplication        constructs back-edges for all the loops\n"
    " --no-dependencies            ignores existing dependencies in the program\n"
    " --print-graph                prints the AEG into graph.dot\n"
    " --max-po-var <n>             limits the number of variables per cycle\n"
    " --max-po-trans <n>           limits the size of pos^+ in terms of pos\n"
    " --ignore-arrays              ignores cycles with multiple accesses to the\n"
    "                              same array\n"
    "\n";
}
