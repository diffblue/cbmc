/*******************************************************************\

Module: Main Module 

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <fstream>
#include <iostream>
#include <memory>
#include <cstdlib>

#include <util/config.h>
#include <util/expr_util.h>
#include <util/i2string.h>

#include <goto-programs/goto_convert_functions.h>
#include <goto-programs/remove_function_pointers.h>
#include <goto-programs/remove_skip.h>
#include <goto-programs/goto_inline.h>
#include <goto-programs/show_claims.h>
#include <goto-programs/set_claims.h>
#include <goto-programs/read_goto_binary.h>
#include <goto-programs/write_goto_binary.h>
#include <goto-programs/interpreter.h>
#include <goto-programs/string_abstraction.h>
#include <goto-programs/string_instrumentation.h>
#include <goto-programs/loop_ids.h>
#include <goto-programs/reachability_slicer.h>
#include <goto-programs/link_to_library.h>

#include <pointer-analysis/value_set_analysis.h>
#include <pointer-analysis/goto_program_dereference.h>
#include <pointer-analysis/add_failed_symbols.h>
#include <pointer-analysis/show_value_sets.h>

#include <analyses/natural_loops.h>
#include <analyses/local_may_alias.h>
#include <analyses/goto_check.h>
#include <analyses/call_graph.h>
#include <analyses/interval_analysis.h>

#include "parseoptions.h"
#include "version.h"
#include "document_claims.h"
#include "uninitialized.h"
#include "full_slicer.h"
#include "show_locations.h"
#include "points_to.h"
#include "alignment_checks.h"
#include "race_check.h"
#include "nondet_volatile.h"
#include "interrupt.h"
#include "mmio.h"
#include "stack_depth.h"
#include "nondet_static.h"
#include "rw_set.h"
#include "concurrency.h"
#include "dump_c.h"
#include "dot.h"
#include "havoc_loops.h"
#include "k_induction.h"
#include "function.h"
#include "branch.h"
#include "wmm/weak_memory.h"
#include "call_sequences.h"
#include "accelerate/accelerate.h"

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
      namespacet ns(symbol_table);

      if(!cmdline.isset("inline"))
      {
        status("Function Pointer Removal");
        remove_function_pointers(symbol_table, goto_functions, false);

        status("Partial Inlining");
        goto_partial_inline(goto_functions, ns, ui_message_handler);
      }
    
      status("Pointer Analysis");
      value_set_analysist value_set_analysis(ns);
      value_set_analysis(goto_functions);

      show_value_sets(get_ui(), goto_functions, value_set_analysis);
      return 0;
    }

    if(cmdline.isset("show-local-may-alias"))
    {
      namespacet ns(symbol_table);

      if(!cmdline.isset("inline"))
      {
        status("Function Pointer Removal");
        remove_function_pointers(symbol_table, goto_functions, false);

        status("Partial Inlining");
        goto_partial_inline(goto_functions, ns, ui_message_handler);
      }
    
      forall_goto_functions(it, goto_functions)
      {
        local_may_aliast local_may_alias(it->second);
        std::cout << ">>>>" << std::endl;
        std::cout << ">>>> " << it->first << std::endl;
        std::cout << ">>>>" << std::endl;
        local_may_alias.output(std::cout, it->second, ns);
        std::cout << std::endl;
      }

      return 0;
    }

    if(cmdline.isset("show-points-to"))
    {
      namespacet ns(symbol_table);

      if(!cmdline.isset("inline"))
      {
        status("Function Pointer Removal");
        remove_function_pointers(symbol_table, goto_functions, false);

        status("Partial Inlining");
        goto_partial_inline(goto_functions, ns, ui_message_handler);
      }
    
      status("Pointer Analysis");
      points_tot points_to;
      points_to(goto_functions);
      points_to.output(std::cout);
      return 0;
    }
    
    if(cmdline.isset("show-call-sequences"))
    {
      show_call_sequences(goto_functions);
      return 0;
    }

    if(cmdline.isset("show-rw-set"))
    {
      namespacet ns(symbol_table);

      if(!cmdline.isset("inline"))
      {
        status("Function Pointer Removal");
        remove_function_pointers(symbol_table, goto_functions, false);

        status("Partial Inlining");
        goto_partial_inline(goto_functions, ns, ui_message_handler);
      }
    
      status("Pointer Analysis");
      value_set_analysist value_set_analysis(ns);
      value_set_analysis(goto_functions);
      
      const symbolt &symbol=ns.lookup("c::main");
      symbol_exprt main(symbol.name, symbol.type);
      
      std::cout << rw_set_functiont(value_set_analysis, ns, goto_functions, main);
      return 0;
    }

    if(cmdline.isset("show-symbol-table"))
    {
      show_symbol_table();
      return 0;
    }

    if(cmdline.isset("show-uninitialized"))
    {
      show_uninitialized(symbol_table, goto_functions, std::cout);
      return 0;
    }

    if(cmdline.isset("interpreter"))
    {
      status("Starting interpreter");
      interpreter(symbol_table, goto_functions);
      return 0;
    }

    if(cmdline.isset("show-claims"))
    {
      const namespacet ns(symbol_table);
      show_claims(ns, get_ui(), goto_functions);
      return 0;
    }

    if(cmdline.isset("document-claims-html"))
    {
      const namespacet ns(symbol_table);
      document_claims_html(ns, goto_functions, std::cout);
      return 0;
    }

    if(cmdline.isset("document-claims-latex"))
    {
      const namespacet ns(symbol_table);
      document_claims_latex(ns, goto_functions, std::cout);
      return 0;
    }

    if(cmdline.isset("show-loops"))
    {
      show_loop_ids(get_ui(), goto_functions);
      return 0;
    }

    if(cmdline.isset("show-natural-loops"))
    {
      const namespacet ns(symbol_table);
      show_natural_loops(goto_functions);
      return 0;
    }

    if(cmdline.isset("show-goto-functions"))
    {
      namespacet ns(symbol_table);
      goto_functions.output(ns, std::cout);
      return 0;
    }

    if(cmdline.isset("show-struct-alignment"))
    {
      print_struct_alignment_problems(symbol_table, std::cout);
      return 0;
    }

    if(cmdline.isset("show-locations"))
    {
      show_locations(get_ui(), goto_functions);
      return 0;
    }

    if(cmdline.isset("dump-c") || cmdline.isset("dump-cpp"))
    {
      const bool is_cpp=cmdline.isset("dump-cpp");
      namespacet ns(symbol_table);
      
      if(cmdline.args.size()==2)
      {
        std::ofstream out(cmdline.args[1].c_str());
        if(!out)
        {
          error("failed to write to "+cmdline.args[1]);
          return 10;
        }
        (is_cpp ? dump_cpp : dump_c)(goto_functions, ns, out);
      }
      else
        (is_cpp ? dump_cpp : dump_c)(goto_functions, ns, std::cout);
        
      return 0;
    }
    
    if(cmdline.isset("call-graph"))
    {
      call_grapht call_graph(goto_functions);
      
      if(cmdline.isset("xml"))
        call_graph.output_xml(std::cout);
      else if(cmdline.isset("dot"))
        call_graph.output_dot(std::cout);
      else
        call_graph.output(std::cout);

      return 0;
    }
    
    if(cmdline.isset("dot"))
    {
      namespacet ns(symbol_table);
      
      if(cmdline.args.size()==2)
      {
        std::ofstream out(cmdline.args[1].c_str());
        if(!out)
        {
          error("failed to write to "+cmdline.args[1]);
          return 10;
        }

        dot(goto_functions, ns, out);
      }
      else
        dot(goto_functions, ns, std::cout);
        
      return 0;
    }

    if(cmdline.isset("accelerate"))
    {
      namespacet ns(symbol_table);
      accelerate_functions(goto_functions, ns);
      remove_skip(goto_functions);
      goto_functions.update();
    }
    
    // write new binary?
    if(cmdline.args.size()==2)
    {
      status("Writing GOTO program to "+cmdline.args[1]);
      
      if(write_goto_binary(
        cmdline.args[1], symbol_table, goto_functions, get_message_handler()))
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
    symbol_table, goto_functions, get_message_handler()))
    throw 0;

  config.ansi_c.set_from_symbol_table(symbol_table);
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

  // check undefined shifts
  if(cmdline.isset("undefined-shift-check"))
    options.set_option("undefined-shift-check", true);
  else
    options.set_option("undefined-shift-check", false);

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

  // unwind loops 
  if(cmdline.isset("unwind"))
  {
    status("Unwinding loops");
    options.set_option("unwind", cmdline.getval("unwind"));
  }

  // we add the library, as some analyses benefit
  
  status("Adding CPROVER library");      
  link_to_library(symbol_table, goto_functions, ui_message_handler);

  namespacet ns(symbol_table);

  // now do full inlining, if requested
  if(cmdline.isset("inline"))
  {
    status("Function Pointer Removal");
    remove_function_pointers(
      symbol_table, goto_functions, cmdline.isset("pointer-check"));

    status("Performing full inlining");
    goto_inline(goto_functions, ns, ui_message_handler);
  }

  // add generic checks, if needed
  goto_check(ns, options, goto_functions);
  
  // check for uninitalized local varibles
  if(cmdline.isset("uninitialized-check"))
  {
    status("Adding checks for uninitialized local variables");
    add_uninitialized_locals_assertions(symbol_table, goto_functions);
  }
  
  // check for maximum call stack size
  if(cmdline.isset("stack-depth"))
  {
    status("Adding check for maximum call stack size");
    stack_depth(symbol_table, goto_functions,
        atoi(cmdline.getval("stack-depth")));
  }

  // ignore default/user-specified initialization of variables with static
  // lifetime
  if(cmdline.isset("nondet-static"))
  {
    status("Adding nondeterministic initialization of static/global variables");
    nondet_static(ns, goto_functions);
  }

  if(cmdline.isset("string-abstraction"))
  {
    status("String Abstraction");
    string_abstraction(symbol_table,
      get_message_handler(), goto_functions);
  }

  if(cmdline.isset("remove-pointers") ||
     cmdline.isset("race-check") ||
     cmdline.isset("mm") ||
     cmdline.isset("isr") ||
     cmdline.isset("concurrency"))
  {
    if(!cmdline.isset("inline"))
    {
      status("Function Pointer Removal");
      remove_function_pointers(symbol_table, goto_functions, cmdline.isset("pointer-check"));

      // do partial inlining
      status("Partial Inlining");
      goto_partial_inline(goto_functions, ns, ui_message_handler);
    }
    
    status("Pointer Analysis");
    value_set_analysist value_set_analysis(ns);
    value_set_analysis(goto_functions);

    if(cmdline.isset("remove-pointers"))
    {
      // removing pointers
      status("Removing Pointers");
      remove_pointers(
        goto_functions, symbol_table, value_set_analysis);
    }

    if(cmdline.isset("race-check"))
    {
      status("Adding Race Checks");
      race_check(
        value_set_analysis,
        symbol_table,
        goto_functions);
    }

    if(cmdline.isset("mm"))
    {
      std::string mm=cmdline.getval("mm");
      memory_modelt model;

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
        ( cmdline.isset("unwind")?atoi(cmdline.getval("unwind")):0 );
      const unsigned max_var =
        ( cmdline.isset("max-var")?atoi(cmdline.getval("max-var")):0 );
      const unsigned max_po_trans =
        ( cmdline.isset("max-po-trans")?atoi(cmdline.getval("max-po-trans")):0 );

      if(mm=="tso")
      {
        status("Adding weak memory (TSO) Instrumentation");
        model=TSO;
      }
      else if(mm=="pso")
      {
        status("Adding weak memory (PSO) Instrumentation");
        model=PSO;
      }
      else if(mm=="rmo")
      {
        status("Adding weak memory (RMO) Instrumentation");
        model=RMO;
      }
      else if(mm=="power")
      {
        status("Adding weak memory (Power) Instrumentation");
        model=Power;
      }
      else
      {
        error("Unknown weak memory model");
        model=Unknown;
      }

      if(model!=Unknown)
        weak_memory(
          model,
          value_set_analysis,
          symbol_table,
          goto_functions,
          cmdline.isset("scc"),
          inst_strategy,
          unwind_loops,
          !cmdline.isset("cfg-kill"),
          cmdline.isset("no-dependencies"),
          max_var,
          max_po_trans,
          !cmdline.isset("no-po-rendering"),
          cmdline.isset("render-cluster-file"),
          cmdline.isset("render-cluster-function"),
          cmdline.isset("cav11"),
          cmdline.isset("hide-internals"));
    }

    // Interrupt handler
    if(cmdline.isset("isr"))
    {
      status("Instrumenting interrupt handler");
      interrupt(
        value_set_analysis,
        symbol_table,
        goto_functions,
        cmdline.getval("isr"));
    }

    // Memory-mapped I/O
    if(cmdline.isset("mmio"))
    {
      status("Instrumenting memory-mapped I/O");
      mmio(
        value_set_analysis,
        symbol_table,
        goto_functions);
    }

    if(cmdline.isset("concurrency"))
    {
      status("Sequentializing concurrency");
      concurrency(
        value_set_analysis,
        symbol_table,
        goto_functions);
    }
  }  

  if(cmdline.isset("interval-analysis"))
  {
    status("Interval analysis");
    interval_analysis(goto_functions);
  }

  if(cmdline.isset("havoc-loops"))
  {
    status("Havocing loops");
    havoc_loops(goto_functions);
  }

  if(cmdline.isset("k-induction"))
  {
    bool base_case=cmdline.isset("base-case");
    bool step_case=cmdline.isset("step-case");

    if(step_case && base_case)
      throw "please specify only one of --step-case and --base-case";
    else if(!step_case && !base_case)
      throw "please specify one of --step-case and --base-case";

    unsigned k=atoi(cmdline.getval("k-induction"));
    
    if(k==0)
      throw "please give k>=1";

    status("Instrumenting k-induction for k="+i2string(k)+", "+
           (base_case?"base case":"step case"));
    
    k_induction(goto_functions, base_case, step_case, k);
  }

  if(cmdline.isset("function-enter"))
  {
    status("Function enter instrumentation");
    function_enter(
      symbol_table,
      goto_functions,
      cmdline.getval("function-enter"));
  }

  if(cmdline.isset("function-exit"))
  {
    status("Function exit instrumentation");
    function_exit(
      symbol_table,
      goto_functions,
      cmdline.getval("function-exit"));
  }

  if(cmdline.isset("branch"))
  {
    status("Branch instrumentation");
    branch(
      symbol_table,
      goto_functions,
      cmdline.getval("branch"));
  }

  // add failed symbols
  add_failed_symbols(symbol_table);
  
  // recalculate numbers, etc.
  goto_functions.update();

  // add loop ids
  goto_functions.compute_loop_numbers();
  
  // nondet volatile?
  if(cmdline.isset("nondet-volatile"))
  {
    status("Making volatile variables non-deterministic");
    nondet_volatile(symbol_table, goto_functions);
  }

  // reachability slice?
  if(cmdline.isset("reachability-slice"))
  {
    status("Performing a reachability slice");
    reachability_slicer(goto_functions);
  }

  // full slice?
  if(cmdline.isset("full-slice"))
  {
    status("Performing a full slice");
    full_slicer(goto_functions);
  }
  
  // label the assertions
  label_claims(goto_functions);
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
    "* *     Goto-Instrument " GOTO_INSTRUMENT_VERSION " - Copyright (C) 2008-2013       * *\n"
    "* *                    Daniel Kroening                      * *\n"
    "* *                 kroening@kroening.com                   * *\n"
    "\n"
    "Usage:                       Purpose:\n"
    "\n"
    " goto-instrument [-?] [-h] [--help]  show help\n"
    " goto-instrument in out              perform instrumentation\n"
    "\n"
    "Main options:\n"
    " --document-claims-html       generate HTML claim documentation\n"
    " --document-claims-latex      generate Latex claim documentation\n"
    " --dump-c                     generate C source\n"
    " --dot                        generate CFG graph in DOT format\n"
    " --interpreter                do concrete execution\n"
    "\n"
    "Diagnosis:\n"
    " --show-loops                 show the loops in the program\n"
    " --show-claims                show claims\n"
    " --show-symbol-table          show symbol table\n"
    " --show-goto-functions        show goto program\n"
    " --show-struct-alignment      show struct members that might be concurrently accessed\n"
    " --show-natural-loops         show natural loop heads\n"
    "\n"
    "Safety checks:\n"
    " --no-assertions              ignore user assertions\n"
    " --bounds-check               add array bounds checks\n"
    " --div-by-zero-check          add division by zero checks\n"
    " --pointer-check              add pointer checks\n"
    " --signed-overflow-check      add arithmetic over- and underflow checks\n"
    " --unsigned-overflow-check    add arithmetic over- and underflow checks\n"
    " --undefined-shift-check      add range checks for shift distances\n"
    " --nan-check                  add floating-point NaN checks\n"
    " --uninitialized-check        add checks for uninitialized locals (experimental)\n"
    " --error-label label          check that label is unreachable\n"
    " --stack-depth n              add check that call stack size of non-inlined functions never exceeds n\n"
    "\n"
    "Semantic transformations:\n"
    " --nondet-volatile            makes reads from volatile variables non-deterministic\n"
    " --unwind <n>                 unwinds the loopds <n> times\n"
    " --isr <function>             instruments an interrupt service routine\n"
    " --mmio                       instruments memory-mapped I/O\n"
    " --nondet-static              add nondeterministic initialization of variables with static lifetime\n"
    " --check-invariant function   instruments invariant checking function\n"
    "\n"
    "Loop transformations:\n"
    " --k-induction <k>            check loops with k-induction\n"
    " --step-case                  k-induction: do step-case\n"
    " --base-case                  k-induction: do base-case\n"
    " --havoc-loops                over-approximate all loops\n"
    " --accelerate                 add loop accelerators\n"
    "\n"
    "Memory model instrumentations:\n"
    " --mm <tso,pso,rmo,power>     instruments a weak memory model\n"
    " --scc                        detects critical cycles per SCC (one thread per SCC)\n"
    " --one-event-per-cycle        only instruments one event per cycle\n"
    " --minimum-interference       instruments an optimal number of events\n"
    " --my-events                  only instruments events whose ids appear in inst.evt\n"
    " --cfg-kill                   enables symbolic execution used to reduce spurious cycles\n"
    " --no-dependencies            no dependency analysis\n"
    " --no-po-rendering            no representation of the threads in the dot\n"
    " --render-cluster-file        clusterises the dot by files\n"
    " --render-cluster-function    clusterises the dot by functions\n"
    "\n"
    "Slicing:\n"
    " --reachability-slicer        slice away instructions that can't reach assertions\n"
    " --full-slice                 slice away instructions that don't affect assertions\n"
    "\n"
    "Other options:\n"
    " --version                    show version and exit\n"
    " --xml-ui                     use XML-formatted output\n"
    "\n";
}
