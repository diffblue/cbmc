/*******************************************************************\

Module: Incremental Symbolic Execution of ANSI-C

Author: Peter Schrammel, Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <fstream>
#include <iostream>
#include <memory>

#include <util/string2int.h>
#include <util/i2string.h>
#include <util/source_location.h>
#include <util/time_stopping.h>
#include <util/message_stream.h>

#include <langapi/mode.h>
#include <langapi/languages.h>
#include <langapi/language_util.h>

#include <ansi-c/ansi_c_language.h>

#include <goto-programs/xml_goto_trace.h>
#include <goto-programs/graphml_goto_trace.h>

#include <goto-symex/build_goto_trace.h>
#include <goto-symex/slice.h>
#include <goto-symex/slice_by_trace.h>
#include <goto-symex/memory_model_sc.h>
#include <goto-symex/memory_model_tso.h>
#include <goto-symex/memory_model_pso.h>

#include "counterexample_beautification.h"
#include "bmc_incremental_one_loop.h"

/*******************************************************************\

Function: bmc_incremental_one_loopt::initialize

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

safety_checkert::resultt bmc_incremental_one_loopt::initialize()
{
  const std::string mm=options.get_option("mm");
 
  if(mm.empty() || mm=="sc")
    memory_model=std::unique_ptr<memory_model_baset>(new memory_model_sct(ns));
  else if(mm=="tso")
    memory_model=std::unique_ptr<memory_model_baset>(new memory_model_tsot(ns));
  else if(mm=="pso")
    memory_model=std::unique_ptr<memory_model_baset>(new memory_model_psot(ns));
  else
  {
    error() << "Invalid memory model " << mm
            << " -- use one of sc, tso, pso" << eom;
    return safety_checkert::ERROR;
  }
  symex.set_message_handler(get_message_handler());
  symex.options=options;
 
  status() << "Starting Bounded Model Checking" << eom;
 
  symex.last_source_location.make_nil();
 
  // get unwinding info
  setup_unwind();
 
  return safety_checkert::UNKNOWN;
}
 
/*******************************************************************\
 
Function: bmc_incremental_one_loopt::step
 
  Inputs: 
 
 Outputs: 
 
 Purpose: run incremental BMC loop
 
 \*******************************************************************/
 
safety_checkert::resultt bmc_incremental_one_loopt::step()
{
  try
  {
    // perform symbolic execution
    bool symex_done = symex(symex_state,goto_functions,
      goto_functions.function_map.at(goto_functions.entry_point()).body);
 
    // add a partial ordering, if required    
    if(equation.has_threads())
    {
      memory_model->set_message_handler(get_message_handler());
      (*memory_model)(equation);
    }
 
    statistics() << "size of program expression: "
		 << equation.SSA_steps.size()
		 << " steps" << eom;
 
    undo_slice(equation); //undo all previous slicings
 
    if(options.get_option("slice-by-trace")!="")
    {
      symex_slice_by_tracet symex_slice_by_trace(ns);
 
      symex_slice_by_trace.slice_by_trace
	(options.get_option("slice-by-trace"), equation);
    }
 
    if(equation.has_threads())
    {
      // we should build a thread-aware SSA slicer
      statistics() << "no slicing due to threads" << eom;
    }
    else
    {
      if(options.get_bool_option("slice-formula"))
      {
	slice(equation);
	statistics() << "slicing removed "
		     << equation.count_ignored_SSA_steps()
		     << " assignments" << eom;
      }
      else
      {
	if(options.get_option("cover")=="")
	{
	  simple_slice(equation);
	  statistics() << "simple slicing removed "
		       << equation.count_ignored_SSA_steps()
		       << " assignments" << eom;
	}
      }
    }
 
    {
      statistics() << "Generated " << symex.total_vccs
		   << " VCC(s), " << symex.remaining_vccs
		   << " remaining after simplification" << eom;
    }
 
    if(options.get_bool_option("show-vcc"))
    {
      show_vcc();
      return safety_checkert::SAFE; // to indicate non-error
    }
     
    if(options.get_option("cover")!="")
    {
      std::string criterion=options.get_option("cover");
      return cover(goto_functions, criterion)?
	safety_checkert::ERROR:safety_checkert::SAFE;
    }

    if(options.get_bool_option("program-only"))
    {
      show_program();
      return safety_checkert::SAFE;
    }
 
    resultt result = safety_checkert::UNKNOWN;

    // any properties to check at all?
    if(symex.remaining_vccs==0)
    {
      report_success();
      result = safety_checkert::SAFE;
    }
    else
    {
      if(options.get_bool_option("all-properties"))
        result = all_properties(goto_functions, prop_conv);
      else
	result = decide(goto_functions, prop_conv);
    }

    resultt term_cond = options.get_bool_option("stop-when-unsat") ? 
      safety_checkert::UNSAFE : safety_checkert::SAFE;
    return ((result==term_cond) && !symex_done) ?
              safety_checkert::UNKNOWN : 
	      result;
  }
 
  catch(std::string &error_str)
  {
    error() << error_str << eom;
    return safety_checkert::ERROR;
  }

  catch(const char *error_str)
  {
    error() << error_str << eom;
    return safety_checkert::ERROR;
  }

  catch(std::bad_alloc)
  {
    error() << "Out of memory" << eom;
    return safety_checkert::ERROR;
  }

  assert(false);
}
 
/*******************************************************************\
 
Function: bmc_incremental_one_loopt::run
 
  Inputs: 

 Outputs: 

 Purpose: run incremental BMC loop

\*******************************************************************/

safety_checkert::resultt bmc_incremental_one_loopt::run()
{
  safety_checkert::resultt result = initialize();
  while(result == safety_checkert::UNKNOWN)
  { 
    result = step();
  }

  return result;
}

/*******************************************************************\

Function: bmc_incremental_one_loopt::decide

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

safety_checkert::resultt bmc_incremental_one_loopt::decide(
  const goto_functionst &goto_functions,
  prop_convt &prop_conv, 
  bool show_report)
{
  prop_conv.set_message_handler(get_message_handler());

  switch(run_decision_procedure(prop_conv))
  {
  case decision_proceduret::D_UNSATISFIABLE:
    if(show_report)
      report_success();
 
    return SAFE;

  case decision_proceduret::D_SATISFIABLE:
    if(show_report)
    {
      if(options.get_bool_option("beautify"))
        counterexample_beautificationt()(
          dynamic_cast<bv_cbmct &>(prop_conv), equation, ns);
   
      error_trace();
      report_failure();
    }
    return UNSAFE;
 
  default:
    if(options.get_bool_option("dimacs") ||
       options.get_option("outfile")!="")
      return ERROR;
      
    error() << "decision procedure failed" << eom;

    return ERROR;
  }
}

/*******************************************************************\

Function: bmc_incremental_one_loopt::setup_unwind

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bmc_incremental_one_loopt::setup_unwind()
{
  bmct::setup_unwind();

  if(options.get_option("unwind-min")!="")
    symex.incr_min_unwind=options.get_unsigned_int_option("unwind-min");
  if(options.get_option("unwind-max")!="")
    symex.incr_max_unwind=options.get_unsigned_int_option("unwind-max");
  symex.ignore_assertions = (symex.incr_min_unwind>=2) &&
    options.get_bool_option("ignore-assertions-before-unwind-min");
  symex.incr_loop_id = options.get_option("incremental-check");

  status() << "Using incremental mode" << eom;
  prop_conv.set_all_frozen();
  equation.is_incremental = true;
}
