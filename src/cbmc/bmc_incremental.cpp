/*******************************************************************\

Module: Incremental Symbolic Execution of ANSI-C

Author: Peter Schrammel, Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>
#include <limits>

#include <goto-symex/slice.h>

#include "bmc_incremental.h"


 /*******************************************************************\
 
Function: bmc_incrementalt::step
 
  Inputs: 
 
 Outputs: 
 
 Purpose: run incremental BMC loop
 
 \*******************************************************************/
 
safety_checkert::resultt bmc_incrementalt::step(
  const goto_functionst &goto_functions)
{
  try
  {
    //We count only new assertions.
    symex.total_vccs = 0;
    symex.remaining_vccs = 0;

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

    slice(); 
 
    resultt result = show(goto_functions);
    if(result != UNKNOWN)
      return result;
 
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

Function: bmc_incrementalt::run
 
  Inputs: 

 Outputs: 

 Purpose: run incremental BMC loop

\*******************************************************************/

safety_checkert::resultt bmc_incrementalt::run(
  const goto_functionst &goto_functions)
{
  safety_checkert::resultt result = initialize();
  while(result == safety_checkert::UNKNOWN)
  { 
    result = step();

    //check unwinding assertions
    if(result == safety_checkert::UNKNOWN &&
       symex.add_loop_check())
    {
      resultt loop_check_result = 
	decide(goto_functions,prop_conv,false);
      bool earliest_loop_exit = 
	options.get_bool_option("earliest-loop-exit");
      if(loop_check_result==SAFE)
	symex.update_loop_info(earliest_loop_exit ? false : true);
      else if(loop_check_result==UNSAFE)
	symex.update_loop_info(earliest_loop_exit ? true : false);
    } 
  }

  return result;
}

/*******************************************************************\

Function: bmc_incrementalt::setup_unwind

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bmc_incrementalt::setup_unwind()
{
  bmct::setup_unwind();

  if(options.get_option("unwind-min")!="")
    symex.incr_min_unwind=options.get_unsigned_int_option("unwind-min");
  if(options.get_option("unwind-max")!="")
    symex.incr_max_unwind=options.get_unsigned_int_option("unwind-max");
  else
    symex.incr_max_unwind = std::numeric_limits<unsigned>::max();

  status() << "Using incremental mode" << eom;
  prop_conv.set_all_frozen();
  equation.is_incremental = true;
}
