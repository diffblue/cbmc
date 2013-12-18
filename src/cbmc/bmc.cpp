/*******************************************************************\

Module: Symbolic Execution of ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <fstream>
#include <cstdlib>
#include <iostream>
#include <memory>

#include <util/i2string.h>
#include <util/location.h>
#include <util/time_stopping.h>
#include <util/message_stream.h>
#include <util/signal_catcher.h>

#include <langapi/mode.h>
#include <langapi/languages.h>
#include <langapi/language_util.h>

#include <ansi-c/ansi_c_language.h>

#include <goto-symex/goto_trace.h>
#include <goto-symex/build_goto_trace.h>
#include <goto-symex/slice.h>
#include <goto-symex/slice_by_trace.h>
#include <goto-symex/xml_goto_trace.h>
#include <goto-symex/memory_model_sc.h>
#include <goto-symex/memory_model_tso.h>
#include <goto-symex/memory_model_pso.h>

#include <solvers/sat/satcheck_minisat2.h>

#include "bmc.h"
#include "bv_cbmc.h"
#include "counterexample_beautification.h"

/*******************************************************************\

Function: bmct::do_unwind_module

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bmct::do_unwind_module(
  decision_proceduret &decision_procedure)
{
}

/*******************************************************************\

Function: bmct::error_trace

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bmct::error_trace(const prop_convt &prop_conv)
{
  status() << "Building error trace" << eom;

  goto_tracet goto_trace;
  build_goto_trace(equation, prop_conv, ns, goto_trace);
  
  #if 0
  if(options.get_option("vcd")!="")
  {
    if(options.get_option("vcd")=="-")
      output_vcd(ns, goto_trace, std::cout);
    else
    {
      std::ofstream out(options.get_option("vcd").c_str());
      output_vcd(ns, goto_trace, out);
    }
  }
  #endif
  
  switch(ui)
  {
  case ui_message_handlert::PLAIN:
    std::cout << "\n" << "Counterexample:" << "\n";
    show_goto_trace(std::cout, ns, goto_trace);
    break;
  
  case ui_message_handlert::XML_UI:
    {
      xmlt xml;
      convert(ns, goto_trace, xml);
      std::cout << xml << "\n";
    }
    break;
  
  default:
    assert(false);
  }
}

/*******************************************************************\

Function: bmct::do_conversion

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bmct::do_conversion(prop_convt &prop_conv)
{
  // convert HDL
  do_unwind_module(prop_conv);

  // convert SSA
  equation.convert(prop_conv);

  // the 'extra constraints'
  forall_expr_list(it, bmc_constraints)
    prop_conv.set_to_true(*it);
}

/*******************************************************************\

Function: bmct::run_decision_procedure

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

decision_proceduret::resultt
bmct::run_decision_procedure(prop_convt &prop_conv)
{
  status() << "Passing problem to " 
           << prop_conv.decision_procedure_text() << eom;

  prop_conv.set_message_handler(get_message_handler());
  prop_conv.set_verbosity(get_verbosity());

  // stop the time
  fine_timet sat_start=current_time();
  
  do_conversion(prop_conv);  

#if 0
  statistics() << "ignored: " <<  equation.count_ignored_SSA_steps() << eom;
  statistics() << "converted: " <<  equation.count_converted_SSA_steps() << eom;
#endif

  status() << "Running " << prop_conv.decision_procedure_text() << eom;

  decision_proceduret::resultt dec_result=prop_conv.dec_solve();
  // output runtime

  {
    fine_timet sat_stop=current_time();
    status() << "Runtime decision procedure: "
             << (sat_stop-sat_start) << "s" << eom;
  }

  return dec_result;
}

/*******************************************************************\

Function: bmct::report_success

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bmct::report_success()
{
  result() << "VERIFICATION SUCCESSFUL" << eom;

  switch(ui)
  {
  case ui_message_handlert::PLAIN:
    break;
    
  case ui_message_handlert::XML_UI:
    {
      xmlt xml("cprover-status");
      xml.data="SUCCESS";
      std::cout << xml;
      std::cout << "\n";
    }
    break;
    
  default:
    assert(false);
  }
}

/*******************************************************************\

Function: bmct::report_failure

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bmct::report_failure()
{
  result() << "VERIFICATION FAILED" << eom;

  switch(ui)
  {
  case ui_message_handlert::PLAIN:
    break;
    
  case ui_message_handlert::XML_UI:
    {
      xmlt xml("cprover-status");
      xml.data="FAILURE";
      std::cout << xml;
      std::cout << "\n";
    }
    break;
    
  default:
    assert(false);
  }
}

/*******************************************************************\

Function: bmct::show_program

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bmct::show_program()
{
  unsigned count=1;

  languagest languages(ns, new_ansi_c_language());
  
  std::cout << "\n" << "Program constraints:" << "\n";

  for(symex_target_equationt::SSA_stepst::const_iterator
      it=equation.SSA_steps.begin();
      it!=equation.SSA_steps.end(); it++)
  {
    if(it->is_assignment())
    {
      std::string string_value;
      languages.from_expr(it->cond_expr, string_value);
      std::cout << "(" << count << ") " << string_value << "\n";

      if(!it->guard.is_true())
      {
        languages.from_expr(it->guard, string_value);
        std::cout << std::string(i2string(count).size()+3, ' ');
        std::cout << "guard: " << string_value << "\n";
      }
      
      count++;
    }
    else if(it->is_assert())
    {
      std::string string_value;
      languages.from_expr(it->cond_expr, string_value);
      std::cout << "(" << count << ") ASSERT("
                << string_value <<") " << "\n";

      if(!it->guard.is_true())
      {
        languages.from_expr(it->guard, string_value);
        std::cout << std::string(i2string(count).size()+3, ' ');
        std::cout << "guard: " << string_value << "\n";
      }

      count++;
    }  
  }
}

/*******************************************************************\

Function: bmct::run

  Inputs: goto functions

 Outputs: true, if FAILED or an error occurred, false if SUCCEEDED

 Purpose: run BMC

\*******************************************************************/

bool bmct::run(const goto_functionst &goto_functions)
{
  const std::string mm=options.get_option("mm");
  std::auto_ptr<memory_model_baset> memory_model(0);
  if(mm.empty() || mm=="sc")
    memory_model.reset(new memory_model_sct(ns));
  else if(mm=="tso")
    memory_model.reset(new memory_model_tsot(ns));
  else if(mm=="pso")
    memory_model.reset(new memory_model_psot(ns));
  else
    throw "Invalid memory model "+mm+" -- use one of sc, tso, pso";

  //symex.total_claims=0;
  symex.set_message_handler(get_message_handler());
  symex.set_verbosity(get_verbosity());
  symex.options=options;

  status() << "Starting Bounded Model Checking" << eom;

  symex.last_location.make_nil();

  try
  {
    // get unwinding info
    setup_unwind();

    bool verification_result = false; //true = "FAILED"

    goto_functionst::function_mapt::const_iterator it=
      goto_functions.function_map.find(ID_main);
    if(it==goto_functions.function_map.end())
      throw "main symbol not found; please set an entry point";
    const goto_programt &body=it->second.body;
    goto_symext::statet symex_state;

    // perform symbolic execution
    bool symex_done = false;

    //THE MAIN LOOP FOR INCREMENTAL UNWINDING
    while(!symex_done) { 
      symex_done = symex(symex_state,goto_functions,body);

      undo_slice(equation); //undo all previous slicings

#if 0
      equation.output(std::cout);
#endif

      // add a partial ordering, if required    
      if(equation.has_threads())
      {
        memory_model->set_message_handler(get_message_handler());
        (*memory_model)(equation); // TODO: not clear whether supports incremental symex
      }

      statistics() << "size of program expression: "
		   << equation.SSA_steps.size()
		   << " steps" << eom;

      try
	{
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
		  simple_slice(equation);
		  statistics() << "simple slicing removed "
			       << equation.count_ignored_SSA_steps()
			       << " assignments" << eom;
		}
	    }

	  if(options.get_bool_option("program-only"))
	    {
	      show_program();
	      return false;
	    }

	  {
	    statistics() << "Generated " << symex.total_claims
			 << " VCC(s), " << symex.remaining_claims
			 << " remaining after simplification" << eom;
	  }

	  if(options.get_bool_option("show-vcc"))
	    {
	      show_vcc();
	      return false;
	    }
  
	  if(options.get_bool_option("cover-assertions"))
	    {
              if(options.get_option("incremental-check")!="")
                throw "incremental vacuity checks not supported";
	      cover_assertions(goto_functions);
	      return false;
	    }
	  if(symex.remaining_claims==0)
	    {
	      report_success();
              continue;
	    }

          //call decision procedure
	  if(options.get_bool_option("all-claims")) {
	    if(all_claims(goto_functions)) return true; //all claims FAILED, exit
	  }
          else {
            verification_result = decide(symex.prop_conv);
            if(verification_result) return true; //bug found, exit
	  }
	}
      catch(std::string &error_str)
	{
	  error(error_str);
	  return true;
	}
      catch(const char *error_str)
	{
	  error(error_str);
	  return true;
	}

    } //while

    return verification_result;
  }
  catch(std::string &error_str)
  {
    message_streamt message_stream(get_message_handler());
    message_stream.err_location(symex.last_location);
    message_stream.error(error_str);
    return true;
  }
  catch(const char *error_str)
  {
    message_streamt message_stream(get_message_handler());
    message_stream.err_location(symex.last_location);
    message_stream.error(error_str);
    return true;
  }
  catch(std::bad_alloc)
  {
    error() << "Out of memory" << eom;
    return true;
  }
  catch(signal_catchert::exceptiont& e)
  {
    error() << e.what() << eom;
    return true;
  }
}

/*******************************************************************\

Function: bmct::decide

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool bmct::decide(prop_convt &prop_conv)
{
  prop_conv.set_message_handler(get_message_handler());
  prop_conv.set_verbosity(get_verbosity());
 
  if(options.get_bool_option("dimacs")) {
    do_conversion(prop_conv);
    return write_dimacs(prop_conv);
  }

  bool result=true;

  switch(run_decision_procedure(prop_conv))
  {
  case decision_proceduret::D_UNSATISFIABLE:
    result=false;
    report_success();
    break;

  case decision_proceduret::D_SATISFIABLE:
    if(options.get_bool_option("beautify")) {
      bv_cbmct& bv_cbmc = dynamic_cast<bv_cbmct&>(prop_conv);
      counterexample_beautificationt()(
        bv_cbmc, equation, ns);
    }
    error_trace(prop_conv);
    report_failure();
    break;

  default:
    error() << "decision procedure failed" << eom;
  }

  return result;
}

/*******************************************************************\

Function: bmct::setup_unwind

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bmct::setup_unwind()
{
  const std::string &set=options.get_option("unwindset");
  unsigned int length=set.length();

  for(unsigned int idx=0; idx<length; idx++)
  {
    std::string::size_type next=set.find(",", idx);
    std::string val=set.substr(idx, next-idx);

    long thread_nr=-1;
    if(!val.empty() &&
       isdigit(val[0]) &&
       val.find(":")!=std::string::npos)
    {
      std::string nr=val.substr(0, val.find(":"));
      thread_nr=atol(nr.c_str());
      val.erase(0, nr.size()+1);
    }

    if(val.rfind(":")!=std::string::npos)
    {
      std::string id=val.substr(0, val.rfind(":"));
      long uw=atol(val.substr(val.rfind(":")+1).c_str());

      symex.set_unwind_limit(id, thread_nr, uw);
    }
    
    if(next==std::string::npos) break;
    idx=next;
  }

  symex.max_unwind=options.get_int_option("unwind");
  if(symex.max_unwind==0) symex.max_unwind = (unsigned)-1;
  symex.incr_min_unwind=options.get_int_option("unwind-min");
  symex.incr_max_unwind=options.get_int_option("unwind-max");
  if(symex.incr_max_unwind==0) symex.incr_max_unwind = (unsigned)-1;
  symex.ignore_assertions = (symex.incr_min_unwind>=2) &&
      options.get_bool_option("ignore-assertions-before-unwind-min");
 
  symex.incr_loop_id = options.get_option("incremental-check");

  //freeze variables where unrollings are stitched together
  if(symex.incr_loop_id!="") symex.prop_conv.freeze_all = true;
}
