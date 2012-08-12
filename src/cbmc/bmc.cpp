/*******************************************************************\

Module: Symbolic Execution of ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <sstream>
#include <fstream>
#include <cstdlib>

#include <i2string.h>
#include <location.h>
#include <time_stopping.h>
#include <message_stream.h>

#include <langapi/mode.h>
#include <langapi/languages.h>
#include <langapi/language_util.h>

#include <ansi-c/ansi_c_language.h>

#include <goto-symex/goto_trace.h>
#include <goto-symex/build_goto_trace.h>
#include <goto-symex/slice.h>
#include <goto-symex/slice_by_trace.h>
#include <goto-symex/xml_goto_trace.h>

#include <solvers/sat/satcheck_minisat2.h>
#include <solvers/prop/cover_goals.h>

#include "bmc.h"
#include "bv_cbmc.h"

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
  status("Building error trace");

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
    std::cout << std::endl << "Counterexample:" << std::endl;
    show_goto_trace(std::cout, ns, goto_trace);
    break;
  
  case ui_message_handlert::OLD_GUI:
    show_goto_trace_gui(std::cout, ns, goto_trace);
    break;
  
  case ui_message_handlert::XML_UI:
    {
      xmlt xml;
      convert(ns, goto_trace, xml);
      std::cout << xml << std::endl;
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
  status("Passing problem to "+prop_conv.decision_procedure_text());

  prop_conv.set_message_handler(get_message_handler());
  prop_conv.set_verbosity(get_verbosity());

  // stop the time
  fine_timet sat_start=current_time();
  
  do_conversion(prop_conv);  

  status("Running "+prop_conv.decision_procedure_text());

  decision_proceduret::resultt dec_result=prop_conv.dec_solve();
  // output runtime

  {
    std::ostringstream str;
    fine_timet sat_stop=current_time();

    str << "Runtime decision procedure: ";
    output_time(sat_stop-sat_start, str);
    str << "s";
    status(str.str());
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
  status("VERIFICATION SUCCESSFUL");

  switch(ui)
  {
  case ui_message_handlert::OLD_GUI:
    std::cout << "SUCCESS" << std::endl
              << "Verification successful" << std::endl
              << ""     << std::endl
              << ""     << std::endl
              << ""     << std::endl
              << ""     << std::endl;
    break;
    
  case ui_message_handlert::PLAIN:
    break;
    
  case ui_message_handlert::XML_UI:
    {
      xmlt xml("cprover-status");
      xml.data="SUCCESS";
      std::cout << xml;
      std::cout << std::endl;
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
  status("VERIFICATION FAILED");

  switch(ui)
  {
  case ui_message_handlert::OLD_GUI:
    break;
    
  case ui_message_handlert::PLAIN:
    break;
    
  case ui_message_handlert::XML_UI:
    {
      xmlt xml("cprover-status");
      xml.data="FAILURE";
      std::cout << xml;
      std::cout << std::endl;
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
  
  std::cout << std::endl << "Program constraints:" << std::endl;

  for(symex_target_equationt::SSA_stepst::const_iterator
      it=equation.SSA_steps.begin();
      it!=equation.SSA_steps.end(); it++)
  {
    if(it->is_assignment())
    {
      std::string string_value;
      languages.from_expr(it->cond_expr, string_value);
      std::cout << "(" << count << ") " << string_value << std::endl;

      if(!it->guard_expr.is_true())
      {
        languages.from_expr(it->guard_expr, string_value);
        std::cout << std::string(i2string(count).size()+3, ' ');
        std::cout << "guard: " << string_value << std::endl;
      }
      
      count++;
    }
    else if(it->is_assert())
    {
      std::string string_value;
      languages.from_expr(it->cond_expr, string_value);
      std::cout << "(" << count << ") ASSERT("
                << string_value <<") " << std::endl;

      if(!it->guard_expr.is_true())
      {
        languages.from_expr(it->guard_expr, string_value);
        std::cout << std::string(i2string(count).size()+3, ' ');
        std::cout << "guard: " << string_value << std::endl;
      }

      count++;
    }  
  }
}

/*******************************************************************\

Function: bmct::run

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool bmct::run(const goto_functionst &goto_functions)
{
  //symex.total_claims=0;
  symex.set_message_handler(get_message_handler());
  symex.set_verbosity(get_verbosity());
  symex.options=options;

  status("Starting Bounded Model Checking");

  symex.last_location.make_nil();

  try
  {
    // get unwinding info
    setup_unwind();

    symex(goto_functions);
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
    message_streamt message_stream(get_message_handler());
    message_stream.error("Out of memory");
    return true;
  }

  print(8, "size of program expression: "+
           i2string(equation.SSA_steps.size())+
           " assignments");

  try
  {
    if(options.get_option("slice-by-trace")!="")
    {
      symex_slice_by_tracet symex_slice_by_trace(ns);

      symex_slice_by_trace.slice_by_trace
	(options.get_option("slice-by-trace"), equation);
    }

    if(options.get_bool_option("slice-formula"))
    {
      slice(equation);
      print(8, "slicing removed "+
        i2string(equation.count_ignored_SSA_steps())+" assignments");
    }
    else
    {
      simple_slice(equation);
      print(8, "simple slicing removed "+
        i2string(equation.count_ignored_SSA_steps())+" assignments");
    }

    if(options.get_bool_option("program-only"))
    {
      show_program();
      return false;
    }

    {
      std::string msg;
      msg="Generated "+i2string(symex.total_claims)+
          " VCC(s), "+i2string(symex.remaining_claims)+
          " remaining after simplification";
      print(8, msg);
    }

    if(options.get_bool_option("show-vcc"))
    {
      show_vcc();
      return false;
    }
    
    if(options.get_bool_option("all-claims"))
      return all_claims(goto_functions);
    
    if(options.get_bool_option("cover-assertions"))
    {
      cover_assertions(goto_functions);
      return false;
    }

    if(symex.remaining_claims==0)
    {
      report_success();
      return false;
    }

    if(options.get_bool_option("boolector"))
      return decide_boolector();
    else if(options.get_bool_option("mathsat"))
      return decide_mathsat();
    else if(options.get_bool_option("cvc"))
      return decide_cvc();
    else if(options.get_bool_option("dimacs"))
      return write_dimacs();
    else if(options.get_bool_option("opensmt"))
      return decide_opensmt();
    else if(options.get_bool_option("refine"))
      return decide_bv_refinement();
    else if(options.get_bool_option("smt1"))
      // this is the 'default' smt1 solver
      return decide_smt1(smt1_dect::BOOLECTOR);
    else if(options.get_bool_option("smt2"))
      // this is the 'default' smt2 solver
      return decide_smt2(smt2_dect::MATHSAT);
    else if(options.get_bool_option("yices"))
      return decide_yices();
    else if(options.get_bool_option("z3"))
      return decide_z3();
    else
      return decide_default();
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

  catch(std::bad_alloc)
  {
    error("Out of memory");
    return true;
  }
}

/*******************************************************************\

Function: bmct::all_claims

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

struct goalt
{
  bvt bv;
  std::string description;
  
  explicit goalt(const goto_programt::instructiont &instruction)
  {
    std::string text=instruction.location.as_string();
    irep_idt comment=instruction.location.get_comment();
    if(comment!="")
      text+=", "+id2string(comment);
    description=text;
  }
  
  goalt()
  {
  }
};

bool bmct::all_claims(const goto_functionst &goto_functions)
{
  satcheck_minisat_no_simplifiert satcheck;
  satcheck.set_message_handler(get_message_handler());
  satcheck.set_verbosity(get_verbosity());
  
  bv_cbmct bv_cbmc(ns, satcheck);
  
  if(options.get_option("arrays-uf")=="never")
    bv_cbmc.unbounded_array=bv_cbmct::U_NONE;
  else if(options.get_option("arrays-uf")=="always")
    bv_cbmc.unbounded_array=bv_cbmct::U_ALL;
    
  prop_convt &prop_conv=bv_cbmc;

  status("Passing problem to "+prop_conv.decision_procedure_text());

  prop_conv.set_message_handler(get_message_handler());
  prop_conv.set_verbosity(get_verbosity());

  // stop the time
  fine_timet sat_start=current_time();
  
  do_conversion(prop_conv);  
  
  // collect _all_ goals in `goal_map'
  typedef std::map<goto_programt::const_targett, goalt> goal_mapt;
  goal_mapt goal_map;
  
  forall_goto_functions(f_it, goto_functions)
    forall_goto_program_instructions(i_it, f_it->second.body)
      if(i_it->is_assert())
        goal_map[i_it]=goalt(*i_it);

  // get the conditions for these goals from formula

  for(symex_target_equationt::SSA_stepst::iterator
      it=equation.SSA_steps.begin();
      it!=equation.SSA_steps.end();
      it++)
  {
    if(it->is_assert())
    {
      std::string text=it->source.pc->location.as_string();
      if(it->comment!="")
        text+=", "+id2string(it->comment);
      goal_map[it->source.pc].bv.push_back(it->cond_literal);
      goal_map[it->source.pc].description=text;
    }
  }
  
  cover_goalst cover_goals(prop_conv);
  
  for(goal_mapt::const_iterator
      it=goal_map.begin();
      it!=goal_map.end();
      it++)
  {
    // the following is TRUE if the bv is empty
    literalt p=prop_conv.prop.lnot(prop_conv.prop.land(it->second.bv));
    cover_goals.add(p, it->second.description);
  }

  status("Running "+prop_conv.decision_procedure_text());

  cover_goals();  

  // output runtime

  {
    std::ostringstream str;
    fine_timet sat_stop=current_time();

    str << "Runtime decision procedure: ";
    output_time(sat_stop-sat_start, str);
    str << "s";
    status(str.str());
  }
  
  // report
  if(ui==ui_message_handlert::XML_UI)
  {
    std::list<cover_goalst::cover_goalt>::const_iterator g_it=
      cover_goals.goals.begin();
      
    for(goal_mapt::const_iterator
        it=goal_map.begin();
        it!=goal_map.end();
        it++, g_it++)
    {
      xmlt xml_result("result");
      xml_result.set_attribute("claim", id2string(it->first->location.get_claim()));

      xml_result.set_attribute("status",
        g_it->covered?"FAILURE":"SUCCESS");
      
      std::cout << xml_result << std::endl;
    }
  }
  else
  {
    status("");
    status("** Results:");
    for(std::list<cover_goalst::cover_goalt>::const_iterator
        g_it=cover_goals.goals.begin();
        g_it!=cover_goals.goals.end();
        g_it++)
      status(g_it->description+": "+(g_it->covered?"FAILED":"OK"));

    status("");
  }
  
  status("** "+i2string(cover_goals.number_covered())+
         " of "+i2string(cover_goals.size())+" failed ("+
         i2string(cover_goals.iterations())+" iterations)");
  
  return false;
}

/*******************************************************************\

Function: bmct::decide

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool bmct::decide(prop_convt &prop_conv)
{
  if(options.get_bool_option("beautify-pbs") ||
     options.get_bool_option("beautify-greedy"))
    throw "sorry, this solver does not support beautification";

  prop_conv.set_message_handler(get_message_handler());
  prop_conv.set_verbosity(get_verbosity());
  
  bool result=true;

  switch(run_decision_procedure(prop_conv))
  {
  case decision_proceduret::D_UNSATISFIABLE:
    result=false;
    report_success();
    break;

  case decision_proceduret::D_SATISFIABLE:
    error_trace(prop_conv);
    report_failure();
    break;

  default:
    error("decision procedure failed");
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

    if(val.rfind(":")!=std::string::npos)
    {
      std::string id=val.substr(0, val.rfind(":"));
      unsigned long uw=atol(val.substr(val.rfind(":")+1).c_str());
      symex.unwind_set[id]=uw;
    }
    
    if(next==std::string::npos) break;
    idx=next;
  }

  symex.max_unwind=options.get_int_option("unwind");
}
