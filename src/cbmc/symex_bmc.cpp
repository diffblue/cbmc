/*******************************************************************\

Module: Bounded Model Checking for ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/location.h>
#include <util/i2string.h>
#include <util/xml.h>
#include <goto-symex/goto_trace.h>
#include <goto-symex/build_goto_trace.h>
#include <solvers/sat/satcheck.h>
#include <solvers/sat/satcheck_minisat2.h>
#include <solvers/prop/literal.h>

#include "symex_bmc.h"
#include "bv_cbmc.h"
#include <iostream>
#include <climits>

/*******************************************************************\

Function: symex_bmct::symex_bmct

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

symex_bmct::symex_bmct(
  const namespacet &_ns,
  symbol_tablet &_new_symbol_table,
  symex_target_equationt &_target,
  prop_convt& _prop_conv):
  goto_symext(_ns, _new_symbol_table, _target),
  prop_conv(_prop_conv),
  loop_last_SSA_step(_target.SSA_steps.end()),
  ui(ui_message_handlert::PLAIN)
{
}


/*******************************************************************\

Function: symex_bmct::symex_step

  Inputs: goto functions, current symbolic execution state

 Outputs: true if symbolic execution is to be interrupted to perform incremental checking

 Purpose: show progress

\*******************************************************************/

bool symex_bmct::symex_step(
  const goto_functionst &goto_functions,
  statet &state)
{
  const locationt &location=state.source.pc->location;

  if(!location.is_nil() && last_location!=location)
  {
    debug() << "BMC at file " << location.get_file()
            << " line " << location.get_line()
            << " function " << location.get_function()
            << eom;

    last_location=location;
  }

  return goto_symext::symex_step(goto_functions, state);
}

/*******************************************************************\

Function: symex_bmct::convert

  Inputs: -

 Outputs: -

 Purpose: continue converting SSA steps where the last conversion stopped

\*******************************************************************/

void symex_bmct::convert() {  
  //TODO: loop_last_SSA_step is probably not needed  
  symex_target_equationt& e_target = dynamic_cast<symex_target_equationt&>(target); 
  if(loop_last_SSA_step == e_target.SSA_steps.end()) //first call
    loop_last_SSA_step = e_target.SSA_steps.begin();
  else {
    loop_last_SSA_step++;
  }

  //get variables where unrollings are stitched together
  symbol_mapt last_symbol_assignments = get_last_symbol_assignments();

  //  loop_last_SSA_step = e_target.convert(prop_conv,loop_last_SSA_step);
  loop_last_SSA_step = e_target.convert(prop_conv,e_target.SSA_steps.begin());

  //freeze variables where unrollings are stitched together
  freeze_variables(last_symbol_assignments);
#if 0
  e_target.output(std::cout);
#endif
}

/*******************************************************************\

Function: symex_bmct::current_activation_literal

  Inputs: -

 Outputs: current activation literal

 Purpose: get activation literal used for the assertions that have been 
          translated in the most recent call to convert()

\*******************************************************************/

literalt symex_bmct::current_activation_literal() {
  symex_target_equationt& e_target = dynamic_cast<symex_target_equationt&>(target); 
  return prop_conv.prop.lnot(e_target.activate_assertions.back());
}

/*******************************************************************\

Function: symex_bmct::check_break

 Inputs: source of the current symbolic execution state

 Outputs: true if the back edge encountered during symbolic execution 
            corresponds to the given loop (incr_loop_id)

 Purpose: defines condition for interrupting symbolic execution 
            for incremental BMC

\*******************************************************************/

bool symex_bmct::check_break(const symex_targett::sourcet &source,
                             unsigned unwind) {
  irep_idt id=(source.thread_nr!=0?(i2string(source.thread_nr)+":"):"")+
              id2string(source.pc->function)+"."+
              i2string(source.pc->loop_number);

  return (unwind>=incr_min_unwind) && (id==incr_loop_id);
}


/*******************************************************************\

Function: symex_bmct::get_unwind

  Inputs: source of the current symbolic execution state, symex unwind counter

 Outputs: true if loop bound has been exceeded 

 Purpose: check whether loop bound for current loop has been reached

\*******************************************************************/

bool symex_bmct::get_unwind(
  const symex_targett::sourcet &source,
  unsigned unwind)
{
  irep_idt id=(source.thread_nr!=0?(i2string(source.thread_nr)+":"):"")+
              id2string(source.pc->function)+"."+
              i2string(source.pc->loop_number);
  unsigned long this_loop_max_unwind=max_unwind;

  if(unwind_set.count(id)!=0)
    this_loop_max_unwind=unwind_set[id];
  if(id==incr_loop_id) {
    this_loop_max_unwind = incr_max_unwind;
    if(unwind+1>=incr_min_unwind) ignore_assertions = false;
  }
  if(this_loop_max_unwind==0) this_loop_max_unwind = UINT_MAX;

  #if 1
  statistics() << "Unwinding loop " << id << " iteration "
               << unwind << " " << source.pc->location
               << " thread " << source.thread_nr << eom;

  if(ui==ui_message_handlert::XML_UI) {
      xmlt xml("current-unwinding");
      xml.data=i2string(unwind);
      std::cout << xml;
      std::cout << "\n";
  }
  #endif

  #if 0
    statistics() << "Unwind bound = " << this_loop_max_unwind << eom;
  #endif

  return unwind>=this_loop_max_unwind;
}

/*******************************************************************\

Function: symex_bmct::get_unwind_recursion

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool symex_bmct::get_unwind_recursion(
  const irep_idt &identifier,
  unsigned unwind)
{
  unsigned long this_loop_max_unwind=max_unwind;

  #if 1
  if(unwind!=0)
  {
    const symbolt &symbol=ns.lookup(identifier);

    statistics() << "Unwinding recursion "
                 << symbol.display_name()
                 << " iteration " << unwind;
      
    if(this_loop_max_unwind!=0)
      statistics() << " (" << this_loop_max_unwind << " max)";

    statistics() << eom;
  }
  #endif

  return this_loop_max_unwind!=0 &&
         unwind>=this_loop_max_unwind;
}

/*******************************************************************\

Function: symex_bmct::no_body

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void symex_bmct::no_body(const irep_idt &identifier)
{
  if(body_warnings.insert(identifier).second)
  {
    warning() <<
      "**** WARNING: no body for function " << identifier << eom;
  }
}

/*******************************************************************\

Function: symex_bmct::freeze_variables

  Inputs:

 Outputs: map (orig_id -> SSA_id) for last assignment of orig_id

 Purpose: get variables where unrollings are stitched together

\*******************************************************************/

symex_bmct::symbol_mapt symex_bmct::get_last_symbol_assignments() {
  symex_target_equationt& e_target = dynamic_cast<symex_target_equationt&>(target); 
  symbol_mapt last_symbol_assignments;
  for(symex_target_equationt::SSA_stepst::iterator it=--e_target.SSA_steps.end();
      it!=loop_last_SSA_step; it--) {
    if(it->is_assignment() && !it->ignore  && !it->converted &&
         it->assignment_type!=symex_target_equationt::GUARD) {
      irep_idt stripped_lhs = it->original_lhs_object.get_identifier();
      if(id2string(stripped_lhs).find("::$tmp::")!=std::string::npos) continue;
      if(last_symbol_assignments.find(stripped_lhs)==last_symbol_assignments.end()) {
        symbol_exprt lhs_sym = it->ssa_lhs;
        last_symbol_assignments.insert(symbol_mapt::value_type(stripped_lhs,lhs_sym));

#if 0
	std::cout << "symbol: " << stripped_lhs << " (" << lhs_sym << ")" << std::endl;
#endif
      }
    }
  }
  return last_symbol_assignments;
}

/*******************************************************************\

Function: symex_bmct::freeze_variables

  Inputs: last assignments to variables

 Outputs:

 Purpose: freeze variables where unrollings are stitched together

\*******************************************************************/

void symex_bmct::freeze_variables(symbol_mapt& last_symbol_assignments) {
  #if 0
  // freeze guard variables
  //not really necessary, 
  //   because variables created through get_literal() are set to be frozen anyway
  const prop_convt::symbolst& symbols = prop_conv.get_symbols();
  for(prop_convt::symbolst::const_iterator it=symbols.begin();
      it!=symbols.end(); it++) {
    if(!it->second.is_constant()) {
      prop_conv.prop.set_frozen(it->second);
    }
  } 
  #endif

  // freeze variables set to be frozen (cached variables, etc)
  const propt::variablest& vars_to_be_frozen = prop_conv.prop.get_vars_to_be_frozen();
  for(propt::variablest::const_iterator it=vars_to_be_frozen.begin();
      it!=vars_to_be_frozen.end(); it++) {
    prop_conv.prop.set_frozen(literalt(*it,false));
  } 

  // freeze variables occurring in last symbol assignments
  for(symbol_mapt::iterator it=last_symbol_assignments.begin();
      it!=last_symbol_assignments.end(); it++) {
    if(it->second.type().id()!=ID_bv && it->second.type().id()!=ID_signedbv &&
       it->second.type().id()!=ID_unsignedbv) continue;
     bvt literals;
     unsigned width =  to_bitvector_type(it->second.type()).get_width();
     literals.resize(width);
     boolbv_mapt lmap =  (dynamic_cast<boolbvt&>(prop_conv)).get_map();
     lmap.get_literals(it->second.get_identifier(),it->second.type(),width,literals);

     for(bvt::iterator l=literals.begin(); l!=literals.end(); l++) {
       if(!l->is_constant()) prop_conv.prop.set_frozen(*l);
     }
  }
}
