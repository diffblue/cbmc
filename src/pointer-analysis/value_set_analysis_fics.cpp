/*******************************************************************\

Module: Value Set Propagation (flow-insensitive, context-sensitive)

Author: Daniel Kroening, kroening@kroening.com
        Daniel Poetzl

\*******************************************************************/

#include <sstream>
#include <memory>

#include <util/prefix.h>
#include <util/cprover_prefix.h>
#include <util/xml_expr.h>
#include <util/xml.h>

#include <langapi/language_util.h>

#include "value_set_analysis_fics.h"

/*******************************************************************\

Function: ai_cs_baset::fixedpoint

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#if 0
bool value_set_analysis_ficst::fixedpoint(
  const goto_programt &goto_program,
  const goto_functionst &goto_functions,
  const ai_cs_stackt &stack,
  const namespacet &ns)
{
  bool changed;

  do
  {
    changed=false;

    // working state
    statet &state=get_state(stack, goto_program.instructions.begin());

    std::set<locationt> call_locations;

    // do all instructions but function calls
    forall_goto_program_instructions(i_it, goto_program)
    {
      locationt from_l=i_it;

      if(from_l->is_function_call())
      {
        call_locations.insert(from_l);
        continue;
      }

      goto_programt::const_targetst successors;
      goto_program.get_successors(from_l, successors);

      for(goto_programt::const_targetst::const_iterator it=successors.begin();
          it!=successors.end();
          it++)
      {
        locationt to_l=*it;

        // new state
        std::unique_ptr<statet> tmp_state(make_temporary_state(state));
        statet &new_values=*tmp_state;

        new_values.transform(from_l, to_l, stack, *this, ns);

        changed|=merge(new_values, from_l, to_l, stack);
      }
    }

    // now do function calls
    for(std::set<locationt>::const_iterator it=call_locations.begin();
        it!=call_locations.end(); it++)
    {
      locationt call_l=*it;

      // return location
      locationt return_l=call_l;
      return_l++;

      const code_function_callt &code=to_code_function_call((*it)->code);

      changed|=do_function_call_rec(
        call_l, // call location
        return_l,
        stack,
        code.function(), // function identifier or pointer expression
        code.arguments(), // arguments as expression vector
        goto_functions,
        ns);
    }

  }
  while(changed);

  return true; // not checked by callers anyways
}
#endif

bool value_set_analysis_ficst::fixedpoint(
  const goto_programt &goto_program,
  const goto_functionst &goto_functions,
  const ai_cs_stackt &stack,
  const namespacet &ns)
{
  bool changed;

  locationt bl=goto_program.instructions.begin();

  locationt el=--goto_program.instructions.end();
  assert(el->is_end_function());

  // working state
  statet &state=get_state(stack, bl);

  do
  {
    changed=false;

    // first time here we declare all the local variables
    if(!seen(stack, bl))
    {
      set_seen(stack, bl);

      forall_goto_program_instructions(i_it, goto_program)
      {
        if(!i_it->is_decl())
          continue;

        goto_programt::const_targetst successors;
        goto_program.get_successors(i_it, successors);
        assert(successors.size()==1);
        locationt s=successors.front();
        assert(!s->is_end_function()); // there must be another dead statement

        std::unique_ptr<statet> tmp_state(make_temporary_state(state));
        statet &new_values=*tmp_state;

        new_values.transform(i_it, s, stack, *this, ns);

        changed|=merge(new_values, i_it, bl, stack); // merge into begin state
      }
    }

    std::list<locationt> call_locations;
    assert(call_locations.empty());

    // do instructions
    forall_goto_program_instructions(i_it, goto_program)
    {
      locationt from_l=i_it;

      if(from_l->is_function_call())
      {
        call_locations.push_back(from_l);
        continue;
      }

      if(from_l->is_decl() || from_l->is_dead() || from_l->is_end_function())
        continue;

      goto_programt::const_targetst successors;
      goto_program.get_successors(from_l, successors);

      for(goto_programt::const_targetst::const_iterator it=successors.begin();
          it!=successors.end();
          it++)
      {
        locationt to_l=*it;

        // new state
        std::unique_ptr<statet> tmp_state(make_temporary_state(state));
        statet &new_values=*tmp_state;

        new_values.transform(from_l, to_l, stack, *this, ns);

        // merge into begin state
        changed|=merge(new_values, from_l, bl, stack);
      }
    }

    // now do function calls
    for(std::list<locationt>::const_iterator it=call_locations.begin();
        it!=call_locations.end(); it++)
    {
      locationt call_l=*it;

      // return location
      locationt return_l=call_l;
      return_l++;

      const code_function_callt &code=to_code_function_call((*it)->code);

      statet &end_state=get_state(stack, el);
      statet *end_state_tmp=NULL;

      if(return_l->is_end_function())
      {
        // switch
        end_state_tmp=make_temporary_state(end_state); // copy
        end_state=state; // copy
      }

      changed|=do_function_call_rec(
        call_l, // call location
        return_l,
        stack,
        code.function(), // function identifier or pointer expression
        code.arguments(), // arguments as expression vector
        goto_functions,
        ns);

      if(return_l->is_end_function())
      {
        // switch back
        state=end_state;
        assert(end_state_tmp!=NULL);
        end_state=*end_state_tmp;
        delete end_state_tmp;
      }
    }
  }
  while(changed);

  // before we leave we handle the dead statements
  std::unique_ptr<statet> tmp_state(make_temporary_state(state));
  statet &new_values=*tmp_state;

  forall_goto_program_instructions(i_it, goto_program)
  {
    if(i_it->is_dead())
    {
      goto_programt::const_targetst successors;
      goto_program.get_successors(i_it, successors);
      assert(successors.size()==1);
      locationt s=successors.front();

      new_values.transform(i_it, s, stack, *this, ns);
    }
  }

  // merge into end state
  merge(new_values, el, el, stack);

  return true; // not checked by callers anyways
}
