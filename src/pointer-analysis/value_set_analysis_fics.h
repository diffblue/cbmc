/*******************************************************************\

Module: Value Set Propagation (flow-insensitive, context-sensitive)

Author: Daniel Kroening, kroening@kroening.com
        Daniel Poetzl

\*******************************************************************/

#ifndef CPROVER_POINTER_ANALYSIS_VALUE_SET_ANALYSIS_FICS_H
#define CPROVER_POINTER_ANALYSIS_VALUE_SET_ANALYSIS_FICS_H

#include <functional>

#include <goto-programs/goto_functions.h>

#include "value_set_domain_cs.h"
#include "value_sets_cs.h"

#include "value_set_analysis_cs.h"

class xmlt;

class value_set_analysis_ficst:public value_set_analysis_cst
{
public:
  value_set_analysis_ficst(
    const goto_functionst &goto_functions,
    in_loopt &in_loop):
      value_set_analysis_cst(in_loop), goto_functions(goto_functions)
  {
  }

  value_set_analysis_ficst(
    const goto_functionst &goto_functions,
    in_loopt &in_loop,
    stack_numberingt &stack_numbering) :
      value_set_analysis_cst(in_loop, stack_numbering),
      goto_functions(goto_functions)
  {
  }

  // template superclass not considered for name resolution
  typedef value_set_analysis_cst baset;
  typedef typename baset::placet placet;
  typedef typename baset::locationt locationt;
  typedef typename baset::goto_functiont goto_functiont;
  typedef typename baset::statet statet;

  virtual void postprocessing()
  {
#if 1
    // validate flow-insensitive state map
    std::set<ai_cs_stackt> stacks;

    forall_goto_functions(it, goto_functions)
    {
      const goto_functiont &goto_function=it->second;

      if(!goto_function.body_available())
        continue;

      const goto_programt &goto_program=goto_function.body;

      forall_goto_program_instructions(i_it, goto_program)
      {
        if(i_it!=goto_program.instructions.begin() &&
           i_it!=--goto_program.instructions.end())
        {
          stacks.clear();
          find_stacks(i_it, stacks);
          assert(stacks.empty());
        }
      }
    }
#endif
  }

  virtual inline value_set_domain_cst &operator[](const placet &place)
  {
    assert(has(place));
    //return baset::operator[](get_begin_place(place));
    return (value_set_domain_cst &)get_state(place.first, place.second);
  }

  virtual inline const value_set_domain_cst &operator[](
    const placet &place) const
  {
    return baset::operator[](get_place(place));
  }

  virtual bool has(const placet &place) const
  {
    return baset::has(get_place(place));
  }

  virtual bool fixedpoint(
    const goto_programt &goto_program,
    const goto_functionst &goto_functions,
    const ai_cs_stackt &stack,
    const namespacet &ns);

  virtual bool visit(
    locationt l,
    const ai_cs_stackt &stack,
    working_sett &working_set,
    const goto_programt &goto_program,
    const goto_functionst &goto_functions,
    const namespacet &ns)=delete;

protected:
  // this one creates states, if need be
  virtual statet &get_state(const ai_cs_stackt &stack, locationt l)
  {
    return baset::get_state(stack, get_location(l));
  }

  virtual const statet &get_const_state(const ai_cs_stackt &stack, locationt l)
  {
    return baset::get_const_state(stack, get_location(l));
  }

  // this one just finds states
  virtual const statet &find_state(
    const ai_cs_stackt &stack,
    locationt l) const
  {
    return baset::find_state(stack, get_location(l));
  }

private:
  const goto_functionst &goto_functions;

  locationt get_begin_location(locationt l) const
  {
    irep_idt id=l->function;
    assert(!id.empty());

    goto_functionst::function_mapt::const_iterator it
      =goto_functions.function_map.find(id);
    assert(it!=goto_functions.function_map.end());

    const goto_functiont &goto_function=it->second;
    assert(goto_function.body_available());

    locationt l_begin=goto_function.body.instructions.begin();

    return l_begin;
  }

  placet get_begin_place(const placet &place) const
  {
    placet begin_place=place;
    begin_place.second=get_begin_location(place.second);
    return begin_place;
  }

  locationt get_location(locationt l) const
  {
    if(l->is_end_thread())
      return l;
    else
      return get_begin_location(l);
  }

  placet get_place(const placet &place) const
  {
    placet changed_place=place;
    changed_place.second=get_location(place.second);
    return changed_place;
  }
};

#endif
