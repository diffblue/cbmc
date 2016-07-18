/*******************************************************************\

Module: Value Set Propagation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_POINTER_ANALYSIS_VALUE_SET_ANALYSIS_CS_H
#define CPROVER_POINTER_ANALYSIS_VALUE_SET_ANALYSIS_CS_H

#include <functional>

#include <analyses/ai_cs.h>

#include "value_set_domain_cs.h"
#include "value_sets_cs.h"

class xmlt;

//#define USE_MAP_ONE

class value_set_analysis_cst:
  public value_sets_cst,
#ifdef USE_MAP_ONE
  public ai_one_cst<value_set_domain_cst,
                    value_set_domain_cs_hasht,
                    std::equal_to<value_set_domain_cst>>
#else
  public ai_cst<value_set_domain_cst>
#endif
{
public:
  value_set_analysis_cst(in_loopt &in_loop):
#ifdef USE_MAP_ONE
    ai_one_cst<value_set_domain_cst,
               value_set_domain_cs_hasht,
               std::equal_to<value_set_domain_cst>>(in_loop)
#else
    ai_cst<value_set_domain_cst>(in_loop)
#endif
    {
    }

  value_set_analysis_cst(in_loopt &in_loop, stack_numberingt &stack_numbering) :
#ifdef USE_MAP_ONE
    ai_one_cst<value_set_domain_cst,
               value_set_domain_cs_hasht,
               std::equal_to<value_set_domain_cst>>(in_loop, stack_numbering)
#else
    ai_cst<value_set_domain_cst>(in_loop, stack_numbering)
#endif
    {
    }

  typedef ai_one_cst<value_set_domain_cst,
                     value_set_domain_cs_hasht,
                     std::equal_to<value_set_domain_cst>> baset;

  // overloading  

  virtual void convert(
    const namespacet &ns,
    const goto_functionst &goto_functions,
    xmlt &dest);

  virtual void convert(
    const namespacet &ns,
    const goto_programt &goto_program,
    xmlt &dest);

  void convert(
    const namespacet &ns,
    const goto_programt &goto_program,
    const irep_idt &identifier,
    xmlt &dest) const;
        
  virtual void statistics(std::ostream &out) const;
      
  // interface value_sets
  virtual void get_values(
    locationt l,
    const ai_cs_stackt &stack,
    const exprt &expr,
    value_setst::valuest &dest,
    const namespacet &ns)
  {
    unsigned stack_number=get_stack_number(stack);
    const placet place(stack, l);
    (*this)[place].base.value_set.get_value_set(expr, dest, ns, stack_number);
  }  
};

#endif
