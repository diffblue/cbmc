/*******************************************************************\

Module: Value Set Propagation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_POINTER_ANALYSIS_VALUE_SETS_CS_H
#define CPROVER_POINTER_ANALYSIS_VALUE_SETS_CS_H

#include <list>

#include <goto-programs/goto_program.h>

// an abstract base class

class value_sets_cst
{
public:
  value_sets_cst()
  {
  }

  typedef std::list<exprt> valuest;

  // this is not const to allow a lazy evaluation  
  virtual void get_values(
    ai_cs_stackt::locationt l,
    const ai_cs_stackt &stack,
    const exprt &expr,
    valuest &dest,
    const namespacet &ns)=0;
    
  virtual ~value_sets_cst()
  {
  }
};

#endif
