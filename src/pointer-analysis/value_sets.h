/*******************************************************************\

Module: Value Set Propagation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_POINTER_ANALYSIS_VALUE_SETS_H
#define CPROVER_POINTER_ANALYSIS_VALUE_SETS_H

#include <list>

#include <goto-programs/goto_program.h>

// an abstract base class

class value_setst
{
public:
  value_setst()
  {
  }

  typedef std::list<exprt> valuest;

  // this is not const to allow a lazy evaluation  
  virtual void get_values(
    goto_programt::const_targett l,
    const exprt &expr,
    valuest &dest)=0;
    
  virtual ~value_setst()
  {
  }
};

#endif
