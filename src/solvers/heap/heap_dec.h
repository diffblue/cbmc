/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_PROP_HEAP_DEC_H
#define CPROVER_PROP_HEAP_DEC_H

#include "heap_conv.h"

/*! \brief Decision procedure interface for heap theory solver
    \ingroup gr_heap
*/
class heap_dect:public heap_convt
{
public:
  heap_dect(
    const namespacet &_ns):
    heap_convt(_ns)
  {
  }

  virtual resultt dec_solve();
  virtual std::string decision_procedure_text() const;
  
  // yes, we are incremental!
  virtual bool has_set_assumptions() const { return false; }
  
protected:

};

#endif
