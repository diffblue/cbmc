/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_POINTER_ARITHMETIC_H
#define CPROVER_POINTER_ARITHMETIC_H

#include <util/expr.h>

struct pointer_arithmetict
{
  exprt pointer, offset;

  pointer_arithmetict(const exprt &src);
  
protected:
  void read(const exprt &src);
  void add_to_offset(const exprt &src);
  void make_pointer(const exprt &src);
};

#endif
