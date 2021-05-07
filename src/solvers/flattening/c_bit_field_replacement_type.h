/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_SOLVERS_FLATTENING_C_BIT_FIELD_REPLACEMENT_TYPE_H
#define CPROVER_SOLVERS_FLATTENING_C_BIT_FIELD_REPLACEMENT_TYPE_H

#include <util/type.h>

class c_bit_field_typet;
class namespacet;

typet c_bit_field_replacement_type(
  const c_bit_field_typet &,
  const namespacet &);

#endif // CPROVER_SOLVERS_FLATTENING_C_BIT_FIELD_REPLACEMENT_TYPE_H
