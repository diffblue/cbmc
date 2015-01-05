/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_BOOLBV_TYPE_H
#define CPROVER_BOOLBV_TYPE_H

#include <util/type.h>

// new stuff
typedef enum
{
  IS_BV, IS_SIGNED, IS_UNSIGNED, IS_FLOAT, IS_FIXED, IS_C_BOOL,
  IS_VERILOGBV, IS_RANGE, IS_UNKNOWN, IS_C_ENUM, IS_C_BIT_FIELD
} bvtypet;

bvtypet get_bvtype(const typet &type);

#endif
