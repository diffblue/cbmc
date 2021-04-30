/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_SOLVERS_FLATTENING_BOOLBV_TYPE_H
#define CPROVER_SOLVERS_FLATTENING_BOOLBV_TYPE_H

class typet;

// new stuff
enum class bvtypet
{
  IS_BV, IS_SIGNED, IS_UNSIGNED, IS_FLOAT, IS_FIXED, IS_C_BOOL,
  IS_VERILOG_SIGNED, IS_VERILOG_UNSIGNED, IS_RANGE, IS_UNKNOWN,
  IS_C_ENUM, IS_C_BIT_FIELD
};

bvtypet get_bvtype(const typet &type);

#endif // CPROVER_SOLVERS_FLATTENING_BOOLBV_TYPE_H
