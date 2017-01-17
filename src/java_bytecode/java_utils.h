/*******************************************************************\

Module: JAVA Bytecode Language Conversion

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_JAVA_BYTECODE_JAVA_UTILS_H
#define CPROVER_JAVA_BYTECODE_JAVA_UTILS_H

#include <util/std_expr.h>
#include <util/mp_arith.h>
#include <util/type.h>

constant_exprt as_number(const mp_integer value, const typet &type);

#endif // CPROVER_JAVA_BYTECODE_JAVA_UTILS_H
