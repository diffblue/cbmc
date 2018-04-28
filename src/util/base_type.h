/*******************************************************************\

Module: Base Type Computation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Base Type Computation

#ifndef CPROVER_UTIL_BASE_TYPE_H
#define CPROVER_UTIL_BASE_TYPE_H

class exprt;
class typet;
class namespacet;

bool base_type_eq(
  const typet &type1,
  const typet &type2,
  const namespacet &ns);

bool base_type_eq(
  const exprt &expr1,
  const exprt &expr2,
  const namespacet &ns);

#endif // CPROVER_UTIL_BASE_TYPE_H
