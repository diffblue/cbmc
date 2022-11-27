/*******************************************************************\

Module: Expression Initialization

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Expression Initialization

#ifndef CPROVER_UTIL_EXPR_INITIALIZER_H
#define CPROVER_UTIL_EXPR_INITIALIZER_H

#include "optional.h"

class exprt;
class namespacet;
class source_locationt;
class typet;

optionalt<exprt>
zero_initializer(const typet &, const source_locationt &, const namespacet &);

optionalt<exprt> nondet_initializer(
  const typet &type,
  const source_locationt &source_location,
  const namespacet &ns);

optionalt<exprt> expr_initializer(
  const typet &type,
  const source_locationt &source_location,
  const namespacet &ns,
  const exprt &init_byte_expr);

exprt duplicate_per_byte(const exprt &init_byte_expr, const typet &output_type);

#endif // CPROVER_UTIL_EXPR_INITIALIZER_H
