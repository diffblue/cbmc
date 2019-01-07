/*******************************************************************\

Module: Expressions in JSON

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Expressions in JSON

#ifndef CPROVER_UTIL_JSON_EXPR_H
#define CPROVER_UTIL_JSON_EXPR_H

#include "json.h"
#include "irep.h"

class typet;
class exprt;
class namespacet;

json_objectt json(
  const exprt &,
  const namespacet &,
  const irep_idt &mode);

json_objectt json(
  const typet &,
  const namespacet &,
  const irep_idt &mode);

#endif // CPROVER_UTIL_JSON_EXPR_H
