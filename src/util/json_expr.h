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

class source_locationt;
class typet;
class exprt;
class namespacet;

json_objectt json(
  const exprt &,
  const namespacet &,
  const irep_idt &mode=ID_unknown);

json_objectt json(
  const typet &,
  const namespacet &,
  const irep_idt &mode=ID_unknown);

json_objectt json(const source_locationt &);

#endif // CPROVER_UTIL_JSON_EXPR_H
