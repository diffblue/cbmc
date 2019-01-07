/*******************************************************************\

Module: Expressions in JSON

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Expressions in JSON

#ifndef CPROVER_GOTO_PROGRAMS_JSON_EXPR_H
#define CPROVER_GOTO_PROGRAMS_JSON_EXPR_H

#include <util/json.h>
#include <util/irep.h>

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

#endif // CPROVER_GOTO_PROGRAMS_JSON_EXPR_H
