/*******************************************************************\

Module: Extract class identifier

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_CLASS_IDENTIFIER_H
#define CPROVER_GOTO_PROGRAMS_CLASS_IDENTIFIER_H

#include <util/expr.h>
#include <util/std_types.h>
#include <util/namespace.h>

exprt get_class_identifier_field(
  exprt this_expr,
  const symbol_typet &suggested_type,
  const namespacet &ns);

#endif
