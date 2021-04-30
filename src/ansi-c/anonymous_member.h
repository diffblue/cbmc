/*******************************************************************\

Module: C Language Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// C Language Type Checking

#ifndef CPROVER_ANSI_C_ANONYMOUS_MEMBER_H
#define CPROVER_ANSI_C_ANONYMOUS_MEMBER_H

#include <util/expr.h>

class namespacet;

exprt get_component_rec(
  const exprt &struct_union,
  const irep_idt &component_name,
  const namespacet &ns);

bool has_component_rec(
  const typet &struct_union_type,
  const irep_idt &component_name,
  const namespacet &ns);

#endif // CPROVER_ANSI_C_ANONYMOUS_MEMBER_H
