/*******************************************************************\

Module: C Language Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/expr.h>
#include <util/namespace.h>

exprt get_component_rec(
  const exprt &struct_union,
  const irep_idt &component_name,
  const namespacet &ns);

bool has_component_rec(
  const typet &struct_union_type,
  const irep_idt &component_name,
  const namespacet &ns);

