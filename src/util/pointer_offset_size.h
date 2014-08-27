/*******************************************************************\

Module: Pointer Logic

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_POINTER_OFFSET_SIZE_H
#define CPROVER_POINTER_OFFSET_SIZE_H

#include "mp_arith.h"
#include "irep.h"

class exprt;
class namespacet;
class struct_typet;
class typet;
class member_exprt;
class constant_exprt;

// these return -1 on failure

mp_integer member_offset(
  const namespacet &ns,
  const struct_typet &type,
  const irep_idt &member);

mp_integer pointer_offset_size(
  const namespacet &ns,
  const typet &type);

mp_integer compute_pointer_offset(
  const namespacet &ns,
  const exprt &expr);

// these return 'nil' on failure

exprt member_offset_expr(
  const member_exprt &,
  const namespacet &ns);

exprt member_offset_expr(
  const struct_typet &type,
  const irep_idt &member,
  const namespacet &ns);

exprt size_of_expr(
  const typet &type,
  const namespacet &ns);

exprt build_sizeof_expr(
  const constant_exprt &expr,
  const namespacet &ns);

#endif
