/*******************************************************************\

Module: JAVA Pointer Casts

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// JAVA Pointer Casts

#ifndef CPROVER_JAVA_BYTECODE_JAVA_POINTER_CASTS_H
#define CPROVER_JAVA_BYTECODE_JAVA_POINTER_CASTS_H

class exprt;
class typet;
class pointer_typet;
class namespacet;

bool find_superclass_with_type(
  exprt &ptr,
  const typet &target_type,
  const namespacet &ns);

exprt make_clean_pointer_cast(
  const exprt &ptr,
  const pointer_typet &target_type,
  const namespacet &ns);

#endif // CPROVER_JAVA_BYTECODE_JAVA_POINTER_CASTS_H
