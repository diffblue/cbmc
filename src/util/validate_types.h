/*******************************************************************\

Module: Validate types

Author: Daniel Poetzl

\*******************************************************************/

#ifndef CPROVER_UTIL_VALIDATE_TYPES_H
#define CPROVER_UTIL_VALIDATE_TYPES_H

class typet;
class namespacet;
enum class validation_modet;

void check_type(const typet &type, const validation_modet vm);

void validate_type(
  const typet &type,
  const namespacet &ns,
  const validation_modet vm);

void validate_full_type(
  const typet &type,
  const namespacet &ns,
  const validation_modet vm);

#endif /* CPROVER_UTIL_VALIDATE_TYPES_H */
