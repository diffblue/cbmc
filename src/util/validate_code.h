/*******************************************************************\

Module: Validate code

Author: Daniel Poetzl

\*******************************************************************/

#ifndef CPROVER_UTIL_VALIDATE_CODE_H
#define CPROVER_UTIL_VALIDATE_CODE_H

class codet;
class namespacet;
enum class validation_modet;

void check_code(const codet &code, const validation_modet vm);

void validate_code(
  const codet &code,
  const namespacet &ns,
  const validation_modet vm);

void validate_full_code(
  const codet &code,
  const namespacet &ns,
  const validation_modet vm);

#endif /* CPROVER_UTIL_VALIDATE_CODE_H */
