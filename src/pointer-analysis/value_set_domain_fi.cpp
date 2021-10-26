/*******************************************************************\

Module: Value Set Domain (Flow Insensitive)

Author: Daniel Kroening, kroening@kroening.com
        CM Wintersteiger

\*******************************************************************/

/// \file
/// Value Set Domain (Flow Insensitive)

#include "value_set_domain_fi.h"

#include <util/std_code.h>

bool value_set_domain_fit::transform(
  const namespacet &ns,
  const irep_idt &function_from,
  locationt from_l,
  const irep_idt &function_to,
  locationt to_l)
{
  value_set.changed = false;

  value_set.set_from(function_from, from_l->location_number);
  value_set.set_to(function_to, to_l->location_number);

  //  std::cout << "transforming: " <<
  //      from_l->function << " " << from_l->location_number << " to " <<
  //      to_l->function << " " << to_l->location_number << '\n';

  switch(from_l->type())
  {
  case GOTO:
    // ignore for now
    break;

  case END_FUNCTION:
    value_set.do_end_function(get_return_lhs(to_l), ns);
    break;

  case SET_RETURN_VALUE:
  case OTHER:
  case ASSIGN:
    value_set.apply_code(from_l->get_code(), ns);
    break;

  case FUNCTION_CALL:
    value_set.do_function_call(function_to, from_l->call_arguments(), ns);
    break;

  case CATCH:
  case THROW:
  case DECL:
  case DEAD:
  case ATOMIC_BEGIN:
  case ATOMIC_END:
  case START_THREAD:
  case END_THREAD:
  case LOCATION:
  case SKIP:
  case ASSERT:
  case ASSUME:
  case INCOMPLETE_GOTO:
  case NO_INSTRUCTION_TYPE:
    // do nothing
    break;
  }

  return (value_set.changed);
}
