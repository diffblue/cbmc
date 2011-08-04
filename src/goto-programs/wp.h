/*******************************************************************\

Module: Weakest Preconditions

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_WP_H
#define CPROVER_WP_H

#include <std_code.h>
#include <namespace.h>

// This computes the weakest precondition of the given program
// piece 'code' with respect to the expression 'post'.

exprt wp(
  const codet &code,
  const exprt &post,
  const namespacet &ns);

#endif
