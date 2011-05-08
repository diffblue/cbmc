/*******************************************************************\

Module: Weakest Preconditions

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_WP_H
#define CPROVER_WP_H

#include <std_code.h>
#include <namespace.h>

exprt wp(const codet &code, const exprt &post, const namespacet &ns);

#endif
