/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_FLATTEN_BYTE_OPERATORS_H
#define CPROVER_FLATTEN_BYTE_OPERATORS_H

#include <expr.h>
#include <namespace.h>

exprt flatten_byte_extract(const exprt &src, const namespacet &ns);
exprt flatten_byte_update(const exprt &src, const namespacet &ns);

#endif
