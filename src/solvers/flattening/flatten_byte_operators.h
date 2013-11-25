/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_FLATTEN_BYTE_OPERATORS_H
#define CPROVER_FLATTEN_BYTE_OPERATORS_H

#include <util/expr.h>
#include <util/namespace.h>

exprt flatten_byte_extract(const exprt &src, const namespacet &ns);
exprt flatten_byte_update(const exprt &src, const namespacet &ns);
exprt flatten_byte_operators(const exprt &src, const namespacet &ns);
bool has_byte_operator(const exprt &src);

#endif
