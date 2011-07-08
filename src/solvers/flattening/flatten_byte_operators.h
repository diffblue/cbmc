/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_FLATTEN_BYTE_OPERATORS_H
#define CPROVER_FLATTEN_BYTE_OPERATORS_H

#include <expr.h>

exprt flatten_byte_extract(const exprt &src);
exprt flatten_byte_update(const exprt &src);

#endif
