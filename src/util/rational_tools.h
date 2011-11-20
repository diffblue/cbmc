/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_RATIONAL_TOOLS_H
#define CPROVER_RAITONAL_TOOLS_H

#include "rational.h"

bool to_rational(const exprt &expr, rationalt &rational_value);
exprt from_rational(const rationalt &rational_value);

#endif
