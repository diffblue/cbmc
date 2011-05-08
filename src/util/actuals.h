/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_ACTUALS_H
#define CPROVER_ACTUALS_H

#include "replace_symbol.h"

void get_actual_map(const exprt &expr,
                    replace_symbolt &actual_map);
                    
#endif
