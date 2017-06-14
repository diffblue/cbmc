/*******************************************************************\

Module: Misc Utilities

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Misc Utilities

#ifndef CPROVER_UTIL_ARRAY_NAME_H
#define CPROVER_UTIL_ARRAY_NAME_H

#include <string>

class namespacet;
class exprt;

std::string array_name(const namespacet &ns, const exprt &expr);

#endif // CPROVER_UTIL_ARRAY_NAME_H
