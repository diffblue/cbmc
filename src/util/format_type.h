/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_UTIL_FORMAT_TYPE_H
#define CPROVER_UTIL_FORMAT_TYPE_H

#include "format.h"

class typet;

//! Formats a type in a generic syntax
//! that is inspired by C/C++/Java, and is meant for debugging
std::ostream &format_rec(std::ostream &, const typet &);

#endif // CPROVER_UTIL_FORMAT_TYPE_H
