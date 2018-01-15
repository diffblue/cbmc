/*******************************************************************\

Module:

Author: Peter Schrammel, peter.schrammel@diffblue.com

\*******************************************************************/

#ifndef CPROVER_UTIL_MEMORY_LIMIT_H
#define CPROVER_UTIL_MEMORY_LIMIT_H

#include <cstddef> // size_t
#include <iosfwd>

void memory_limits(std::ostream &);
bool set_memory_limit(std::size_t soft_limit);

#endif // CPROVER_UTIL_MEMORY_LIMIT_H
