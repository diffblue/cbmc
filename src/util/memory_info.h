/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_MEMORY_INFO_H
#define CPROVER_UTIL_MEMORY_INFO_H

#include <cstddef>
#include <iosfwd>

void memory_info(std::ostream &);

/// Return current peak resident set size in bytes, or 0 if unavailable.
std::size_t peak_memory_bytes();

#endif // CPROVER_UTIL_MEMORY_INFO_H
