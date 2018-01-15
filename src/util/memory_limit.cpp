/*******************************************************************\

Module:

Author: Peter Schrammel, peter.schrammel@diffblue.com

\*******************************************************************/

#include "memory_limit.h"

#ifdef __linux__
#include <sys/resource.h>
#endif

#include <ostream>

/// Outputs the memory limits to the given output stream
/// \param out: output stream
void memory_limits(std::ostream &out)
{
#ifdef __linux__
  struct rlimit mem_limit;
  getrlimit(RLIMIT_AS, &mem_limit);

  out << "  soft limit: " << mem_limit.rlim_cur << '\n';
  out << "  hard limit: " << mem_limit.rlim_max;
#else
  out << "  not supported";
#endif
}

/// Sets the soft memory limit of the current process
/// \param soft_limit: the soft limit in bytes
/// \return: true if setting the limit succeeded
bool set_memory_limit(std::size_t soft_limit)
{
#ifdef __linux__
  struct rlimit mem_limit;
  getrlimit(RLIMIT_AS, &mem_limit);
  mem_limit.rlim_cur = soft_limit;
  setrlimit(RLIMIT_AS, &mem_limit);
  getrlimit(RLIMIT_AS, &mem_limit);
  return mem_limit.rlim_cur == soft_limit;
#else
  // not supported
  return false;
#endif
}
