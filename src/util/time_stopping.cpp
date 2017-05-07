/*******************************************************************\

Module: Time Stopping

Author: Daniel Kroening

Date: February 2004

\*******************************************************************/

/// \file
/// Time Stopping

#include "time_stopping.h"

#include <sstream>

#if defined(_WIN32) && !defined(__MINGW32__)
#include <windows.h>
#include <winbase.h>
#else
#include <sys/time.h>
#endif

#if defined(_WIN32) && !defined(__MINGW32__)
// NOLINTNEXTLINE(readability/identifiers)
struct timezone
{
  int dummy;
};

// NOLINTNEXTLINE(readability/identifiers)
void gettimeofday(struct timeval* p, struct timezone *tz)
{
  union
  {
    long long ns100; /*time since 1 Jan 1601 in 100ns units */
    FILETIME ft;
  } _now;

  GetSystemTimeAsFileTime(&(_now.ft));
  p->tv_usec=(long)((_now.ns100 / 10LL) % 1000000LL);
  p->tv_sec= (long)((_now.ns100-(116444736000000000LL))/10000000LL);
}
#endif

absolute_timet current_time()
{
  // NOLINTNEXTLINE(readability/identifiers)
  struct timeval tv;
  // NOLINTNEXTLINE(readability/identifiers)
  struct timezone tz;

  gettimeofday(&tv, &tz);

  return absolute_timet(tv.tv_usec/1000+(unsigned long long)tv.tv_sec*1000);
}

std::ostream &operator << (std::ostream &out, const time_periodt &period)
{
  return out << static_cast<double>(period.get_t())/1000;
}

std::string time_periodt::as_string() const
{
  std::ostringstream out;
  out << *this;
  return out.str();
}
