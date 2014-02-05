/*******************************************************************\

Module:

Author: Michael Tautschnig, michael.tautschnig@cs.ox.ac.uk

\*******************************************************************/

#include <cerrno>
#include <cstdlib>
#include <limits>
#include <cassert>

#include "string2int.h"

/*******************************************************************\

Function: safe_str2number

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

template <typename T>
inline T safe_str2number(const char *str, int base)
{
  int errno_bak=errno;
  errno=0;
  char * endptr;
// _strtoi64 is available in Visual Studio, but not yet in MINGW
#ifdef _MSC_VER
  const __int64 val=_strtoi64(str, &endptr, base);
#else
  const long long val=strtoll(str, &endptr, base);
#endif
  assert(0 == errno);
  errno=errno_bak;
  assert(endptr!=str);
  assert(val <= std::numeric_limits<T>::max());
  assert(val >= std::numeric_limits<T>::min());
  return (T)val;
}

/*******************************************************************\

Function: safe_str2int

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int safe_str2int(const char *str, int base)
{
  return safe_str2number<int>(str, base);
}

/*******************************************************************\

Function: safe_str2unsigned

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

unsigned safe_str2unsigned(const char *str, int base)
{
  return safe_str2number<unsigned>(str, base);
}

/*******************************************************************\

Function: safe_string2int

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int safe_string2int(const std::string &str, int base)
{
  return safe_str2number<int>(str.c_str(), base);
}

/*******************************************************************\

Function: safe_string2unsigned

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

unsigned safe_string2unsigned(const std::string &str, int base)
{
  return safe_str2number<unsigned>(str.c_str(), base);
}

