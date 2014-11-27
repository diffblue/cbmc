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

Function: safe_c_str2number

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

template <typename T>
inline T str2number(const char *str, int base, bool safe)
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

  if(safe)
  {
    assert(0 == errno);
    errno=errno_bak;
    assert(endptr!=str);
    assert(val <= std::numeric_limits<T>::max());
    assert(val >= std::numeric_limits<T>::min());
  }
  
  return (T)val;
}

/*******************************************************************\

Function: safe_c_str2int

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int safe_c_str2int(const char *str, int base)
{
  return str2number<int>(str, base, true);
}

/*******************************************************************\

Function: safe_c_str2unsigned

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

unsigned safe_c_str2unsigned(const char *str, int base)
{
  return str2number<unsigned>(str, base, true);
}

/*******************************************************************\

Function: safe_string2int

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int safe_string2int(const std::string &str, int base)
{
  return str2number<int>(str.c_str(), base, true);
}

/*******************************************************************\

Function: safe_string2unsigned

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

unsigned safe_string2unsigned(const std::string &str, int base)
{
  return str2number<unsigned>(str.c_str(), base, true);
}

/*******************************************************************\

Function: unsafe_c_str2int

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int unsafe_c_str2int(const char *str, int base)
{
  return str2number<int>(str, base, false);
}

/*******************************************************************\

Function: unsafe_c_str2unsigned

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

unsigned unsafe_c_str2unsigned(const char *str, int base)
{
  return str2number<unsigned>(str, base, false);
}

/*******************************************************************\

Function: unsafe_string2int

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int unsafe_string2int(const std::string &str, int base)
{
  return str2number<int>(str.c_str(), base, false);
}

/*******************************************************************\

Function: unsafe_string2unsigned

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

unsigned unsafe_string2unsigned(const std::string &str, int base)
{
  return str2number<unsigned>(str.c_str(), base, false);
}

/*******************************************************************\

Function: unsafe_string2signedlonglong

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

signed long long int unsafe_string2signedlonglong(const std::string &str, int base)
{
  return str2number<signed long long int>(str.c_str(), base, false);
}

/*******************************************************************\

Function: unsafe_string2unsignedlonglong

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

unsigned long long int unsafe_string2unsignedlonglong(const std::string &str, int base)
{
  return str2number<unsigned long long int>(str.c_str(), base, false);
}

