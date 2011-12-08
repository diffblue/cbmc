/*******************************************************************\

Module:

Author: Michael Tautschnig, michael.tautschnig@cs.ox.ac.uk

\*******************************************************************/

#include "string2int.h"

#include <cerrno>
#include <cstdlib>
#include <limits>
#include <cassert>

/*******************************************************************\

Function: safe_string2number

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

template <typename T>
T safe_string2number(const char *str, int base)
{
  int errno_bak=errno;
  errno=0;
  char * endptr;
  const long long val=strtoll(str, &endptr, base);
  assert(0 == errno);
  errno=errno_bak;
  assert(endptr!=str);
  assert(val <= std::numeric_limits<T>::max());
  assert(val >= std::numeric_limits<T>::min());
  return val;
}

/*******************************************************************\

Function: safe_string2int

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int safe_string2int(const char *str, int base)
{
  return safe_string2number<int>(str, base);
}

/*******************************************************************\

Function: safe_string2unsigned

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

unsigned safe_string2unsigned(const char *str, int base)
{
  return safe_string2number<unsigned>(str, base);
}

