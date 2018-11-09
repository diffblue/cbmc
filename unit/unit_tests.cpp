/*******************************************************************\

Module: Catch Tests

Author: Diffblue Ltd.

\*******************************************************************/

#define CATCH_CONFIG_MAIN
#include <testing-utils/use_catch.h>
#include <util/irep.h>

// Debug printer for irept
std::ostream &operator<<(std::ostream &os, const irept &value)
{
  os << value.pretty();
  return os;
}
