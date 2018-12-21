/*******************************************************************\

Module: Catch Tests

Author: Diffblue Ltd.

\*******************************************************************/

#define CATCH_CONFIG_MAIN
#include <testing-utils/catch.hpp>
#include <util/irep.h>

// Debug printer for irept
std::ostream &operator<<(std::ostream &os, const irept &value)
{
  os << value.pretty();
  return os;
}
