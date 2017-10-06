/*******************************************************************\

 Module: Catch Tests

 Author: Diffblue Limited. All rights reserved.

\*******************************************************************/

#define CATCH_CONFIG_MAIN
#include "catch.hpp"
#include <util/irep.h>

// Debug printer for irept
std::ostream &operator<<(std::ostream &os, const irept &value)
{
  os << value.pretty();
  return os;
}
