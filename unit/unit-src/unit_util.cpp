/*******************************************************************\

 Module: Unit Test Utility Functions

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/
#include "unit_util.h"

std::ostream &operator<<(std::ostream &os, const irept &value)
{
  os << value.pretty();
  return os;
}
