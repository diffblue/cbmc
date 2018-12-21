/*******************************************************************\

Module: Unit test utilities

Author: Diffblue Ltd.

\*******************************************************************/

#include "run_test_with_compilers.h"

void run_test_with_compilers(
  const std::function<void(const std::string &)> &test_with_compiler)
{
  test_with_compiler(std::string("openjdk_8"));
  test_with_compiler(std::string("eclipse"));
  test_with_compiler(std::string("oracle_8"));
  test_with_compiler(std::string("oracle_9"));
}
