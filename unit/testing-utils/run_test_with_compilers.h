/*******************************************************************\

Module: Unit test utilities

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// Utility for running a test with different compilers.

#ifndef CPROVER_TESTING_UTILS_RUN_TEST_WITH_COMPILERS_H
#define CPROVER_TESTING_UTILS_RUN_TEST_WITH_COMPILERS_H

#include <functional>
#include <string>

void run_test_with_compilers(
  const std::function<void(const std::string &)> &test_with_compiler);

#endif // CPROVER_TESTING_UTILS_RUN_TEST_WITH_COMPILERS_H
