/*******************************************************************\

Module: Unit test utilities

Author: Diffblue Limited.

\*******************************************************************/

#ifndef CPROVER_TESTING_UTILS_REQUIRE_VECTORS_EQUAL_UNORDERED_H
#define CPROVER_TESTING_UTILS_REQUIRE_VECTORS_EQUAL_UNORDERED_H

#include <testing-utils/catch.hpp>
#include <vector>

/// Checks whether two vectors are equal, ignoring ordering
/// \tparam T: The type of the vector contents
/// \param actual: The vector to check
/// \param expected: The vector to check against
template <class T>
void require_vectors_equal_unordered(
  const std::vector<T> &actual,
  const std::vector<T> &expected)
{
  REQUIRE(actual.size() == expected.size());
  REQUIRE_THAT(actual, Catch::Matchers::Vector::ContainsMatcher<T>{expected});
}

#endif // CPROVER_TESTING_UTILS_REQUIRE_VECTORS_EQUAL_UNORDERED_H
