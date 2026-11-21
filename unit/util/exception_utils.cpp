/*******************************************************************\

Module: Unit tests for cprover_exception_baset

Author: Daniel Kroening

\*******************************************************************/

#include <util/exception_utils.h>

#include <testing-utils/use_catch.h>

#include <type_traits>

namespace
{
/// cprover_exception_baset can only be constructed through derived classes.
class test_exceptiont : public cprover_exception_baset
{
};
} // namespace

static_assert(
  !std::is_default_constructible<cprover_exception_baset>::value,
  "cprover_exception_baset is to be used through derived classes only");

TEST_CASE(
  "cprover_exception_baset default construction",
  "[core][util][exception_utils]")
{
  test_exceptiont e;
  CHECK(e.reason().empty());
}

TEST_CASE(
  "cprover_exception_baset with message via operator<<",
  "[core][util][exception_utils]")
{
  auto e = test_exceptiont{} << "something went wrong";
  CHECK(e.what() == "something went wrong");
}

TEST_CASE(
  "cprover_exception_baset streaming multiple values",
  "[core][util][exception_utils]")
{
  auto e = test_exceptiont{} << "error " << 42 << " occurred";
  CHECK(e.what() == "error 42 occurred");
}

TEST_CASE(
  "operator<< preserves the exception type",
  "[core][util][exception_utils]")
{
  // must not slice to cprover_exception_baset
  REQUIRE_THROWS_AS(
    throw system_exceptiont{"file"} << " not found", system_exceptiont);
}

TEST_CASE(
  "cprover_exception_baset copy constructor",
  "[core][util][exception_utils]")
{
  auto original = test_exceptiont{} << "copy test";

  test_exceptiont copy(original);
  CHECK(copy.what() == "copy test");

  // Modifying the copy doesn't affect the original
  copy << " extra";
  CHECK(copy.what() == "copy test extra");
  CHECK(original.what() == "copy test");
}

TEST_CASE(
  "operator<< on a temporary yields the exception itself",
  "[core][util][exception_utils]")
{
  // The result must not be a reference to the temporary, which no longer
  // exists at the end of the full expression.
  static_assert(
    std::is_same<decltype(test_exceptiont{} << "text"), test_exceptiont>::value,
    "");
  test_exceptiont e;
  static_assert(
    std::is_same<decltype(e << "text"), test_exceptiont &>::value, "");
  e << "text";
  CHECK(e.what() == "text");
}

TEST_CASE(
  "cprover_exception_baset constructed with a reason appends to it",
  "[core][util][exception_utils]")
{
  auto e = system_exceptiont{"file"} << " not found";
  CHECK(e.what() == "file not found");
}
