/*******************************************************************\

Module: Unit tests for cprover_exception_baset

Author: Daniel Kroening

\*******************************************************************/

#include <util/exception_utils.h>

#include <testing-utils/use_catch.h>

TEST_CASE(
  "cprover_exception_baset default construction",
  "[core][util][exception_utils]")
{
  cprover_exception_baset e;
  CHECK(e.reason().empty());
}

TEST_CASE(
  "cprover_exception_baset with message via operator<<",
  "[core][util][exception_utils]")
{
  auto e = cprover_exception_baset{} << "something went wrong";
  CHECK(e.what() == "something went wrong");
}

TEST_CASE(
  "cprover_exception_baset streaming multiple values",
  "[core][util][exception_utils]")
{
  auto e = cprover_exception_baset{} << "error " << 42 << " occurred";
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
  auto original = cprover_exception_baset{} << "copy test";

  cprover_exception_baset copy(original);
  CHECK(copy.what() == "copy test");

  // Modifying the copy doesn't affect the original
  copy << " extra";
  CHECK(copy.what() == "copy test extra");
  CHECK(original.what() == "copy test");
}
