// Author: Diffblue Ltd.

#include <testing-utils/use_catch.h>

#include <solvers/smt2_incremental/smt_response_validation.h>

TEST_CASE("response_or_errort storage", "[core][smt2_incremental]")
{
  SECTION("Error response")
  {
    const std::string message{"Test error message"};
    const response_or_errort<smt_responset> error{message};
    CHECK_FALSE(error.get_if_valid());
    CHECK(*error.get_if_error() == std::vector<std::string>{message});
  }
  SECTION("Valid response")
  {
    const response_or_errort<smt_responset> valid{smt_unsupported_responset{}};
    CHECK_FALSE(valid.get_if_error());
    CHECK(*valid.get_if_valid() == smt_unsupported_responset{});
  }
}
