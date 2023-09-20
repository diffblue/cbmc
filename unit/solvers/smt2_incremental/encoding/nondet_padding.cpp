// Author: Diffblue Ltd.

#include <util/expr_cast.h>
#include <util/std_expr.h>

#include <solvers/smt2_incremental/encoding/nondet_padding.h>
#include <testing-utils/invariant.h>
#include <testing-utils/use_catch.h>

TEST_CASE("Nondet padding expression", "[core][smt2_incremental]")
{
  const bv_typet type{8};
  const exprt padding = nondet_padding_exprt{type};
  SECTION("Valid usage")
  {
    REQUIRE(padding.type() == type);
    REQUIRE(nullptr != expr_try_dynamic_cast<nondet_padding_exprt>(padding));
  }
  const auto type_error = invariant_failure_containing(
    "Nondet padding is expected to pad a bit vector type.");
  SECTION("Failed downcasts")
  {
    const exprt not_padding = symbol_exprt{"foo", empty_typet{}};
    REQUIRE(
      nullptr == expr_try_dynamic_cast<nondet_padding_exprt>(not_padding));
    const exprt wrong_type = [&]() {
      exprt padding = nondet_padding_exprt{type};
      padding.type() = empty_typet{};
      return padding;
    }();
    cbmc_invariants_should_throwt invariants_throw;
    CHECK_THROWS_MATCHES(
      expr_checked_cast<nondet_padding_exprt>(wrong_type),
      invariant_failedt,
      type_error);
  }
  SECTION("Construction with incorrect type")
  {
    cbmc_invariants_should_throwt invariants_throw;
    CHECK_THROWS_MATCHES(
      nondet_padding_exprt{empty_typet{}}, invariant_failedt, type_error);
  }
}
