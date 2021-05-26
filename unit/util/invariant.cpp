// Author: Diffblue Ltd.

/// \file Tests for macros in src/util/invariant.h

#include <testing-utils/invariant.h>
#include <testing-utils/use_catch.h>

#include <util/invariant.h>

TEST_CASE("Using the UNIMPLEMENTED macro", "[invariant]")
{
  cbmc_invariants_should_throwt invariants_throw;
  REQUIRE_THROWS_MATCHES(
    []() { UNIMPLEMENTED; }(),
    invariant_failedt,
    invariant_failure_containing("Reason: Unimplemented"));
}

TEST_CASE("Using the UNIMPLEMENTED_FEATURE macro", "[invariant]")
{
  cbmc_invariants_should_throwt invariants_throw;
  REQUIRE_THROWS_MATCHES(
    []() { UNIMPLEMENTED_FEATURE("example"); }(),
    invariant_failedt,
    invariant_failure_containing("Reason: Reached unimplemented example"));
}
