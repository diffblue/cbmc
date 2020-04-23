/*******************************************************************\

Module: Unit test for max_malloc_size

Author: Thomas Kiley

\*******************************************************************/

#include <ansi-c/ansi_c_internal_additions.cpp>
#include <testing-utils/use_catch.h>

TEST_CASE(
  "max_malloc_size",
  "[core][ansi-c][ansi_c_internal_additions][max_malloc_size]")
{
  cbmc_invariants_should_throwt throw_invariants;

  SECTION("Too many bits for pointer ID")
  {
    REQUIRE_THROWS_AS(max_malloc_size(4, 4), invariant_failedt);
    REQUIRE_THROWS_AS(max_malloc_size(4, 5), invariant_failedt);
  }

  SECTION("Not enough bits for pointer ID")
  {
    REQUIRE_THROWS_AS(max_malloc_size(4, 0), invariant_failedt);
  }

  SECTION("Not enough bits in the pointer")
  {
    REQUIRE_THROWS_AS(max_malloc_size(0, 0), invariant_failedt);
  }

  SECTION("Valid allocation size configurations")
  {
    // The one bit offset can be used to store 0, or -1, so we can allocate
    // a single bit
    REQUIRE(max_malloc_size(4, 3) == 1);
    // Here we use 4 bits for the object ID, leaving 3 for the offset
    REQUIRE(max_malloc_size(8, 4) == 8);
    REQUIRE(max_malloc_size(128, 64) == 9223372036854775808ull /*2^63*/);
    REQUIRE(
      max_malloc_size(128, 63) == string2integer("18446744073709551616"
                                                 /*2^64*/));
  }
}
