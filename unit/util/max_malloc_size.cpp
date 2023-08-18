/*******************************************************************\

Module: Unit test for max_malloc_size

Author: Thomas Kiley

\*******************************************************************/

#include <util/config.h>

#include <testing-utils/use_catch.h>

TEST_CASE("max_malloc_size", "[core][util][config][max_malloc_size]")
{
  cbmc_invariants_should_throwt throw_invariants;

  configt config_backup = config;

  SECTION("Too many bits for pointer ID")
  {
    config.ansi_c.pointer_width = 4;
    config.bv_encoding.object_bits = 4;
    REQUIRE_THROWS_AS(config.max_malloc_size(), invariant_failedt);
    config.bv_encoding.object_bits = 5;
    REQUIRE_THROWS_AS(config.max_malloc_size(), invariant_failedt);
  }

  SECTION("Not enough bits for pointer ID")
  {
    config.ansi_c.pointer_width = 4;
    config.bv_encoding.object_bits = 0;
    REQUIRE_THROWS_AS(config.max_malloc_size(), invariant_failedt);
  }

  SECTION("Not enough bits in the pointer")
  {
    config.ansi_c.pointer_width = 0;
    config.bv_encoding.object_bits = 0;
    REQUIRE_THROWS_AS(config.max_malloc_size(), invariant_failedt);
  }

  SECTION("Valid allocation size configurations")
  {
    // The one bit offset can be used to store 0, or -1, so we can allocate
    // a single bit
    config.ansi_c.pointer_width = 4;
    config.bv_encoding.object_bits = 3;
    REQUIRE(config.max_malloc_size() == 1);
    // Here we use 4 bits for the object ID, leaving 3 for the offset
    config.ansi_c.pointer_width = 8;
    config.bv_encoding.object_bits = 4;
    REQUIRE(config.max_malloc_size() == 8);
    config.ansi_c.pointer_width = 128;
    config.bv_encoding.object_bits = 64;
    REQUIRE(config.max_malloc_size() == 9223372036854775808ull /*2^63*/);
    config.bv_encoding.object_bits = 63;
    REQUIRE(
      config.max_malloc_size() == string2integer("18446744073709551616"
                                                 /*2^64*/));
  }

  std::swap(config_backup, config);
}
