// Author: Michael Tautschnig

/// \file
/// Unit tests for popcount_exprt::lower() and
/// count_leading_zeros_exprt::lower() with signed operands whose width
/// is not a power of two.

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/namespace.h>
#include <util/simplify_expr.h>
#include <util/symbol_table.h>

#include <testing-utils/use_catch.h>

TEST_CASE(
  "popcount of signed non-power-of-2 width constant",
  "[core][util][bitvector_expr]")
{
  symbol_tablet symbol_table;
  const namespacet ns{symbol_table};

  // 3-bit signed value -1: binary 111, popcount = 3.
  // The old code did a single typecast from signedbv[3] to unsignedbv[4],
  // which sign-extends 111 -> 1111 (popcount 4).  The fix first casts to
  // unsignedbv[3] (preserving bits), then zero-extends to unsignedbv[4].
  SECTION("signedbv 3-bit -1 has popcount 3")
  {
    const signedbv_typet s3{3};
    const auto minus_one = from_integer(-1, s3);
    const popcount_exprt pc{minus_one};
    const exprt lowered = simplify_expr(pc.lower(), ns);
    const auto result = numeric_cast<mp_integer>(lowered);
    REQUIRE(result.has_value());
    CHECK(result.value() == 3);
  }

  // 5-bit signed value -4: binary 11100, popcount = 3.
  // Old code: signedbv[5] -> unsignedbv[8] sign-extends to 11111100
  // (popcount 6).  Fix: signedbv[5] -> unsignedbv[5] -> unsignedbv[8]
  // zero-extends to 00011100 (popcount 3).
  SECTION("signedbv 5-bit -4 has popcount 3")
  {
    const signedbv_typet s5{5};
    const auto val = from_integer(-4, s5);
    const popcount_exprt pc{val};
    const exprt lowered = simplify_expr(pc.lower(), ns);
    const auto result = numeric_cast<mp_integer>(lowered);
    REQUIRE(result.has_value());
    CHECK(result.value() == 3);
  }

  // Unsigned non-power-of-2 width should still work (no sign issue).
  SECTION("unsignedbv 3-bit 5 (101) has popcount 2")
  {
    const unsignedbv_typet u3{3};
    const auto val = from_integer(5, u3);
    const popcount_exprt pc{val};
    const exprt lowered = simplify_expr(pc.lower(), ns);
    const auto result = numeric_cast<mp_integer>(lowered);
    REQUIRE(result.has_value());
    CHECK(result.value() == 2);
  }
}

TEST_CASE(
  "count_leading_zeros of signed non-power-of-2 width constant",
  "[core][util][bitvector_expr]")
{
  symbol_tablet symbol_table;
  const namespacet ns{symbol_table};

  // 3-bit signed value -2: binary 110, leading zeros = 0.
  // Old code: signedbv[3] -> unsignedbv[4] sign-extends to 1110 (clz 0),
  // then subtracts (4-3)=1 giving -1.  Fix: signedbv[3] -> unsignedbv[3]
  // -> unsignedbv[4] zero-extends to 0110 (clz 1), subtract 1 -> 0.
  SECTION("signedbv 3-bit -2 has clz 0")
  {
    const signedbv_typet s3{3};
    const auto val = from_integer(-2, s3);
    const count_leading_zeros_exprt clz{val};
    const exprt lowered = simplify_expr(clz.lower(), ns);
    const auto result = numeric_cast<mp_integer>(lowered);
    REQUIRE(result.has_value());
    CHECK(result.value() == 0);
  }

  // 5-bit signed value -16: binary 10000, leading zeros = 0.
  SECTION("signedbv 5-bit -16 has clz 0")
  {
    const signedbv_typet s5{5};
    const auto val = from_integer(-16, s5);
    const count_leading_zeros_exprt clz{val};
    const exprt lowered = simplify_expr(clz.lower(), ns);
    const auto result = numeric_cast<mp_integer>(lowered);
    REQUIRE(result.has_value());
    CHECK(result.value() == 0);
  }

  // 5-bit signed value 2: binary 00010, leading zeros = 3.
  SECTION("signedbv 5-bit 2 has clz 3")
  {
    const signedbv_typet s5{5};
    const auto val = from_integer(2, s5);
    const count_leading_zeros_exprt clz{val};
    const exprt lowered = simplify_expr(clz.lower(), ns);
    const auto result = numeric_cast<mp_integer>(lowered);
    REQUIRE(result.has_value());
    CHECK(result.value() == 3);
  }
}
