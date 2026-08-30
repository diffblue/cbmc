/*******************************************************************\

Module: Unit tests for util/ieee_float

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include <util/ieee_float.h>

#include <testing-utils/use_catch.h>

#include <limits>

TEST_CASE("Make an IEEE 754 one", "[core][util][ieee_float]")
{
  auto spec = ieee_float_spect::single_precision();
  REQUIRE(ieee_floatt::one(spec) == 1);
}

TEST_CASE("round_to_integral", "[unit][util][ieee_float]")
{
  auto from_double = [](double d) -> ieee_float_valuet
  {
    ieee_float_valuet v;
    v.from_double(d);
    return v;
  };

  auto round_to_integral =
    [](ieee_float_valuet op, ieee_floatt::rounding_modet rm) {
      return ieee_floatt{op, rm}.round_to_integral();
    };

  const auto dp = ieee_float_spect::double_precision();

  const auto NaN = ieee_float_valuet::NaN(dp);
  const auto plus_inf = ieee_float_valuet::plus_infinity(dp);
  const auto minus_inf = ieee_float_valuet::minus_infinity(dp);
  const auto dmax = std::numeric_limits<double>::max();

  const auto up = ieee_floatt::ROUND_TO_PLUS_INF;

  REQUIRE(round_to_integral(NaN, up) == NaN);
  REQUIRE(round_to_integral(plus_inf, up) == plus_inf);
  REQUIRE(round_to_integral(minus_inf, up) == minus_inf);
  REQUIRE(round_to_integral(from_double(0), up) == 0);
  REQUIRE(round_to_integral(from_double(-0.0), up) == -0.0);
  REQUIRE(round_to_integral(from_double(1), up) == 1);
  REQUIRE(round_to_integral(from_double(0.1), up) == 1);
  REQUIRE(round_to_integral(from_double(-0.1), up) == -0.0);
  REQUIRE(round_to_integral(from_double(0.5), up) == 1);
  REQUIRE(round_to_integral(from_double(0.49999999), up) == 1);
  REQUIRE(round_to_integral(from_double(0.500000001), up) == 1);
  REQUIRE(round_to_integral(from_double(10.1), up) == 11);
  REQUIRE(round_to_integral(from_double(-10.1), up) == -10);
  REQUIRE(round_to_integral(from_double(0x1.0p+52), up) == 0x1.0p+52);
  REQUIRE(round_to_integral(from_double(dmax), up) == dmax);

  const auto down = ieee_floatt::ROUND_TO_MINUS_INF;

  REQUIRE(round_to_integral(NaN, down) == NaN);
  REQUIRE(round_to_integral(plus_inf, down) == plus_inf);
  REQUIRE(round_to_integral(minus_inf, down) == minus_inf);
  REQUIRE(round_to_integral(from_double(0), down) == 0);
  REQUIRE(round_to_integral(from_double(-0.0), down) == -0.0);
  REQUIRE(round_to_integral(from_double(1), down) == 1);
  REQUIRE(round_to_integral(from_double(0.1), down) == 0);
  REQUIRE(round_to_integral(from_double(-0.1), down) == -1);
  REQUIRE(round_to_integral(from_double(0.5), down) == 0);
  REQUIRE(round_to_integral(from_double(0.49999999), down) == 0);
  REQUIRE(round_to_integral(from_double(0.500000001), down) == 0);
  REQUIRE(round_to_integral(from_double(10.1), down) == 10);
  REQUIRE(round_to_integral(from_double(-10.1), down) == -11);
  REQUIRE(round_to_integral(from_double(0x1.0p+52), down) == 0x1.0p+52);
  REQUIRE(round_to_integral(from_double(dmax), down) == dmax);

  const auto even = ieee_floatt::ROUND_TO_EVEN;

  REQUIRE(round_to_integral(NaN, even) == NaN);
  REQUIRE(round_to_integral(plus_inf, even) == plus_inf);
  REQUIRE(round_to_integral(minus_inf, even) == minus_inf);
  REQUIRE(round_to_integral(from_double(0), even) == 0);
  REQUIRE(round_to_integral(from_double(-0.0), even) == -0.0);
  REQUIRE(round_to_integral(from_double(1), even) == 1);
  REQUIRE(round_to_integral(from_double(0.1), even) == 0);
  REQUIRE(round_to_integral(from_double(-0.1), even) == -0.0);
  REQUIRE(round_to_integral(from_double(0.5), even) == 0);
  REQUIRE(round_to_integral(from_double(0.49999999), even) == 0);
  REQUIRE(round_to_integral(from_double(0.500000001), even) == 1);
  REQUIRE(round_to_integral(from_double(10.1), even) == 10);
  REQUIRE(round_to_integral(from_double(-10.1), even) == -10);
  REQUIRE(round_to_integral(from_double(0x1.0p+52), even) == 0x1.0p+52);
  REQUIRE(round_to_integral(from_double(dmax), even) == dmax);

  const auto zero = ieee_floatt::ROUND_TO_ZERO;

  REQUIRE(round_to_integral(NaN, zero) == NaN);
  REQUIRE(round_to_integral(plus_inf, zero) == plus_inf);
  REQUIRE(round_to_integral(minus_inf, zero) == minus_inf);
  REQUIRE(round_to_integral(from_double(0), zero) == 0);
  REQUIRE(round_to_integral(from_double(-0.0), zero) == -0.0);
  REQUIRE(round_to_integral(from_double(1), zero) == 1);
  REQUIRE(round_to_integral(from_double(0.1), zero) == 0);
  REQUIRE(round_to_integral(from_double(-0.1), zero) == -0.0);
  REQUIRE(round_to_integral(from_double(0.5), zero) == 0);
  REQUIRE(round_to_integral(from_double(0.49999999), zero) == 0);
  REQUIRE(round_to_integral(from_double(0.500000001), zero) == 0);
  REQUIRE(round_to_integral(from_double(10.1), zero) == 10);
  REQUIRE(round_to_integral(from_double(-10.1), zero) == -10);
  REQUIRE(round_to_integral(from_double(0x1.0p+52), zero) == 0x1.0p+52);
  REQUIRE(round_to_integral(from_double(dmax), zero) == dmax);

  const auto away = ieee_floatt::ROUND_TO_AWAY;

  REQUIRE(round_to_integral(NaN, away) == NaN);
  REQUIRE(round_to_integral(plus_inf, away) == plus_inf);
  REQUIRE(round_to_integral(minus_inf, away) == minus_inf);
  REQUIRE(round_to_integral(from_double(0), away) == 0);
  REQUIRE(round_to_integral(from_double(-0.0), away) == -0.0);
  REQUIRE(round_to_integral(from_double(1), away) == 1);
  REQUIRE(round_to_integral(from_double(0.1), away) == 0);
  REQUIRE(round_to_integral(from_double(-0.1), away) == -0.0);
  REQUIRE(round_to_integral(from_double(0.5), away) == 1);
  REQUIRE(round_to_integral(from_double(0.49999999), away) == 0);
  REQUIRE(round_to_integral(from_double(0.500000001), away) == 1);
  REQUIRE(round_to_integral(from_double(10.1), away) == 10);
  REQUIRE(round_to_integral(from_double(-10.1), away) == -10);
  REQUIRE(round_to_integral(from_double(0x1.0p+52), away) == 0x1.0p+52);
  REQUIRE(round_to_integral(from_double(dmax), away) == dmax);
}

TEST_CASE(
  "ieee_float_valuet to_double / to_float round-trip",
  "[core][util][ieee_float]")
{
  auto from_double = [](double d) -> ieee_float_valuet
  {
    ieee_float_valuet v;
    v.from_double(d);
    return v;
  };
  auto from_float = [](float f) -> ieee_float_valuet
  {
    ieee_float_valuet v;
    v.from_float(f);
    return v;
  };

  SECTION("to_double is a bit-exact reinterpretation")
  {
    REQUIRE(from_double(0.0).to_double() == 0.0);
    REQUIRE(from_double(1.0).to_double() == 1.0);
    REQUIRE(from_double(-2.5).to_double() == -2.5);
    REQUIRE(from_double(3.14159).to_double() == 3.14159);
    REQUIRE(
      from_double(std::numeric_limits<double>::infinity()).to_double() ==
      std::numeric_limits<double>::infinity());
    REQUIRE(
      from_double(std::numeric_limits<double>::max()).to_double() ==
      std::numeric_limits<double>::max());
  }

  SECTION("to_float is a bit-exact reinterpretation")
  {
    REQUIRE(from_float(0.0f).to_float() == 0.0f);
    REQUIRE(from_float(1.0f).to_float() == 1.0f);
    REQUIRE(from_float(-2.5f).to_float() == -2.5f);
    REQUIRE(
      from_float(std::numeric_limits<float>::infinity()).to_float() ==
      std::numeric_limits<float>::infinity());
  }
}

TEST_CASE(
  "ieee_float_valuet to_integer truncates towards zero",
  "[core][util][ieee_float]")
{
  auto from_double = [](double d) -> ieee_float_valuet
  {
    ieee_float_valuet v;
    v.from_double(d);
    return v;
  };

  // to_integer always rounds towards zero (truncation), independent of any
  // rounding mode -- this is the caveat that justifies it living on
  // ieee_float_valuet rather than ieee_floatt.
  SECTION("positive values truncate down")
  {
    REQUIRE(from_double(0.0).to_integer() == 0);
    REQUIRE(from_double(0.9).to_integer() == 0);
    REQUIRE(from_double(1.0).to_integer() == 1);
    REQUIRE(from_double(3.9).to_integer() == 3);
    REQUIRE(from_double(1e10).to_integer() == 10000000000);
  }

  SECTION("negative values truncate towards zero, not down")
  {
    REQUIRE(from_double(-0.0).to_integer() == 0);
    REQUIRE(from_double(-0.9).to_integer() == 0);
    REQUIRE(from_double(-1.0).to_integer() == -1);
    // truncation towards zero gives -3, not -4 (which round-to-minus-infinity
    // would give)
    REQUIRE(from_double(-3.9).to_integer() == -3);
    REQUIRE(from_double(-1e10).to_integer() == -10000000000);
  }

  SECTION("NaN and infinities map to zero")
  {
    const auto dp = ieee_float_spect::double_precision();
    REQUIRE(ieee_float_valuet::NaN(dp).to_integer() == 0);
    REQUIRE(ieee_float_valuet::plus_infinity(dp).to_integer() == 0);
    REQUIRE(ieee_float_valuet::minus_infinity(dp).to_integer() == 0);
  }
}

TEST_CASE(
  "ieee_float_spect: x86 extended specs",
  "[core][util][ieee_float][x86_extended]")
{
  // The 80-bit value contains 1 sign + 15 exponent + 1 explicit integer
  // bit + 63 fraction bits.  Storage may add padding to reach 96 or 128
  // bits.

  const auto x86_80 = ieee_float_spect::x86_80();
  REQUIRE(x86_80.f == 63);
  REQUIRE(x86_80.e == 15);
  REQUIRE(x86_80.x86_extended);
  REQUIRE(x86_80.value_width() == 80);
  REQUIRE(x86_80.width() == 80);

  const auto x86_96 = ieee_float_spect::x86_96();
  REQUIRE(x86_96.f == 63);
  REQUIRE(x86_96.e == 15);
  REQUIRE(x86_96.x86_extended);
  REQUIRE(x86_96.value_width() == 80);
  REQUIRE(x86_96.width() == 96);

  const auto x86_128 = ieee_float_spect::x86_128();
  REQUIRE(x86_128.f == 63);
  REQUIRE(x86_128.e == 15);
  REQUIRE(x86_128.x86_extended);
  REQUIRE(x86_128.value_width() == 80);
  REQUIRE(x86_128.width() == 128);

  // The bias is 2^(e-1)-1 = 16383.
  REQUIRE(x86_128.bias() == 16383);
}

TEST_CASE(
  "ieee_float_valuet: pack/unpack on x86 80-bit extended (all storage widths)",
  "[core][util][ieee_float][x86_extended]")
{
  // Reference encodings captured on macOS-15 x86_64 hardware (Apple
  // clang 17.0.0).  The 80-bit value pattern is the same across all
  // three storage widths; only the leading zero padding differs.
  //
  //   1.0L  -> 00 00 00 00 00 00 00 80 ff 3f [+ 0..6 zero pad bytes]
  //   -1.0L -> 00 00 00 00 00 00 00 80 ff bf [+ 0..6 zero pad bytes]
  //   2.0L  -> 00 00 00 00 00 00 00 80 00 40 [+ 0..6 zero pad bytes]
  //   0.5L  -> 00 00 00 00 00 00 00 80 fe 3f [+ 0..6 zero pad bytes]
  //   0.0L  -> 00 00 00 00 00 00 00 00 00 00 [+ 0..6 zero pad bytes]
  //
  // Storage padding is zero on Linux/macOS, so the mp_integer
  // representation is just the bottom 80 bits of the value, regardless
  // of whether the storage container is 80, 96 or 128 bits.

  auto from_hex = [](const char *hex) -> mp_integer
  { return string2integer(hex, 16); };

  // The bottom 80 bits of each reference value, written as a hex
  // big-endian word.  These are reused for x86_80, x86_96 and x86_128
  // because the storage padding above the value bits is zero.
  const mp_integer one_80 = from_hex("3FFF8000000000000000");
  const mp_integer neg_one_80 = from_hex("BFFF8000000000000000");
  const mp_integer two_80 = from_hex("40008000000000000000");
  const mp_integer half_80 = from_hex("3FFE8000000000000000");
  const mp_integer zero_80 = 0;

  // Smallest positive denormal: J=0, exp=0, frac=1.  Hardware encodes
  // this as 80 bits with the low fraction bit set and the J-bit clear,
  // i.e. mp_integer value 1.  Verifies the canonical denormal pattern
  // from `float_utilst::pack` / `float_bvt::pack` (J=0 for exp=0).
  const mp_integer smallest_denormal_80 = 1;

  // Positive infinity: J=1, exp=all-1s, frac=0.
  const mp_integer pos_inf_80 = from_hex("7FFF8000000000000000");

  // A representable quiet NaN: J=1, exp=all-1s, frac with at least one
  // bit set (here, the fraction MSB so the NaN is "quiet" on hardware
  // that interprets that bit as the quiet flag).
  const mp_integer quiet_nan_80 = from_hex("7FFFC000000000000000");

  for(const auto &spec :
      {ieee_float_spect::x86_80(),
       ieee_float_spect::x86_96(),
       ieee_float_spect::x86_128()})
  {
    auto make = [&spec](mp_integer i) -> ieee_floatt
    {
      ieee_floatt v{spec, ieee_floatt::ROUND_TO_EVEN};
      v.from_integer(i);
      return v;
    };

    // Hardware-reference round-trip for representable integer values.
    {
      const auto v = make(1);
      REQUIRE(v.pack() == one_80);

      ieee_float_valuet u{spec};
      u.unpack(one_80);
      REQUIRE(u == v);
    }

    {
      const auto v = make(-1);
      REQUIRE(v.pack() == neg_one_80);

      ieee_float_valuet u{spec};
      u.unpack(neg_one_80);
      REQUIRE(u == v);
    }

    {
      const auto v = make(2);
      REQUIRE(v.pack() == two_80);

      ieee_float_valuet u{spec};
      u.unpack(two_80);
      REQUIRE(u == v);
    }

    {
      const auto v = make(0);
      REQUIRE(v.pack() == zero_80);

      ieee_float_valuet u{spec};
      u.unpack(zero_80);
      REQUIRE(u == v);
    }

    // Round-trip a range of integers through pack/unpack.
    for(int i : {-1024, -3, -2, -1, 0, 1, 2, 3, 7, 1024})
    {
      const auto v = make(i);
      ieee_float_valuet u{spec};
      u.unpack(v.pack());
      REQUIRE(u == v);
    }

    // Non-integer encodings: NaN, infinity, smallest denormal.  These
    // exercise the special-case branches in `unpack`/`pack` that are
    // not reached by the integer round-trip above.

    // Positive infinity: unpack -> classify as infinity -> pack
    // re-emits the same canonical pattern.
    {
      ieee_float_valuet u{spec};
      u.unpack(pos_inf_80);
      REQUIRE(u.is_infinity());
      REQUIRE(!u.get_sign());
      REQUIRE(u.pack() == pos_inf_80);
    }

    // A quiet NaN.  Pack re-emits a canonical NaN pattern, which is
    // not necessarily bitwise equal to the input (the exact NaN
    // payload is implementation-defined), so we only check that the
    // round-trip preserves the NaN classification.
    {
      ieee_float_valuet u{spec};
      u.unpack(quiet_nan_80);
      REQUIRE(u.is_NaN());

      ieee_float_valuet u2{spec};
      u2.unpack(u.pack());
      REQUIRE(u2.is_NaN());
    }

    // Smallest positive denormal: J=0, exp=0, frac=1.  This catches
    // the pseudo-denormal bug in the pack path: an x86 denormal must
    // be encoded with J=0, and `unpack` of J=0+exp=0 must take the
    // denormal branch (exponent -bias+1) rather than the
    // pseudo-denormal/normal branch (-bias).
    {
      ieee_float_valuet u{spec};
      u.unpack(smallest_denormal_80);
      REQUIRE(u.pack() == smallest_denormal_80);
    }
  }
}
