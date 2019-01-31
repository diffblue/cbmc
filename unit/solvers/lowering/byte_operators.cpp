/*******************************************************************\

 Module: Unit tests for byte_extract/byte_update lowering

 Author: Michael Tautschnig

\*******************************************************************/

#include <testing-utils/use_catch.h>

#include <solvers/lowering/expr_lowering.h>

#include <util/arith_tools.h>
#include <util/byte_operators.h>
#include <util/c_types.h>
#include <util/cmdline.h>
#include <util/config.h>
#include <util/expr_util.h>
#include <util/namespace.h>
#include <util/pointer_offset_size.h>
#include <util/simplify_expr.h>
#include <util/simplify_expr_class.h>
#include <util/std_types.h>
#include <util/symbol_table.h>

SCENARIO("byte_extract_lowering", "[core][solvers][lowering][byte_extract]")
{
  // this test does require a proper architecture to be set so that byte extract
  // uses adequate endianness
  cmdlinet cmdline;
  config.set(cmdline);

  const symbol_tablet symbol_table;
  const namespacet ns(symbol_table);

  GIVEN("A byte_extract over a POD")
  {
    const exprt deadbeef = from_integer(0xdeadbeef, unsignedbv_typet(32));
    const byte_extract_exprt be1(
      ID_byte_extract_little_endian,
      deadbeef,
      from_integer(1, index_type()),
      signedbv_typet(8));

    THEN("byte_extract lowering yields the expected value")
    {
      const exprt lower_be1 = lower_byte_extract(be1, ns);
      const exprt lower_be1_s = simplify_expr(lower_be1, ns);

      REQUIRE(!has_subexpr(lower_be1, ID_byte_extract_little_endian));
      REQUIRE(lower_be1.type() == be1.type());
      REQUIRE(lower_be1_s == from_integer(0xbe, signedbv_typet(8)));

      byte_extract_exprt be2 = be1;
      be2.id(ID_byte_extract_big_endian);
      const exprt lower_be2 = lower_byte_extract(be2, ns);
      const exprt lower_be2_s = simplify_expr(lower_be2, ns);

      REQUIRE(!has_subexpr(lower_be2, ID_byte_extract_big_endian));
      REQUIRE(lower_be2.type() == be2.type());
      REQUIRE(lower_be2_s == from_integer(0xad, signedbv_typet(8)));
    }
  }

  GIVEN("A collection of types")
  {
    unsignedbv_typet u8(8);
    unsignedbv_typet u32(32);
    unsignedbv_typet u64(64);

    constant_exprt size = from_integer(8, size_type());

    std::vector<typet> types = {
      struct_typet({{"comp1", u32}, {"comp2", u64}}),
#if 0
      // not currently handled: components not byte aligned
      struct_typet({{"comp1", u32},
                    {"compX", c_bit_field_typet(u8, 4)},
                    {"pad", c_bit_field_typet(u8, 4)},
                    {"comp2", u8}}),
#endif
      union_typet({{"compA", u32}, {"compB", u64}}),
      c_enum_typet(unsignedbv_typet(16)),
      array_typet(u8, size),
      array_typet(u64, size),
      unsignedbv_typet(24),
      signedbv_typet(128),
      ieee_float_spect::single_precision().to_type(),
      pointer_typet(u64, 64),
      vector_typet(u8, size),
      vector_typet(u64, size),
      complex_typet(u32)
    };

    simplify_exprt simp(ns);

    THEN("byte_extract lowering yields the expected value")
    {
      for(const auto &t1 : types)
      {
        std::ostringstream oss;
        for(int i = 0; i < 64; ++i)
          oss << integer2binary(i, 8);

        const auto type_bits = pointer_offset_bits(t1, ns);
        REQUIRE(type_bits);
        const auto type_bits_int = numeric_cast_v<std::size_t>(*type_bits);
        REQUIRE(type_bits_int <= oss.str().size());
        const exprt s =
          simp.bits2expr(oss.str().substr(0, type_bits_int), t1, true);
        REQUIRE(s.is_not_nil());

        for(const auto &t2 : types)
        {
          oss.str("");
          for(int i = 2; i < 66; ++i)
            oss << integer2binary(i, 8);

          const auto type_bits_2 = pointer_offset_bits(t2, ns);
          REQUIRE(type_bits_2);
          const auto type_bits_2_int =
            numeric_cast_v<std::size_t>(*type_bits_2);
          REQUIRE(type_bits_2_int <= oss.str().size());
          const exprt r =
            simp.bits2expr(oss.str().substr(0, type_bits_2_int), t2, true);
          REQUIRE(r.is_not_nil());

          const byte_extract_exprt be1(
            ID_byte_extract_little_endian,
            s,
            from_integer(2, index_type()),
            t2);

          const exprt lower_be1 = lower_byte_extract(be1, ns);
          const exprt lower_be1_s = simplify_expr(lower_be1, ns);

          // TODO: does not currently hold
          // REQUIRE(!has_subexpr(lower_be1, ID_byte_extract_little_endian));
          REQUIRE(lower_be1.type() == be1.type());
          // TODO: does not currently hold
          // REQUIRE(lower_be1 == r);
          // TODO: does not currently hold
          // REQUIRE(lower_be1_s == r);

          const byte_extract_exprt be2(
            ID_byte_extract_big_endian, s, from_integer(2, index_type()), t2);

          const exprt lower_be2 = lower_byte_extract(be2, ns);
          const exprt lower_be2_s = simplify_expr(lower_be2, ns);

          // TODO: does not currently hold
          REQUIRE(!has_subexpr(lower_be2, ID_byte_extract_big_endian));
          REQUIRE(lower_be2.type() == be2.type());
          // TODO: does not currently hold
          // REQUIRE(lower_be2 == r);
          // TODO: does not currently hold
          // REQUIRE(lower_be2_s == r);
        }
      }
    }
  }
}

SCENARIO("byte_update_lowering", "[core][solvers][lowering][byte_update]")
{
  // this test does require a proper architecture to be set so that byte extract
  // uses adequate endianness
  cmdlinet cmdline;
  config.set(cmdline);

  const symbol_tablet symbol_table;
  const namespacet ns(symbol_table);

  GIVEN("A byte_update of a POD")
  {
    const exprt deadbeef = from_integer(0xdeadbeef, unsignedbv_typet(32));
    const byte_update_exprt bu1(
      ID_byte_update_little_endian,
      deadbeef,
      from_integer(1, index_type()),
      from_integer(0x42, unsignedbv_typet(8)));

    THEN("byte_update lowering yields the expected value")
    {
      const exprt lower_bu1 = lower_byte_operators(bu1, ns);
      const exprt lower_bu1_s = simplify_expr(lower_bu1, ns);

      REQUIRE(!has_subexpr(lower_bu1, ID_byte_extract_little_endian));
      REQUIRE(!has_subexpr(lower_bu1, ID_byte_update_little_endian));
      REQUIRE(lower_bu1.type() == bu1.type());
      REQUIRE(lower_bu1_s == from_integer(0xdead42ef, unsignedbv_typet(32)));

#if 0
      // this is currently broken, #2058 will fix it
      byte_update_exprt bu2 = bu1;
      bu2.id(ID_byte_update_big_endian);
      const exprt lower_bu2 = lower_byte_operators(bu2, ns);
      const exprt lower_bu2_s = simplify_expr(lower_bu2, ns);

      REQUIRE(!has_subexpr(lower_bu2, ID_byte_extract_big_endian));
      REQUIRE(!has_subexpr(lower_bu2, ID_byte_update_big_endian));
      REQUIRE(lower_bu2.type() == bu2.type());
      REQUIRE(lower_bu2_s == from_integer(0xde42beef, unsignedbv_typet(32)));
#endif
    }
  }

  GIVEN("A collection of types")
  {
    unsignedbv_typet u8(8);
    unsignedbv_typet u32(32);
    unsignedbv_typet u64(64);

    constant_exprt size = from_integer(8, size_type());

    std::vector<typet> types = {
    // TODO: only arrays and scalars
    // struct_typet({{"comp1", u32}, {"comp2", u64}}),
#if 0
      // not currently handled: components not byte aligned
      struct_typet({{"comp1", u32},
                    {"compX", c_bit_field_typet(u8, 4)},
                    {"pad", c_bit_field_typet(u8, 4)},
                    {"comp2", u8}}),
#endif
      // TODO: only arrays and scalars
      // union_typet({{"compA", u32}, {"compB", u64}}),
      // c_enum_typet(unsignedbv_typet(16)),
      array_typet(u8, size),
      array_typet(u64, size),
      unsignedbv_typet(24),
      signedbv_typet(128),
      ieee_float_spect::single_precision().to_type(),
      pointer_typet(u64, 64),
      // TODO: only arrays and scalars
      // vector_typet(u8, size),
      // vector_typet(u64, size),
      // complex_typet(u32)
    };

    simplify_exprt simp(ns);

    THEN("byte_update lowering yields the expected value")
    {
      for(const auto &t1 : types)
      {
        std::ostringstream oss;
        for(int i = 0; i < 64; ++i)
          oss << integer2binary(i, 8);

        const auto type_bits = pointer_offset_bits(t1, ns);
        REQUIRE(type_bits);
        const auto type_bits_int = numeric_cast_v<std::size_t>(*type_bits);
        REQUIRE(type_bits_int <= oss.str().size());
        const exprt s =
          simp.bits2expr(oss.str().substr(0, type_bits_int), t1, true);
        REQUIRE(s.is_not_nil());

        for(const auto &t2 : types)
        {
          oss.str("");
          for(int i = 64; i < 128; ++i)
            oss << integer2binary(i, 8);

          const auto type_bits_2 = pointer_offset_bits(t2, ns);
          REQUIRE(type_bits_2);
          const auto type_bits_2_int =
            numeric_cast_v<std::size_t>(*type_bits_2);
          REQUIRE(type_bits_2_int <= oss.str().size());
          const exprt u =
            simp.bits2expr(oss.str().substr(0, type_bits_2_int), t2, true);
          REQUIRE(u.is_not_nil());

          // TODO: currently required
          if(type_bits < type_bits_2)
            continue;

          const byte_update_exprt bu1(
            ID_byte_update_little_endian, s, from_integer(2, index_type()), u);

          const exprt lower_bu1 = lower_byte_operators(bu1, ns);
          const exprt lower_bu1_s = simplify_expr(lower_bu1, ns);

          REQUIRE(!has_subexpr(lower_bu1, ID_byte_update_little_endian));
          REQUIRE(!has_subexpr(lower_bu1, ID_byte_extract_little_endian));
          REQUIRE(lower_bu1.type() == bu1.type());
          // TODO: does not currently hold
          // REQUIRE(lower_bu1 == u);
          // TODO: does not currently hold
          // REQUIRE(lower_bu1_s == u);

          const byte_update_exprt bu2(
            ID_byte_update_big_endian, s, from_integer(2, index_type()), u);

          const exprt lower_bu2 = lower_byte_operators(bu2, ns);
          const exprt lower_bu2_s = simplify_expr(lower_bu2, ns);

          REQUIRE(!has_subexpr(lower_bu2, ID_byte_update_big_endian));
          REQUIRE(!has_subexpr(lower_bu2, ID_byte_extract_big_endian));
          REQUIRE(lower_bu2.type() == bu2.type());
          // TODO: does not currently hold
          // REQUIRE(lower_bu2 == u);
          // TODO: does not currently hold
          // REQUIRE(lower_bu2_s == u);
        }
      }
    }
  }
}
