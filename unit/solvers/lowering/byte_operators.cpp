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
#include <util/simplify_utils.h>
#include <util/std_types.h>
#include <util/string_constant.h>
#include <util/symbol_table.h>

TEST_CASE("byte extract and bits", "[core][solvers][lowering][byte_extract]")
{
  // this test does require a proper architecture to be set so that byte extract
  // uses adequate endianness
  cmdlinet cmdline;
  config.set(cmdline);

  const symbol_tablet symbol_table;
  const namespacet ns(symbol_table);

  const unsignedbv_typet u16{16};
  const exprt sixteen_bits = from_integer(0x1234, u16);
  const array_typet bit_array_type{bv_typet{1}, from_integer(16, size_type())};

  bool little_endian;
  GIVEN("Little endian")
  {
    little_endian = true;

    const auto bit_string = expr2bits(sixteen_bits, little_endian, ns);
    REQUIRE(bit_string.has_value());
    REQUIRE(bit_string->size() == 16);

    const auto array_of_bits =
      bits2expr(*bit_string, bit_array_type, little_endian, ns);
    REQUIRE(array_of_bits.has_value());

    const auto bit_string2 = expr2bits(*array_of_bits, little_endian, ns);
    REQUIRE(bit_string2.has_value());
    REQUIRE(*bit_string == *bit_string2);

    const byte_extract_exprt be1{little_endian ? ID_byte_extract_little_endian
                                               : ID_byte_extract_big_endian,
                                 sixteen_bits,
                                 from_integer(0, c_index_type()),
                                 bit_array_type};
    const exprt lower_be1 = lower_byte_extract(be1, ns);
    REQUIRE(lower_be1 == *array_of_bits);
  }

  GIVEN("Big endian")
  {
    little_endian = false;

    const auto bit_string = expr2bits(sixteen_bits, little_endian, ns);
    REQUIRE(bit_string.has_value());
    REQUIRE(bit_string->size() == 16);

    const auto array_of_bits =
      bits2expr(*bit_string, bit_array_type, little_endian, ns);
    REQUIRE(array_of_bits.has_value());

    const auto bit_string2 = expr2bits(*array_of_bits, little_endian, ns);
    REQUIRE(bit_string2.has_value());
    REQUIRE(*bit_string == *bit_string2);

    const byte_extract_exprt be1{little_endian ? ID_byte_extract_little_endian
                                               : ID_byte_extract_big_endian,
                                 sixteen_bits,
                                 from_integer(0, c_index_type()),
                                 bit_array_type};
    const exprt lower_be1 = lower_byte_extract(be1, ns);
    REQUIRE(lower_be1 == *array_of_bits);
  }
}

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
      from_integer(1, c_index_type()),
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

  GIVEN("A an unbounded byte_extract over a bounded operand")
  {
    const exprt deadbeef = from_integer(0xdeadbeef, unsignedbv_typet(32));
    const byte_extract_exprt be1(
      ID_byte_extract_little_endian,
      deadbeef,
      from_integer(1, c_index_type()),
      struct_typet(
        {{"unbounded_array",
          array_typet(
            unsignedbv_typet(16), exprt(ID_infinity, size_type()))}}));

    THEN("byte_extract lowering does not raise an exception")
    {
      const exprt lower_be1 = lower_byte_extract(be1, ns);

      REQUIRE(!has_subexpr(lower_be1, ID_byte_extract_little_endian));
      REQUIRE(lower_be1.type() == be1.type());

      byte_extract_exprt be2 = be1;
      be2.id(ID_byte_extract_big_endian);
      const exprt lower_be2 = lower_byte_extract(be2, ns);

      REQUIRE(!has_subexpr(lower_be2, ID_byte_extract_big_endian));
      REQUIRE(lower_be2.type() == be2.type());
    }
  }

  GIVEN("A an unbounded union byte_extract over a bounded operand")
  {
    const exprt deadbeef = from_integer(0xdeadbeef, unsignedbv_typet(32));
    const byte_extract_exprt be1(
      ID_byte_extract_little_endian,
      deadbeef,
      from_integer(1, c_index_type()),
      union_typet(
        {{"unbounded_array",
          array_typet(
            unsignedbv_typet(16), exprt(ID_infinity, size_type()))}}));

    THEN("byte_extract lowering does not raise an exception")
    {
      const exprt lower_be1 = lower_byte_extract(be1, ns);

      REQUIRE(!has_subexpr(lower_be1, ID_byte_extract_little_endian));
      REQUIRE(lower_be1.type() == be1.type());

      byte_extract_exprt be2 = be1;
      be2.id(ID_byte_extract_big_endian);
      const exprt lower_be2 = lower_byte_extract(be2, ns);

      REQUIRE(!has_subexpr(lower_be2, ID_byte_extract_big_endian));
      REQUIRE(lower_be2.type() == be2.type());
    }
  }

  GIVEN("A an empty union byte_extract over a bounded operand")
  {
    const exprt deadbeef = from_integer(0xdeadbeef, unsignedbv_typet(32));
    const byte_extract_exprt be1(
      ID_byte_extract_little_endian,
      deadbeef,
      from_integer(1, c_index_type()),
      union_typet{});

    THEN("byte_extract lowering does not raise an exception")
    {
      const exprt lower_be1 = lower_byte_extract(be1, ns);

      REQUIRE(!has_subexpr(lower_be1, ID_byte_extract_little_endian));
      REQUIRE(lower_be1.type() == be1.type());

      byte_extract_exprt be2 = be1;
      be2.id(ID_byte_extract_big_endian);
      const exprt lower_be2 = lower_byte_extract(be2, ns);

      REQUIRE(!has_subexpr(lower_be2, ID_byte_extract_big_endian));
      REQUIRE(lower_be2.type() == be2.type());
    }
  }

  GIVEN("A a byte_extract from a string constant")
  {
    string_constantt s("ABCD");
    const byte_extract_exprt be1(
      ID_byte_extract_little_endian,
      s,
      from_integer(1, c_index_type()),
      unsignedbv_typet(16));

    THEN("byte_extract lowering yields the expected value")
    {
      const exprt lower_be1 = lower_byte_extract(be1, ns);

      REQUIRE(!has_subexpr(lower_be1, ID_byte_extract_little_endian));
      REQUIRE(lower_be1.type() == be1.type());
      REQUIRE(
        lower_be1 == from_integer((int{'C'} << 8) + 'B', unsignedbv_typet(16)));

      byte_extract_exprt be2 = be1;
      be2.id(ID_byte_extract_big_endian);
      const exprt lower_be2 = lower_byte_extract(be2, ns);

      REQUIRE(!has_subexpr(lower_be2, ID_byte_extract_big_endian));
      REQUIRE(lower_be2.type() == be2.type());
      REQUIRE(
        lower_be2 == from_integer((int{'B'} << 8) + 'C', unsignedbv_typet(16)));
    }
  }

  GIVEN("A collection of types")
  {
    unsignedbv_typet u8(8);
    signedbv_typet s8(8);
    unsignedbv_typet u16(16);
    signedbv_typet s16(16);
    unsignedbv_typet u32(32);
    signedbv_typet s32(32);
    unsignedbv_typet u64(64);
    signedbv_typet s64(64);

    constant_exprt size = from_integer(8, size_type());

    std::vector<typet> types = {
      struct_typet({{"comp1", u16}, {"comp2", u16}}),
      struct_typet({{"comp1", u32}, {"comp2", u64}}),
      struct_typet({{"comp1", u32},
                    {"compX", c_bit_field_typet(u8, 4)},
                    {"pad", c_bit_field_typet(u8, 4)},
                    {"comp2", u8}}),
      union_typet({{"compA", u32}, {"compB", u64}}),
      c_enum_typet(u16),
      c_enum_typet(unsignedbv_typet(128)),
      array_typet(u8, size),
      array_typet(s32, size),
      array_typet(u64, size),
      unsignedbv_typet(24),
      unsignedbv_typet(128),
      signedbv_typet(24),
      signedbv_typet(128),
      ieee_float_spect::single_precision().to_type(),
      // generates the correct value, but remains wrapped in a typecast
      // pointer_typet(u64, 64),
      vector_typet(u8, size),
      vector_typet(u64, size),
      complex_typet(s16),
      complex_typet(u64)};

    THEN("byte_extract lowering yields the expected value")
    {
      for(const auto &endianness :
          {ID_byte_extract_little_endian, ID_byte_extract_big_endian})
      {
        for(const auto &t1 : types)
        {
          std::ostringstream oss;
          for(int i = 0; i < 64; ++i)
          {
            std::string bits = integer2binary(i, 8);
            std::reverse(bits.begin(), bits.end());
            oss << bits;
          }

          const auto type_bits = pointer_offset_bits(t1, ns);
          REQUIRE(type_bits);
          const auto type_bits_int = numeric_cast_v<std::size_t>(*type_bits);
          REQUIRE(type_bits_int <= oss.str().size());
          const auto s = bits2expr(
            oss.str().substr(0, type_bits_int),
            t1,
            endianness == ID_byte_extract_little_endian,
            ns);
          REQUIRE(s.has_value());

          for(const auto &t2 : types)
          {
            oss.str("");
            for(int i = 2; i < 64; ++i)
            {
              std::string bits = integer2binary(i, 8);
              std::reverse(bits.begin(), bits.end());
              oss << bits;
            }

            const auto type_bits_2 = pointer_offset_bits(t2, ns);
            REQUIRE(type_bits_2);

            // for now only extract within bounds
            if(*type_bits_2 + 16 > *type_bits)
              continue;

            const auto type_bits_2_int =
              numeric_cast_v<std::size_t>(*type_bits_2);
            REQUIRE(type_bits_2_int <= oss.str().size());
            const auto r = bits2expr(
              oss.str().substr(0, type_bits_2_int),
              t2,
              endianness == ID_byte_extract_little_endian,
              ns);
            REQUIRE(r.has_value());

            const byte_extract_exprt be(
              endianness, *s, from_integer(2, c_index_type()), t2);

            const exprt lower_be = lower_byte_extract(be, ns);
            const exprt lower_be_s = simplify_expr(lower_be, ns);

            REQUIRE(!has_subexpr(lower_be, ID_byte_extract_little_endian));
            REQUIRE(!has_subexpr(lower_be, ID_byte_extract_big_endian));
            REQUIRE(lower_be.type() == be.type());
            REQUIRE(lower_be == *r);
            REQUIRE(lower_be_s == *r);
          }
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
      from_integer(1, c_index_type()),
      from_integer(0x42, unsignedbv_typet(8)));

    THEN("byte_update lowering yields the expected value")
    {
      const exprt lower_bu1 = lower_byte_operators(bu1, ns);
      const exprt lower_bu1_s = simplify_expr(lower_bu1, ns);

      REQUIRE(!has_subexpr(lower_bu1, ID_byte_extract_little_endian));
      REQUIRE(!has_subexpr(lower_bu1, ID_byte_update_little_endian));
      REQUIRE(lower_bu1.type() == bu1.type());
      REQUIRE(lower_bu1_s == from_integer(0xdead42ef, unsignedbv_typet(32)));

      byte_update_exprt bu2 = bu1;
      bu2.id(ID_byte_update_big_endian);
      const exprt lower_bu2 = lower_byte_operators(bu2, ns);
      const exprt lower_bu2_s = simplify_expr(lower_bu2, ns);

      REQUIRE(!has_subexpr(lower_bu2, ID_byte_extract_big_endian));
      REQUIRE(!has_subexpr(lower_bu2, ID_byte_update_big_endian));
      REQUIRE(lower_bu2.type() == bu2.type());
      REQUIRE(lower_bu2_s == from_integer(0xde42beef, unsignedbv_typet(32)));
    }
  }

  GIVEN("A collection of types")
  {
    unsignedbv_typet u8(8);
    signedbv_typet s8(8);
    unsignedbv_typet u16(16);
    signedbv_typet s16(16);
    unsignedbv_typet u32(32);
    signedbv_typet s32(32);
    unsignedbv_typet u64(64);
    signedbv_typet s64(64);

    constant_exprt size = from_integer(8, size_type());

    std::vector<typet> types = {
      struct_typet({{"comp1", u16}, {"comp2", u16}}),
      struct_typet({{"comp1", u32}, {"comp2", u64}}),
      struct_typet({{"comp1", u32},
                    {"compX", c_bit_field_typet(u8, 4)},
                    {"pad", c_bit_field_typet(u8, 4)},
                    {"comp2", u8}}),
      union_typet({{"compA", u32}, {"compB", u64}}),
      c_enum_typet(u16),
      c_enum_typet(unsignedbv_typet(128)),
      array_typet(u8, size),
      array_typet(s32, size),
      array_typet(u64, size),
      unsignedbv_typet(24),
      unsignedbv_typet(128),
      signedbv_typet(24),
      signedbv_typet(128),
      ieee_float_spect::single_precision().to_type(),
      // generates the correct value, but remains wrapped in a typecast
      // pointer_typet(u64, 64),
      vector_typet(u8, size),
      vector_typet(u64, size),
      // complex_typet(s16),
      // complex_typet(u64)
    };

    THEN("byte_update lowering yields the expected value")
    {
      for(const auto &endianness :
          {ID_byte_update_little_endian, ID_byte_update_big_endian})
      {
        for(const auto &t1 : types)
        {
          std::ostringstream oss;
          for(int i = 0; i < 64; ++i)
          {
            std::string bits = integer2binary(i, 8);
            std::reverse(bits.begin(), bits.end());
            oss << bits;
          }

          const auto type_bits = pointer_offset_bits(t1, ns);
          REQUIRE(type_bits);
          const auto type_bits_int = numeric_cast_v<std::size_t>(*type_bits);
          REQUIRE(type_bits_int <= oss.str().size());
          const std::string s_string = oss.str().substr(0, type_bits_int);
          const auto s = bits2expr(
            s_string, t1, endianness == ID_byte_update_little_endian, ns);
          REQUIRE(s.has_value());

          for(const auto &t2 : types)
          {
            oss.str("");
            for(int i = 64; i < 128; ++i)
            {
              std::string bits = integer2binary(i, 8);
              std::reverse(bits.begin(), bits.end());
              oss << bits;
            }

            const auto type_bits_2 = pointer_offset_bits(t2, ns);
            REQUIRE(type_bits_2);

            // for now only update within bounds
            if(*type_bits_2 + 16 > *type_bits)
              continue;

            const auto type_bits_2_int =
              numeric_cast_v<std::size_t>(*type_bits_2);
            REQUIRE(type_bits_2_int <= oss.str().size());
            const std::string u_string = oss.str().substr(0, type_bits_2_int);
            const auto u = bits2expr(
              u_string, t2, endianness == ID_byte_update_little_endian, ns);
            REQUIRE(u.has_value());

            std::string r_string = s_string;
            r_string.replace(16, u_string.size(), u_string);
            const auto r = bits2expr(
              r_string, t1, endianness == ID_byte_update_little_endian, ns);
            REQUIRE(r.has_value());

            const byte_update_exprt bu(
              endianness, *s, from_integer(2, c_index_type()), *u);

            const exprt lower_bu = lower_byte_operators(bu, ns);
            const exprt lower_bu_s = simplify_expr(lower_bu, ns);

            REQUIRE(!has_subexpr(lower_bu, endianness));
            REQUIRE(!has_subexpr(lower_bu, ID_byte_extract_big_endian));
            REQUIRE(!has_subexpr(lower_bu, ID_byte_extract_little_endian));
            REQUIRE(lower_bu.type() == bu.type());
            REQUIRE(lower_bu == *r);
            REQUIRE(lower_bu_s == *r);
          }
        }
      }
    }
  }
}
