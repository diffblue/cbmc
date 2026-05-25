/*******************************************************************\

Module: Unit tests of the expression simplifier

Author: Michael Tautschnig

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/byte_operators.h>
#include <util/c_types.h>
#include <util/cmdline.h>
#include <util/config.h>
#include <util/mathematical_expr.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>
#include <util/pointer_predicates.h>
#include <util/simplify_expr.h>
#include <util/simplify_utils.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

#include <testing-utils/empty_namespace.h>
#include <testing-utils/use_catch.h>

TEST_CASE("Simplify pointer_offset(address of array index)", "[core][util]")
{
  config.set_arch("none");

  array_typet array_type(char_type(), from_integer(2, size_type()));
  symbol_exprt array("A", array_type);
  index_exprt index(array, from_integer(1, c_index_type()));
  address_of_exprt address_of(index);

  exprt p_o=pointer_offset(address_of);

  exprt simp = simplify_expr(p_o, empty_namespace);

  REQUIRE(simp.is_constant());
  const mp_integer offset_value =
    numeric_cast_v<mp_integer>(to_constant_expr(simp));
  REQUIRE(offset_value==1);
}

TEST_CASE("Simplify byte extract", "[core][util]")
{
  // this test does require a proper architecture to be set so that byte extract
  // uses adequate endianness
  cmdlinet cmdline;
  config.set(cmdline);

  // byte-extracting type T at offset 0 from an object of type T yields the
  // object
  symbol_exprt s("foo", size_type());
  byte_extract_exprt be =
    make_byte_extract(s, from_integer(0, c_index_type()), size_type());

  exprt simp = simplify_expr(be, empty_namespace);

  REQUIRE(simp == s);
}

TEST_CASE("expr2bits and bits2expr respect bit order", "[core][util]")
{
  const namespacet &ns = empty_namespace;

  exprt deadbeef = from_integer(0xdeadbeef, unsignedbv_typet(32));

  const auto le = expr2bits(deadbeef, true, ns);
  REQUIRE(le.has_value());
  REQUIRE(le->size() == 32);

  const auto should_be_deadbeef1 =
    bits2expr(*le, unsignedbv_typet(32), true, ns);
  REQUIRE(deadbeef == *should_be_deadbeef1);

  const auto be = expr2bits(deadbeef, false, ns);
  REQUIRE(be.has_value());
  REQUIRE(be->size() == 32);

  const auto should_be_deadbeef2 =
    bits2expr(*be, unsignedbv_typet(32), false, ns);
  REQUIRE(deadbeef == *should_be_deadbeef2);

  c_bit_field_typet four_bits{unsignedbv_typet{8}, 4};
  struct_typet st{{{"s", unsignedbv_typet{16}},
                   {"bf1", four_bits},
                   {"bf2", four_bits},
                   {"b", unsignedbv_typet{8}}}};

  const auto fill_struct_le = bits2expr(*le, st, true, ns);
  REQUIRE(fill_struct_le.has_value());
  REQUIRE(
    to_struct_expr(*fill_struct_le).operands()[1] ==
    from_integer(0xd, four_bits));
  REQUIRE(
    to_struct_expr(*fill_struct_le).operands()[2] ==
    from_integer(0xa, four_bits));

  const auto fill_struct_be = bits2expr(*be, st, false, ns);
  REQUIRE(fill_struct_be.has_value());
  REQUIRE(
    to_struct_expr(*fill_struct_be).operands()[1] ==
    from_integer(0xb, four_bits));
  REQUIRE(
    to_struct_expr(*fill_struct_be).operands()[2] ==
    from_integer(0xe, four_bits));
}

TEST_CASE("Simplify extractbit", "[core][util]")
{
  // this test does require a proper architecture to be set so that byte extract
  // uses adequate endianness
  const cmdlinet cmdline;
  config.set(cmdline);

  // binary: 1101 1110 1010 1101 1011 1110 1110 1111
  //         ^MSB                               LSB^
  //              bit23^                  bit4^
  // extractbit and extractbits use offsets with respect to the
  // least-significant bit, endianess does not impact them
  const exprt deadbeef = from_integer(0xdeadbeef, unsignedbv_typet(32));

  exprt eb1 = extractbit_exprt(deadbeef, 4);
  bool unmodified = simplify(eb1, empty_namespace);

  REQUIRE(!unmodified);
  REQUIRE(eb1 == false_exprt());

  exprt eb2 = extractbit_exprt(deadbeef, 23);
  unmodified = simplify(eb2, empty_namespace);

  REQUIRE(!unmodified);
  REQUIRE(eb2 == true_exprt());
}

TEST_CASE("Simplify extractbits", "[core][util]")
{
  // this test does require a proper architecture to be set so that byte extract
  // uses adequate endianness
  const cmdlinet cmdline;
  config.set(cmdline);

  const exprt deadbeef = from_integer(0xdeadbeef, unsignedbv_typet(32));

  exprt eb = extractbits_exprt(deadbeef, 8, unsignedbv_typet(8));
  bool unmodified = simplify(eb, empty_namespace);

  REQUIRE(!unmodified);
  REQUIRE(eb == from_integer(0xbe, unsignedbv_typet(8)));
}

TEST_CASE("Simplify shift", "[core][util]")
{
  const namespacet &ns = empty_namespace;

  REQUIRE(
    simplify_expr(shl_exprt(from_integer(5, signedbv_typet(8)), 1), ns) ==
    from_integer(10, signedbv_typet(8)));

  REQUIRE(
    simplify_expr(ashr_exprt(from_integer(5, signedbv_typet(8)), 1), ns) ==
    from_integer(2, signedbv_typet(8)));

  REQUIRE(
    simplify_expr(lshr_exprt(from_integer(5, unsignedbv_typet(8)), 1), ns) ==
    from_integer(2, unsignedbv_typet(8)));

  REQUIRE(
    simplify_expr(ashr_exprt(from_integer(-4, signedbv_typet(8)), 1), ns) ==
    from_integer(-2, signedbv_typet(8)));

  REQUIRE(
    simplify_expr(lshr_exprt(from_integer(-4, signedbv_typet(8)), 1), ns) ==
    from_integer(126, signedbv_typet(8)));
}

TEST_CASE("Simplify dynamic object comparison", "[core][util]")
{
  const namespacet &ns = empty_namespace;

  dynamic_object_exprt dynamic_object(signedbv_typet(8));
  dynamic_object.set_instance(1);

  address_of_exprt address_of_dynamic_object(dynamic_object);

  equal_exprt compare_null(
    address_of_dynamic_object,
    null_pointer_exprt(to_pointer_type(address_of_dynamic_object.type())));
  REQUIRE(simplify_expr(compare_null, ns) == false_exprt());

  typecast_exprt cast_address(
    address_of_dynamic_object, pointer_type(signedbv_typet(16)));

  equal_exprt compare_null_through_cast(
    cast_address, null_pointer_exprt(to_pointer_type(cast_address.type())));
  REQUIRE(simplify_expr(compare_null_through_cast, ns) == false_exprt());

  dynamic_object_exprt other_dynamic_object(signedbv_typet(8));
  other_dynamic_object.set_instance(2);
  address_of_exprt address_of_other_dynamic_object(other_dynamic_object);

  equal_exprt compare_pointer_objects(
    pointer_object(address_of_dynamic_object),
    pointer_object(address_of_other_dynamic_object));

  REQUIRE(simplify_expr(compare_pointer_objects, ns) == false_exprt());

  symbol_exprt s{"foo", signedbv_typet{8}};
  address_of_exprt address_of_symbol{s};

  equal_exprt compare_symbol_dynamic{address_of_dynamic_object,
                                     address_of_symbol};

  REQUIRE(simplify_expr(compare_symbol_dynamic, ns) == false_exprt{});
}

TEST_CASE("Simplify pointer_object equality", "[core][util]")
{
  // this test requires a proper architecture to be set up so that pointers have
  // a width
  const cmdlinet cmdline;
  config.set(cmdline);

  exprt p_o_void =
    pointer_object(null_pointer_exprt{pointer_type(empty_typet{})});
  exprt p_o_int =
    pointer_object(null_pointer_exprt{pointer_type(signedbv_typet(32))});

  exprt simp = simplify_expr(equal_exprt{p_o_void, p_o_int}, empty_namespace);

  REQUIRE(simp == true);
}

TEST_CASE("Simplify cast from bool", "[core][util]")
{
  const namespacet &ns = empty_namespace;

  {
    // this checks that ((int)B)==1 turns into B
    exprt B = symbol_exprt("B", bool_typet());
    exprt comparison = equal_exprt(
      typecast_exprt(B, signedbv_typet(32)),
      from_integer(1, signedbv_typet(32)));

    exprt simp = simplify_expr(comparison, ns);

    REQUIRE(simp == B);
  }

  {
    // this checks that ((int)B)==0 turns into !B
    exprt B = symbol_exprt("B", bool_typet());
    exprt comparison = equal_exprt(
      typecast_exprt(B, signedbv_typet(32)),
      from_integer(0, signedbv_typet(32)));

    exprt simp = simplify_expr(comparison, ns);

    REQUIRE(simp == not_exprt(B));
  }

  {
    // this checks that ((int)B)!=1 turns into !B
    exprt B = symbol_exprt("B", bool_typet());
    exprt comparison = notequal_exprt(
      typecast_exprt(B, signedbv_typet(32)),
      from_integer(1, signedbv_typet(32)));

    exprt simp = simplify_expr(comparison, ns);

    REQUIRE(simp == not_exprt(B));
  }

  {
    // this checks that ((int)B)!=0 turns into B
    exprt B = symbol_exprt("B", bool_typet());
    exprt comparison = notequal_exprt(
      typecast_exprt(B, signedbv_typet(32)),
      from_integer(0, signedbv_typet(32)));

    exprt simp = simplify_expr(comparison, ns);

    REQUIRE(simp == B);
  }
}

TEST_CASE("simplify_expr boolean expressions", "[core][util]")
{
  const namespacet &ns = empty_namespace;

  SECTION("Binary boolean operations")
  {
    struct test_entryt
    {
      exprt lhs;
      exprt rhs;
      exprt expected_value;
    };

    SECTION("AND")
    {
      std::vector<test_entryt> test_values = {
        {true_exprt(), true_exprt(), true_exprt()},
        {true_exprt(), false_exprt(), false_exprt()},
        {false_exprt(), true_exprt(), false_exprt()},
        {false_exprt(), false_exprt(), false_exprt()},
      };

      for(const auto &entry : test_values)
      {
        const exprt result = simplify_expr(and_exprt{entry.lhs, entry.rhs}, ns);
        REQUIRE(result == entry.expected_value);
      }
    }

    SECTION("OR")
    {
      std::vector<test_entryt> test_values = {
        {true_exprt(), true_exprt(), true_exprt()},
        {true_exprt(), false_exprt(), true_exprt()},
        {false_exprt(), true_exprt(), true_exprt()},
        {false_exprt(), false_exprt(), false_exprt()},
      };

      for(const auto &entry : test_values)
      {
        const exprt result = simplify_expr(or_exprt{entry.lhs, entry.rhs}, ns);
        REQUIRE(result == entry.expected_value);
      }
    }

    SECTION("Implies")
    {
      std::vector<test_entryt> test_values = {
        {true_exprt(), true_exprt(), true_exprt()},
        {true_exprt(), false_exprt(), false_exprt()},
        {false_exprt(), true_exprt(), true_exprt()},
        {false_exprt(), false_exprt(), true_exprt()},
      };

      for(const auto &entry : test_values)
      {
        const exprt result =
          simplify_expr(implies_exprt{entry.lhs, entry.rhs}, ns);
        REQUIRE(result == entry.expected_value);
      }
    }
  }
  SECTION("Not")
  {
    REQUIRE(simplify_expr(not_exprt{true_exprt()}, ns) == false_exprt());
    REQUIRE(simplify_expr(not_exprt{false_exprt()}, ns) == true_exprt());
  }
  SECTION("Nested boolean expressions")
  {
    INFO("((!true) || (false => false)) && true)")
    REQUIRE(
      simplify_expr(
        and_exprt{or_exprt{not_exprt{true_exprt{}},
                           implies_exprt{false_exprt{}, false_exprt{}}},
                  true_exprt{}},
        ns) == true_exprt{});
  }
  SECTION("Numeric comparisons")
  {
    struct test_entryt
    {
      irep_idt comparison;
      int lhs;
      int rhs;
      exprt expected;
    };

    std::vector<test_entryt> comparisons = {
      {ID_lt, -1, 1, true_exprt()},
      {ID_lt, 1, 1, false_exprt()},
      {ID_lt, 1, -1, false_exprt()},

      {ID_le, -1, 1, true_exprt()},
      {ID_le, 1, 1, true_exprt()},
      {ID_le, 1, -1, false_exprt()},

      {ID_ge, -1, 1, false_exprt()},
      {ID_ge, 1, 1, true_exprt()},
      {ID_ge, 1, -1, true_exprt()},

      {ID_gt, -1, 1, false_exprt()},
      {ID_gt, 1, 1, false_exprt()},
      {ID_gt, 1, -1, true_exprt()},
    };

    const auto binary_relation_from = [](const test_entryt &entry) {
      const signedbv_typet int_type(32);
      return binary_relation_exprt{from_integer(entry.lhs, int_type),
                                   entry.comparison,
                                   from_integer(entry.rhs, int_type)};
    };

    for(const test_entryt &test_entry : comparisons)
    {
      REQUIRE(
        simplify_expr(binary_relation_from(test_entry), ns) ==
        test_entry.expected);
    }
  }
}

TEST_CASE("Simplifying cast expressions", "[core][util]")
{
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);
  const auto short_type = signedbv_typet(16);
  const auto int_type = signedbv_typet(32);
  const auto long_type = signedbv_typet(64);
  array_typet array_type(int_type, from_integer(5, int_type));

  symbolt a_symbol{"a", array_type, irep_idt{}};
  a_symbol.base_name = "a";
  a_symbol.is_lvalue = true;
  symbol_table.add(a_symbol);

  symbolt i_symbol{"i", int_type, irep_idt{}};
  i_symbol.base_name = "i";
  i_symbol.is_lvalue = true;
  symbol_table.add(i_symbol);

  config.set_arch("none");

  SECTION("Simplifying a[(signed long int)0]")
  {
    // a[(signed long int)0]
    index_exprt expr{symbol_exprt{"a", array_type},
                     typecast_exprt{from_integer(0, int_type), long_type}};
    // cast is applied on the constant
    const auto simplified_expr = simplify_expr(expr, ns);
    REQUIRE(
      simplified_expr ==
      index_exprt{symbol_exprt{"a", array_type}, from_integer(0, long_type)});
  }
  SECTION("Simplifying a[(signed long int)i]")
  {
    // a[(signed long int)0]
    index_exprt expr{symbol_exprt{"a", array_type},
                     typecast_exprt{i_symbol.symbol_expr(), long_type}};
    // Cast is not removed as up casting a symbol
    const auto simplified_expr = simplify_expr(expr, ns);
    REQUIRE(simplified_expr == expr);
  }
  SECTION("Simplifying a[(signed int)i]")
  {
    // a[(signed int)i]
    index_exprt expr{symbol_exprt{"a", array_type},
                     typecast_exprt{i_symbol.symbol_expr(), int_type}};

    const auto simplified_expr = simplify_expr(expr, ns);
    REQUIRE(
      simplified_expr ==
      index_exprt{symbol_exprt{"a", array_type}, i_symbol.symbol_expr()});
  }
  SECTION("Simplifying a[(signed short)0]")
  {
    // a[(signed short)0]
    index_exprt expr{symbol_exprt{"a", array_type},
                     typecast_exprt{from_integer(0, int_type), short_type}};

    // Can be simplified as the number is a constant
    const auto simplified_expr = simplify_expr(expr, ns);
    REQUIRE(
      simplified_expr ==
      index_exprt{symbol_exprt{"a", array_type}, from_integer(0, short_type)});
  }
  SECTION("Simplifying a[(signed short)i]")
  {
    // a[(signed short)i]
    index_exprt expr{symbol_exprt{"a", array_type},
                     typecast_exprt{i_symbol.symbol_expr(), short_type}};

    // No simplification as the cast may have an effect
    const auto simplified_expr = simplify_expr(expr, ns);
    REQUIRE(simplified_expr == expr);
  }

  SECTION("Simplifying (unsigned)(B ? 4 : 5) > 3")
  {
    signedbv_typet sbv{4};
    unsignedbv_typet ubv{4};

    symbol_exprt b{"B", bool_typet{}};
    if_exprt if_b{b, from_integer(4, sbv), from_integer(5, sbv)};

    binary_relation_exprt comparison_gt{
      typecast_exprt{if_b, ubv}, ID_gt, from_integer(3, ubv)};
    exprt simp = simplify_expr(comparison_gt, ns);

    REQUIRE(simp == true_exprt{});
  }
}

TEST_CASE("Simplify bitor", "[core][util]")
{
  SECTION("Simplification for raw bitvector")
  {
    bv_typet bv{4};
    constant_exprt zero = from_integer(0, bv);
    symbol_exprt b{"B", bv};

    REQUIRE(simplify_expr(bitor_exprt{b, zero}, empty_namespace) == b);
  }
}

TEST_CASE("Simplify inequality", "[core][util]")
{
  {
    // This checks that 3 < (B ? 4 : 5) simplifies to true, just like (B ? 4 :
    // 5) > 3 simplifies to true.
    signedbv_typet sbv{4};
    symbol_exprt b{"B", bool_typet{}};
    if_exprt if_b{b, from_integer(4, sbv), from_integer(5, sbv)};

    binary_relation_exprt comparison_gt{if_b, ID_gt, from_integer(3, sbv)};
    exprt simp = simplify_expr(comparison_gt, empty_namespace);

    REQUIRE(simp == true_exprt{});

    binary_relation_exprt comparison_lt{from_integer(3, sbv), ID_lt, if_b};
    simp = simplify_expr(comparison_lt, empty_namespace);

    REQUIRE(simp == true_exprt{});
  }
}

TEST_CASE("Simplify bitxor", "[core][util]")
{
  config.set_arch("none");

  SECTION("Simplification for c_bool")
  {
    constant_exprt false_c_bool = from_integer(0, c_bool_type());

    REQUIRE(
      simplify_expr(
        bitxor_exprt{false_c_bool, false_c_bool}, empty_namespace) ==
      false_c_bool);
  }
}

TEST_CASE("Simplify power", "[core][util]")
{
  SECTION("Simplification for power")
  {
    symbol_exprt a{"a", integer_typet{}};

    REQUIRE(
      simplify_expr(
        power_exprt{a, from_integer(1, integer_typet{})}, empty_namespace) ==
      a);
  }
}

TEST_CASE("Simplify pointer cast of pointer arithmetic", "[core][util]")
{
  config.set_arch("none");

  SECTION("Same element size: (char*)(unsigned_char_ptr + 1)")
  {
    // (char*)(ptr + 1) where ptr is unsigned char* should push the cast inside
    auto uchar_ptr_type = pointer_type(unsigned_char_type());
    auto char_ptr_type = pointer_type(signed_char_type());
    symbol_exprt ptr{"ptr", uchar_ptr_type};
    plus_exprt ptr_plus_1{ptr, from_integer(1, pointer_diff_type())};
    typecast_exprt cast{ptr_plus_1, char_ptr_type};

    exprt result = simplify_expr(cast, empty_namespace);

    // Expected: (char*)ptr + 1
    plus_exprt expected{
      typecast_exprt{ptr, char_ptr_type}, from_integer(1, pointer_diff_type())};
    REQUIRE(result == expected);
  }

  SECTION("Element size ratio 4: (char*)(int_ptr + 1)")
  {
    // (char*)(ptr + 1) where ptr is int* should scale offset by 4
    auto int_ptr_type = pointer_type(signed_int_type());
    auto char_ptr_type = pointer_type(signed_char_type());
    symbol_exprt ptr{"ptr", int_ptr_type};
    plus_exprt ptr_plus_1{ptr, from_integer(1, pointer_diff_type())};
    typecast_exprt cast{ptr_plus_1, char_ptr_type};

    exprt result = simplify_expr(cast, empty_namespace);

    // Expected: (char*)ptr + 4
    plus_exprt expected{
      typecast_exprt{ptr, char_ptr_type}, from_integer(4, pointer_diff_type())};
    REQUIRE(result == expected);
  }
}

TEST_CASE("Simplify quantifier", "[core][util]")
{
  const namespacet &ns = empty_namespace;

  SECTION("Simplification for exists")
  {
    symbol_exprt a{"a", integer_typet{}};

    REQUIRE(simplify_expr(exists_exprt{a, false_exprt{}}, ns) == false_exprt{});

    REQUIRE(simplify_expr(exists_exprt{a, true_exprt{}}, ns) == true_exprt{});
  }

  SECTION("Simplification for forall")
  {
    symbol_exprt a{"a", integer_typet{}};

    REQUIRE(simplify_expr(forall_exprt{a, false_exprt{}}, ns) == false_exprt{});

    REQUIRE(simplify_expr(forall_exprt{a, true_exprt{}}, ns) == true_exprt{});
  }
}

TEST_CASE("Simplify all-zero constant in bitand", "[core][util]")
{
  const unsignedbv_typet u8{8};
  const symbol_exprt x{"x", u8};
  const auto zero = from_integer(0, u8);
  const bitand_exprt band{x, zero};
  REQUIRE(simplify_expr(band, empty_namespace) == zero);
}

TEST_CASE("Simplify all-ones constant in bitor", "[core][util]")
{
  const unsignedbv_typet u8{8};
  const symbol_exprt x{"x", u8};
  const auto ones = from_integer(255, u8);
  const bitor_exprt bor{x, ones};
  REQUIRE(simplify_expr(bor, empty_namespace) == ones);
}

TEST_CASE("Simplify all-zero constant in bitand with bv_typet", "[core][util]")
{
  const bv_typet bv8{8};
  const symbol_exprt x{"x", bv8};
  const auto zero = bv8.all_zeros_expr();
  const bitand_exprt band{x, zero};
  REQUIRE(simplify_expr(band, empty_namespace) == zero);
}

TEST_CASE("Simplify all-ones constant in bitor with bv_typet", "[core][util]")
{
  const bv_typet bv8{8};
  const symbol_exprt x{"x", bv8};
  const auto ones = bv8.all_ones_expr();
  const bitor_exprt bor{x, ones};
  REQUIRE(simplify_expr(bor, empty_namespace) == ones);
}

TEST_CASE("Simplify flatten nested OR", "[core][util]")
{
  const symbol_exprt a{"a", bool_typet{}};
  const symbol_exprt b{"b", bool_typet{}};
  const symbol_exprt c{"c", bool_typet{}};

  // (a || (b || c)) should flatten to (a || b || c)
  const or_exprt inner{b, c};
  const or_exprt nested{a, inner};
  REQUIRE(simplify_expr(nested, empty_namespace) == or_exprt{a, b, c});
}

TEST_CASE("Simplify flatten nested AND", "[core][util]")
{
  const symbol_exprt a{"a", bool_typet{}};
  const symbol_exprt b{"b", bool_typet{}};
  const symbol_exprt c{"c", bool_typet{}};

  // (a && (b && c)) should flatten to (a && b && c)
  const and_exprt inner{b, c};
  const and_exprt nested{a, inner};
  REQUIRE(simplify_expr(nested, empty_namespace) == and_exprt{a, b, c});
}

TEST_CASE("Simplify complementary pair in OR", "[core][util]")
{
  const symbol_exprt a{"a", bool_typet{}};

  // (a || !a) should simplify to true
  const or_exprt expr{a, not_exprt{a}};
  REQUIRE(simplify_expr(expr, empty_namespace) == true_exprt{});
}

TEST_CASE("Simplify complementary pair in AND", "[core][util]")
{
  const symbol_exprt a{"a", bool_typet{}};

  // (a && !a) should simplify to false
  const and_exprt expr{a, not_exprt{a}};
  REQUIRE(simplify_expr(expr, empty_namespace) == false_exprt{});
}

TEST_CASE("Simplify complementary pair in nested OR", "[core][util]")
{
  const symbol_exprt a{"a", bool_typet{}};
  const symbol_exprt b{"b", bool_typet{}};

  // (a || (b || !a)) should simplify to true (after flattening)
  const or_exprt inner{b, not_exprt{a}};
  const or_exprt expr{a, inner};
  REQUIRE(simplify_expr(expr, empty_namespace) == true_exprt{});
}
