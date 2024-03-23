// Author: Diffblue Ltd.

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/c_types.h>
#include <util/mathematical_types.h>
#include <util/namespace.h>
#include <util/symbol_table.h>

#include <solvers/smt2_incremental/encoding/nondet_padding.h>
#include <solvers/smt2_incremental/encoding/struct_encoding.h>
#include <testing-utils/use_catch.h>

struct struct_encoding_test_environmentt
{
  symbol_tablet symbol_table;
  namespacet ns{symbol_table};
  struct_encodingt struct_encoding{ns};

  static struct_encoding_test_environmentt make()
  {
    return {};
  }

private:
  struct_encoding_test_environmentt() = default;
};

TEST_CASE(
  "struct encoding of non-stuct type is a no-op",
  "[core][smt2_incremental]")
{
  auto test = struct_encoding_test_environmentt::make();
  typet input = signedbv_typet{8};
  REQUIRE(test.struct_encoding.encode(input) == input);
}

TEST_CASE("struct encoding of types", "[core][smt2_incremental]")
{
  const struct_union_typet::componentst components{
    {"foo", unsignedbv_typet{8}}, {"bar", signedbv_typet{16}}};
  struct_typet struct_type{components};
  type_symbolt type_symbol{"my_structt", struct_type, ID_C};
  auto test = struct_encoding_test_environmentt::make();
  test.symbol_table.insert(type_symbol);
  struct_tag_typet struct_tag{type_symbol.name};
  SECTION("direct struct_tag_type encoding")
  {
    REQUIRE(test.struct_encoding.encode(struct_tag) == bv_typet{24});
  }
  SECTION("array of structs encoding")
  {
    const auto index_type = signedbv_typet{32};
    const auto array_size = from_integer(5, index_type);
    array_typet array_of_struct{struct_tag, array_size};
    array_typet expected_encoded_array{bv_typet{24}, array_size};
    REQUIRE(
      test.struct_encoding.encode(array_of_struct) == expected_encoded_array);
  }
  SECTION("array of array of structs encoding")
  {
    const auto index_type = signedbv_typet{32};
    const auto array_size_inner = from_integer(4, index_type);
    const auto array_size_outer = from_integer(2, index_type);
    array_typet array_of_struct{struct_tag, array_size_inner};
    array_typet array_of_array_of_struct{array_of_struct, array_size_outer};
    array_typet expected_encoded_array{
      array_typet{bv_typet{24}, array_size_inner}, array_size_outer};
    REQUIRE(
      test.struct_encoding.encode(array_of_array_of_struct) ==
      expected_encoded_array);
  }
}

TEST_CASE("Encoding of union types", "[core][smt2_incremental]")
{
  auto test = struct_encoding_test_environmentt::make();
  SECTION("Two components")
  {
    const struct_union_typet::componentst components{
      {"foo", unsignedbv_typet{8}}, {"bar", signedbv_typet{16}}};
    union_typet union_type{components};
    type_symbolt type_symbol{"my_uniont", union_type, ID_C};
    test.symbol_table.insert(type_symbol);
    union_tag_typet union_tag{type_symbol.name};
    SECTION("Direct union_tag_type encoding")
    {
      REQUIRE(test.struct_encoding.encode(union_tag) == bv_typet{16});
    }
    SECTION("Array of unions encoding")
    {
      const auto index_type = signedbv_typet{32};
      const auto array_size = from_integer(5, index_type);
      array_typet array_of_struct{union_tag, array_size};
      array_typet expected_encoded_array{bv_typet{16}, array_size};
      REQUIRE(
        test.struct_encoding.encode(array_of_struct) == expected_encoded_array);
    }
    SECTION("Array of array of unions encoding")
    {
      const auto index_type = signedbv_typet{32};
      const auto array_size_inner = from_integer(4, index_type);
      const auto array_size_outer = from_integer(2, index_type);
      array_typet array_of_struct{union_tag, array_size_inner};
      array_typet array_of_array_of_struct{array_of_struct, array_size_outer};
      array_typet expected_encoded_array{
        array_typet{bv_typet{16}, array_size_inner}, array_size_outer};
      REQUIRE(
        test.struct_encoding.encode(array_of_array_of_struct) ==
        expected_encoded_array);
    }
  }
  SECTION("Empty union")
  {
    const struct_union_typet::componentst components{};
    union_typet union_type{components};
    type_symbolt type_symbol{"my_empty_uniont", union_type, ID_C};
    test.symbol_table.insert(type_symbol);
    union_tag_typet union_tag{type_symbol.name};
    SECTION("Direct union_tag_type encoding")
    {
      REQUIRE(test.struct_encoding.encode(union_tag) == bv_typet{8});
    }
    SECTION("Value enoding")
    {
      const symbolt symbol{"my_empty_union", union_tag, ID_C};
      test.symbol_table.insert(symbol);
      const auto symbol_is_empty =
        equal_exprt{symbol.symbol_expr(), empty_union_exprt{union_tag}};
      const auto expected = equal_exprt{
        symbol_exprt{"my_empty_union", bv_typet{8}},
        from_integer(0, bv_typet{8})};
      REQUIRE(test.struct_encoding.encode(symbol_is_empty) == expected);
    }
  }
}

exprt make_member_name_expression(const irep_idt component_name)
{
  exprt result{ID_member_name};
  result.set(ID_component_name, component_name);
  return result;
}

TEST_CASE("struct encoding of expressions", "[core][smt2_incremental]")
{
  const struct_union_typet::componentst component_types{
    {"green", signedbv_typet{32}},
    {"eggs", unsignedbv_typet{16}},
    {"ham", signedbv_typet{24}}};
  const struct_typet struct_type{component_types};
  const type_symbolt type_symbol{"my_structt", struct_type, ID_C};
  auto test = struct_encoding_test_environmentt::make();
  test.symbol_table.insert(type_symbol);
  const struct_tag_typet struct_tag{type_symbol.name};
  const symbolt struct_value_symbol{"my_struct", struct_tag, ID_C};
  test.symbol_table.insert(struct_value_symbol);
  const auto symbol_expr = struct_value_symbol.symbol_expr();
  const auto symbol_expr_as_bv = symbol_exprt{"my_struct", bv_typet{72}};
  SECTION("struct typed symbol expression")
  {
    REQUIRE(test.struct_encoding.encode(symbol_expr) == symbol_expr_as_bv);
  }
  SECTION("struct equality expression")
  {
    const auto struct_equal = equal_exprt{symbol_expr, symbol_expr};
    const auto bv_equal = equal_exprt{symbol_expr_as_bv, symbol_expr_as_bv};
    REQUIRE(test.struct_encoding.encode(struct_equal) == bv_equal);
  }
  SECTION("expression for a struct from list of components")
  {
    const symbolt green_ham{"ham", signedbv_typet{32}, ID_C};
    test.symbol_table.insert(green_ham);
    const auto forty_two = from_integer(42, unsignedbv_typet{16});
    const auto minus_one = from_integer(-1, signedbv_typet{24});
    const exprt::operandst components{
      green_ham.symbol_expr(), forty_two, minus_one};
    const struct_exprt struct_expr{components, struct_tag};
    const concatenation_exprt expected_result{
      {green_ham.symbol_expr(), forty_two, minus_one}, bv_typet{72}};
    REQUIRE(test.struct_encoding.encode(struct_expr) == expected_result);
    SECTION("struct containing a single struct")
    {
      const struct_typet struct_struct_type{
        struct_union_typet::componentst{{"inner", struct_tag}}};
      const type_symbolt struct_struct_type_symbol{
        "struct_structt", struct_type, ID_C};
      test.symbol_table.insert(type_symbol);
      const struct_tag_typet struct_struct_tag{type_symbol.name};
      const struct_exprt struct_struct{
        exprt::operandst{struct_expr}, struct_struct_tag};
      REQUIRE(test.struct_encoding.encode(struct_struct) == expected_result);
    }
  }
  SECTION("member expression selecting a data member of a struct")
  {
    const symbolt breakfast{"breakfast", struct_tag, ID_C};
    test.symbol_table.insert(breakfast);
    SECTION("First member")
    {
      const typet field_type = signedbv_typet{32};
      const exprt zero = from_integer(0, field_type);
      const exprt input = equal_exprt{
        zero, member_exprt{breakfast.symbol_expr(), "green", field_type}};
      const exprt expected = equal_exprt{
        zero,
        extractbits_exprt{
          symbol_exprt{"breakfast", bv_typet{72}}, 40, field_type}};
      REQUIRE(test.struct_encoding.encode(input) == expected);
    }
    SECTION("Second member")
    {
      const typet field_type = unsignedbv_typet{16};
      const exprt dozen = from_integer(12, field_type);
      const exprt input = equal_exprt{
        dozen, member_exprt{breakfast.symbol_expr(), "eggs", field_type}};
      const exprt expected = equal_exprt{
        dozen,
        extractbits_exprt{
          symbol_exprt{"breakfast", bv_typet{72}}, 24, field_type}};
      REQUIRE(test.struct_encoding.encode(input) == expected);
    }
    SECTION("Third member")
    {
      const typet field_type = signedbv_typet{24};
      const exprt two = from_integer(2, field_type);
      const exprt input = equal_exprt{
        two, member_exprt{breakfast.symbol_expr(), "ham", field_type}};
      const exprt expected = equal_exprt{
        two,
        extractbits_exprt{
          symbol_exprt{"breakfast", bv_typet{72}}, 0, field_type}};
      REQUIRE(test.struct_encoding.encode(input) == expected);
    }
  }
  SECTION("with expression producing new struct with substituted member")
  {
    SECTION("First member")
    {
      const with_exprt with{
        symbol_expr,
        make_member_name_expression("green"),
        from_integer(0, signedbv_typet{32})};
      const concatenation_exprt expected{
        {from_integer(0, signedbv_typet{32}),
         extractbits_exprt{symbol_expr_as_bv, 24, unsignedbv_typet{16}},
         extractbits_exprt{symbol_expr_as_bv, 0, signedbv_typet{24}}},
        bv_typet{72}};
      REQUIRE(test.struct_encoding.encode(with) == expected);
    }
    SECTION("Second member")
    {
      const with_exprt with{
        symbol_expr,
        make_member_name_expression("eggs"),
        from_integer(0, unsignedbv_typet{16})};
      const concatenation_exprt expected{
        {extractbits_exprt{symbol_expr_as_bv, 40, signedbv_typet{32}},
         from_integer(0, unsignedbv_typet{16}),
         extractbits_exprt{symbol_expr_as_bv, 0, signedbv_typet{24}}},
        bv_typet{72}};
      REQUIRE(test.struct_encoding.encode(with) == expected);
    }
    SECTION("Third member")
    {
      const with_exprt with{
        symbol_expr,
        make_member_name_expression("ham"),
        from_integer(0, signedbv_typet{24})};
      const concatenation_exprt expected{
        {extractbits_exprt{symbol_expr_as_bv, 40, signedbv_typet{32}},
         extractbits_exprt{symbol_expr_as_bv, 24, unsignedbv_typet{16}},
         from_integer(0, signedbv_typet{24})},
        bv_typet{72}};
      REQUIRE(test.struct_encoding.encode(with) == expected);
    }
    SECTION("First and second members")
    {
      const concatenation_exprt expected{
        {from_integer(0, signedbv_typet{32}),
         from_integer(1, unsignedbv_typet{16}),
         extractbits_exprt{symbol_expr_as_bv, 0, signedbv_typet{24}}},
        bv_typet{72}};
      SECTION("Operands in field order")
      {
        with_exprt with_in_order{
          symbol_expr,
          make_member_name_expression("green"),
          from_integer(0, signedbv_typet{32})};
        with_in_order.operands().push_back(make_member_name_expression("eggs"));
        with_in_order.operands().push_back(
          from_integer(1, unsignedbv_typet{16}));
        REQUIRE(test.struct_encoding.encode(with_in_order) == expected);
      }
      SECTION("Operands in reverse order vs fields")
      {
        with_exprt with_reversed{
          symbol_expr,
          make_member_name_expression("eggs"),
          from_integer(1, unsignedbv_typet{16})};
        with_reversed.operands().push_back(
          make_member_name_expression("green"));
        with_reversed.operands().push_back(from_integer(0, signedbv_typet{32}));
        REQUIRE(test.struct_encoding.encode(with_reversed) == expected);
      }
    }
    SECTION("First and third members")
    {
      const concatenation_exprt expected{
        {from_integer(0, signedbv_typet{32}),
         extractbits_exprt{symbol_expr_as_bv, 24, unsignedbv_typet{16}},
         from_integer(1, signedbv_typet{24})},
        bv_typet{72}};
      SECTION("Operands in field order")
      {
        with_exprt with_in_order{
          symbol_expr,
          make_member_name_expression("green"),
          from_integer(0, signedbv_typet{32})};
        with_in_order.operands().push_back(make_member_name_expression("ham"));
        with_in_order.operands().push_back(from_integer(1, signedbv_typet{24}));
        REQUIRE(test.struct_encoding.encode(with_in_order) == expected);
      }
      SECTION("Operands in reverse order vs fields")
      {
        with_exprt with_reversed{
          symbol_expr,
          make_member_name_expression("ham"),
          from_integer(1, signedbv_typet{24})};
        with_reversed.operands().push_back(
          make_member_name_expression("green"));
        with_reversed.operands().push_back(from_integer(0, signedbv_typet{32}));
        REQUIRE(test.struct_encoding.encode(with_reversed) == expected);
      }
    }
    SECTION("Second and third members")
    {
      const concatenation_exprt expected{
        {extractbits_exprt{symbol_expr_as_bv, 40, signedbv_typet{32}},
         from_integer(0, unsignedbv_typet{16}),
         from_integer(1, signedbv_typet{24})},
        bv_typet{72}};
      SECTION("Operands in field order")
      {
        with_exprt with_in_order{
          symbol_expr,
          make_member_name_expression("eggs"),
          from_integer(0, unsignedbv_typet{16})};
        with_in_order.operands().push_back(make_member_name_expression("ham"));
        with_in_order.operands().push_back(from_integer(1, signedbv_typet{24}));
        REQUIRE(test.struct_encoding.encode(with_in_order) == expected);
      }
      SECTION("Operands in reverse order vs fields")
      {
        with_exprt with_reversed{
          symbol_expr,
          make_member_name_expression("ham"),
          from_integer(1, signedbv_typet{24})};
        with_reversed.operands().push_back(make_member_name_expression("eggs"));
        with_reversed.operands().push_back(
          from_integer(0, unsignedbv_typet{16}));
        REQUIRE(test.struct_encoding.encode(with_reversed) == expected);
      }
    }
    SECTION("All members")
    {
      const concatenation_exprt expected{
        {from_integer(1, signedbv_typet{32}),
         from_integer(2, unsignedbv_typet{16}),
         from_integer(3, signedbv_typet{24})},
        bv_typet{72}};
      SECTION("Operands in field order")
      {
        with_exprt with{
          symbol_expr,
          make_member_name_expression("green"),
          from_integer(1, signedbv_typet{32})};
        with.operands().push_back(make_member_name_expression("eggs"));
        with.operands().push_back(from_integer(2, unsignedbv_typet{16}));
        with.operands().push_back(make_member_name_expression("ham"));
        with.operands().push_back(from_integer(3, signedbv_typet{24}));
        REQUIRE(test.struct_encoding.encode(with) == expected);
      }
      SECTION("Operands out of order vs fields")
      {
        with_exprt with{
          symbol_expr,
          make_member_name_expression("eggs"),
          from_integer(2, unsignedbv_typet{16})};
        with.operands().push_back(make_member_name_expression("ham"));
        with.operands().push_back(from_integer(3, signedbv_typet{24}));
        with.operands().push_back(make_member_name_expression("green"));
        with.operands().push_back(from_integer(1, signedbv_typet{32}));
        REQUIRE(test.struct_encoding.encode(with) == expected);
      }
    }
  }
}

TEST_CASE("decoding into struct expressions.", "[core][smt2_incremental]")
{
  const struct_union_typet::componentst component_types{
    {"green", signedbv_typet{32}},
    {"eggs", unsignedbv_typet{16}},
    {"ham", signedbv_typet{24}}};
  const struct_typet struct_type{component_types};
  const type_symbolt type_symbol{"my_structt", struct_type, ID_C};
  auto test = struct_encoding_test_environmentt::make();
  test.symbol_table.insert(type_symbol);
  const struct_tag_typet struct_tag{type_symbol.name};
  const struct_exprt expected{
    {from_integer(3, signedbv_typet{32}),
     from_integer(2, unsignedbv_typet{16}),
     from_integer(1, signedbv_typet{24})},
    struct_tag};
  const exprt encoded = constant_exprt{"30002000001", bv_typet{72}};
  REQUIRE(test.struct_encoding.decode(encoded, struct_tag) == expected);
}

TEST_CASE("decoding into union expressions.", "[core][smt2_incremental]")
{
  auto test = struct_encoding_test_environmentt::make();
  SECTION("Single union component")
  {
    const struct_union_typet::componentst type_components{
      {"eggs", unsignedbv_typet{16}}};
    const union_typet union_type{type_components};
    const type_symbolt type_symbol{"my_uniont", union_type, ID_C};
    test.symbol_table.insert(type_symbol);
    const union_tag_typet union_tag{type_symbol.name};
    const union_exprt expected{
      "eggs", from_integer(12, unsignedbv_typet{16}), union_tag};
    const exprt encoded = from_integer(12, bv_typet{16});
    REQUIRE(test.struct_encoding.decode(encoded, union_tag) == expected);
  }
  SECTION("Multiple union components")
  {
    const struct_union_typet::componentst type_components{
      {"green", signedbv_typet{32}},
      {"eggs", unsignedbv_typet{16}},
      {"ham", signedbv_typet{24}}};
    const union_typet union_type{type_components};
    const type_symbolt type_symbol{"my_uniont", union_type, ID_C};
    test.symbol_table.insert(type_symbol);
    const union_tag_typet union_tag{type_symbol.name};
    const union_exprt expected{
      "green", from_integer(-42, signedbv_typet{32}), union_tag};
    const exprt encoded = from_integer((~uint32_t{42} + 1), bv_typet{32});
    REQUIRE(test.struct_encoding.decode(encoded, union_tag) == expected);
  }
  SECTION("Empty union")
  {
    const struct_union_typet::componentst type_components{};
    const union_typet union_type{type_components};
    const type_symbolt type_symbol{"my_empty_uniont", union_type, ID_C};
    test.symbol_table.insert(type_symbol);
    const union_tag_typet union_tag{type_symbol.name};
    const empty_union_exprt expected{union_tag};
    const exprt encoded = from_integer(0, bv_typet{8});
    REQUIRE(test.struct_encoding.decode(encoded, union_tag) == expected);
  }
}

TEST_CASE("encoding of struct with no members", "[core][smt2_incremental]")
{
  auto test = struct_encoding_test_environmentt::make();
  const struct_union_typet::componentst component_types{};
  const type_symbolt type_symbol{"emptyt", struct_typet{component_types}, ID_C};
  test.symbol_table.insert(type_symbol);
  const struct_tag_typet type_reference{type_symbol.name};
  const auto expected_type = bv_typet{8};
  const auto expected_zero_byte = from_integer(0, expected_type);
  SECTION("Type of empty struct")
  {
    REQUIRE(test.struct_encoding.encode(type_reference) == expected_type);
  }
  SECTION("Empty struct typed symbol expression")
  {
    const symbolt empty_value_symbol{"foo", type_reference, ID_C};
    test.symbol_table.insert(empty_value_symbol);
    const auto symbol_expr = empty_value_symbol.symbol_expr();
    const exprt expected_symbol = symbol_exprt{"foo", expected_type};
    REQUIRE(test.struct_encoding.encode(symbol_expr) == expected_symbol);
  }
  SECTION("Struct expression")
  {
    const struct_exprt empty{{}, type_reference};
    REQUIRE(test.struct_encoding.encode(empty) == expected_zero_byte);
  }
}

TEST_CASE(
  "encoding of single member struct expressions",
  "[core][smt2_incremental]")
{
  const struct_union_typet::componentst component_types{
    {"eggs", signedbv_typet{32}}};
  const type_symbolt type_symbol{"foot", struct_typet{component_types}, ID_C};
  auto test = struct_encoding_test_environmentt::make();
  test.symbol_table.insert(type_symbol);
  const struct_tag_typet struct_tag{type_symbol.name};
  const symbolt struct_value_symbol{"foo", struct_tag, ID_C};
  test.symbol_table.insert(struct_value_symbol);
  const auto symbol_expr = struct_value_symbol.symbol_expr();
  const auto symbol_expr_as_bv = symbol_exprt{"foo", bv_typet{32}};
  SECTION("struct typed symbol expression")
  {
    REQUIRE(test.struct_encoding.encode(symbol_expr) == symbol_expr_as_bv);
  }
  SECTION("struct equality expression")
  {
    const auto struct_equal = equal_exprt{symbol_expr, symbol_expr};
    const auto bv_equal = equal_exprt{symbol_expr_as_bv, symbol_expr_as_bv};
    REQUIRE(test.struct_encoding.encode(struct_equal) == bv_equal);
  }
  SECTION("expression for a struct from (single item) list of components")
  {
    const auto dozen = from_integer(12, signedbv_typet{32});
    const struct_exprt struct_expr{{dozen}, struct_tag};
    REQUIRE(test.struct_encoding.encode(struct_expr) == dozen);
  }
}

TEST_CASE("encoding of union expressions", "[core][smt2_incremental]")
{
  const struct_union_typet::componentst components{
    {"eggs", unsignedbv_typet{8}}, {"ham", signedbv_typet{32}}};
  const type_symbolt type_symbol{"foot", union_typet{components}, ID_C};
  auto test = struct_encoding_test_environmentt::make();
  test.symbol_table.insert(type_symbol);
  const union_tag_typet union_tag{type_symbol.name};
  const symbolt union_value_symbol{"foo", union_tag, ID_C};
  test.symbol_table.insert(union_value_symbol);
  const auto symbol_expr = union_value_symbol.symbol_expr();
  const auto symbol_expr_as_bv = symbol_exprt{"foo", bv_typet{32}};
  const auto dozen = from_integer(12, unsignedbv_typet{8});
  const auto partial_union = union_exprt{"eggs", dozen, union_tag};
  const auto partial_union_as_bv = concatenation_exprt{
    {nondet_padding_exprt{bv_typet{24}}, dozen}, bv_typet{32}};
  SECTION("Union typed symbol expression")
  {
    REQUIRE(test.struct_encoding.encode(symbol_expr) == symbol_expr_as_bv);
  }
  SECTION("Expression for a union from a component")
  {
    REQUIRE(test.struct_encoding.encode(partial_union) == partial_union_as_bv);
    const auto one = from_integer(1, unsignedbv_typet{32});
    const auto full_union = union_exprt{"ham", one, union_tag};
    const auto full_union_as_bv = typecast_exprt{one, bv_typet{32}};
    REQUIRE(test.struct_encoding.encode(full_union) == full_union_as_bv);
  }
  SECTION("Union equality expression")
  {
    const auto union_equal = equal_exprt{symbol_expr, partial_union};
    const auto bv_equal = equal_exprt{symbol_expr_as_bv, partial_union_as_bv};
    REQUIRE(test.struct_encoding.encode(union_equal) == bv_equal);
  }
  SECTION("member expression selecting a data member of a union")
  {
    SECTION("Member which fits the size of the whole union")
    {
      const typet field_type = signedbv_typet{32};
      const exprt zero = from_integer(0, field_type);
      const exprt input =
        equal_exprt{zero, member_exprt{symbol_expr, "ham", field_type}};
      const exprt expected =
        equal_exprt{zero, extractbits_exprt{symbol_expr_as_bv, 0, field_type}};
      REQUIRE(test.struct_encoding.encode(input) == expected);
    }
    SECTION("Member which is smaller than the union as a whole")
    {
      const typet field_type = unsignedbv_typet{8};
      const exprt input =
        equal_exprt{dozen, member_exprt{symbol_expr, "eggs", field_type}};
      const exprt expected =
        equal_exprt{dozen, extractbits_exprt{symbol_expr_as_bv, 0, field_type}};
      REQUIRE(test.struct_encoding.encode(input) == expected);
    }
  }
}
