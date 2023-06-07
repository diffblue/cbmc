// Author: Diffblue Ltd.

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/mathematical_types.h>
#include <util/namespace.h>
#include <util/symbol_table.h>

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
          symbol_exprt{"breakfast", bv_typet{72}}, 71, 40, field_type}};
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
          symbol_exprt{"breakfast", bv_typet{72}}, 39, 24, field_type}};
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
          symbol_exprt{"breakfast", bv_typet{72}}, 23, 0, field_type}};
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
         extractbits_exprt{symbol_expr_as_bv, 39, 24, unsignedbv_typet{16}},
         extractbits_exprt{symbol_expr_as_bv, 23, 0, signedbv_typet{24}}},
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
        {extractbits_exprt{symbol_expr_as_bv, 71, 40, signedbv_typet{32}},
         from_integer(0, unsignedbv_typet{16}),
         extractbits_exprt{symbol_expr_as_bv, 23, 0, signedbv_typet{24}}},
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
        {extractbits_exprt{symbol_expr_as_bv, 71, 40, signedbv_typet{32}},
         extractbits_exprt{symbol_expr_as_bv, 39, 24, unsignedbv_typet{16}},
         from_integer(0, signedbv_typet{24})},
        bv_typet{72}};
      REQUIRE(test.struct_encoding.encode(with) == expected);
    }
    SECTION("First and second members")
    {
      const concatenation_exprt expected{
        {from_integer(0, signedbv_typet{32}),
         from_integer(1, unsignedbv_typet{16}),
         extractbits_exprt{symbol_expr_as_bv, 23, 0, signedbv_typet{24}}},
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
         extractbits_exprt{symbol_expr_as_bv, 39, 24, unsignedbv_typet{16}},
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
        {extractbits_exprt{symbol_expr_as_bv, 71, 40, signedbv_typet{32}},
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
