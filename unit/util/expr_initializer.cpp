// Author: Diffblue Ltd.

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/c_types.h>
#include <util/expr_initializer.h>
#include <util/namespace.h>
#include <util/std_code.h>
#include <util/symbol_table.h>

#include <testing-utils/use_catch.h>

/// Helper struct to hold useful test components.
struct expr_initializer_test_environmentt
{
  symbol_tablet symbol_table;
  namespacet ns{symbol_table};
  source_locationt loc{};

  static expr_initializer_test_environmentt make()
  {
    return {};
  }

private:
  expr_initializer_test_environmentt() = default;
};

/// Helper function to create and populate a c_enum_typet type.
static c_enum_typet make_c_enum_type(const unsignedbv_typet &underlying_type)
{
  c_enum_typet enum_type{underlying_type};

  auto &members = enum_type.members();
  members.reserve(3);

  for(unsigned int i = 0; i < 3; ++i)
  {
    c_enum_typet::c_enum_membert member;
    member.set_identifier("V" + std::to_string(i));
    member.set_base_name("V" + std::to_string(i));
    member.set_value(integer2bvrep(i, underlying_type.get_width()));
    members.push_back(member);
  }
  return enum_type;
}

/// Create a type symbol and a type_tag and populate with the symbol_table in
/// with the symbol.
static tag_typet
create_tag_populate_env(const typet &type, symbol_tablet &symbol_table)
{
  const type_symbolt type_symbol{"my_type_symbol", type, ID_C};
  symbol_table.insert(type_symbol);

  if(can_cast_type<c_enum_typet>(type))
  {
    return c_enum_tag_typet{type_symbol.name};
  }
  else if(can_cast_type<struct_typet>(type))
  {
    return struct_tag_typet{type_symbol.name};
  }
  else if(can_cast_type<union_typet>(type))
  {
    return union_tag_typet{type_symbol.name};
  }
  UNREACHABLE;
}

TEST_CASE("nondet_initializer boolean", "[core][util][expr_initializer]")
{
  auto test = expr_initializer_test_environmentt::make();
  typet input = bool_typet{};
  const auto result = nondet_initializer(input, test.loc, test.ns);
  REQUIRE(result.has_value());
  const auto expected = side_effect_expr_nondett{bool_typet{}, test.loc};
  REQUIRE(result.value() == expected);
}

TEST_CASE("nondet_initializer signed_bv", "[core][util][expr_initializer]")
{
  auto test = expr_initializer_test_environmentt::make();
  typet input = signedbv_typet{8};
  const auto result = nondet_initializer(input, test.loc, test.ns);
  REQUIRE(result.has_value());
  const auto expected = side_effect_expr_nondett{signedbv_typet{8}, test.loc};
  REQUIRE(result.value() == expected);
}

TEST_CASE("nondet_initializer c_enum", "[core][util][expr_initializer]")
{
  auto test = expr_initializer_test_environmentt::make();
  const unsignedbv_typet enum_underlying_type{8};
  const auto enum_type = make_c_enum_type(enum_underlying_type);
  const auto result = nondet_initializer(enum_type, test.loc, test.ns);
  REQUIRE(result.has_value());
  const auto expected = side_effect_expr_nondett{enum_type, test.loc};
  REQUIRE(result.value() == expected);

  // Repeat with the c_enum_tag_typet instead of the c_enum_typet it points to
  const auto c_enum_tag_type =
    create_tag_populate_env(enum_type, test.symbol_table);
  const auto tag_result =
    nondet_initializer(c_enum_tag_type, test.loc, test.ns);
}

TEST_CASE(
  "nondet_initializer on fixed-size array of signed 8 bit elements",
  "[core][util][expr_initializer]")
{
  auto test = expr_initializer_test_environmentt::make();
  typet inner_type = signedbv_typet{8};
  const std::size_t elem_count = 3;
  typet array_type =
    array_typet{inner_type, from_integer(elem_count, signedbv_typet{8})};
  const auto result = nondet_initializer(array_type, test.loc, test.ns);
  REQUIRE(result.has_value());
  std::vector<exprt> array_values{
    elem_count, side_effect_expr_nondett{signedbv_typet{8}, test.loc}};
  const auto expected = array_exprt{
    array_values,
    array_typet{
      signedbv_typet{8}, from_integer(elem_count, signedbv_typet{8})}};
  REQUIRE(result.value() == expected);
}

TEST_CASE(
  "nondet_initializer on array of nondet size",
  "[core][util][expr_initializer]")
{
  auto test = expr_initializer_test_environmentt::make();
  typet inner_type = signedbv_typet{8};
  typet array_type = array_typet{
    inner_type, side_effect_expr_nondett{signedbv_typet{8}, test.loc}};
  const auto result = nondet_initializer(array_type, test.loc, test.ns);
  REQUIRE(result.has_value());
  const auto expected = side_effect_expr_nondett{
    array_typet{
      inner_type, side_effect_expr_nondett{signedbv_typet{8}, test.loc}},
    test.loc};
  REQUIRE(result.value() == expected);
}

TEST_CASE(
  "nondet_initializer on fixed-size array of fixed-size arrays",
  "[core][util][expr_initializer]")
{
  auto test = expr_initializer_test_environmentt::make();
  typet inner_type = signedbv_typet{8};
  const std::size_t elem_count = 3;
  typet inner_array_type =
    array_typet{inner_type, from_integer(elem_count, signedbv_typet{8})};
  typet array_type =
    array_typet{inner_array_type, from_integer(elem_count, signedbv_typet{8})};
  const auto result = nondet_initializer(array_type, test.loc, test.ns);
  REQUIRE(result.has_value());
  std::vector<exprt> inner_array_values{
    elem_count, side_effect_expr_nondett{signedbv_typet{8}, test.loc}};
  const auto inner_expected = array_exprt{
    inner_array_values,
    array_typet{
      signedbv_typet{8}, from_integer(elem_count, signedbv_typet{8})}};
  std::vector<exprt> array_values{elem_count, inner_expected};
  const auto expected = array_exprt{
    array_values,
    array_typet{
      array_typet{
        signedbv_typet{8}, from_integer(elem_count, signedbv_typet{8})},
      from_integer(elem_count, signedbv_typet{8})}};
  REQUIRE(result.value() == expected);
}

TEST_CASE(
  "nondet_initializer nested struct type",
  "[core][util][expr_initializer]")
{
  auto test = expr_initializer_test_environmentt::make();
  const struct_union_typet::componentst sub_struct_components{
    {"foo", signedbv_typet{32}}, {"bar", unsignedbv_typet{16}}};
  const struct_typet inner_struct_type{sub_struct_components};
  const struct_union_typet::componentst struct_components{
    {"fizz", bool_typet{}}, {"bar", inner_struct_type}};
  const struct_typet struct_type{struct_components};
  const auto result = nondet_initializer(struct_type, test.loc, test.ns);
  REQUIRE(result.has_value());
  const exprt::operandst expected_inner_struct_fields{
    side_effect_expr_nondett{signedbv_typet{32}, test.loc},
    side_effect_expr_nondett{unsignedbv_typet{16}, test.loc}};
  const struct_exprt expected_inner_struct_expr{
    expected_inner_struct_fields, inner_struct_type};
  const exprt::operandst expected_struct_fields{
    side_effect_expr_nondett{bool_typet{}, test.loc},
    expected_inner_struct_expr};
  const struct_exprt expected_struct_expr{expected_struct_fields, struct_type};
  REQUIRE(result.value() == expected_struct_expr);

  const auto inner_struct_tag_type =
    create_tag_populate_env(inner_struct_type, test.symbol_table);
  const auto tag_result =
    nondet_initializer(inner_struct_tag_type, test.loc, test.ns);
  REQUIRE(tag_result.has_value());
  const struct_exprt expected_inner_struct_tag_expr{
    expected_inner_struct_fields, inner_struct_tag_type};
  REQUIRE(tag_result.value() == expected_inner_struct_tag_expr);
}

TEST_CASE("nondet_initializer union type", "[core][util][expr_initializer]")
{
  auto test = expr_initializer_test_environmentt::make();
  const struct_union_typet::componentst inner_struct_components{
    {"foo", signedbv_typet{32}}, {"bar", unsignedbv_typet{16}}};
  const struct_typet inner_struct_type{inner_struct_components};
  const struct_union_typet::componentst union_components{
    {"foo", signedbv_typet{256}},
    {"bar", unsignedbv_typet{16}},
    {"fizz", bool_typet{}},
    {"array",
     array_typet{signedbv_typet{8}, from_integer(8, signedbv_typet{8})}},
    {"struct", inner_struct_type}};
  const union_typet union_type{union_components};
  const auto result = nondet_initializer(union_type, test.loc, test.ns);
  REQUIRE(result.has_value());
  const union_exprt expected_union{
    "foo", side_effect_expr_nondett{signedbv_typet{256}, test.loc}, union_type};
  REQUIRE(result.value() == expected_union);

  const auto union_tag_type =
    create_tag_populate_env(union_type, test.symbol_table);
  const auto tag_result = nondet_initializer(union_tag_type, test.loc, test.ns);
  REQUIRE(tag_result.has_value());
  const union_exprt expected_union_tag{
    "foo",
    side_effect_expr_nondett{signedbv_typet{256}, test.loc},
    union_tag_type};
  REQUIRE(tag_result.value() == expected_union_tag);
}

TEST_CASE(
  "nondet_initializer union type with nondet sized array (fails)",
  "[core][util][expr_initializer]")
{
  auto test = expr_initializer_test_environmentt::make();
  const struct_union_typet::componentst union_components{
    {"foo", signedbv_typet{256}},
    {"array",
     array_typet{
       signedbv_typet{8},
       side_effect_expr_nondett{signedbv_typet{8}, test.loc}}}};
  const union_typet union_type{union_components};
  const auto result = nondet_initializer(union_type, test.loc, test.ns);
  REQUIRE_FALSE(result.has_value());
}

TEST_CASE("nondet_initializer string type", "[core][util][expr_initializer]")
{
  auto test = expr_initializer_test_environmentt::make();
  const string_typet string_type{};
  const auto result = nondet_initializer(string_type, test.loc, test.ns);
  REQUIRE(result.has_value());
  const side_effect_expr_nondett expected_string{string_typet{}, test.loc};
  REQUIRE(result.value() == expected_string);
}
