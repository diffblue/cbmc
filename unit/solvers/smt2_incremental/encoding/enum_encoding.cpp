// Author: Diffblue Ltd.

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/c_types.h>
#include <util/namespace.h>
#include <util/symbol_table.h>

#include <solvers/smt2_incremental/encoding/enum_encoding.h>
#include <testing-utils/use_catch.h>

static c_enum_typet make_c_enum_type(
  const unsignedbv_typet &underlying_type,
  unsigned int value_count)
{
  c_enum_typet enum_type{underlying_type};

  auto &members = enum_type.members();
  members.reserve(value_count);

  for(unsigned int i = 0; i < value_count; ++i)
  {
    c_enum_typet::c_enum_membert member;
    member.set_identifier("V" + std::to_string(i));
    member.set_base_name("V" + std::to_string(i));
    member.set_value(integer2bvrep(i, underlying_type.get_width()));
    members.push_back(member);
  }
  return enum_type;
}

static constant_exprt create_enum_tag_typed_constant(
  const mp_integer &value,
  const c_enum_typet &enum_type,
  const c_enum_tag_typet &enum_tag_type)
{
  constant_exprt constant = from_integer(value, enum_type);
  constant.type() = enum_tag_type;
  return constant;
}

TEST_CASE("enum encoding of expressions", "[core][smt2_incremental]")
{
  std::size_t size;
  int value_count;
  using rowt = std::pair<int, int>;
  std::tie(size, value_count) = GENERATE(
    rowt{32, 42},
    rowt{64, 42},
    rowt{42, 42},
    rowt{2, 42},
    rowt{1, 42},
    rowt{42, 1},
    rowt{42, 0});

  INFO(
    "Checking enum of underlying size " + std::to_string(size) + " with " +
    std::to_string(value_count) + " elements");

  const unsignedbv_typet enum_underlying_type{size};
  const c_enum_typet enum_type =
    make_c_enum_type(enum_underlying_type, value_count);
  const type_symbolt enum_symbol{"my_enum", enum_type, ID_C};
  symbol_tablet symbol_table;
  const namespacet ns{symbol_table};
  symbol_table.insert(enum_symbol);
  const c_enum_tag_typet enum_tag{enum_symbol.name};
  const symbolt enum_value_symbol{"my_enum_value", enum_tag, ID_C};
  symbol_table.insert(enum_value_symbol);
  const auto symbol_expr = enum_value_symbol.symbol_expr();
  const auto symbol_expr_as_bv =
    symbol_exprt{"my_enum_value", unsignedbv_typet{size}};

  SECTION("enum lowering of non-enum type is a no-op")
  {
    constant_exprt expr = from_integer(10, signedbv_typet{42});
    REQUIRE(lower_enum(expr, ns) == expr);
  }

  SECTION("enum_tag typed symbol expression")
  {
    REQUIRE(lower_enum(symbol_expr, ns) == symbol_expr_as_bv);
  }

  SECTION("enum_tag equality expression")
  {
    const auto enum_equal = equal_exprt{symbol_expr, symbol_expr};
    const auto expected_bv_equal =
      equal_exprt{symbol_expr_as_bv, symbol_expr_as_bv};
    REQUIRE(lower_enum(enum_equal, ns) == expected_bv_equal);
  }

  SECTION("enum_tag in array")
  {
    const array_typet original_array_type{
      enum_tag, from_integer(2, unsignedbv_typet{32})};
    const array_typet lowered_array_type{
      enum_underlying_type, from_integer(2, unsignedbv_typet{32})};
    const array_exprt original_array_expr{
      {create_enum_tag_typed_constant(3, enum_type, enum_tag),
       create_enum_tag_typed_constant(3, enum_type, enum_tag)},
      original_array_type};
    const array_exprt expected_array_expr{
      {from_integer(3, unsignedbv_typet{size}),
       from_integer(3, unsignedbv_typet{size})},
      lowered_array_type};
    REQUIRE(lower_enum(original_array_expr, ns) == expected_array_expr);
  }
}
