// Author: Diffblue Ltd.

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/namespace.h>
#include <util/pointer_predicates.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

#include <solvers/smt2_incremental/object_tracking.h>
#include <testing-utils/use_catch.h>

#include <string>
#include <utility>

TEST_CASE("find_object_base_expression", "[core][smt2_incremental]")
{
  const std::size_t pointer_bits = 64;
  SECTION("Address of symbol")
  {
    // Constructed address of expression should be equivalent to the following
    // C expression - `&base`.
    const typet base_type = unsignedbv_typet{8};
    const symbol_exprt object_base{"base", base_type};
    const address_of_exprt address_of{
      object_base, pointer_typet{base_type, pointer_bits}};
    INFO("Address of expression is: " + address_of.pretty(2, 0));
    CHECK(find_object_base_expression(address_of) == object_base);
  }
  SECTION("Address of index")
  {
    // Constructed address of expression should be equivalent to the following
    // C expression - `&(base[index])`.
    const unsignedbv_typet element_type{8};
    const signedbv_typet index_type{pointer_bits};
    const array_typet base_type{element_type, from_integer(42, index_type)};
    const symbol_exprt object_base{"base", base_type};
    const symbol_exprt index{"index", index_type};
    const pointer_typet pointer_type{element_type, pointer_bits};
    const address_of_exprt address_of{
      index_exprt{object_base, index}, pointer_type};
    INFO("Address of expression is: " + address_of.pretty(2, 0));
    CHECK(find_object_base_expression(address_of) == object_base);
  }
  SECTION("Address of struct member")
  {
    // Constructed address of expression should be equivalent to the following
    // C expression - `&(base.baz)`.
    const struct_tag_typet base_type{"structt"};
    const symbol_exprt object_base{"base", base_type};
    const unsignedbv_typet member_type{8};
    const address_of_exprt address_of{
      member_exprt{object_base, "baz", member_type},
      pointer_typet{member_type, pointer_bits}};
    INFO("Address of expression is: " + address_of.pretty(2, 0));
    CHECK(find_object_base_expression(address_of) == object_base);
  }
  SECTION("Address of index of struct member")
  {
    // Constructed address of expression should be equivalent to the following
    // C expression - `&(base.baz[index])`.
    const struct_tag_typet base_type{"structt"};
    const symbol_exprt object_base{"base", base_type};

    const unsignedbv_typet element_type{8};
    const signedbv_typet index_type{pointer_bits};
    const array_typet member_type{element_type, from_integer(42, index_type)};
    const symbol_exprt index{"index", index_type};

    const address_of_exprt address_of{
      index_exprt{member_exprt{object_base, "baz", member_type}, index},
      pointer_typet{element_type, pointer_bits}};
    INFO("Address of expression is: " + address_of.pretty(2, 0));
    CHECK(find_object_base_expression(address_of) == object_base);
  }
  SECTION("Address of struct member at index")
  {
    // Constructed address of expression should be equivalent to the following
    // C expression - `&(base[index].qux)`.
    const struct_tag_typet element_type{"struct_elementt"};
    const signedbv_typet index_type{pointer_bits};
    const array_typet base_type{element_type, from_integer(42, index_type)};
    const symbol_exprt object_base{"base", base_type};
    const symbol_exprt index{"index", index_type};
    const unsignedbv_typet member_type{8};
    const address_of_exprt address_of{
      member_exprt{index_exprt{object_base, index}, "qux", member_type},
      pointer_typet{member_type, pointer_bits}};
    INFO("Address of expression is: " + address_of.pretty(2, 0));
    CHECK(find_object_base_expression(address_of) == object_base);
  }
}

TEST_CASE("Tracking object base expressions", "[core][smt2_incremental]")
{
  const typet base_type = pointer_typet{signedbv_typet{16}, 18};
  const symbol_exprt foo{
    "foo", array_typet(base_type, from_integer(2, size_type()))};
  const symbol_exprt bar{"bar", base_type};
  const symbol_exprt qux{"qux", struct_typet{}};
  const symbol_exprt index{"index", base_type};
  const pointer_typet pointer_type{base_type, 32};
  const exprt bar_address = address_of_exprt{bar, pointer_type};
  const exprt compound_expression = and_exprt{
    equal_exprt{
      address_of_exprt{index_exprt{foo, index}, pointer_type}, bar_address},
    notequal_exprt{
      address_of_exprt{
        member_exprt(qux, "baz", unsignedbv_typet{8}), pointer_type},
      bar_address}};
  SECTION("Find base expressions")
  {
    std::vector<exprt> expressions;
    find_object_base_expressions(compound_expression, [&](const exprt &expr) {
      expressions.push_back(expr);
    });
    CHECK(expressions == std::vector<exprt>{bar, qux, bar, foo});
  }
  smt_object_mapt object_map = initial_smt_object_map();
  SECTION("Check initial object map has null pointer")
  {
    REQUIRE(object_map.size() == 2);
    const exprt null_pointer = null_pointer_exprt{::pointer_type(void_type())};
    const auto actual_null_object = object_map.find(null_pointer);
    CHECK(actual_null_object->first == null_pointer);
    CHECK(actual_null_object->second.unique_id == 0);
    CHECK(actual_null_object->second.base_expression == null_pointer);
    const exprt invalid_object_pointer = make_invalid_pointer_expr();
    const auto actual_invalid_object_pointer =
      object_map.find(invalid_object_pointer);
    CHECK(actual_invalid_object_pointer->first == invalid_object_pointer);
    CHECK(actual_invalid_object_pointer->second.unique_id == 1);
    CHECK(
      actual_invalid_object_pointer->second.base_expression ==
      invalid_object_pointer);
  }
  symbol_tablet symbol_table;
  namespacet ns{symbol_table};
  SECTION("Check objects of compound expression not yet tracked")
  {
    CHECK_FALSE(objects_are_already_tracked(compound_expression, object_map));
  }
  track_expression_objects(compound_expression, ns, object_map);
  SECTION("Tracking expression objects")
  {
    CHECK(object_map.size() == 5);
    const auto foo_object = object_map.find(foo);
    REQUIRE(foo_object != object_map.end());
    CHECK(foo_object->second.base_expression == foo);
    CHECK(foo_object->second.unique_id == 4);
    const auto bar_object = object_map.find(bar);
    REQUIRE(bar_object != object_map.end());
    CHECK(bar_object->second.base_expression == bar);
    CHECK(bar_object->second.unique_id == 2);
  }
  SECTION("Confirming objects are tracked.")
  {
    CHECK(objects_are_already_tracked(compound_expression, object_map));
  }
}

static symbolt make_size_variable()
{
  symbolt size_variable;
  size_variable.name = "size_variable";
  size_variable.base_name = "size_variable";
  size_variable.type = size_type();
  return size_variable;
}

TEST_CASE("Tracking object sizes.", "[core][smt2_incremental]")
{
  // Configuration needs to be performed before tracking because the size_type()
  // width depends on the global configuration.
  config.ansi_c.mode = configt::ansi_ct::flavourt::GCC;
  config.ansi_c.set_arch_spec_x86_64();
  smt_object_mapt object_map = initial_smt_object_map();
  symbol_tablet symbol_table;
  const symbolt size_variable = make_size_variable();
  symbol_table.insert(size_variable);
  const symbol_exprt size_expr = size_variable.symbol_expr();
  namespacet ns{symbol_table};
  exprt base_object;
  exprt expected_size;
  using rowt = std::pair<decltype(base_object), decltype(expected_size)>;
  std::tie(base_object, expected_size) = GENERATE_REF(
    rowt{from_integer(0, unsignedbv_typet{(8)}), from_integer(1, size_type())},
    rowt{from_integer(42, signedbv_typet{16}), from_integer(2, size_type())},
    rowt{from_integer(-24, signedbv_typet{32}), from_integer(4, size_type())},
    rowt{from_integer(2, unsignedbv_typet{64}), from_integer(8, size_type())},
    rowt{
      symbol_exprt{"array", array_typet{unsignedbv_typet{8}, size_expr}},
      size_expr},
    rowt{
      symbol_exprt{"array", array_typet{signedbv_typet{32}, size_expr}},
      mult_exprt{size_expr, from_integer(4, size_type())}});
  track_expression_objects(address_of_exprt{base_object}, ns, object_map);
  const auto object = object_map.find(base_object);
  REQUIRE(object != object_map.end());
  REQUIRE(object->second.size == expected_size);
}

static typet make_type_dynamic(typet base_type)
{
  base_type.set(ID_C_dynamic, true);
  return base_type;
}

TEST_CASE("Tracking dynamic object status.", "[core][smt2_incremental]")
{
  config.ansi_c.mode = configt::ansi_ct::flavourt::GCC;
  config.ansi_c.set_arch_spec_x86_64();
  smt_object_mapt object_map = initial_smt_object_map();
  symbol_tablet symbol_table;
  namespacet ns{symbol_table};
  exprt base_object;
  bool expected_dynamic_status;
  using rowt =
    std::pair<decltype(base_object), decltype(expected_dynamic_status)>;
  std::tie(base_object, expected_dynamic_status) = GENERATE_REF(
    rowt{from_integer(0, unsignedbv_typet{(8)}), false},
    rowt{symbol_exprt{"foo", bool_typet{}}, false},
    rowt{symbol_exprt{SYMEX_DYNAMIC_PREFIX "bar", bool_typet{}}, true},
    rowt{from_integer(42, make_type_dynamic(signedbv_typet{16})), true});
  INFO("base_object is - " + base_object.pretty(1, 0));
  track_expression_objects(address_of_exprt{base_object}, ns, object_map);
  const auto object = object_map.find(base_object);
  REQUIRE(object != object_map.end());
  REQUIRE(object->second.is_dynamic == expected_dynamic_status);
}
