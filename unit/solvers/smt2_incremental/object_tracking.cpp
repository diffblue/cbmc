// Author: Diffblue Ltd.

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/namespace.h>
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
    REQUIRE(object_map.size() == 1);
    const exprt null_pointer = null_pointer_exprt{::pointer_type(void_type())};
    CHECK(object_map.begin()->first == null_pointer);
    CHECK(object_map.begin()->second.unique_id == 0);
    CHECK(object_map.begin()->second.base_expression == null_pointer);
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
    CHECK(object_map.size() == 4);
    const auto foo_object = object_map.find(foo);
    REQUIRE(foo_object != object_map.end());
    CHECK(foo_object->second.base_expression == foo);
    CHECK(foo_object->second.unique_id == 3);
    const auto bar_object = object_map.find(bar);
    REQUIRE(bar_object != object_map.end());
    CHECK(bar_object->second.base_expression == bar);
    CHECK(bar_object->second.unique_id == 1);
  }
  SECTION("Confirming objects are tracked.")
  {
    CHECK(objects_are_already_tracked(compound_expression, object_map));
  }
}
