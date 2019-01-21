/*******************************************************************\

Module: Unit tests for value_sett

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// Unit tests for value_sett

#include <testing-utils/catch.hpp>

#include <pointer-analysis/value_set.h>
#include <util/arith_tools.h>
#include <util/byte_operators.h>

static bool object_descriptor_matches(
  const exprt &descriptor_expr, const exprt &target)
{
  if(descriptor_expr.id() != ID_object_descriptor)
    return false;
  const auto &descriptor = to_object_descriptor_expr(descriptor_expr);

  if(
    target.type().id() == ID_pointer &&
    target == null_pointer_exprt(to_pointer_type(target.type())))
  {
    return
      descriptor.object().id() == "NULL-object" &&
      descriptor.object().type() == target.type().subtype();
  }
  else
  {
    return descriptor.object() == target;
  }
}

SCENARIO(
  "value_sett", "[core][pointer-analysis][value_set]")
{
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);
  value_sett value_set;

  GIVEN("A value-set containing some structure-typed objects")
  {
    // Create struct A { A *x; A *y }

    struct_typet struct_A({{"x", pointer_typet(struct_tag_typet("A"), 64)},
                           {"y", pointer_typet(struct_tag_typet("A"), 64)}});
    struct_A.set_tag("A");

    auto &A_x = struct_A.components()[0];
    auto &A_y = struct_A.components()[1];

    A_x.set_base_name("x");
    A_x.set_pretty_name("x");

    A_y.set_base_name("y");
    A_y.set_pretty_name("y");

    type_symbolt A_symbol(struct_A);
    A_symbol.name = "A";
    A_symbol.base_name = "A";
    A_symbol.pretty_name = "A";

    symbol_table.add(A_symbol);

    // Create global symbols struct A a1, a2, a3;

    symbolt a1_symbol;
    a1_symbol.name = "a1";
    a1_symbol.base_name = "a1";
    a1_symbol.pretty_name = "a1";
    a1_symbol.type = struct_tag_typet(A_symbol.name);
    a1_symbol.is_static_lifetime = true;
    symbol_table.add(a1_symbol);

    symbolt a2_symbol;
    a2_symbol.name = "a2";
    a2_symbol.base_name = "a2";
    a2_symbol.pretty_name = "a2";
    a2_symbol.type = struct_tag_typet(A_symbol.name);
    a2_symbol.is_static_lifetime = true;
    symbol_table.add(a2_symbol);

    symbolt a3_symbol;
    a3_symbol.name = "a3";
    a3_symbol.base_name = "a3";
    a3_symbol.pretty_name = "a3";
    a3_symbol.type = struct_tag_typet(A_symbol.name);
    a3_symbol.is_static_lifetime = true;
    symbol_table.add(a3_symbol);

    // Assign a1.x = &a2; a1.y = &a3:

    member_exprt a1_x(a1_symbol.symbol_expr(), A_x);
    member_exprt a1_y(a1_symbol.symbol_expr(), A_y);

    code_assignt assign_x(a1_x, address_of_exprt(a2_symbol.symbol_expr()));
    code_assignt assign_y(a1_y, address_of_exprt(a3_symbol.symbol_expr()));

    value_set.apply_code(assign_x, ns);
    value_set.apply_code(assign_y, ns);

    null_pointer_exprt null_A_ptr(to_pointer_type(a1_x.type()));

    WHEN("We query what a1.x points to")
    {
      std::list<exprt> a1_x_result;
      value_set.get_value_set(a1_x, a1_x_result, ns);

      THEN("It should point to 'a2'")
      {
        REQUIRE(a1_x_result.size() == 1);
        const exprt &result = *a1_x_result.begin();
        REQUIRE(object_descriptor_matches(result, a2_symbol.symbol_expr()));
      }
    }

    WHEN("We query what a1.y points to")
    {
      std::list<exprt> a1_y_result;
      value_set.get_value_set(a1_y, a1_y_result, ns);

      THEN("It should point to 'a3'")
      {
        REQUIRE(a1_y_result.size() == 1);
        const exprt &result = *a1_y_result.begin();
        REQUIRE(object_descriptor_matches(result, a3_symbol.symbol_expr()));
      }
    }

    WHEN("We query what (a1 WITH x = NULL).x points to")
    {
      with_exprt a1_with(
        a1_symbol.symbol_expr(), member_exprt(nil_exprt(), A_x), null_A_ptr);

      member_exprt member_of_with(a1_with, A_x);

      std::list<exprt> matching_with_result;
      value_set.get_value_set(member_of_with, matching_with_result, ns);

      THEN("It should be NULL")
      {
        REQUIRE(matching_with_result.size() == 1);
        const exprt &result = *matching_with_result.begin();
        REQUIRE(object_descriptor_matches(result, null_A_ptr));
      }
    }

    WHEN("We query what (a1 WITH x = NULL).y points to")
    {
      with_exprt a1_with(
        a1_symbol.symbol_expr(), member_exprt(nil_exprt(), A_x), null_A_ptr);

      member_exprt member_of_with(a1_with, A_y);

      std::list<exprt> non_matching_with_result;
      value_set.get_value_set(member_of_with, non_matching_with_result, ns);

      THEN("It should point to 'a3'")
      {
        REQUIRE(non_matching_with_result.size() == 1);
        const exprt &result = *non_matching_with_result.begin();
        REQUIRE(object_descriptor_matches(result, a3_symbol.symbol_expr()));
      }
    }

    WHEN("We query what (a1 WITH x = NULL) points to")
    {
      with_exprt a1_with(
        a1_symbol.symbol_expr(), member_exprt(nil_exprt(), A_x), null_A_ptr);

      std::list<exprt> maybe_matching_with_result;
      value_set.get_value_set(a1_with, maybe_matching_with_result, ns);

      THEN("It may point to NULL")
      {
        bool found = false;
        for(const exprt &e : maybe_matching_with_result)
        {
          if(object_descriptor_matches(e, a1_with.new_value()))
            found = true;
        }

        REQUIRE(found);
      }

      THEN("It may point to 'a2'")
      {
        // This happens because no entry for the whole struct is recorded, so
        // value_sett tries looking up the struct's first component.

        bool found = false;
        for(const exprt &e : maybe_matching_with_result)
        {
          if(object_descriptor_matches(e, a2_symbol.symbol_expr()))
            found = true;
        }

        REQUIRE(found);
      }
    }

    WHEN("We query what '{ .x = &a2, .y = &a3 }.x' points to")
    {
      struct_exprt struct_constant(
        {address_of_exprt(a2_symbol.symbol_expr()),
         address_of_exprt(a3_symbol.symbol_expr())},
        struct_tag_typet(A_symbol.name));

      member_exprt member_of_constant(struct_constant, A_x);

      std::list<exprt> member_of_constant_result;
      value_set.get_value_set(
        member_of_constant, member_of_constant_result, ns);

      THEN("It should point to 'a2'")
      {
        REQUIRE(member_of_constant_result.size() == 1);
        const exprt &result = *member_of_constant_result.begin();
        REQUIRE(object_descriptor_matches(result, a2_symbol.symbol_expr()));
      }
    }
  }

  GIVEN("Some global integer symbols")
  {
    // Make some global integers i1, i2, i3:
    signedbv_typet int32_type(32);
    pointer_typet int32_ptr(int32_type, 64);

    symbolt i1;
    i1.name = "i1";
    i1.base_name = "i1";
    i1.pretty_name = "i1";
    i1.type = int32_type;
    i1.is_static_lifetime = true;
    symbol_table.add(i1);

    symbolt i2;
    i2.name = "i2";
    i2.base_name = "i2";
    i2.pretty_name = "i2";
    i2.type = int32_type;
    i2.is_static_lifetime = true;
    symbol_table.add(i2);

    symbolt i3;
    i3.name = "i3";
    i3.base_name = "i3";
    i3.pretty_name = "i3";
    i3.type = int32_type;
    i3.is_static_lifetime = true;
    symbol_table.add(i3);

    WHEN("We query { &i1, &i2 }[i3]")
    {
      array_exprt arr(
        {address_of_exprt(i1.symbol_expr()),
         address_of_exprt(i2.symbol_expr())},
        array_typet(int32_ptr, from_integer(2, int32_type)));

      index_exprt index_of_arr(arr, i3.symbol_expr());

      std::list<exprt> index_of_arr_result;
      value_set.get_value_set(index_of_arr, index_of_arr_result, ns);

      THEN("We should get either &i1 or &i2, but not unknown")
      {
        REQUIRE(index_of_arr_result.size() == 2);

        bool found_i1 = false, found_i2 = false;
        for(const exprt &result : index_of_arr_result)
        {
          if(object_descriptor_matches(result, i1.symbol_expr()))
            found_i1 = true;
          else if(object_descriptor_matches(result, i2.symbol_expr()))
            found_i2 = true;
        }

        REQUIRE(found_i1);
        REQUIRE(found_i2);
      }
    }

    WHEN("We query (ARRAY_OF(&i1))[i3]")
    {
      array_of_exprt arr(
        address_of_exprt(i1.symbol_expr()),
        array_typet(int32_ptr, from_integer(2, int32_type)));

      index_exprt index_of_arr(arr, i3.symbol_expr());

      std::list<exprt> index_of_arr_result;
      value_set.get_value_set(index_of_arr, index_of_arr_result, ns);

      THEN("We should get &i1")
      {
        REQUIRE(index_of_arr_result.size() == 1);
        REQUIRE(
          object_descriptor_matches(
            *index_of_arr_result.begin(), i1.symbol_expr()));
      }
    }
  }
}
