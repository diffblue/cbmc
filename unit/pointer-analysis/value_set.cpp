/*******************************************************************\

Module: Unit tests for value_sett

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// Unit tests for value_sett

#include <util/arith_tools.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>
#include <util/symbol_table.h>

#include <pointer-analysis/value_set.h>
#include <testing-utils/use_catch.h>

#include <climits>

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
    return descriptor.object().id() == "NULL-object" &&
           descriptor.object().type() ==
             to_pointer_type(target.type()).base_type();
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

    struct_typet struct_A(
      {{"x", pointer_typet(struct_tag_typet("A"), sizeof(void *) * CHAR_BIT)},
       {"y", pointer_typet(struct_tag_typet("A"), sizeof(void *) * CHAR_BIT)}});
    struct_A.set_tag("A");

    auto &A_x = struct_A.components()[0];
    auto &A_y = struct_A.components()[1];

    A_x.set_base_name("x");
    A_x.set_pretty_name("x");

    A_y.set_base_name("y");
    A_y.set_pretty_name("y");

    type_symbolt A_symbol{"A", struct_A, irep_idt{}};
    A_symbol.base_name = "A";
    A_symbol.pretty_name = "A";

    symbol_table.add(A_symbol);

    // Create global symbols struct A a1, a2, a3;

    symbolt a1_symbol{"a1", struct_tag_typet(A_symbol.name), irep_idt{}};
    a1_symbol.base_name = "a1";
    a1_symbol.pretty_name = "a1";
    a1_symbol.is_static_lifetime = true;
    symbol_table.add(a1_symbol);

    symbolt a2_symbol{"a2", struct_tag_typet(A_symbol.name), irep_idt{}};
    a2_symbol.base_name = "a2";
    a2_symbol.pretty_name = "a2";
    a2_symbol.is_static_lifetime = true;
    symbol_table.add(a2_symbol);

    symbolt a3_symbol{"a3", struct_tag_typet(A_symbol.name), irep_idt{}};
    a3_symbol.base_name = "a3";
    a3_symbol.pretty_name = "a3";
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
      const std::vector<exprt> a1_x_result = value_set.get_value_set(a1_x, ns);

      THEN("It should point to 'a2'")
      {
        REQUIRE(a1_x_result.size() == 1);
        const exprt &result = *a1_x_result.begin();
        REQUIRE(object_descriptor_matches(result, a2_symbol.symbol_expr()));
      }
    }

    WHEN("We query what a1.y points to")
    {
      const std::vector<exprt> a1_y_result = value_set.get_value_set(a1_y, ns);

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
        a1_symbol.symbol_expr(), exprt{ID_member_name}, null_A_ptr);
      a1_with.where().set(ID_component_name, A_x.get_name());

      member_exprt member_of_with(a1_with, A_x);

      const std::vector<exprt> matching_with_result =
        value_set.get_value_set(member_of_with, ns);

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
        a1_symbol.symbol_expr(), exprt{ID_member_name}, null_A_ptr);
      a1_with.where().set(ID_component_name, A_x.get_name());

      member_exprt member_of_with(a1_with, A_y);

      const std::vector<exprt> non_matching_with_result =
        value_set.get_value_set(member_of_with, ns);

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
        a1_symbol.symbol_expr(), exprt{ID_member_name}, null_A_ptr);
      a1_with.where().set(ID_component_name, A_x.get_name());

      const std::vector<exprt> maybe_matching_with_result =
        value_set.get_value_set(a1_with, ns);

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

      auto member_of_constant_result = value_set.get_value_set(
        member_of_constant, ns);

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
    pointer_typet int32_ptr(int32_type, sizeof(void *) * CHAR_BIT);

    symbolt i1{"i1", int32_type, irep_idt{}};
    i1.base_name = "i1";
    i1.pretty_name = "i1";
    i1.is_static_lifetime = true;
    symbol_table.add(i1);

    symbolt i2{"i2", int32_type, irep_idt{}};
    i2.base_name = "i2";
    i2.pretty_name = "i2";
    i2.is_static_lifetime = true;
    symbol_table.add(i2);

    symbolt i3{"i3", int32_type, irep_idt{}};
    i3.base_name = "i3";
    i3.pretty_name = "i3";
    i3.is_static_lifetime = true;
    symbol_table.add(i3);

    WHEN("We query { &i1, &i2 }[i3]")
    {
      array_exprt arr(
        {address_of_exprt(i1.symbol_expr()),
         address_of_exprt(i2.symbol_expr())},
        array_typet(int32_ptr, from_integer(2, int32_type)));

      index_exprt index_of_arr(arr, i3.symbol_expr());

      const std::vector<exprt> index_of_arr_result =
        value_set.get_value_set(index_of_arr, ns);

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

      std::vector<exprt> index_of_arr_result =
        value_set.get_value_set(index_of_arr, ns);

      THEN("We should get &i1")
      {
        REQUIRE(index_of_arr_result.size() == 1);
        REQUIRE(
          object_descriptor_matches(
            *index_of_arr_result.begin(), i1.symbol_expr()));
      }
    }
  }

  GIVEN("A value-set containing pointers with offsets")
  {
    signedbv_typet int_type{sizeof(int) * CHAR_BIT};
    pointer_typet int_ptr_type{int_type, sizeof(void *) * CHAR_BIT};

    // Create struct S { int a; char b }
    struct_typet struct_S{{{"a", int_type}, {"b", unsignedbv_typet{CHAR_BIT}}}};
    struct_S.set_tag("S");

    auto &S_a = struct_S.components()[0];
    auto &S_b = struct_S.components()[1];

    S_a.set_base_name("a");
    S_a.set_pretty_name("a");

    S_b.set_base_name("b");
    S_b.set_pretty_name("b");

    type_symbolt S_symbol{"S", struct_S, irep_idt{}};
    S_symbol.base_name = "S";
    S_symbol.pretty_name = "S";

    symbol_table.add(S_symbol);

    // Create global symbols struct S s, int *p

    symbolt s_symbol{"s", struct_tag_typet{S_symbol.name}, irep_idt{}};
    s_symbol.pretty_name = "s";
    s_symbol.is_static_lifetime = true;
    symbol_table.add(s_symbol);

    symbolt p1_symbol{"p1", int_ptr_type, irep_idt{}};
    p1_symbol.pretty_name = "p1";
    p1_symbol.is_static_lifetime = true;
    symbol_table.add(p1_symbol);

    // Assign p1 = &s + s.a + s.a; (which we cannot easily create via regression
    // tests, because front-ends would turn this into binary expressions)
    member_exprt s_a(s_symbol.symbol_expr(), S_a);
    code_assignt assign_p1{
      p1_symbol.symbol_expr(),
      plus_exprt{
        {typecast_exprt{
           address_of_exprt{s_symbol.symbol_expr()}, p1_symbol.type},
         s_a,
         s_a},
        int_ptr_type}};

    value_set.apply_code(assign_p1, ns);

    WHEN("We query what p1 points to")
    {
      const std::vector<exprt> p1_result =
        value_set.get_value_set(p1_symbol.symbol_expr(), ns);

      THEN("It should point to 's'")
      {
        REQUIRE(p1_result.size() == 1);
        const exprt &result = *p1_result.begin();
        REQUIRE(object_descriptor_matches(result, s_symbol.symbol_expr()));
      }
    }

    symbolt p2_symbol{"p2", int_ptr_type, irep_idt{}};
    p2_symbol.pretty_name = "p2";
    p2_symbol.is_static_lifetime = true;
    symbol_table.add(p2_symbol);

    // Assign p2 = &s - s.a; (which the simplifier would always rewrite to &s +
    // -(s.a), so use the value_sett::assign interface to wrongly claim
    // simplification had already taken place)
    value_set.assign(
      p2_symbol.symbol_expr(),
      minus_exprt{
        typecast_exprt{
          address_of_exprt{s_symbol.symbol_expr()}, p2_symbol.type},
        s_a},
      ns,
      true,
      true);

    WHEN("We query what p2 points to")
    {
      const std::vector<exprt> p2_result =
        value_set.get_value_set(p2_symbol.symbol_expr(), ns);

      THEN("It should point to 's'")
      {
        REQUIRE(p2_result.size() == 1);
        const exprt &result = *p2_result.begin();
        REQUIRE(object_descriptor_matches(result, s_symbol.symbol_expr()));
      }
    }

    symbolt A_symbol{
      "A", array_typet{int_type, from_integer(2, int_type)}, irep_idt{}};
    A_symbol.pretty_name = "A";
    A_symbol.is_static_lifetime = true;
    symbol_table.add(A_symbol);

    symbolt p3_symbol{"p3", int_ptr_type, irep_idt{}};
    p3_symbol.pretty_name = "p3";
    p3_symbol.is_static_lifetime = true;
    symbol_table.add(p3_symbol);

    // Assign p3 = &A[1]; (which the simplifier would always rewrite to A +
    // sizeof(int), so use the value_sett::assign interface to wrongly claim
    // simplification had already taken place)
    value_set.assign(
      p3_symbol.symbol_expr(),
      address_of_exprt{
        index_exprt{A_symbol.symbol_expr(), from_integer(1, int_type)}},
      ns,
      true,
      true);

    WHEN("We query what p3 points to")
    {
      const std::vector<exprt> p3_result =
        value_set.get_value_set(p3_symbol.symbol_expr(), ns);

      THEN("It should point to 'A'")
      {
        REQUIRE(p3_result.size() == 1);
        const exprt &result = *p3_result.begin();
        REQUIRE(object_descriptor_matches(
          result,
          index_exprt{
            A_symbol.symbol_expr(),
            from_integer(0, to_array_type(A_symbol.type).index_type())}));
      }
    }
  }
}
