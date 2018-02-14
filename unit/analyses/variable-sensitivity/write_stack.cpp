/*******************************************************************\

 Module: Write Stack Unit Tests

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

/// \file
/// Unit tests for construction of write stack

#include <testing-utils/catch.hpp>

#include <stack>
#include <iostream>

#include <util/config.h>
#include <util/symbol.h>
#include <util/symbol_table.h>
#include <util/namespace.h>
#include <util/std_expr.h>
#include <util/std_code.h>
#include <util/ui_message.h>
#include <ansi-c/ansi_c_language.h>
#include <ansi-c/expr2c.h>
#include <analyses/variable-sensitivity/write_stack_entry.h>
#include <analyses/variable-sensitivity/write_stack.h>
#include <analyses/variable-sensitivity/abstract_enviroment.h>
#include <analyses/variable-sensitivity/variable_sensitivity_object_factory.h>

#if 0
#include <src/expr/require_expr.h>
#include <src/ansi-c/c_to_expr.h>


SCENARIO("Constructing write stacks",
  "[core][analyses][variable-sensitivity][continuation-stack]")
{
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  optionst options;
  options.set_option("pointers", true);
  options.set_option("arrays", true);
  options.set_option("structs", true);
  variable_sensitivity_object_factoryt::instance().set_options(options);

  config.set_arch("none");

  abstract_environmentt environment;
  environment.make_top();

  c_to_exprt to_expr;

  GIVEN("A int x")
  {
    typet basic_symbol_type=signedbv_typet(32);
    symbol_table.add(
      auxiliary_symbolt("x", basic_symbol_type));

    WHEN("Constructing from &x")
    {
      exprt in_expr=to_expr("&x", ns);
      CAPTURE(expr2c(in_expr, ns));

      THEN("The constructed stack should be &x")
      {
        auto stack=write_stackt(in_expr, environment, ns);
        REQUIRE_FALSE(stack.is_top_value());
        const exprt &out_expr=stack.to_expression();

        CAPTURE(expr2c(out_expr, ns));

        REQUIRE(out_expr.id()==ID_address_of);
        const exprt &object=out_expr.op0();
        require_exprt::require_symbol(object, "x");
      }
    }
  }
  GIVEN("A int a[5]")
  {
    typet array_type=
      array_typet(signedbv_typet(32), constant_exprt::integer_constant(5));
    symbol_table.add(auxiliary_symbolt("a", array_type));

    WHEN("Constructing from a")
    {
      exprt in_expr=to_expr("a", ns);
      THEN("The constructed stack should be &a[0]")
      {
        auto stack=write_stackt(in_expr, environment, ns);
        REQUIRE_FALSE(stack.is_top_value());
        const exprt &out_expr=stack.to_expression();

        CAPTURE(expr2c(out_expr, ns));

        REQUIRE(out_expr.id()==ID_address_of);
        const index_exprt &index_expr=
          require_exprt::require_index(out_expr.op0(), 0);
        require_exprt::require_symbol(index_expr.array(), "a");
      }
    }
    WHEN("Constructing from &a")
    {
      exprt in_expr=to_expr("&a", ns);

      THEN("The constructed stack should be &a")
      {
        auto stack=write_stackt(in_expr, environment, ns);
        REQUIRE_FALSE(stack.is_top_value());
        const exprt &out_expr=stack.to_expression();

        CAPTURE(expr2c(out_expr, ns));

        // TODO: make consistent with above
        REQUIRE(out_expr.id()==ID_address_of);
        require_exprt::require_symbol(out_expr.op0(), "a");
      }
    }
    WHEN("Constructing from &a[0]")
    {
      exprt in_expr=to_expr("&a[0]", ns);

      CAPTURE(expr2c(in_expr, ns));
      THEN("The constructed stack should be &a[0]")
      {
        auto stack=write_stackt(in_expr, environment, ns);
        REQUIRE_FALSE(stack.is_top_value());
        const exprt &out_expr=stack.to_expression();

        CAPTURE(expr2c(out_expr, ns));

        REQUIRE(out_expr.id()==ID_address_of);
        const exprt &object=out_expr.op0();
        const index_exprt &index_expr=
          require_exprt::require_index(object, 0);
        require_exprt::require_symbol(index_expr.array(), "a");
      }
    }
    WHEN("Constructing from &a[1]")
    {
      exprt in_expr=to_expr("&a[1]", ns);

      CAPTURE(expr2c(in_expr, ns));
      THEN("The constructed stack should be &a[1]")
      {
        auto stack=write_stackt(in_expr, environment, ns);
        REQUIRE_FALSE(stack.is_top_value());
        const exprt &out_expr=stack.to_expression();

        CAPTURE(expr2c(out_expr, ns));

        REQUIRE(out_expr.id()==ID_address_of);
        const index_exprt &index_expr=
          require_exprt::require_index(out_expr.op0(), 1);
        require_exprt::require_symbol(index_expr.array(), "a");
      }
    }
    WHEN("Constructing from &a[0]+1")
    {
      exprt in_expr=to_expr("&a[0]+1", ns);

      CAPTURE(expr2c(in_expr, ns));
      THEN("The constructed stack should be &a[1]")
      {
        auto stack=write_stackt(in_expr, environment, ns);
        REQUIRE_FALSE(stack.is_top_value());
        const exprt &out_expr=stack.to_expression();

        CAPTURE(expr2c(out_expr, ns));

        REQUIRE(out_expr.id()==ID_address_of);
        const index_exprt &index_expr=
          require_exprt::require_index(out_expr.op0(), 1);
        require_exprt::require_symbol(index_expr.array(), "a");
      }
    }
    WHEN("Constructing from &a[1]+1")
    {
      exprt in_expr=to_expr("&a[1]+1", ns);

      CAPTURE(expr2c(in_expr, ns));

      THEN("The constructed stack should be &a[2]")
      {
        auto stack=write_stackt(in_expr, environment, ns);
        REQUIRE_FALSE(stack.is_top_value());
        const exprt &out_expr=stack.to_expression();

        CAPTURE(expr2c(out_expr, ns));

        REQUIRE(out_expr.id()==ID_address_of);
        const index_exprt &index_expr=
          require_exprt::require_index(out_expr.op0(), 2);
        require_exprt::require_symbol(index_expr.array(), "a");
      }
    }
    WHEN("Constructing from &a[1]-1")
    {
      exprt in_expr=to_expr("&a[1]-1", ns);

      CAPTURE(expr2c(in_expr, ns));

      THEN("The constructed stack should be &a[0]")
      {
        auto stack=write_stackt(in_expr, environment, ns);
        REQUIRE_FALSE(stack.is_top_value());
        const exprt &out_expr=stack.to_expression();

        CAPTURE(expr2c(out_expr, ns));

        REQUIRE(out_expr.id()==ID_address_of);
        const index_exprt &index_expr=
          require_exprt::require_index(out_expr.op0(), 0);
        require_exprt::require_symbol(index_expr.array(), "a");
      }
    }
    WHEN("Constructing from 1+&a[1]")
    {
      exprt in_expr=to_expr("1+&a[1]", ns);

      CAPTURE(expr2c(in_expr, ns));

      THEN("The constructed stack should be &a[2]")
      {
        auto stack=write_stackt(in_expr, environment, ns);
        REQUIRE_FALSE(stack.is_top_value());
        const exprt &out_expr=stack.to_expression();

        CAPTURE(expr2c(out_expr, ns));

        REQUIRE(out_expr.id()==ID_address_of);
        const index_exprt &index_expr=
          require_exprt::require_index(out_expr.op0(), 2);
        require_exprt::require_symbol(index_expr.array(), "a");
      }
    }
    GIVEN("A symbol int x")
    {
      typet basic_symbol_type=signedbv_typet(32);
      symbolt basic_symbol=
        auxiliary_symbolt("x", basic_symbol_type);
      symbol_table.add(basic_symbol);

      WHEN("Constructing from &a[x] (x top)")
      {
        exprt in_expr=to_expr("&a[x]", ns);

        CAPTURE(expr2c(in_expr, ns));
        THEN("The constructed stack should be &a[TOP]")
        {
          auto stack=write_stackt(in_expr, environment, ns);
          REQUIRE_FALSE(stack.is_top_value());
          const exprt &out_expr=stack.to_expression();

          CAPTURE(expr2c(out_expr, ns));

          REQUIRE(out_expr.id()==ID_address_of);
          const index_exprt &index_expr=
            require_exprt::require_top_index(out_expr.op0());
          require_exprt::require_symbol(index_expr.array(), "a");
        }
      }
      WHEN("Constructing from &a[x] (x known to be 2")
      {
        // Create an abstract_object_pointer representing 2
        abstract_object_pointert x_value=
          environment.abstract_object_factory(
            basic_symbol_type,
            to_expr("2", ns),
            ns);
        environment.assign(basic_symbol.symbol_expr(), x_value, ns);

        exprt in_expr=to_expr("&a[x]", ns);

        CAPTURE(expr2c(in_expr, ns));
        THEN("The constructed stack should be &a[2]")
        {
          auto stack=write_stackt(in_expr, environment, ns);
          REQUIRE_FALSE(stack.is_top_value());
          const exprt &out_expr=stack.to_expression();

          CAPTURE(expr2c(out_expr, ns));

          REQUIRE(out_expr.id()==ID_address_of);
          const index_exprt &index_expr=
            require_exprt::require_index(out_expr.op0(), 2);
          require_exprt::require_symbol(index_expr.array(), "a");
        }
      }
    }
  }

  GIVEN("A struct str{ int comp, int comp2 }")
  {
    struct_union_typet::componentt component("comp", signedbv_typet(32));
    struct_union_typet::componentt component2("comp2", signedbv_typet(32));
    struct_typet struct_type;
    struct_type.set_tag("str");
    struct_type.components().push_back(component);
    struct_type.components().push_back(component2);

    symbolt struct_symbol;
    struct_symbol.base_name="str";
    struct_symbol.name="tag-str";
    struct_symbol.type=struct_type;
    struct_symbol.is_type=true;

    symbol_table.add(struct_symbol);

    GIVEN("A struct str s")
    {
      symbol_table.add(
        auxiliary_symbolt("s", struct_type));

      WHEN("Constructing from &s.comp")
      {
        exprt in_expr=to_expr("&s.comp", ns);
        CAPTURE(expr2c(in_expr, ns));

        THEN("The constructed stack should be &s.comp")
        {
          auto stack=write_stackt(in_expr, environment, ns);
          REQUIRE_FALSE(stack.is_top_value());
          const exprt &out_expr=stack.to_expression();

          CAPTURE(expr2c(out_expr, ns));

          REQUIRE(out_expr.id()==ID_address_of);
          const member_exprt &member_exrp=
            require_exprt::require_member(out_expr.op0(), "comp");
          // TODO: verify member expr
          require_exprt::require_symbol(member_exrp.compound(), "s");
        }
      }
      WHEN("Constructing from &s.comp2")
      {
        exprt in_expr=to_expr("&s.comp2", ns);
        CAPTURE(expr2c(in_expr, ns));

        THEN("The constructed stack should be &s.comp2")
        {
          auto stack=write_stackt(in_expr, environment, ns);
          REQUIRE_FALSE(stack.is_top_value());
          const exprt &out_expr=stack.to_expression();

          CAPTURE(expr2c(out_expr, ns));

          REQUIRE(out_expr.id()==ID_address_of);
          const member_exprt &member_exrp=
            require_exprt::require_member(out_expr.op0(), "comp2");
          // TODO: verify member expr
          require_exprt::require_symbol(member_exrp.compound(), "s");
        }
      }
      WHEN("Constructing from &s")
      {
        exprt in_expr=to_expr("&s", ns);
        CAPTURE(expr2c(in_expr, ns));

        THEN("Then should get a write stack representing &s")
        {
          auto stack=write_stackt(in_expr, environment, ns);
          REQUIRE_FALSE(stack.is_top_value());
          const exprt &out_expr=stack.to_expression();

          CAPTURE(expr2c(out_expr, ns));

          REQUIRE(out_expr.id()==ID_address_of);
          const exprt &object=out_expr.op0();
          require_exprt::require_symbol(object, "s");
        }
      }
      WHEN("Constructing from (int *)&s")
      {
        // TODO: we could in theory analyse the struct and offset the pointer
        // but not yet
        exprt in_expr=to_expr("(int *)&s", ns);
        CAPTURE(expr2c(in_expr, ns));

        THEN("Then should get a top stack")
        {
          auto stack=write_stackt(in_expr, environment, ns);
          REQUIRE(stack.is_top_value());
        }
      }
      WHEN("Constructing from &s.comp + 1")
      {
        // TODO: we could in theory analyse the struct and offset the pointer
        // but not yet
        exprt in_expr=to_expr("&s.comp + 1", ns);
        CAPTURE(expr2c(in_expr, ns));

        THEN("Then should get a top stack")
        {
          auto stack=write_stackt(in_expr, environment, ns);
          REQUIRE(stack.is_top_value());
        }
      }
    }
    GIVEN("struct str arr_s[5]")
    {
      typet array_type=
        array_typet(struct_type, constant_exprt::integer_constant(5));
      symbol_table.add(
        auxiliary_symbolt("arr_s", array_type));

      WHEN("&arr_s[1].comp")
      {
        exprt in_expr=to_expr("&arr_s[1].comp", ns);
        CAPTURE(expr2c(in_expr, ns));

        THEN("The constructed stack should be &arr_s[1].comp")
        {
          auto stack=write_stackt(in_expr, environment, ns);
          REQUIRE_FALSE(stack.is_top_value());
          const exprt &out_expr=stack.to_expression();

          CAPTURE(expr2c(out_expr, ns));

          REQUIRE(out_expr.id()==ID_address_of);

          const member_exprt &member_expr=
            require_exprt::require_member(out_expr.op0(), "comp");
          const index_exprt &index_expr=
            require_exprt::require_index(member_expr.compound(), 1);

          require_exprt::require_symbol(index_expr.array(), "arr_s");
        }
      }
      WHEN("&arr_s[1]")
      {
        exprt in_expr=to_expr("&arr_s[1]", ns);
        CAPTURE(expr2c(in_expr, ns));

        THEN("The constructed stack should be TOP")
        {
          auto stack=write_stackt(in_expr, environment, ns);
          REQUIRE_FALSE(stack.is_top_value());
          const exprt &out_expr=stack.to_expression();

          CAPTURE(expr2c(out_expr, ns));

          REQUIRE(out_expr.id()==ID_address_of);
          const exprt &object=out_expr.op0();
          const index_exprt &index_expr=require_exprt::require_index(object, 1);
          require_exprt::require_symbol(index_expr.array(), "arr_s");
        }
      }
      GIVEN("A symbol int x")
      {
        typet basic_symbol_type=signedbv_typet(32);
        symbol_table.add(
          auxiliary_symbolt("x", basic_symbol_type));

        WHEN("Constructing from &arr_s[x].comp (x top)")
        {
          exprt in_expr=to_expr("&arr_s[x].comp", ns);

          CAPTURE(expr2c(in_expr, ns));
          THEN("The constructed stack should be &arr_s[TOP].comp")
          {
            auto stack=write_stackt(in_expr, environment, ns);
            REQUIRE_FALSE(stack.is_top_value());
            const exprt &out_expr=stack.to_expression();

            CAPTURE(expr2c(out_expr, ns));

            REQUIRE(out_expr.id()==ID_address_of);
            const member_exprt &member_expr=
              require_exprt::require_member(out_expr.op0(), "comp");

            const index_exprt &index_expr=
              require_exprt::require_top_index(member_expr.compound());

            require_exprt::require_symbol(index_expr.array(), "arr_s");
          }
        }
      }
    }
  }
  GIVEN("A pointer to an integer int * p = &x")
  {
    // in a top environment - to construct from say (p + 1) we should always
    // return top. If the enviroment was not top, we could do better if p has an
    // offset at the top of its write_stack. Of course if it doesn't

    // int x;
    typet basic_symbol_type=signedbv_typet(32);
    symbol_table.add(
      auxiliary_symbolt("x", basic_symbol_type));

    // int * p
    typet pointer_type=pointer_typet(basic_symbol_type);
    symbolt pointer_symbol=
      auxiliary_symbolt("p", pointer_type);
    symbol_table.add(pointer_symbol);

    // Create an abstract_object_pointer representing 2
    abstract_object_pointert x_value=
      environment.abstract_object_factory(
        pointer_type,
        to_expr("&x", ns),
        ns);
    environment.assign(pointer_symbol.symbol_expr(), x_value, ns);

    WHEN("Constructing the write stack from p + 1")
    {
      exprt in_expr=to_expr("p + 1", ns);
      CAPTURE(expr2c(in_expr, ns));

      THEN("The constructed stack should be TOP")
      {
        // Since we don't allow constructing a pointer to a struct yet
        auto stack=write_stackt(in_expr, environment, ns);
        REQUIRE(stack.is_top_value());
      }
    }
    WHEN("Constructing the write stack from 1 + p")
    {
      exprt in_expr=to_expr("1 + p", ns);
      CAPTURE(expr2c(in_expr, ns));

      auto stack=write_stackt(in_expr, environment, ns);

      THEN("Get a top write stack")
      {
        REQUIRE(stack.is_top_value());
      }
    }
    WHEN("Constructing the write stack from p - 1")
    {
      exprt in_expr=to_expr("p - 1", ns);
      CAPTURE(expr2c(in_expr, ns));

      auto stack=write_stackt(in_expr, environment, ns);

      THEN("Get a top write stack")
      {
        REQUIRE(stack.is_top_value());
      }
    }
    WHEN("Constructing the write stack from &p[1]")
    {
      exprt in_expr=to_expr("&p[1]", ns);
      CAPTURE(expr2c(in_expr, ns));

      auto stack=write_stackt(in_expr, environment, ns);

      THEN("Get a top write stack")
      {
        REQUIRE(stack.is_top_value());
      }
    }
  }
}
#endif

