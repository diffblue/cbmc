/*******************************************************************\

Module: Unit test for ssa_expr.h/ssa_expr.cpp

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

#include <testing-utils/use_catch.h>

#include <util/arith_tools.h>
#include <util/ssa_expr.h>
#include <util/symbol_table.h>

TEST_CASE("Constructor of ssa_exprt", "[unit][util][ssa_expr]")
{
  GIVEN("An expression containing member access, array access and a symbol")
  {
    const signedbv_typet int_type{32};
    const array_typet array_type{int_type, from_integer(10, int_type)};
    std::vector<struct_typet::componentt> components;
    components.emplace_back("array_field", array_type);
    const struct_typet struct_type{components};
    const symbol_exprt symbol{"sym", struct_type};
    const index_exprt index{member_exprt{symbol, components.back()},
                            from_integer(9, int_type)};

    WHEN("construct an ssa_exprt from `sym.array_field[9]`")
    {
      const ssa_exprt ssa{index};
      THEN("the ssa_exprt has identifier 'sym..array_field[[9]]'")
      {
        REQUIRE(ssa.get_identifier() == "sym..array_field[[9]]");
        REQUIRE(ssa.get_l1_object_identifier() == "sym..array_field[[9]]");
      }
      THEN("the ssa_exprt has no level set")
      {
        REQUIRE(ssa.get_level_0() == irep_idt{});
        REQUIRE(ssa.get_level_1() == irep_idt{});
        REQUIRE(ssa.get_level_2() == irep_idt{});
      }
    }
  }
}

TEST_CASE("Set level", "[unit][util][ssa_expr]")
{
  GIVEN("An SSA expression constructed from a symbol")
  {
    const signedbv_typet int_type{32};
    const symbol_exprt symbol{"sym", int_type};
    ssa_exprt ssa(symbol);

    WHEN("set_level_0")
    {
      ssa.set_level_0(1);
      REQUIRE(ssa.get_level_0() == "1");
      REQUIRE(ssa.get_level_1() == irep_idt{});
      REQUIRE(ssa.get_level_2() == irep_idt{});
      REQUIRE(ssa.get_original_expr() == symbol);
      REQUIRE(ssa.get_identifier() == "sym!1");
      REQUIRE(ssa.get_l1_object_identifier() == "sym!1");
    }

    WHEN("set_level_1")
    {
      ssa.set_level_1(3);
      REQUIRE(ssa.get_level_0() == irep_idt{});
      REQUIRE(ssa.get_level_1() == "3");
      REQUIRE(ssa.get_level_2() == irep_idt{});
      REQUIRE(ssa.get_original_expr() == symbol);
      REQUIRE(ssa.get_identifier() == "sym@3");
      REQUIRE(ssa.get_l1_object_identifier() == "sym@3");
    }

    WHEN("set_level_2")
    {
      ssa.set_level_2(7);
      REQUIRE(ssa.get_level_0() == irep_idt{});
      REQUIRE(ssa.get_level_1() == irep_idt{});
      REQUIRE(ssa.get_level_2() == "7");
      REQUIRE(ssa.get_original_expr() == symbol);
      REQUIRE(ssa.get_identifier() == "sym#7");
      REQUIRE(ssa.get_l1_object_identifier() == "sym");
    }
  }
}

TEST_CASE("Set expression", "[unit][util][ssa_expr]")
{
  GIVEN("An SSA expression constructed from a symbol")
  {
    const signedbv_typet int_type{32};
    const array_typet array_type{int_type, from_integer(10, int_type)};
    const symbol_exprt symbol{"sym", array_type};
    const index_exprt index{symbol, from_integer(9, int_type)};
    ssa_exprt ssa(symbol);
    ssa.set_level_0(1);
    ssa.set_level_1(3);
    ssa.set_level_2(7);

    WHEN("call set_expression with an index_exprt")
    {
      ssa.set_expression(index);
      THEN("Indices are preserved")
      {
        REQUIRE(ssa.get_level_0() == "1");
        REQUIRE(ssa.get_level_1() == "3");
        REQUIRE(ssa.get_level_2() == "7");
      }
      THEN("The underlying expression has been replaced")
      {
        REQUIRE(ssa.get_original_expr() == index);
      }
      THEN("The identifiers are updated")
      {
        REQUIRE(ssa.get_identifier() == "sym!1@3#7[[9]]");
        REQUIRE(ssa.get_l1_object_identifier() == "sym!1@3[[9]]");
      }
    }
  }
}

TEST_CASE("ssa_exprt::get_object_name", "[unit][util][ssa_expr]")
{
  GIVEN("An ssa_exprt constructed from a symbol")
  {
    const signedbv_typet int_type{32};
    const symbol_exprt symbol{"sym", int_type};
    const ssa_exprt ssa{symbol};

    THEN("The object name is the same as the symbol name")
    {
      REQUIRE(ssa.get_object_name() == "sym");
    }
  }

  GIVEN("An expression containing member access, array access and a symbol")
  {
    const signedbv_typet int_type{32};
    const array_typet array_type{int_type, from_integer(10, int_type)};
    std::vector<struct_typet::componentt> components;
    components.emplace_back("array_field", array_type);
    const struct_typet struct_type{components};
    const symbol_exprt symbol{"sym", struct_type};
    const index_exprt index{member_exprt{symbol, components.back()},
                            from_integer(9, int_type)};
    const ssa_exprt ssa{symbol};

    THEN("The object name is the same as the symbol")
    {
      REQUIRE(ssa.get_object_name() == "sym");
    }
  }
}

TEST_CASE("ssa_exprt::get_l1_object", "[unit][util][ssa_expr]")
{
  const signedbv_typet int_type{32};
  const array_typet array_type{int_type, from_integer(10, int_type)};

  GIVEN("An ssa_exprt obtained from a symbol")
  {
    const symbol_exprt symbol{"sym", int_type};
    ssa_exprt ssa{symbol};
    ssa.set_level_0(1);
    ssa.set_level_1(3);
    ssa.set_level_2(7);

    // Check we have constructed the desired SSA expression
    REQUIRE(ssa.get_identifier() == "sym!1@3#7");

    WHEN("get_l1_object is called on the SSA expression")
    {
      const ssa_exprt l1_object = ssa.get_l1_object();
      THEN("level 0 and level 1 are the same, l2 is removed")
      {
        REQUIRE(l1_object.get_level_0() == "1");
        REQUIRE(l1_object.get_level_1() == "3");
        REQUIRE(l1_object.get_level_2() == irep_idt{});
        REQUIRE(l1_object.get_identifier() == "sym!1@3");
      }
    }
  }

  GIVEN("An ssa_exprt containing member access, array access and a symbol")
  {
    std::vector<struct_typet::componentt> components;
    components.emplace_back("array_field", array_type);
    const struct_typet struct_type{components};
    const symbol_exprt symbol{"sym", struct_type};
    const index_exprt index{member_exprt{symbol, components.back()},
                            from_integer(9, int_type)};
    ssa_exprt ssa{index};
    ssa.set_level_0(1);
    ssa.set_level_1(3);
    ssa.set_level_2(7);

    // Check we have constructed the desired SSA expression
    REQUIRE(ssa.get_identifier() == "sym!1@3#7..array_field[[9]]");

    WHEN("get_l1_object is called on the SSA expression")
    {
      const ssa_exprt l1_object = ssa.get_l1_object();
      THEN("level 0 and level 1 are the same, l2 is removed")
      {
        REQUIRE(l1_object.get_level_0() == "1");
        REQUIRE(l1_object.get_level_1() == "3");
        REQUIRE(l1_object.get_level_2() == irep_idt{});
        REQUIRE(l1_object.get_identifier() == "sym!1@3");
      }
    }
  }

  GIVEN("An ssa_exprt with its L2 index set")
  {
    const symbol_exprt symbol{"sym", int_type};
    ssa_exprt ssa{symbol};
    ssa.set_level_2(7);

    WHEN("Its L1 object is taken")
    {
      const ssa_exprt l1_object = ssa.get_l1_object();
      THEN("It should compare equal to the base symbol")
      {
        REQUIRE(l1_object == ssa_exprt{symbol});
      }
    }
  }
}
