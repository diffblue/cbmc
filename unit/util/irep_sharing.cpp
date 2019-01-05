/// Author: Diffblue Ltd.

/// \file Tests that irep sharing works correctly

#include <testing-utils/catch.hpp>
#include <util/irep.h>

#ifdef SHARING

SCENARIO("irept_sharing_trade_offs", "[!mayfail][core][utils][irept]")
{
  GIVEN("An irept created with move_to_sub")
  {
    irept test_irep(ID_1);
    irept test_subirep(ID_1);
    irept test_subsubirep(ID_1);
    test_subirep.move_to_sub(test_subsubirep);
    test_irep.move_to_sub(test_subirep);
    THEN("Calling read() on a copy should return object with the same address")
    {
      irept irep = test_irep;
      REQUIRE(&irep.read() == &test_irep.read());
    }
    THEN("Changing subs in the original using a reference taken before "
      "copying should not change them in the copy")
    {
      irept &sub = test_irep.get_sub()[0];
      irept irep = test_irep;
      sub.id(ID_0);
      REQUIRE(test_irep.get_sub()[0].id() == ID_0);
      REQUIRE(irep.get_sub()[0].id() == ID_1);
    }
    THEN("Holding a reference to a sub should not prevent sharing")
    {
      irept &sub = test_irep.get_sub()[0];
      irept irep = test_irep;
      REQUIRE(&irep.read() == &test_irep.read());
      sub = irept(ID_0);
      REQUIRE(irep.get_sub()[0].id() == test_irep.get_sub()[0].id());
    }
  }
}

SCENARIO("irept_sharing", "[core][utils][irept]")
{
  GIVEN("An irept created with move_to_sub")
  {
    irept test_irep(ID_1);
    irept test_subirep(ID_1);
    irept test_subsubirep(ID_1);
    test_subirep.move_to_sub(test_subsubirep);
    test_irep.move_to_sub(test_subirep);
    THEN("Copies of a copy should return object with the same address")
    {
      irept irep1 = test_irep;
      irept irep2 = irep1;
      REQUIRE(&irep1.read() == &irep2.read());
    }
    THEN("Changing subs in the original should not change them in a copy")
    {
      irept irep = test_irep;
      test_irep.get_sub()[0].id(ID_0);
      REQUIRE(irep.get_sub()[0].id() == ID_1);
    }
    THEN("Changing subs in a copy should not change them in the original")
    {
      irept irep = test_irep;
      irep.get_sub()[0].id(ID_0);
      REQUIRE(test_irep.get_sub()[0].id() == ID_1);
      REQUIRE(irep.get_sub()[0].id() == ID_0);
    }
    THEN("Getting a reference to a sub in a copy should break sharing")
    {
      irept irep = test_irep;
      irept &sub = irep.get_sub()[0];
      REQUIRE(&irep.read() != &test_irep.read());
      sub = irept(ID_0);
      REQUIRE(irep.get_sub()[0].id() != test_irep.get_sub()[0].id());
    }
    THEN(
      "Getting a reference to a sub in the original should break sharing")
    {
      irept irep = test_irep;
      irept &sub = test_irep.get_sub()[0];
      REQUIRE(&irep.read() != &test_irep.read());
      sub = irept(ID_0);
      REQUIRE(irep.get_sub()[0].id() != test_irep.get_sub()[0].id());
    }
    THEN("Changing an id in the original should break sharing")
    {
      irept irep = test_irep;
      test_irep.id(ID_0);
      REQUIRE(&irep.read() != &test_irep.read());
      REQUIRE(irep.id() != test_irep.id());
    }
    // the following would be desirable for irept to be safe, but we know it
    // presently does not hold; see #1855 for a proposed solution
    // THEN("Holding a reference to an operand should prevent sharing")
    // {
    //   irept &operand = test_irep.get_sub()[0];
    //   irept irep = test_irep;
    //   REQUIRE(&irep.read() != &test_irep.read());
    //   operand = irept(ID_0);
    //   REQUIRE(irep.get_sub()[0].id() != test_irep.get_sub()[0].id());
    // }
    THEN("Changing an id should not prevent sharing")
    {
      test_irep.id(ID_0);
      irept irep = test_irep;
      REQUIRE(&irep.read() == &test_irep.read());
    }
  }
}

#include <util/expr.h>

SCENARIO("exprt_sharing_trade_offs", "[!mayfail][core][utils][exprt]")
{
  GIVEN("An expression created with add_to_operands(std::move(...))")
  {
    exprt test_expr(ID_1);
    exprt test_subexpr(ID_1);
    exprt test_subsubexpr(ID_1);
    test_subexpr.add_to_operands(std::move(test_subsubexpr));
    test_expr.add_to_operands(std::move(test_subexpr));
    THEN("Calling read() on a copy should return object with the same address")
    {
      exprt expr = test_expr;
      REQUIRE(&expr.read() == &test_expr.read());
    }
    THEN("Changing operands in the original using a reference taken before "
      "copying should not change them in the copy")
    {
      exprt &operand = test_expr.op0();
      exprt expr = test_expr;
      operand.id(ID_0);
      REQUIRE(test_expr.op0().id() == ID_0);
      REQUIRE(expr.op0().id() == ID_1);
    }
    THEN("Holding a reference to an operand should not prevent sharing")
    {
      exprt &operand = test_expr.op0();
      exprt expr = test_expr;
      REQUIRE(&expr.read() == &test_expr.read());
      operand = exprt(ID_0);
      REQUIRE(expr.op0().id() == test_expr.op0().id());
    }
  }
}

SCENARIO("exprt_sharing", "[core][utils][exprt]")
{
  GIVEN("An expression created with add_to_operands(std::move(...))")
  {
    exprt test_expr(ID_1);
    exprt test_subexpr(ID_1);
    exprt test_subsubexpr(ID_1);
    test_subexpr.add_to_operands(std::move(test_subsubexpr));
    test_expr.add_to_operands(std::move(test_subexpr));
    THEN("Copies of a copy should return object with the same address")
    {
      exprt expr1 = test_expr;
      exprt expr2 = expr1;
      REQUIRE(&expr1.read() == &expr2.read());
    }
    THEN("Changing operands in the original should not change them in a copy")
    {
      exprt expr = test_expr;
      test_expr.op0().id(ID_0);
      REQUIRE(expr.op0().id() == ID_1);
    }
    THEN("Changing operands in a copy should not change them in the original")
    {
      exprt expr = test_expr;
      expr.op0().id(ID_0);
      REQUIRE(test_expr.op0().id() == ID_1);
      REQUIRE(expr.op0().id() == ID_0);
    }
    THEN("Getting a reference to an operand in a copy should break sharing")
    {
      exprt expr = test_expr;
      exprt &operand = expr.op0();
      REQUIRE(&expr.read() != &test_expr.read());
      operand = exprt(ID_0);
      REQUIRE(expr.op0().id() != test_expr.op0().id());
    }
    THEN(
      "Getting a reference to an operand in the original should break sharing")
    {
      exprt expr = test_expr;
      exprt &operand = test_expr.op0();
      REQUIRE(&expr.read() != &test_expr.read());
      operand = exprt(ID_0);
      REQUIRE(expr.op0().id() != test_expr.op0().id());
    }
    THEN("Changing an id in the original should break sharing")
    {
      exprt expr = test_expr;
      test_expr.id(ID_0);
      REQUIRE(&expr.read() != &test_expr.read());
      REQUIRE(expr.id() != test_expr.id());
    }
    // the following would be desirable for irept to be safe, but we know it
    // presently does not hold; see #1855 for a proposed solution
    // THEN("Holding a reference to an operand should prevent sharing")
    // {
    //   exprt &operand = test_expr.op0();
    //   exprt expr = test_expr;
    //   REQUIRE(&expr.read() != &test_expr.read());
    //   operand = exprt(ID_0);
    //   REQUIRE(expr.op0().id() != test_expr.op0().id());
    // }
    THEN("Changing an id should not prevent sharing")
    {
      test_expr.id(ID_0);
      exprt expr = test_expr;
      REQUIRE(&expr.read() == &test_expr.read());
    }
  }
}

#endif
