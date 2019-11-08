/*******************************************************************\

Module: Unit tests of expr_dynamic_cast

Author: Nathan Phillips <Nathan.Phillips@diffblue.com>

\*******************************************************************/

/// \file
/// expr_dynamic_cast Unit Tests

#include <testing-utils/use_catch.h>

#include <util/byte_operators.h>
#include <util/mathematical_expr.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/std_types.h>

SCENARIO("expr_dynamic_cast",
  "[core][utils][expr_cast][expr_dynamic_cast]")
{
  symbol_exprt symbol_expr("dummy", empty_typet());

  GIVEN("A const exprt reference to a symbolt")
  {
    const exprt &expr=symbol_expr;

    // Check pointer overload is used, when casting from reference.
    static_assert(
      std::is_same<
        decltype(expr_try_dynamic_cast<symbol_exprt>(expr)),
        const symbol_exprt *>::value,
      "expr_try_dynamic_cast on a reference parameter must return a pointer.");

    THEN("Try-casting from exprt reference to symbol_exprt pointer "
         "returns a value")
    {
      REQUIRE(expr_try_dynamic_cast<symbol_exprt>(expr)!=nullptr);
    }

    THEN("Casting from exprt pointer to transt pointer doesn't return a value")
    {
      REQUIRE(expr_try_dynamic_cast<transt>(expr)==nullptr);
    }
  }
  GIVEN("A exprt reference to a symbolt")
  {
    exprt &expr=symbol_expr;

    THEN("Casting from exprt reference to symbol_exprt reference "
         "returns a value")
    {
      REQUIRE(expr_try_dynamic_cast<symbol_exprt>(expr)!=nullptr);
    }

    THEN("Casting from exprt reference to transt reference "
         "doesn't return a value")
    {
      REQUIRE(expr_try_dynamic_cast<transt>(expr)==nullptr);
    }
  }
  GIVEN("A const exprt reference to a symbolt")
  {
    const exprt &expr_ref=symbol_expr;

    THEN(
      "Casting from exprt reference to symbol_exprt reference should not throw")
    {
      REQUIRE_NOTHROW(expr_dynamic_cast<symbol_exprt>(expr_ref));
    }

    THEN("Casting from exprt reference to transt reference should throw")
    {
      // This no longer throws exceptions when our custom asserts are set to
      //  abort the program
      // REQUIRE_THROWS_AS(
      //   expr_dynamic_cast<transt>(expr_ref),
      //   std::bad_cast);
    }
  }
  GIVEN("A exprt reference to a symbolt")
  {
    exprt &expr_ref=symbol_expr;

    THEN(
      "Casting from exprt reference to symbol_exprt reference should not throw")
    {
      REQUIRE_NOTHROW(expr_dynamic_cast<symbol_exprt>(expr_ref));
    }

    THEN("Casting from exprt reference to transt reference should throw")
    {
      // This no longer throws exceptions when our custom asserts are set to
      //  abort the program
      // REQUIRE_THROWS_AS(
      //   expr_dynamic_cast<transt>(expr_ref),
      //   std::bad_cast);
    }

    THEN(
      "Casting from non-const exprt reference to const symbol_exprt reference "
      "should be fine")
    {
      REQUIRE_NOTHROW(expr_dynamic_cast<symbol_exprt>(expr_ref));
    }
  }
  GIVEN("An exprt value upcast from a symbolt")
  {
    exprt expr = symbol_exprt::typeless(irep_idt());

    THEN(
      "Trying casting from an exprt lvalue to a symbol_exprt should yield a "
      "non null pointer.")
    {
      symbol_exprt *result = expr_try_dynamic_cast<symbol_exprt>(expr);
      REQUIRE(result != nullptr);
    }

    THEN(
      "Trying casting from an exprt lvalue to a transt should yield a null "
      "pointer.")
    {
      transt *result = expr_try_dynamic_cast<transt>(expr);
      REQUIRE(result == nullptr);
    }

    THEN(
      "Trying casting from an exprt rvalue reference to a symbol_exprt should "
      "yield a non empty optional.")
    {
      optionalt<symbol_exprt> result =
        expr_try_dynamic_cast<symbol_exprt>(std::move(expr));
      REQUIRE(result.has_value());
    }

    THEN(
      "Trying casting from an exprt rvalue reference to a transt should yield "
      "a empty optional.")
    {
      optionalt<transt> result = expr_try_dynamic_cast<transt>(std::move(expr));
      REQUIRE_FALSE(result.has_value());
    }
  }

  GIVEN("A byte extract expression with little endianness")
  {
    auto byte = byte_extract_exprt(
      ID_byte_extract_little_endian,
      symbol_exprt(typet()),
      constant_exprt("0", typet()),
      typet());
    THEN("try_expr_dynamic_cast<byte_extract_expr> returns non-empty")
    {
      REQUIRE(expr_try_dynamic_cast<byte_extract_exprt>(byte));
    }
  }
  GIVEN("A byte extract expression with big endianness")
  {
    auto byte = byte_extract_exprt(
      ID_byte_extract_big_endian,
      symbol_exprt(typet()),
      constant_exprt("0", typet()),
      typet());
    THEN("try_expr_dynamic_cast<byte_extract_expr> returns non-empty")
    {
      REQUIRE(expr_try_dynamic_cast<byte_extract_exprt>(byte));
    }
  }
  GIVEN("An expression that is not a byte extract")
  {
    const exprt expr = exprt();
    THEN("try_expr_dynamic_cast<byte_extract_expr> returns empty")
    {
      REQUIRE_FALSE(expr_try_dynamic_cast<byte_extract_exprt>(expr));
    }
  }
}

SCENARIO("can_cast_expr", "[core][utils][expr_cast][can_cast_expr]")
{
  GIVEN("A byte extract expression with little endianness")
  {
    auto byte = byte_extract_exprt(
      ID_byte_extract_little_endian,
      symbol_exprt(typet()),
      constant_exprt("0", typet()),
      typet());
    THEN("can_expr_expr<byte_extract_expr> returns true")
    {
      REQUIRE(can_cast_expr<byte_extract_exprt>(byte));
    }
  }
  GIVEN("A byte extract expression with big endianness")
  {
    auto byte = byte_extract_exprt(
      ID_byte_extract_big_endian,
      symbol_exprt(typet()),
      constant_exprt("0", typet()),
      typet());
    THEN("can_expr_expr<byte_extract_expr> returns true")
    {
      REQUIRE(can_cast_expr<byte_extract_exprt>(byte));
    }
  }
  GIVEN("An expression that is not a byte extract")
  {
    const exprt expr = exprt();
    THEN("can_expr_expr<byte_extract_expr> returns false")
    {
      REQUIRE_FALSE(can_cast_expr<byte_extract_exprt>(expr));
    }
  }
}

SCENARIO("type_dynamic_cast", "[core][utils][expr_cast][type_dynamic_cast]")
{
  string_typet string_type;
  GIVEN("A typet value upcast from a string_typet")
  {
    typet type = string_type;

    THEN(
      "Trying casting from a typet lvalue to a string_typet should yield a non "
      "null pointer.")
    {
      string_typet *result = type_try_dynamic_cast<string_typet>(type);
      REQUIRE(result != nullptr);
    }

    THEN(
      "Trying casting from a typet lvalue to a struct_typet should yield a "
      "null pointer.")
    {
      struct_typet *result = type_try_dynamic_cast<struct_typet>(type);
      REQUIRE(result == nullptr);
    }

    THEN(
      "Trying casting from a typet rvalue reference to a symbol_exprt should "
      "yield a non empty optional.")
    {
      optionalt<string_typet> result =
        type_try_dynamic_cast<string_typet>(std::move(type));
      REQUIRE(result.has_value());
    }

    THEN(
      "Trying casting from a typet rvalue reference to a struct_typet should "
      "yield a empty optional.")
    {
      optionalt<struct_typet> result =
        type_try_dynamic_cast<struct_typet>(std::move(type));
      REQUIRE_FALSE(result.has_value());
    }
  }
  GIVEN("A const typet reference upcast from a string_typet")
  {
    const typet &type = string_type;

    THEN(
      "Trying casting from a const reference to a string_typet should yield a "
      "non null pointer to const.")
    {
      const string_typet *result = type_try_dynamic_cast<string_typet>(type);
      REQUIRE(result != nullptr);
    }

    THEN(
      "Trying casting from a const reference to a struct_typet should yield a "
      "null pointer to const.")
    {
      const struct_typet *result = type_try_dynamic_cast<struct_typet>(type);
      REQUIRE(result == nullptr);
    }
  }
  GIVEN("A typet reference upcast from a string_typet")
  {
    typet &type = string_type;

    THEN(
      "Trying casting from a reference to a string_typet should yield a non "
      "null pointer.")
    {
      string_typet *result = type_try_dynamic_cast<string_typet>(type);
      REQUIRE(result != nullptr);
    }

    THEN(
      "Trying casting from a reference to a struct_typet should yield a null "
      "pointer.")
    {
      struct_typet *result = type_try_dynamic_cast<struct_typet>(type);
      REQUIRE(result == nullptr);
    }
  }
}
