/*******************************************************************\

Module: Does Remove Const Unit Tests

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// Does Remove Const Unit Tests

#include <testing-utils/catch.hpp>

#include <util/std_expr.h>
#include <util/std_code.h>
#include <util/std_types.h>
#include <util/c_types.h>

#include <ansi-c/c_qualifiers.h>
#include <goto-programs/goto_program.h>
#include <analyses/does_remove_const.h>
#include <analyses/does_remove_const/does_remove_const_util.h>

SCENARIO("does_expr_lose_const",
  "[core][analyses][does_remove_const][does_expr_remove_const]")
{
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);
  goto_programt program;
  does_remove_constt does_remove_const(program, ns);
  does_remove_const_testt does_remove_const_test(does_remove_const);

  GIVEN("Const and non-const primitive and pointers to primitives")
  {
    c_qualifierst const_qualifier;
    const_qualifier.is_constant=true;

    // const int
    typet const_primitive_type=integer_typet();
    const_qualifier.write(const_primitive_type);

    // int
    typet non_const_primitive_type=integer_typet();

    // pointer (can be reassigned)
    //   to int (value can be changed)
    // int *
    typet pointer_to_int_type=pointer_type(non_const_primitive_type);

    // const pointer (can't be reassigned)
    //   to int (value can be changed)
    // int * const
    typet const_pointer_to_int_type=pointer_type(non_const_primitive_type);
    const_qualifier.write(const_pointer_to_int_type);

    // pointer (can be reassigned)
    //   to const int (value can't be changed)
    // const int *
    typet pointer_to_const_int_type=pointer_type(const_primitive_type);

    // constant pointer (can't be reassigned)
    //   to const int (value can't be changed)
    // const int * const
    typet const_pointer_to_const_int_type=pointer_type(const_primitive_type);
    const_qualifier.write(const_pointer_to_const_int_type);

    symbol_exprt const_primitive_symbol(
      "const_primitive", const_primitive_type);
    symbol_exprt non_const_primitive_symbol(
      "non_const_primitive", non_const_primitive_type);
    symbol_exprt pointer_to_int_symbol(
      "pointer_to_int", pointer_to_int_type);
    symbol_exprt const_pointer_to_int_symbol(
      "const_pointer_to_int", const_pointer_to_int_type);
    symbol_exprt pointer_to_const_int_symbol(
      "pointer_to_const_int", pointer_to_const_int_type);
    symbol_exprt const_pointer_to_const_int_symbol(
      "const_pointer_to_const_int", const_pointer_to_const_int_type);

    WHEN("Casting from int to int")
    {
      typecast_exprt cast_expr(
        non_const_primitive_symbol, non_const_primitive_type);

      THEN("The cast_expr does not lose const-correctness")
      {
        bool result=does_remove_const_test.does_expr_lose_const(cast_expr);
        REQUIRE_FALSE(result);
      }
    }
    WHEN("Casting from const int to int")
    {
      typecast_exprt cast_expr(
        non_const_primitive_symbol, const_primitive_type);

      THEN("The cast_expr does not lose const-correctness")
      {
        bool result=does_remove_const_test.does_expr_lose_const(cast_expr);
        REQUIRE_FALSE(result);
      }
    }
    WHEN("Casting from int to const int")
    {
      typecast_exprt cast_expr(
        non_const_primitive_symbol, const_primitive_type);

      THEN("The cast_expr does not lose const-correctness")
      {
        bool result=does_remove_const_test.does_expr_lose_const(cast_expr);
        REQUIRE_FALSE(result);
      }
    }
    WHEN("Casting from const int to const int")
    {
      typecast_exprt cast_expr(
        const_primitive_symbol, const_primitive_type);

      THEN("The cast_expr does not lose const-correctness")
      {
        bool result=does_remove_const_test.does_expr_lose_const(cast_expr);
        REQUIRE_FALSE(result);
      }
    }
    WHEN("Casting from int * to int *")
    {
      typecast_exprt cast_expr(
        pointer_to_int_symbol, pointer_to_int_type);
      THEN("The cast_expr does not lose const-correctness")
      {
        bool result=does_remove_const_test.does_expr_lose_const(cast_expr);
        REQUIRE_FALSE(result);
      }
    }
    WHEN("Casting from const int * to int *")
    {
      typecast_exprt cast_expr(
        pointer_to_const_int_symbol, pointer_to_int_type);
      THEN("The cast_expr does lose const-correctness")
      {
        bool result=does_remove_const_test.does_expr_lose_const(cast_expr);
        REQUIRE(result);
      }
    }
    WHEN("Casting from int * b const to int *")
    {
      typecast_exprt cast_expr(
        const_pointer_to_int_symbol, pointer_to_int_type);
      THEN("The cast_expr does not lose const-correctness")
      {
        bool result=does_remove_const_test.does_expr_lose_const(cast_expr);
        REQUIRE_FALSE(result);
      }
    }
    WHEN("Casting from const int * b const to int *")
    {
      typecast_exprt cast_expr(
        const_pointer_to_const_int_symbol, pointer_to_int_type);
      THEN("The cast_expr does lose const-correctness")
      {
        bool result=does_remove_const_test.does_expr_lose_const(cast_expr);
        REQUIRE(result);
      }
    }
    WHEN("Casting from int * to const int *")
    {
      typecast_exprt cast_expr(
        pointer_to_int_symbol, pointer_to_const_int_type);
      THEN("The cast_expr does not lose const-correctness")
      {
        bool result=does_remove_const_test.does_expr_lose_const(cast_expr);
        REQUIRE_FALSE(result);
      }
    }
    WHEN("Casting from const int * to const int *")
    {
      typecast_exprt cast_expr(
        pointer_to_const_int_symbol, pointer_to_const_int_type);
      THEN("The cast_expr does not lose const-correctness")
      {
        bool result=does_remove_const_test.does_expr_lose_const(cast_expr);
        REQUIRE_FALSE(result);
      }
    }
    WHEN("Casting from int * b const to const int *")
    {
      typecast_exprt cast_expr(
        const_pointer_to_int_symbol, pointer_to_const_int_type);
      THEN("The cast_expr does not lose const-correctness")
      {
        bool result=does_remove_const_test.does_expr_lose_const(cast_expr);
        REQUIRE_FALSE(result);
      }
    }
    WHEN("Casting from const int * b const to const int *")
    {
      typecast_exprt cast_expr(
        const_pointer_to_const_int_symbol, pointer_to_const_int_type);
      THEN("The cast_expr does not lose const-correctness")
      {
        bool result=does_remove_const_test.does_expr_lose_const(cast_expr);
        REQUIRE_FALSE(result);
      }
    }
    WHEN("Casting from int * to int * const")
    {
      typecast_exprt cast_expr(
        pointer_to_int_symbol, const_pointer_to_int_type);
      THEN("The cast_expr does not lose const-correctness")
      {
        bool result=does_remove_const_test.does_expr_lose_const(cast_expr);
        REQUIRE_FALSE(result);
      }
    }
    WHEN("Casting from const int * to int * const")
    {
      typecast_exprt cast_expr(
        pointer_to_const_int_symbol, const_pointer_to_int_type);
      THEN("The cast_expr does lose const-correctness")
      {
        bool result=does_remove_const_test.does_expr_lose_const(cast_expr);
        REQUIRE(result);
      }
    }
    WHEN("Casting from int * b const to int * const")
    {
      typecast_exprt cast_expr(
        const_pointer_to_int_symbol, const_pointer_to_int_type);
      THEN("The cast_expr does not lose const-correctness")
      {
        bool result=does_remove_const_test.does_expr_lose_const(cast_expr);
        REQUIRE_FALSE(result);
      }
    }
    WHEN("Casting from const int * b const to int * const")
    {
      typecast_exprt cast_expr(
        const_pointer_to_const_int_symbol, const_pointer_to_int_type);
      THEN("The cast_expr does not lose const-correctness")
      {
        bool result=does_remove_const_test.does_expr_lose_const(cast_expr);
        REQUIRE(result);
      }
    }
    WHEN("Casting from int * to const int * const")
    {
      typecast_exprt cast_expr(
        pointer_to_int_symbol, const_pointer_to_const_int_type);
      THEN("The cast_expr does not lose const-correctness")
      {
        bool result=does_remove_const_test.does_expr_lose_const(cast_expr);
        REQUIRE_FALSE(result);
      }
    }
    WHEN("Casting from const int * to const int * const")
    {
      typecast_exprt cast_expr(
        pointer_to_const_int_symbol, const_pointer_to_const_int_type);
      THEN("The cast_expr does not lose const-correctness")
      {
        bool result=does_remove_const_test.does_expr_lose_const(cast_expr);
        REQUIRE_FALSE(result);
      }
    }
    WHEN("Casting from int * b const to const int * const")
    {
      typecast_exprt cast_expr(
        const_pointer_to_int_symbol, const_pointer_to_const_int_type);
      THEN("The cast_expr does not lose const-correctness")
      {
        bool result=does_remove_const_test.does_expr_lose_const(cast_expr);
        REQUIRE_FALSE(result);
      }
    }
    WHEN("Casting from const int * b const to const int * const")
    {
      typecast_exprt cast_expr(
        const_pointer_to_const_int_symbol, const_pointer_to_const_int_type);
      THEN("The cast_expr does not lose const-correctness")
      {
        bool result=does_remove_const_test.does_expr_lose_const(cast_expr);
        REQUIRE_FALSE(result);
      }
    }

    WHEN("Casting from &(int)  to int *")
    {
      typecast_exprt cast_expr(
        address_of_exprt(non_const_primitive_symbol), pointer_to_int_type);

      THEN("The typecast_expr does not lose const-correctness")
      {
        bool result=does_remove_const_test.does_expr_lose_const(cast_expr);
        REQUIRE_FALSE(result);
      }
    }
    WHEN("Casting from &(const int) to int *")
    {
      typecast_exprt cast_expr(
        address_of_exprt(const_primitive_symbol), pointer_to_int_type);

      THEN("The cast_expr does lose const-correctness")
      {
        bool result=does_remove_const_test.does_expr_lose_const(cast_expr);
        REQUIRE(result);
      }
    }
    WHEN("Casting from &(int) to const int *")
    {
      typecast_exprt cast_expr(
        address_of_exprt(non_const_primitive_symbol),
        pointer_to_const_int_type);

      THEN("The cast_expr does not lose const-correctness")
      {
        bool result=does_remove_const_test.does_expr_lose_const(cast_expr);
        REQUIRE_FALSE(result);
      }
    }
    WHEN("Casting from &(const int) to const int *")
    {
      typecast_exprt cast_expr(
        address_of_exprt(const_primitive_symbol), pointer_to_const_int_type);

      THEN("The cast_expr does not lose const-correctness")
      {
        bool result=does_remove_const_test.does_expr_lose_const(cast_expr);
        REQUIRE_FALSE(result);
      }
    }
    WHEN("Casting from &(int) to int * const")
    {
      typecast_exprt cast_expr(
        address_of_exprt(non_const_primitive_symbol),
        const_pointer_to_int_type);

      THEN("The cast_expr does not lose const-correctness")
      {
        bool result=does_remove_const_test.does_expr_lose_const(cast_expr);
        REQUIRE_FALSE(result);
      }
    }
    WHEN("Casting from &(const int) to int * const")
    {
      typecast_exprt cast_expr(
        address_of_exprt(const_primitive_symbol), const_pointer_to_int_type);

      THEN("The cast_expr does lose const-correctness")
      {
        bool result=does_remove_const_test.does_expr_lose_const(cast_expr);
        REQUIRE(result);
      }
    }
    WHEN("Casting from &(int) to const int * const")
    {
      typecast_exprt cast_expr(
        address_of_exprt(non_const_primitive_symbol),
        const_pointer_to_const_int_type);

      THEN("The cast_expr does not lose const-correctness")
      {
        bool result=does_remove_const_test.does_expr_lose_const(cast_expr);
        REQUIRE_FALSE(result);
      }
    }
    WHEN("Casting from &(const int) to const int * const")
    {
      typecast_exprt cast_expr(
        address_of_exprt(const_primitive_symbol),
        const_pointer_to_const_int_type);

      THEN("The cast_expr does not lose const-correctness")
      {
        bool result=does_remove_const_test.does_expr_lose_const(cast_expr);
        REQUIRE_FALSE(result);
      }
    }
  }
}
