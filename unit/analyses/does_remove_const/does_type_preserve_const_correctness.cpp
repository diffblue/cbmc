/*******************************************************************\

Module: Does Remove Const Unit Tests

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// Does Remove Const Unit Tests

#include <testing-utils/use_catch.h>

#include <util/c_types.h>
#include <util/mathematical_types.h>
#include <util/namespace.h>
#include <util/symbol_table.h>

#include <ansi-c/c_qualifiers.h>

#include <goto-programs/goto_program.h>

#include <analyses/does_remove_const/does_remove_const_util.h>
#include <analyses/does_remove_const.h>

SCENARIO("does_type_preserve_const_correctness",
  "[core][analyses][does_remove_const][does_type_preserve_const_correctness]")
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

    WHEN("Comparing int to int")
    {
      THEN("The target type preserves the const-correctness of the source type")
      {
        bool result=
          does_remove_const_test.does_type_preserve_const_correctness(
            &non_const_primitive_type, &non_const_primitive_type);
        REQUIRE(result);
      }
    }
    WHEN("Comparing const int to int")
    {
      THEN("The target type preserves the const-correctness of the source type")
      {
        bool result=
          does_remove_const_test.does_type_preserve_const_correctness(
            &const_primitive_type, &non_const_primitive_type);
        REQUIRE(result);
      }
    }
    WHEN("Comparing int to const int")
    {
      THEN("The target type preserves the const-correctness of the source type")
      {
        bool result=
          does_remove_const_test.does_type_preserve_const_correctness(
            &non_const_primitive_type, &const_primitive_type);
        REQUIRE(result);
      }
    }
    WHEN("Comparing const int to const int")
    {
      THEN("The target type preserves the const-correctness of the source type")
      {
        bool result=
          does_remove_const_test.does_type_preserve_const_correctness(
            &const_primitive_type, &const_primitive_type);
        REQUIRE(result);
      }
    }
    WHEN("Comparing int * to int *")
    {
      THEN("The target type preserves the const-correctness of the source type")
      {
        bool result=
          does_remove_const_test.does_type_preserve_const_correctness(
            &pointer_to_int_type, &pointer_to_int_type);
        REQUIRE(result);
      }
    }
    WHEN("Comparing const int * to int *")
    {
      THEN("The target type preserves the const-correctness of the source type")
      {
        bool result=
          does_remove_const_test.does_type_preserve_const_correctness(
            &pointer_to_const_int_type, &pointer_to_int_type);
        REQUIRE(result);
      }
    }
    WHEN("Comparing int * b const to int *")
    {
      THEN("The target type preserves the const-correctness of the source type")
      {
        bool result=
          does_remove_const_test.does_type_preserve_const_correctness(
            &const_pointer_to_int_type, &pointer_to_int_type);
        REQUIRE(result);
      }
    }
    WHEN("Comparing const int * b const to int *")
    {
      THEN("The target type preserves the const-correctness of the source type")
      {
        bool result=
          does_remove_const_test.does_type_preserve_const_correctness(
            &const_pointer_to_const_int_type, &pointer_to_int_type);
        REQUIRE(result);
      }
    }
    WHEN("Comparing int * to const int *")
    {
      THEN("The target type loses const-correctness of the source type")
      {
        bool result=
          does_remove_const_test.does_type_preserve_const_correctness(
            &pointer_to_int_type, &pointer_to_const_int_type);
        REQUIRE_FALSE(result);
      }
    }
    WHEN("Comparing const int * to const int *")
    {
      THEN("The target type preserves the const-correctness of the source type")
      {
        bool result=
          does_remove_const_test.does_type_preserve_const_correctness(
            &pointer_to_const_int_type, &pointer_to_const_int_type);
        REQUIRE(result);
      }
    }
    WHEN("Comparing int * b const to const int *")
    {
      THEN("The target type loses const-correctness of the source type")
      {
        bool result=
          does_remove_const_test.does_type_preserve_const_correctness(
            &const_pointer_to_int_type, &pointer_to_const_int_type);
        REQUIRE_FALSE(result);
      }
    }
    WHEN("Comparing const int * b const to const int *")
    {
      THEN("The target type preserves the const-correctness of the source type")
      {
        bool result=
          does_remove_const_test.does_type_preserve_const_correctness(
            &const_pointer_to_const_int_type, &pointer_to_const_int_type);
        REQUIRE(result);
      }
    }
    WHEN("Comparing int * to int * const")
    {
      THEN("The target type preserves the const-correctness of the source type")
      {
        bool result=
          does_remove_const_test.does_type_preserve_const_correctness(
            &pointer_to_int_type, &const_pointer_to_int_type);
        REQUIRE(result);
      }
    }
    WHEN("Comparing const int * to int * const")
    {
      THEN("The target type preserves the const-correctness of the source type")
      {
        bool result=
          does_remove_const_test.does_type_preserve_const_correctness(
           &pointer_to_const_int_type, &const_pointer_to_int_type);
        REQUIRE(result);
      }
    }
    WHEN("Comparing int * b const to int * const")
    {
      THEN("The target type preserves the const-correctness of the source type")
      {
        bool result=
          does_remove_const_test.does_type_preserve_const_correctness(
           &const_pointer_to_int_type, &const_pointer_to_int_type);
        REQUIRE(result);
      }
    }
    WHEN("Comparing const int * b const to int * const")
    {
      THEN("The target type preserves the const-correctness of the source type")
      {
        bool result=
          does_remove_const_test.does_type_preserve_const_correctness(
           &const_pointer_to_const_int_type, &const_pointer_to_int_type);
        REQUIRE(result);
      }
    }
    WHEN("Comparing int * to const int * const")
    {
      THEN("The target type loses const-correctness of the source type")
      {
        bool result=
          does_remove_const_test.does_type_preserve_const_correctness(
           &pointer_to_int_type, &const_pointer_to_const_int_type);
        REQUIRE_FALSE(result);
      }
    }
    WHEN("Comparing const int * to const int * const")
    {
      THEN("The target type preserves the const-correctness of the source type")
      {
        bool result=
          does_remove_const_test.does_type_preserve_const_correctness(
           &pointer_to_const_int_type, &const_pointer_to_const_int_type);
        REQUIRE(result);
      }
    }
    WHEN("Comparing int * b const to const int * const")
    {
      THEN("The target type loses const-correctness of the source type")
      {
        bool result=
          does_remove_const_test.does_type_preserve_const_correctness(
           &const_pointer_to_int_type, &const_pointer_to_const_int_type);
        REQUIRE_FALSE(result);
      }
    }
    WHEN("Comparing const int * b const to const int * const")
    {
      THEN("The target type preserves the const-correctness of the source type")
      {
        bool result=
          does_remove_const_test.does_type_preserve_const_correctness(
           &const_pointer_to_const_int_type, &const_pointer_to_const_int_type);
        REQUIRE(result);
      }
    }
  }
}
