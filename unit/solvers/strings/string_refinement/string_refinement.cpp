/*******************************************************************\

Module: Unit tests for sparse arrays in
        solvers/refinement/string_refinement.cpp

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

#include <testing-utils/use_catch.h>

#include <solvers/sat/satcheck.h>
#include <solvers/strings/string_refinement.h>
#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/mathematical_types.h>
#include <util/std_expr.h>
#include <util/std_types.h>
#include <util/symbol_table.h>

SCENARIO("string refinement", "[core][solvers][strings][string_refinement]")
{
  config.set_arch("none");

  string_refinementt::infot info;

  null_message_handlert log{};
  info.message_handler = &log;

  symbol_tablet symbol_table;
  namespacet ns{symbol_table};
  info.ns = &ns;

  satcheckt sat_solver{log};
  info.prop = &sat_solver;

  string_refinementt solver{info};

  GIVEN("An array of characters, with its associated pointer and length")
  {
    const signedbv_typet int_type{64};
    const unsignedbv_typet char_type{16};
    const array_typet char_array_type{char_type, infinity_exprt{int_type}};
    const refined_string_typet string_type{int_type, pointer_type(char_type)};
    const symbol_exprt array1{"array1", char_array_type};
    const symbol_exprt pointer1{"pointer1", pointer_type(char_type)};
    const symbol_exprt length1{"length1", int_type};
    const refined_string_exprt string_expr{length1, pointer1, string_type};

    // associate_array_to_pointer : (char[], *char) -> int
    const symbol_exprt associate_array_to_pointer{
      ID_cprover_associate_array_to_pointer_func,
      mathematical_function_typet{{char_array_type, pointer_type(char_type)},
                                  int_type}};

    // associate_length_to_array : (int, char[]) -> int
    const symbol_exprt associate_length_to_array{
      ID_cprover_associate_length_to_array_func,
      mathematical_function_typet{{int_type, char_array_type}, int_type}};

    // length_function : (string) -> int
    const symbol_exprt length_function{
      ID_cprover_string_length_func,
      mathematical_function_typet{{string_type}, int_type}};

    // char_at_function : (string, int) -> char
    const symbol_exprt char_at_function{
      ID_cprover_string_char_at_func,
      mathematical_function_typet{{string_type, int_type}, char_type}};

    // return_code1 == associate_array_to_pointer(array1, pointer1)
    const symbol_exprt return_code1{"return_code1", int_type};
    solver.set_to(
      equal_exprt{
        return_code1,
        function_application_exprt{associate_array_to_pointer,
                                   std::vector<exprt>{array1, pointer1}}},
      true);

    // return_code2 == associate_length_to_array(length1, array1)
    const symbol_exprt return_code2{"return_code2", int_type};
    solver.set_to(
      equal_exprt{
        return_code1,
        function_application_exprt{associate_length_to_array,
                                   std::vector<exprt>{array1, length1}}},
      true);

    WHEN(
      "return_length == string_length({length1, pointer1}) "
      "and return_length == 15")
    {
      const symbol_exprt return_length{"return_length", int_type};
      solver.set_to(
        equal_exprt{return_length,
                    function_application_exprt{
                      length_function, std::vector<exprt>{string_expr}}},
        true);

      solver.set_to(
        equal_exprt{return_length, from_integer(15, int_type)}, true);

      auto result = solver.dec_solve();
      THEN("The formula is satisfiable")
      {
        REQUIRE(result == decision_proceduret::resultt::D_SATISFIABLE);
      }
      THEN("the model for the result and length1 are `15`")
      {
        const exprt return_length_model = solver.get(return_length);
        REQUIRE(return_length_model == from_integer(15, int_type));
        const exprt length1_model = solver.get(length1);
        REQUIRE(return_length_model == from_integer(15, int_type));
      }
      THEN("the model of array1 is an array of length 15")
      {
        const exprt array_model = solver.get(array1);
        REQUIRE(can_cast_expr<array_exprt>(array_model));
        REQUIRE(to_array_expr(array_model).operands().size() == 15);
      }
    }

    WHEN("length1 == 10 and 'b' == string_char_at({length1, pointer1}, 9)")
    {
      solver.set_to(equal_exprt{length1, from_integer(10, int_type)}, true);

      solver.set_to(
        equal_exprt{
          from_integer('b', char_type),
          function_application_exprt{
            char_at_function,
            std::vector<exprt>{string_expr, from_integer(9, int_type)}}},
        true);

      THEN(
        "The formula is satisfiable and the model of the array should have"
        "length 10 and end with 'b'")
      {
        auto result = solver.dec_solve();
        REQUIRE(result == decision_proceduret::resultt::D_SATISFIABLE);
        const exprt array_model = solver.get(array1);
        REQUIRE(can_cast_expr<array_exprt>(array_model));
        const std::vector<exprt> &elements =
          to_array_expr(array_model).operands();
        REQUIRE(elements.size() == 10);
        REQUIRE(elements[9].is_constant());
        REQUIRE(numeric_cast_v<char>(to_constant_expr(elements[9])) == 'b');
      }
    }

    WHEN(
      "g1 => length1 = 10 && 'b' == string_char_at({length1, pointer1}, 9)"
      " and g2 => 'c' == string_char_at({length1, pointer1}, 3)"
      " and g1 && g2")
    {
      const symbol_exprt g1{"g1", bool_typet{}};
      solver.set_to(
        implies_exprt{
          g1,
          and_exprt{equal_exprt{length1, from_integer(10, int_type)},
                    equal_exprt{from_integer('b', char_type),
                                function_application_exprt{
                                  char_at_function,
                                  std::vector<exprt>{
                                    string_expr, from_integer(9, int_type)}}}}},
        true);

      const symbol_exprt g2{"g2", bool_typet{}};
      solver.set_to(
        implies_exprt{
          g2,
          and_exprt{equal_exprt{length1, from_integer(10, int_type)},
                    equal_exprt{from_integer('c', char_type),
                                function_application_exprt{
                                  char_at_function,
                                  std::vector<exprt>{
                                    string_expr, from_integer(3, int_type)}}}}},
        true);

      solver.set_to(and_exprt{g1, g2}, true);

      THEN(
        "The model for array1 has length 10 and contains 'c' at "
        " position 3 and b at position 9")
      {
        auto result = solver.dec_solve();
        REQUIRE(result == decision_proceduret::resultt::D_SATISFIABLE);
        const exprt array_model = solver.get(array1);
        REQUIRE(can_cast_expr<array_exprt>(array_model));
        const std::vector<exprt> &elements =
          to_array_expr(array_model).operands();
        REQUIRE(elements.size() == 10);
        REQUIRE(elements[3].is_constant());
        REQUIRE(numeric_cast_v<char>(to_constant_expr(elements[3])) == 'c');
        REQUIRE(elements[9].is_constant());
        REQUIRE(numeric_cast_v<char>(to_constant_expr(elements[9])) == 'b');
      }
    }

    WHEN(
      "g1 => 'b' == string_char_at({length1, pointer1}, 9)"
      " and g2 => 'c' == string_char_at({length1, pointer1}, 9) "
      " and length1 == 10 && !g1 && g2")
    {
      const symbol_exprt g1{"g1", bool_typet{}};
      solver.set_to(
        implies_exprt{
          g1,
          equal_exprt{
            from_integer('b', char_type),
            function_application_exprt{
              char_at_function,
              std::vector<exprt>{string_expr, from_integer(9, int_type)}}}},
        true);

      const symbol_exprt g2{"g2", bool_typet{}};
      solver.set_to(
        implies_exprt{
          g2,
          equal_exprt{
            from_integer('c', char_type),
            function_application_exprt{
              char_at_function,
              std::vector<exprt>{string_expr, from_integer(9, int_type)}}}},
        true);

      solver.set_to(
        and_exprt{
          equal_exprt{length1, from_integer(10, int_type)}, not_exprt{g1}, g2},
        true);
      THEN("The model for array1 has length 10 and contains 'c' at position 9")
      {
        auto result = solver.dec_solve();
        REQUIRE(result == decision_proceduret::resultt::D_SATISFIABLE);
        const exprt array_model = solver.get(array1);
        REQUIRE(can_cast_expr<array_exprt>(array_model));
        const std::vector<exprt> &elements =
          to_array_expr(array_model).operands();
        REQUIRE(elements.size() == 10);
        REQUIRE(elements[9].is_constant());
        REQUIRE(numeric_cast_v<char>(to_constant_expr(elements[9])) == 'c');
      }
    }
  }
}
