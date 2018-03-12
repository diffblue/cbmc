/*******************************************************************\

 Module: Unit tests for dependency graph
   solvers/refinement/string_refinement.cpp

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

#include <testing-utils/catch.hpp>

#include <util/arith_tools.h>
#include <util/std_types.h>
#include <util/std_expr.h>
#include <java_bytecode/java_types.h>
#include <solvers/refinement/string_refinement_util.h>

#ifdef DEBUG
#include <iostream>
#include <java_bytecode/java_bytecode_language.h>
#include <langapi/mode.h>
#include <util/symbol_table.h>
#endif

typet length_type()
{
  return signedbv_typet(32);
}

/// Make a struct with a pointer content and an integer length
struct_exprt make_string_argument(std::string name)
{
  struct_typet type;
  const array_typet char_array(char_type(), infinity_exprt(length_type()));
  type.components().emplace_back("length", length_type());
  type.components().emplace_back("content", pointer_type(char_array));

  const symbol_exprt length(name + "_length", length_type());
  const symbol_exprt content(name + "_content", pointer_type(java_char_type()));
  struct_exprt expr(type);
  expr.operands().push_back(length);
  expr.operands().push_back(content);
  return expr;
}

SCENARIO("dependency_graph", "[core][solvers][refinement][string_refinement]")
{
  GIVEN("dependency graph")
  {
    string_dependencest dependences;
    refined_string_typet string_type(java_char_type(), java_int_type());
    const exprt string1 = make_string_argument("string1");
    const exprt string2 = make_string_argument("string2");
    const exprt string3 = make_string_argument("string3");
    const exprt string4 = make_string_argument("string4");
    const exprt string5 = make_string_argument("string5");
    const exprt string6 = make_string_argument("string6");
    const symbol_exprt lhs("lhs", unsignedbv_typet(32));
    const symbol_exprt lhs2("lhs2", unsignedbv_typet(32));
    const symbol_exprt lhs3("lhs3", unsignedbv_typet(32));
    code_typet fun_type;

    // fun1 is s3 = s1.concat(s2)
    function_application_exprt fun1(fun_type);
    fun1.function() = symbol_exprt(ID_cprover_string_concat_func);
    fun1.arguments().push_back(string3.op0());
    fun1.arguments().push_back(string3.op1());
    fun1.arguments().push_back(string1);
    fun1.arguments().push_back(string2);

    // fun2 is s5 = s3.concat(s4)
    function_application_exprt fun2(fun_type);
    fun2.function() = symbol_exprt(ID_cprover_string_concat_func);
    fun2.arguments().push_back(string5.op0());
    fun2.arguments().push_back(string5.op1());
    fun2.arguments().push_back(string3);
    fun2.arguments().push_back(string4);

    // fun3 is s6 = s5.concat(s2)
    function_application_exprt fun3(fun_type);
    fun3.function() = symbol_exprt(ID_cprover_string_concat_func);
    fun3.arguments().push_back(string6.op0());
    fun3.arguments().push_back(string6.op1());
    fun3.arguments().push_back(string5);
    fun3.arguments().push_back(string2);

    const equal_exprt equation1(lhs, fun1);
    const equal_exprt equation2(lhs2, fun2);
    const equal_exprt equation3(lhs3, fun3);

    WHEN("We add dependencies")
    {
      symbol_generatort generator;
      array_poolt array_pool(generator);

      bool success = add_node(dependences, equation1, array_pool);
      REQUIRE(success);
      success = add_node(dependences, equation2, array_pool);
      REQUIRE(success);
      success = add_node(dependences, equation3, array_pool);
      REQUIRE(success);

#ifdef DEBUG // useful output for visualizing the graph
      {
        register_language(new_java_bytecode_language);
        symbol_tablet symbol_table;
        namespacet ns(symbol_table);
        dependencies.output_dot(std::cerr, [&](const exprt &expr) { // NOLINT
          return from_expr(ns, "", expr);
        });
      }
#endif

      // The dot output of the graph would look like:
      // ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
      // digraph dependencies {
      // "string_refinement#char_array_symbol#3" -> primitive0;
      // "string_refinement#char_array_symbol#6" -> primitive1;
      // "string_refinement#char_array_symbol#9" -> primitive2;
      // primitive0 -> "string_refinement#char_array_symbol#1";
      // primitive0 -> "string_refinement#char_array_symbol#2";
      // primitive1 -> "string_refinement#char_array_symbol#3";
      // primitive1 -> "string_refinement#char_array_symbol#5";
      // primitive2 -> "string_refinement#char_array_symbol#6";
      // primitive2 -> "string_refinement#char_array_symbol#2";
      // }
      // ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

      const array_string_exprt char_array1 =
        array_pool.find(string1.op1(), string1.op0());
      const array_string_exprt char_array2 =
        array_pool.find(string2.op1(), string2.op0());
      const array_string_exprt char_array3 =
        array_pool.find(string3.op1(), string3.op0());
      const array_string_exprt char_array4 =
        array_pool.find(string4.op1(), string4.op0());
      const array_string_exprt char_array5 =
        array_pool.find(string5.op1(), string5.op0());
      const array_string_exprt char_array6 =
        array_pool.find(string6.op1(), string6.op0());

      THEN("string3 depends on primitive0")
      {
        const auto &node = dependences.get_node(char_array3);
        const std::vector<string_dependencest::builtin_function_nodet>
          &depends = dependences.dependencies(node);
        REQUIRE(depends.size() == 1);
        const auto &primitive0 = dependences.get_builtin_function(depends[0]);

        THEN("primitive0 depends on string1 and string2")
        {
          const auto &depends2 = primitive0.string_arguments();
          REQUIRE(depends2.size() == 2);
          REQUIRE(depends2[0] == char_array1);
          REQUIRE(depends2[1] == char_array2);
        }
      }

      THEN("string5 depends on primitive1")
      {
        const auto &node = dependences.get_node(char_array5);
        const std::vector<string_dependencest::builtin_function_nodet>
          &depends = dependences.dependencies(node);
        REQUIRE(depends.size() == 1);
        const auto &primitive1 = dependences.get_builtin_function(depends[0]);

        THEN("primitive1 depends on string3 and string4")
        {
          const auto &depends2 = primitive1.string_arguments();
          REQUIRE(depends2.size() == 2);
          REQUIRE(depends2[0] == char_array3);
          REQUIRE(depends2[1] == char_array4);
        }
      }

      THEN("string6 depends on primitive2")
      {
        const auto &node = dependences.get_node(char_array6);
        const std::vector<string_dependencest::builtin_function_nodet>
          &depends = dependences.dependencies(node);
        REQUIRE(depends.size() == 1);
        const auto &primitive2 = dependences.get_builtin_function(depends[0]);

        THEN("primitive2 depends on string5 and string2")
        {
          const auto &depends2 = primitive2.string_arguments();
          REQUIRE(depends2.size() == 2);
          REQUIRE(depends2[0] == char_array5);
          REQUIRE(depends2[1] == char_array2);
        }
      }
    }
  }
}
