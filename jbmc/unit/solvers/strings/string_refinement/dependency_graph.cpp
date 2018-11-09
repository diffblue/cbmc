/*******************************************************************\

Module: Unit tests for dependency graph in
        solvers/refinement/string_refinement.cpp

Author: Diffblue Ltd.

\*******************************************************************/

#include <testing-utils/use_catch.h>

#include <java_bytecode/java_types.h>
#include <solvers/strings/string_refinement_util.h>
#include <util/arith_tools.h>
#include <util/std_expr.h>
#include <util/std_types.h>

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
  const array_typet char_array(char_type(), infinity_exprt(length_type()));
  struct_typet type(
    {{"length", length_type()}, {"content", pointer_type(char_array)}});

  symbol_exprt length(name + "_length", length_type());
  symbol_exprt content(name + "_content", pointer_type(java_char_type()));
  return struct_exprt({std::move(length), std::move(content)}, std::move(type));
}

SCENARIO("dependency_graph", "[core][solvers][refinement][string_refinement]")
{
  GIVEN("dependency graph")
  {
    string_dependenciest dependencies;
    const typet string_type =
      refined_string_typet(java_int_type(), pointer_type(java_char_type()));
    const exprt string1 = make_string_argument("string1");
    const exprt string2 = make_string_argument("string2");
    const exprt string3 = make_string_argument("string3");
    const exprt string4 = make_string_argument("string4");
    const exprt string5 = make_string_argument("string5");
    const exprt string6 = make_string_argument("string6");
    const symbol_exprt lhs("lhs", unsignedbv_typet(32));
    const symbol_exprt lhs2("lhs2", unsignedbv_typet(32));
    const symbol_exprt lhs3("lhs3", unsignedbv_typet(32));
    const java_method_typet fun_type(
      {java_method_typet::parametert(length_type()),
       java_method_typet::parametert(pointer_type(java_char_type())),
       java_method_typet::parametert(string_type),
       java_method_typet::parametert(string_type)},
      unsignedbv_typet(32));

    // fun1 is s3 = s1.concat(s2)
    const function_application_exprt fun1(
      symbol_exprt(ID_cprover_string_concat_func),
      {string3.op0(), string3.op1(), string1, string2},
      fun_type);

    // fun2 is s5 = s3.concat(s4)
    const function_application_exprt fun2(
      symbol_exprt(ID_cprover_string_concat_func),
      {string5.op0(), string5.op1(), string3, string4},
      fun_type);

    // fun3 is s6 = s5.concat(s2)
    const function_application_exprt fun3(
      symbol_exprt(ID_cprover_string_concat_func),
      {string6.op0(), string6.op1(), string5, string2},
      fun_type);

    const equal_exprt equation1(lhs, fun1);
    const equal_exprt equation2(lhs2, fun2);
    const equal_exprt equation3(lhs3, fun3);

    WHEN("We add dependencies")
    {
      symbol_generatort generator;
      array_poolt array_pool(generator);

      bool success = add_node(dependencies, equation1, array_pool);
      REQUIRE(success);
      success = add_node(dependencies, equation2, array_pool);
      REQUIRE(success);
      success = add_node(dependencies, equation3, array_pool);
      REQUIRE(success);

#ifdef DEBUG // useful output for visualizing the graph
      {
        register_language(new_java_bytecode_language);
        symbol_tablet symbol_table;
        namespacet ns(symbol_table);
        dependencies.output_dot(std::cerr);
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
        const auto &node = dependencies.get_node(char_array3);
        std::size_t nb_dependencies = 0;
        dependencies.for_each_dependency(
          node, [&](const string_dependenciest::builtin_function_nodet &n) {
            nb_dependencies++;
            THEN("primitive0 depends on string1 and string2")
            {
              const auto &depends2 = n.data->string_arguments();
              REQUIRE(depends2.size() == 2);
              REQUIRE(depends2[0] == char_array1);
              REQUIRE(depends2[1] == char_array2);
            }
          });
        REQUIRE(nb_dependencies == 1);
      }

      THEN("string5 depends on primitive1")
      {
        const auto &node = dependencies.get_node(char_array5);
        std::size_t nb_dependencies = 0;
        dependencies.for_each_dependency(
          node, [&](const string_dependenciest::builtin_function_nodet &n) {
            nb_dependencies++;
            THEN("primitive1 depends on string3 and string4")
            {
              const auto &depends2 = n.data->string_arguments();
              REQUIRE(depends2.size() == 2);
              REQUIRE(depends2[0] == char_array3);
              REQUIRE(depends2[1] == char_array4);
            }
          });
        REQUIRE(nb_dependencies == 1);
      }

      THEN("string6 depends on primitive2")
      {
        const auto &node = dependencies.get_node(char_array6);
        std::size_t nb_dependencies = 0;
        dependencies.for_each_dependency(
          node,
          [&](const string_dependenciest::builtin_function_nodet &n) { // NOLINT
            nb_dependencies++;
            THEN("primitive2 depends on string5 and string2")
            {
              const auto &depends2 = n.data->string_arguments();
              REQUIRE(depends2.size() == 2);
              REQUIRE(depends2[0] == char_array5);
              REQUIRE(depends2[1] == char_array2);
            }
          });
        REQUIRE(nb_dependencies == 1);
      }
    }
  }
}
