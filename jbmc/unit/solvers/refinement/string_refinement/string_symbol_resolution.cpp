/*******************************************************************\

Module: Unit tests for string_identifiers_resolution_from_equations
        in solvers/refinement/string_refinement.cpp

Author: Diffblue Ltd.

\*******************************************************************/

#include <testing-utils/catch.hpp>

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/std_expr.h>
#include <solvers/refinement/string_refinement.h>
#include <util/symbol_table.h>
#include <langapi/mode.h>
#include <java_bytecode/java_bytecode_language.h>
#include <iostream>

SCENARIO("string_identifiers_resolution_from_equations",
"[core][solvers][refinement][string_refinement]")
{
  // For printing expression
  register_language(new_java_bytecode_language);
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);
  messaget::mstreamt &stream = messaget().debug();

  GIVEN("Some equations")
  {
    constant_exprt a("a", string_typet());
    constant_exprt b("b", string_typet());
    constant_exprt c("c", string_typet());
    constant_exprt d("d", string_typet());
    constant_exprt e("e", string_typet());
    constant_exprt f("f", string_typet());

    struct_typet struct_type;
    struct_type.components().emplace_back("str1", string_typet());
    struct_type.components().emplace_back("str2", string_typet());
    struct_exprt struct_expr({a, f}, struct_type);
    symbol_exprt symbol_struct("sym_struct", struct_type);

    std::vector<equal_exprt> equations;
    equations.emplace_back(a, b);
    equations.emplace_back(b, c);
    equations.emplace_back(d, e);
    equations.emplace_back(symbol_struct, struct_expr);

    WHEN("There is no function call")
    {
      union_find_replacet symbol_resolve =
        string_identifiers_resolution_from_equations(
          equations, ns, stream);

      THEN("The symbol resolution structure is empty")
      {
        REQUIRE(symbol_resolve.to_vector().empty());
      }
    }

    WHEN("There is a function call")
    {
      java_method_typet::parameterst parameters;
      typet return_type;
      symbol_exprt fun_sym(
        "f", java_method_typet(std::move(parameters), return_type));
      const function_application_exprt fun(fun_sym, {c}, bool_typet());
      symbol_exprt bool_sym("bool_b", bool_typet());
      equations.emplace_back(bool_sym, fun);
      union_find_replacet symbol_resolve =
        string_identifiers_resolution_from_equations(
          equations, ns, stream);

      THEN("Equations that depend on it should be added")
      {
        REQUIRE(symbol_resolve.find(b) == symbol_resolve.find(c));
        REQUIRE(symbol_resolve.find(a) == symbol_resolve.find(b));

        member_exprt sym_m1(symbol_struct, "str1", string_typet());
        member_exprt sym_m2(symbol_struct, "str2", string_typet());

        REQUIRE(symbol_resolve.find(sym_m1) == symbol_resolve.find(c));
        REQUIRE(symbol_resolve.find(sym_m2) == symbol_resolve.find(f));
      }

      THEN("Equations that do not depend on it should not be added")
      {
        REQUIRE(symbol_resolve.find(d) != symbol_resolve.find(e));
      }

      THEN("No other equation is added")
      {
        REQUIRE(symbol_resolve.find(a) != symbol_resolve.find(d));
        REQUIRE(symbol_resolve.find(a) != symbol_resolve.find(f));
        REQUIRE(symbol_resolve.find(d) != symbol_resolve.find(f));
      }
    }
  }
}
