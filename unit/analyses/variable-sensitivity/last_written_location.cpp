/*******************************************************************\

 Module: Write Stack Unit Tests

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

/// \file
/// Unit tests for testing of correct tracking of
/// last written location by objects

#include <testing-utils/catch.hpp>

#include <iostream>
#include <string>

#include <util/expr.h>
#include <util/std_expr.h>
#include <util/std_types.h>
#include <util/symbol.h>
#include <util/symbol_table.h>
#include <util/namespace.h>
#include <util/type.h>
#include <analyses/variable-sensitivity/abstract_enviroment.h>
#include <util/arith_tools.h>

//#include <src/ansi-c/c_to_expr.h>

SCENARIO("Constructing two environments to make sure we correctly identify modified symbols",
    "[core][analyses][variable-sensitivity][last-written-location]")
{
  GIVEN("Two identifiers that contain integer values")
  {
    const irep_idt identifier = "hello";
    auto first_val = symbol_exprt(identifier, integer_typet());
    symbolt first_sym;
    first_sym.name = first_val.get_identifier();

    auto rhs_val = from_integer(5, integer_typet());

    const irep_idt second_identifier = "world";
    auto second_val = symbol_exprt(second_identifier, integer_typet());
    symbolt second_sym;
    second_sym.name = second_val.get_identifier();

    symbol_tablet symbol_table;

    symbol_table.add(first_sym);
    symbol_table.add(second_sym);
    namespacet ns(symbol_table);

    WHEN("The identifiers get inserted into two environments")
    {
      abstract_environmentt env;

      auto first_eval_rhs = env.eval(rhs_val, ns);
      auto first_eval_res = env.eval(first_val, ns);

      auto second_eval_res = env.eval(second_val, ns);
      auto rhs_val_2 = from_integer(10, integer_typet());
      auto second_eval_rhs = env.eval(rhs_val_2, ns);

      env.assign(first_val, first_eval_rhs, ns);
      env.assign(second_val, second_eval_rhs, ns);

      abstract_environmentt second_env;
      second_env.assign(first_val, first_eval_rhs, ns);
      second_env.assign(second_val, second_eval_rhs, ns);

      THEN("The modified symbols between the two domains should be none") {
        auto changed_vals = abstract_environmentt::modified_symbols(
          env, second_env);
        REQUIRE(changed_vals.size() == 0);
      }
    }
  }
  GIVEN("Two identifiers that contain integer values")
  {
    const irep_idt identifier = "hello";
    auto first_val = symbol_exprt(identifier, integer_typet());
    symbolt first_sym;
    first_sym.name = first_val.get_identifier();

    auto rhs_val = from_integer(5, integer_typet());

    const irep_idt second_identifier = "world";
    auto second_val = symbol_exprt(second_identifier, integer_typet());
    symbolt second_sym;
    second_sym.name = second_val.get_identifier();

    symbol_tablet symbol_table;

    symbol_table.add(first_sym);
    symbol_table.add(second_sym);
    namespacet ns(symbol_table);

    WHEN("The identifiers get inserted into two environments, but one of \
          them has a different value in one of the environments")
    {
      abstract_environmentt env;

      auto first_eval_rhs = env.eval(rhs_val, ns);
      auto first_eval_res = env.eval(first_val, ns);

      auto second_eval_res = env.eval(second_val, ns);
      auto rhs_val_2 = from_integer(10, integer_typet());
      auto second_eval_rhs = env.eval(rhs_val_2, ns);

      env.assign(first_val, first_eval_rhs, ns);
      env.assign(second_val, second_eval_rhs, ns);

      auto rhs_val_3 = from_integer(20, integer_typet());

      abstract_environmentt second_env;
      auto new_rhs_val = second_env.eval(rhs_val_3, ns);
      second_env.assign(first_val, first_eval_rhs, ns);
      second_env.assign(second_val, new_rhs_val, ns);

      THEN("The modified symbols between the two domains should be none") {
      auto changed_vals = abstract_environmentt::modified_symbols(
          env, second_env);
        REQUIRE(changed_vals.size() == 0);
      }
    }
  }
}
