/*******************************************************************\

 Module: Write Stack Unit Tests

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

/// \file
/// Unit tests for testing of correct tracking of
/// last written location by objects

#include "catch.hpp"

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

//#include <src/ansi-c/c_to_expr.h>

SCENARIO("Constructing two environments to make sure we correctly identify modified symbols",
    "[core][analyses][variable-sensitivity][last-written-location]")
{
    const irep_idt identifier = "hello";
    auto first_val = symbol_exprt(identifier, integer_typet());
    symbolt first_sym;
    first_sym.name = first_val.get_identifier();

    auto rhs_val = constant_exprt::integer_constant(5);
    
    const irep_idt second_identifier = "world";
    auto second_val = symbol_exprt(second_identifier, integer_typet());
    symbolt second_sym;
    second_sym.name = second_val.get_identifier();
    
    symbol_tablet symbol_table;

    symbol_table.add(first_sym);
    symbol_table.add(second_sym);
    namespacet ns(symbol_table);
    
    abstract_environmentt env;
    
    auto first_eval_rhs = env.eval(rhs_val, ns);
    auto first_eval_res = env.eval(first_val, ns);
    
    auto second_eval_res = env.eval(second_val, ns);
    auto rhs_val_2 = constant_exprt::integer_constant(10);
    auto second_eval_rhs = env.eval(rhs_val_2, ns);
    
    env.assign(first_val, first_eval_rhs, ns);
    env.assign(second_val, second_eval_rhs, ns);

    abstract_environmentt second_env;
    second_env.assign(first_val, first_eval_rhs, ns);
    second_env.assign(second_val, second_eval_rhs, ns);

    auto changed_vals = abstract_environmentt::modified_symbols(
        env, second_env);
    for (auto const &val : changed_vals) {
        std::cout << val.pretty() << std::endl;
    }
}
