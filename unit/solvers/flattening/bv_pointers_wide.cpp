/*******************************************************************\

Module: Unit tests for bv_pointers_widet

Author: CBMC Contributors

\*******************************************************************/

/// \file
/// Unit tests for bv_pointers_widet

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/cout_message.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

#include <solvers/flattening/bv_pointers_wide.h>
#include <solvers/sat/satcheck.h>
#include <testing-utils/use_catch.h>

SCENARIO("bv_pointers_widet", "[core][solvers][flattening][bv_pointers_widet]")
{
  // Ensure config is set up for pointer width
  config.ansi_c.set_ILP32();

  console_message_handlert message_handler;
  message_handler.set_verbosity(0);

  GIVEN("Two pointer symbols to distinct objects")
  {
    satcheckt satcheck(message_handler);
    symbol_tablet symbol_table;
    namespacet ns(symbol_table);
    bv_pointers_widet bvp(ns, satcheck, message_handler);

    const signedbv_typet int_type(32);
    const pointer_typet ptr_type = pointer_type(int_type);

    // &x != &y should be satisfiable
    const symbol_exprt x("x", int_type);
    const symbol_exprt y("y", int_type);

    const address_of_exprt addr_x(x);
    const address_of_exprt addr_y(y);

    THEN("&x == &x is satisfiable")
    {
      bvp << equal_exprt(addr_x, addr_x);
      REQUIRE(bvp() == decision_proceduret::resultt::D_SATISFIABLE);
    }
  }
}
