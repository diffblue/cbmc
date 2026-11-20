/*******************************************************************\

Module: Unit tests for bv_pointerst

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// Unit tests for bv_pointerst

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/mp_arith.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>

#include <solvers/flattening/bv_pointers.h>
#include <solvers/sat/satcheck.h>
#include <testing-utils/empty_namespace.h>
#include <testing-utils/message.h>
#include <testing-utils/use_catch.h>

/// Check that \p expr and its simplified form are equal under bv_pointerst.
static void require_simplification_agrees(const exprt &expr)
{
  const exprt simplified = simplify_expr(expr, empty_namespace);
  REQUIRE(simplified != expr);

  satcheckt satcheck{null_message_handler};
  bv_pointerst solver{empty_namespace, satcheck, null_message_handler};
  solver.set_to_false(equal_exprt{expr, simplified});
  REQUIRE(solver() == decision_proceduret::resultt::D_UNSATISFIABLE);
}

TEST_CASE(
  "bv_pointerst agrees with the simplifier on integer-address pointer "
  "constants",
  "[core][solvers][flattening][bv_pointers]")
{
  config.ansi_c.set_LP64();
  const pointer_typet pointer = pointer_type(char_type());
  const std::size_t width = pointer.get_width();

  // values with and without the sign bit set
  for(const mp_integer &value :
      {string2integer("0303030303030303", 16),
       string2integer("8303030303030303", 16)})
  {
    const constant_exprt constant{integer2bvrep(value, width), pointer};

    // casts to an integer of the same width
    for(const typet &type :
        {typet{unsignedbv_typet{width}},
         typet{signedbv_typet{width}},
         typet{bv_typet{width}}})
    {
      require_simplification_agrees(typecast_exprt{constant, type});

      // (T *)x == c with an integer x of the same width
      const symbol_exprt x{"x", type};
      require_simplification_agrees(
        equal_exprt{typecast_exprt{x, pointer}, constant});
    }
  }
}
