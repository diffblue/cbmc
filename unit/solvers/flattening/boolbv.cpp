/*******************************************************************\

Module: Unit tests for boolbvt

Author: Daniel Kroening

\*******************************************************************/

/// \file
/// Unit tests for boolbvt

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/byte_operators.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/cout_message.h>
#include <util/namespace.h>
#include <util/std_expr.h>

#include <solvers/flattening/boolbv.h>
#include <solvers/sat/satcheck.h>
#include <testing-utils/empty_namespace.h>
#include <testing-utils/message.h>
#include <testing-utils/use_catch.h>

SCENARIO("boolbvt", "[core][solvers][flattening][boolbvt]")
{
  console_message_handlert message_handler;
  message_handler.set_verbosity(0);

  GIVEN("A satisfiable bit-vector formula f")
  {
    satcheckt satcheck(message_handler);
    boolbvt boolbv(empty_namespace, satcheck, message_handler);

    unsignedbv_typet u32(32);
    boolbv << equal_exprt(symbol_exprt("x", u32), from_integer(10, u32));

    THEN("is indeed satisfiable")
    {
      REQUIRE(boolbv() == decision_proceduret::resultt::D_SATISFIABLE);
    }
    THEN("is unsatisfiable under an inconsistent assumption")
    {
      auto assumption =
        equal_exprt(symbol_exprt("x", u32), from_integer(11, u32));
      REQUIRE(
        boolbv(assumption) == decision_proceduret::resultt::D_UNSATISFIABLE);
    }
  }
}

SCENARIO(
  "boolbvt convert_let with a byte_update in an unbounded array value",
  "[core][solvers][flattening][boolbvt]")
{
  // A let-bound symbol of unbounded array type whose value still contains a
  // byte_update operator must have that operator lowered before it is handed
  // to the array theory: boolbvt::convert_let computes a lowered value but,
  // before the fix, passed the un-lowered value to record_array_let_binding,
  // tripping `DATA_INVARIANT(false, "byte_update should be removed before
  // collect_arrays")` in collect_arrays.  This pins that fix.
  GIVEN("a let binding an unbounded array to a byte_update expression")
  {
    config.ansi_c.mode = configt::ansi_ct::flavourt::GCC;
    config.ansi_c.set_arch_spec_x86_64();
    satcheckt satcheck{null_message_handler};
    symbol_tablet symbol_table;
    namespacet ns{symbol_table};
    boolbvt boolbv{ns, satcheck, null_message_handler};

    const unsignedbv_typet u8{8};
    // non-constant size => unbounded array
    const array_typet array_type{u8, symbol_exprt{"N", size_type()}};
    const symbol_exprt a{"a", array_type};
    const symbol_exprt x{"x", u8};

    const symbol_exprt b{"b", array_type};
    const exprt array_value = byte_update_exprt{
      ID_byte_update_little_endian,
      b,
      from_integer(0, c_index_type()),
      x,
      /* bits_per_byte */ 8};

    const let_exprt let{
      a,
      array_value,
      equal_exprt{index_exprt{a, from_integer(0, c_index_type())}, x}};

    THEN("the let converts without tripping a DATA_INVARIANT")
    {
      boolbv << let;
      REQUIRE(boolbv() == decision_proceduret::resultt::D_SATISFIABLE);
    }
  }
}
