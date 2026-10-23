/*******************************************************************\

Module: Unit tests for boolbvt

Author: Daniel Kroening

\*******************************************************************/

/// \file
/// Unit tests for boolbvt

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
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

SCENARIO(
  "boolbvt::convert_extractbits with non-constant index",
  "[core][solvers][flattening][boolbvt]")
{
  // End-to-end SAT-based check that the non-constant-index lowering in
  // boolbvt::convert_extractbits is correct: pin the index to a known
  // value via an assumption and assert that the extracted bits equal
  // the expected slice. Without the lowering, convert_extractbits used
  // to call conversion_failed which returns fresh unconstrained
  // variables, so the pinned-value check below would not be entailed
  // and the corresponding UNSATISFIABLE assumption would be SAT instead.
  console_message_handlert message_handler;
  message_handler.set_verbosity(0);

  GIVEN("A 16-bit source and an 8-bit non-constant index")
  {
    satcheckt satcheck(message_handler);
    symbol_tablet symbol_table;
    namespacet ns(symbol_table);
    boolbvt boolbv(ns, satcheck, message_handler);

    const unsignedbv_typet u8{8};
    const unsignedbv_typet u16{16};
    const unsignedbv_typet u4{4};
    const symbol_exprt src{"src", u16};
    const symbol_exprt idx{"idx", u8};

    // src = 0xABCD = 1010101111001101, idx = 4
    // extractbits(src, idx, u4) selects bits [idx+3 .. idx], i.e. for
    // idx=4 the nibble at bits 7..4 of 0xABCD == 0xC.
    boolbv << equal_exprt{src, from_integer(0xABCD, u16)};
    boolbv << equal_exprt{idx, from_integer(4, u8)};

    const extractbits_exprt extract{src, idx, u4};
    const equal_exprt good{extract, from_integer(0xC, u4)};
    const equal_exprt bad{extract, from_integer(0xA, u4)};

    THEN("the encoding selects the nibble at bits idx..idx+3")
    {
      // good is entailed -> ~good is unsat
      REQUIRE(
        boolbv(not_exprt{good}) ==
        decision_proceduret::resultt::D_UNSATISFIABLE);
    }

    THEN("the encoding does NOT pick a different nibble")
    {
      // bad is unsat under the same model
      REQUIRE(boolbv(bad) == decision_proceduret::resultt::D_UNSATISFIABLE);
    }
  }

  GIVEN("Index wider than source (truncation case)")
  {
    satcheckt satcheck(message_handler);
    symbol_tablet symbol_table;
    namespacet ns(symbol_table);
    boolbvt boolbv(ns, satcheck, message_handler);

    const unsignedbv_typet u16{16};
    const unsignedbv_typet u32{32};
    const unsignedbv_typet u4{4};
    const symbol_exprt src{"src", u16};
    const symbol_exprt idx{"idx", u32};

    boolbv << equal_exprt{src, from_integer(0x1234, u16)};
    boolbv << equal_exprt{idx, from_integer(8, u32)};

    // For idx=8, extractbits(src, idx, u4) selects bits 11..8 of 0x1234,
    // which is the nibble 0x2.
    const extractbits_exprt extract{src, idx, u4};
    const equal_exprt good{extract, from_integer(0x2, u4)};

    THEN("the truncated index still selects the right nibble")
    {
      REQUIRE(
        boolbv(not_exprt{good}) ==
        decision_proceduret::resultt::D_UNSATISFIABLE);
    }
  }
}
