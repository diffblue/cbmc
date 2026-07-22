/*******************************************************************\

Module: Unit tests for bv_pointerst

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// Unit tests for bv_pointerst

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

#include <solvers/flattening/bv_pointers.h>
#include <solvers/sat/satcheck.h>
#include <testing-utils/message.h>
#include <testing-utils/use_catch.h>

SCENARIO(
  "bv_pointerst pointer arithmetic with in-range results",
  "[core][solvers][flattening][bv_pointerst]")
{
  config.ansi_c.mode = configt::ansi_ct::flavourt::GCC;
  config.ansi_c.set_arch_spec_x86_64();

  symbol_tablet symbol_table;
  const namespacet ns{symbol_table};
  satcheckt satcheck{null_message_handler};
  bv_pointerst bv_pointers{ns, satcheck, null_message_handler};

  const pointer_typet char_pointer = pointer_type(char_type());

  GIVEN("A pointer minus an unsigned integer")
  {
    // Front-ends need not convert the integer operand to a signed type, and
    // negating an unsigned integer in its own type wraps around.
    const symbol_exprt array{
      "a", array_typet{char_type(), from_integer(10, size_type())}};
    auto element_address = [&](int index)
    {
      return address_of_exprt{
        index_exprt{array, from_integer(index, signed_size_type())},
        char_pointer};
    };
    const symbol_exprt n{"n", size_type()};

    bv_pointers << equal_exprt{n, from_integer(1, size_type())};
    bv_pointers << notequal_exprt{
      minus_exprt{element_address(5), n}, element_address(4)};

    THEN("the result points to the preceding element")
    {
      REQUIRE(bv_pointers() == decision_proceduret::resultt::D_UNSATISFIABLE);
    }
  }

  GIVEN("The address of an array element at a negative index")
  {
    // The index must not be interpreted as an unsigned value (the type of
    // the element size), as that would yield an out-of-range offset.
    const struct_typet struct_type{
      {{"hdr", char_type()},
       {"arr", array_typet{char_type(), from_integer(4, size_type())}}}};
    const symbol_exprt s{"s", struct_type};
    const member_exprt arr{s, "arr", struct_type.components()[1].type()};
    const symbol_exprt i{"i", signed_int_type()};

    bv_pointers << equal_exprt{i, from_integer(-1, signed_int_type())};
    bv_pointers << notequal_exprt{
      address_of_exprt{index_exprt{arr, i}, char_pointer},
      address_of_exprt{member_exprt{s, "hdr", char_type()}, char_pointer}};

    THEN("the result points to the preceding member")
    {
      REQUIRE(bv_pointers() == decision_proceduret::resultt::D_UNSATISFIABLE);
    }
  }
}
