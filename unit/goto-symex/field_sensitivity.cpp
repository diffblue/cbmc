/*******************************************************************\

Module: Unit tests for field_sensitivityt

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// Unit tests for field_sensitivityt handling of arrays whose index type is
/// not enumerable (e.g. struct-keyed "map" arrays as used by the Strata heap
/// model `Map Ref _`). Such arrays must be treated monolithically: element
/// enumeration builds indices via from_integer(i, index_type), which is only
/// defined for integer/bitvector/enum index types.

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/invariant.h>
#include <util/magic.h>
#include <util/namespace.h>
#include <util/ssa_expr.h>
#include <util/std_expr.h>
#include <util/std_types.h>
#include <util/symbol_table.h>

#include <goto-programs/goto_program.h>

#include <goto-symex/field_sensitivity.h>
#include <goto-symex/goto_symex_state.h>
#include <testing-utils/use_catch.h>

SCENARIO(
  "field sensitivity treats non-enumerable array index types monolithically",
  "[core][goto-symex][field_sensitivity]")
{
  // Turn invariant violations into exceptions: without the enumerable-index
  // guard, get_fields aborts inside from_integer (PRECONDITION) when it tries
  // to build a struct-typed index constant. Throwing mode turns a regression
  // into a clean test failure instead of killing the test binary.
  const cbmc_invariants_should_throwt invariants_throw;

  symbol_tablet symbol_table;
  namespacet ns{symbol_table};

  const signedbv_typet int_type{32};

  // A struct type used as an array index ("map key"), as produced by front
  // ends that model heaps as struct-keyed maps.
  struct_typet key_type{{{"id", int_type}}};
  key_type.set_tag("key");

  const field_sensitivityt field_sensitivity{
    DEFAULT_MAX_FIELD_SENSITIVITY_ARRAY_SIZE, false, irep_idt{}};

  // Minimal symex state, required by the get_fields interface.
  std::list<goto_programt::instructiont> target;
  symex_targett::sourcet source{"fun", target.begin()};
  guard_managert guard_manager;
  std::size_t count = 0;
  auto fresh_name = [&count](const irep_idt &) { return count++; };
  goto_symex_statet state{
    source,
    DEFAULT_MAX_FIELD_SENSITIVITY_ARRAY_SIZE,
    false,
    irep_idt{},
    guard_manager,
    fresh_name};

  GIVEN("a small array with an integer index type")
  {
    const array_typet array_type{int_type, from_integer(2, int_type)};
    const ssa_exprt array_ssa{symbol_exprt{"some_array", array_type}};

    THEN("it is divisible and get_fields enumerates its elements")
    {
      REQUIRE(field_sensitivity.is_divisible(array_ssa, true));

      exprt fields;
      REQUIRE_NOTHROW(
        fields = field_sensitivity.get_fields(ns, state, array_ssa, true));
      REQUIRE(fields.id() == ID_array);
      REQUIRE(fields.operands().size() == 2);
    }
  }

  GIVEN("a small array with a struct (map-key) index type")
  {
    array_typet map_type{int_type, from_integer(2, int_type)};
    map_type.index_type_nonconst() = key_type;
    const ssa_exprt map_ssa{symbol_exprt{"some_map", map_type}};

    THEN("it is not divisible and get_fields leaves it unchanged")
    {
      REQUIRE(!field_sensitivity.is_divisible(map_ssa, true));

      // Without the enumerable-index-type guard this aborts in
      // from_integer(i, key_type).
      exprt fields;
      REQUIRE_NOTHROW(
        fields = field_sensitivity.get_fields(ns, state, map_ssa, true));
      REQUIRE(fields == map_ssa);
    }
  }
}
