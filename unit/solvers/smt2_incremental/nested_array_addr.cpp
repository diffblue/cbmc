// Author: Michael Tautschnig

/// \file
/// Unit tests for lower_address_of_array_index with nested array indices.

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>
#include <util/std_expr.h>

#include <solvers/smt2_incremental/convert_expr_to_smt.h>
#include <testing-utils/use_catch.h>

TEST_CASE(
  "lower_address_of_array_index nested array uses correct element pointer type",
  "[core][smt2_incremental]")
{
  // For int a[3][4], &a[i][j] is lowered by two passes of
  // lower_address_of_array_index:
  //   &a[i][j]  ->  &(a[i])[j]  ->  (int*)&(a[i]) + j
  //   &(a[i])   ->  (int(*)[4])&a + i
  // The inner &(a[i]) must get pointer-to-element type int(*)[4], not
  // int* (which is the outer address_of type). Using int* makes +i
  // scale by sizeof(int)=4 instead of sizeof(int[4])=16.

  config.ansi_c.mode = configt::ansi_ct::flavourt::GCC;
  config.ansi_c.set_arch_spec_x86_64();

  const signedbv_typet int_type{32};
  const unsignedbv_typet idx_type{64};
  const array_typet inner_array_type{
    int_type, from_integer(4, signed_size_type())};
  const array_typet outer_array_type{
    inner_array_type, from_integer(3, signed_size_type())};

  const symbol_exprt a{"a", outer_array_type};
  const exprt i = from_integer(1, idx_type);
  const exprt j = from_integer(2, idx_type);

  // Build &a[i][j]: address_of(index(index(a, i), j))
  const index_exprt a_i{a, i};
  const index_exprt a_i_j{a_i, j};
  const address_of_exprt addr_a_i_j{a_i_j};

  // The outer pointer type is int* (pointer to int_type).
  const pointer_typet outer_ptr_type =
    type_checked_cast<pointer_typet>(addr_a_i_j.type());
  REQUIRE(outer_ptr_type.base_type() == int_type);

  const exprt lowered = lower_address_of_array_index(addr_a_i_j);

  // After lowering, the result should be:
  //   (int*)(  (int(*)[4])&a + i  ) + j
  // i.e., a plus_exprt with:
  //   - lhs: typecast from (int(*)[4])&a+i to int*
  //   - rhs: j
  // The key check: the inner plus must use pointer-to-inner_array_type,
  // not pointer-to-int_type.

  // The top-level should be a plus of something and j.
  const auto *top_plus = expr_try_dynamic_cast<plus_exprt>(lowered);
  REQUIRE(top_plus != nullptr);
  CHECK(top_plus->op1() == j);

  // The lhs should be a typecast (because the inner element pointer type
  // differs from the outer pointer type).
  const auto *cast = expr_try_dynamic_cast<typecast_exprt>(top_plus->op0());
  REQUIRE(cast != nullptr);
  CHECK(cast->type() == outer_ptr_type);

  // Inside the typecast: a plus of address_of(a) with element pointer
  // type and i.
  const auto *inner_plus = expr_try_dynamic_cast<plus_exprt>(cast->op());
  REQUIRE(inner_plus != nullptr);
  CHECK(inner_plus->op1() == i);

  const auto *inner_addr =
    expr_try_dynamic_cast<address_of_exprt>(inner_plus->op0());
  REQUIRE(inner_addr != nullptr);
  // The inner address_of must have pointer-to-inner_array_type.
  const auto &inner_ptr_type =
    type_checked_cast<pointer_typet>(inner_addr->type());
  CHECK(inner_ptr_type.base_type() == inner_array_type);
}
