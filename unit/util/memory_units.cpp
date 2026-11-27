/*******************************************************************\

Module: Unit tests for memory_sizet

Author: Diffblue Ltd

\*******************************************************************/

/// \file
/// Unit tests for memory_sizet

#include <util/memory_units.h>

#include <testing-utils/use_catch.h>

#include <type_traits>
#include <utility>

// Trivially copyable (and thus noexcept-movable) so that containers can
// relocate their elements with memmove.
static_assert(std::is_trivially_copyable<memory_sizet>::value, "");
static_assert(std::is_nothrow_move_constructible<memory_sizet>::value, "");
static_assert(std::is_nothrow_move_assignable<memory_sizet>::value, "");

TEST_CASE("memory_sizet copy and move", "[core][util][memory_units]")
{
  const memory_sizet size = memory_sizet::from_bytes(3 * 1024 * 1024);

  memory_sizet copy{size};
  REQUIRE(copy.get_mebibytes() == 3);

  memory_sizet moved{std::move(copy)};
  REQUIRE(moved.get_bytes() == size.get_bytes());

  memory_sizet assigned;
  REQUIRE(assigned.get_bytes() == 0);
  assigned = moved;
  REQUIRE(assigned.get_bytes() == size.get_bytes());
  assigned = memory_sizet::from_bytes(1024);
  REQUIRE(assigned.get_kibibytes() == 1);
}
