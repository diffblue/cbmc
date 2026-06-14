/*******************************************************************\

Module: Unit tests of expression size/offset computation

Author: Michael Tautschnig

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/byte_operators.h>
#include <util/c_types.h>
#include <util/cmdline.h>
#include <util/config.h>
#include <util/namespace.h>
#include <util/pointer_offset_size.h>
#include <util/std_expr.h>

#include <testing-utils/empty_namespace.h>
#include <testing-utils/use_catch.h>

TEST_CASE("Build subexpression to access element at offset into array")
{
  // this test does require a proper architecture to be set so that byte extract
  // uses adequate endianness
  cmdlinet cmdline;
  config.set(cmdline);

  const namespacet &ns = empty_namespace;

  const signedbv_typet t(32);

  array_typet array_type(t, from_integer(2, size_type()));
  symbol_exprt a("array", array_type);

  {
    const auto result = get_subexpression_at_offset(a, 0, t, ns);
    REQUIRE(result.value() == index_exprt(a, from_integer(0, c_index_type())));
  }

  {
    const auto result = get_subexpression_at_offset(a, 32 / 8, t, ns);
    REQUIRE(result.value() == index_exprt(a, from_integer(1, c_index_type())));
  }

  {
    const auto result =
      get_subexpression_at_offset(a, from_integer(0, size_type()), t, ns);
    REQUIRE(result.value() == index_exprt(a, from_integer(0, c_index_type())));
  }

  {
    const auto result =
      get_subexpression_at_offset(a, size_of_expr(t, ns).value(), t, ns);
    REQUIRE(result.value() == index_exprt(a, from_integer(1, c_index_type())));
  }

  {
    const signedbv_typet small_t(8);
    const auto result = get_subexpression_at_offset(a, 1, small_t, ns);
    REQUIRE(
      result.value() == make_byte_extract(
                          index_exprt(a, from_integer(0, c_index_type())),
                          from_integer(1, c_index_type()),
                          small_t));
  }

  {
    const signedbv_typet int16_t(16);
    const auto result = get_subexpression_at_offset(a, 3, int16_t, ns);
    // At offset 3 there are only 8 bits remaining in an element of type t so
    // not enough to fill a 16 bit int, so this cannot be transformed in an
    // index_exprt.
    REQUIRE(
      result.value() ==
      make_byte_extract(a, from_integer(3, c_index_type()), int16_t));
  }
}

TEST_CASE("Build subexpression to access element at offset into struct")
{
  // this test does require a proper architecture to be set so that byte extract
  // uses adequate endianness
  cmdlinet cmdline;
  config.set(cmdline);

  const namespacet &ns = empty_namespace;

  const signedbv_typet t(32);

  struct_typet st({{"foo", t}, {"bar", t}});

  symbol_exprt s("struct", st);

  {
    const auto result = get_subexpression_at_offset(s, 0, t, ns);
    REQUIRE(result.value() == member_exprt(s, "foo", t));
  }

  {
    const auto result = get_subexpression_at_offset(s, 32 / 8, t, ns);
    REQUIRE(result.value() == member_exprt(s, "bar", t));
  }

  {
    const auto result =
      get_subexpression_at_offset(s, from_integer(0, size_type()), t, ns);
    REQUIRE(result.value() == member_exprt(s, "foo", t));
  }

  {
    const auto result =
      get_subexpression_at_offset(s, size_of_expr(t, ns).value(), t, ns);
    REQUIRE(result.value() == member_exprt(s, "bar", t));
  }

  {
    const signedbv_typet small_t(8);
    const auto result = get_subexpression_at_offset(s, 1, small_t, ns);
    REQUIRE(
      result.value() ==
      make_byte_extract(
        member_exprt(s, "foo", t), from_integer(1, c_index_type()), small_t));
  }
}

TEST_CASE("is_zero_width predicate", "[core][util][pointer_offset_size]")
{
  cmdlinet cmdline;
  config.set(cmdline);

  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  // Trivial cases.
  REQUIRE(is_zero_width(empty_typet{}, ns));
  REQUIRE_FALSE(is_zero_width(signedbv_typet{32}, ns));

  // Zero-width bitvector. bv_typet permits a zero width.
  REQUIRE(is_zero_width(bv_typet{0}, ns));

  // Struct with all-empty components is zero-width.
  {
    struct_typet st({{"a", empty_typet{}}, {"b", empty_typet{}}});
    REQUIRE(is_zero_width(st, ns));
  }

  // Struct with at least one non-zero-width component is not zero-width.
  {
    struct_typet st({{"a", empty_typet{}}, {"b", signedbv_typet{32}}});
    REQUIRE_FALSE(is_zero_width(st, ns));
  }

  // Array of empty type is zero-width regardless of size — the predicate
  // deliberately ignores the array length, since we may still need to
  // model out-of-bounds accesses.
  {
    array_typet at_const(empty_typet{}, from_integer(2, size_type()));
    REQUIRE(is_zero_width(at_const, ns));

    array_typet at_sym(empty_typet{}, symbol_exprt{"n", size_type()});
    REQUIRE(is_zero_width(at_sym, ns));
  }

  // struct_tag_typet that resolves (via symbol table) to an empty struct
  // is zero-width — exercises the tag-following recursion.
  {
    type_symbolt empty_struct_symbol{
      "empty_struct_t",
      struct_typet({{"a", empty_typet{}}, {"b", empty_typet{}}}),
      ID_C};
    symbol_table.insert(empty_struct_symbol);

    struct_tag_typet stag{empty_struct_symbol.name};
    REQUIRE(is_zero_width(stag, ns));
  }

  // c_enum_tag_typet recurses into the underlying c_enum_typet, which
  // recurses into its subtype. A regular C enum (signed int subtype)
  // is not zero-width. (Behaviour changed in this PR — the predicate
  // previously fell through to `return false` for any tag kind other
  // than struct/union, which happened to give the correct answer for
  // this case but was an unprincipled coincidence.)
  {
    c_enum_typet enum_signed_int{signed_int_type()};
    type_symbolt enum_symbol{"my_enum_t", enum_signed_int, ID_C};
    symbol_table.insert(enum_symbol);

    c_enum_tag_typet etag{enum_symbol.name};
    REQUIRE_FALSE(is_zero_width(etag, ns));
  }

  // Hypothetical zero-width c_enum: subtype is zero-width, so the
  // resolved enum is too. Without this PR's added arm the predicate
  // would have returned false here.
  {
    c_enum_typet enum_empty{empty_typet{}};
    type_symbolt zw_enum_symbol{"zero_width_enum_t", enum_empty, ID_C};
    symbol_table.insert(zw_enum_symbol);

    c_enum_tag_typet zw_etag{zw_enum_symbol.name};
    REQUIRE(is_zero_width(zw_etag, ns));

    // The unwrapped c_enum_typet itself also recurses into its subtype.
    REQUIRE(is_zero_width(enum_empty, ns));
  }
}
