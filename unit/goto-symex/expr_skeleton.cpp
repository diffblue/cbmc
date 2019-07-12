/*******************************************************************\

Module: Unit tests for expr_skeleton

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

#include <testing-utils/message.h>
#include <testing-utils/use_catch.h>

#include <goto-symex/expr_skeleton.h>
#include <testing-utils/expr_query.h>
#include <util/arith_tools.h>
#include <util/byte_operators.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/namespace.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

SCENARIO("expr skeleton", "[core][goto-symex][symex-assign][expr-skeleton]")
{
  const symbol_exprt foo{"foo", typet{}};
  GIVEN("Skeletons `☐`, `☐[index]` and `☐.field1`")
  {
    const expr_skeletont empty_skeleton{foo.type()};
    const signedbv_typet int_type{32};
    const expr_skeletont index_skeleton =
      expr_skeletont::remove_op0(index_exprt{
        array_exprt{array_typet{int_type, from_integer(2, size_type())}},
        from_integer(1, size_type())});
    const expr_skeletont member_skeleton = expr_skeletont::remove_op0(
      member_exprt{symbol_exprt{"struct1", typet{}}, "field1", int_type});
    THEN(
      "Applying the skeletons to `foo` gives `foo`, `foo[index]` and "
      "`foo.field1` respectively")
    {
      REQUIRE(empty_skeleton.apply(foo) == foo);
      REQUIRE(
        index_skeleton.apply(foo) ==
        index_exprt{foo, from_integer(1, size_type()), int_type});
      REQUIRE(
        member_skeleton.apply(foo) == member_exprt{foo, "field1", int_type});
    }
    THEN(
      "The composition of `☐[index]` with `☐.field1` applied to `foo` gives "
      "`foo.field1[index]`")
    {
      const expr_skeletont composition =
        index_skeleton.compose(member_skeleton);
      REQUIRE(
        composition.apply(foo) ==
        index_exprt{member_exprt{foo, "field1", int_type},
                    from_integer(1, size_type()),
                    int_type});
    }
    THEN(
      "The composition of `☐[index]` with `☐` applied to `foo` gives "
      "`foo[index]`")
    {
      const expr_skeletont composition = index_skeleton.compose(empty_skeleton);
      REQUIRE(
        composition.apply(foo) ==
        index_exprt{foo, from_integer(1, size_type()), int_type});
    }
  }
}

SCENARIO(
  "revert byte extract",
  "[core][goto-symex][symex-assign][expr-skeleton]")
{
  config.ansi_c.pointer_width = config.ansi_c.int_width = 32;
  config.ansi_c.endianness = configt::ansi_ct::endiannesst::IS_LITTLE_ENDIAN;
  const signedbv_typet int_type{32};
  const struct_typet my_struct{{struct_typet::componentt{"field1", int_type},
                                struct_typet::componentt{"field2", int_type}}};
  const array_typet struct_array_type{my_struct, from_integer(10, size_type())};
  const symbol_exprt foo{"foo", struct_array_type};
  const symbol_exprt bar{"bar", my_struct};
  const symbol_exprt baz{"baz", int_type};
  symbol_tablet symbol_table;
  namespacet ns{symbol_table};
  GIVEN("Skeleton `☐[2].field2`")
  {
    const expr_skeletont skeleton = [&] {
      const exprt skeleton_with_foo = member_exprt{
        index_exprt{foo, from_integer(2, size_type())}, "field2", int_type};
      return expr_skeletont::remove_op0(skeleton_with_foo)
        .compose(expr_skeletont::remove_op0(skeleton_with_foo.op0()));
    }();
    THEN(
      "Reverting byte_extract with offset = 16, type = my_struct gives "
      "skeleton `☐.field2` because `☐[2]` is equivalent to an offset of 16")
    {
      expr_skeletont s = expr_skeletont::revert_byte_extract(
        skeleton, from_integer(16, size_type()), my_struct, ns);
      REQUIRE(s.apply(bar) == member_exprt{bar, "field2", int_type});
    }
    THEN(
      "Reverting byte_extract with offset = 9, type = my_struct gives a "
      "skeleton s `byte_extract(☐, 7).field2`")
    {
      expr_skeletont s = expr_skeletont::revert_byte_extract(
        skeleton, from_integer(9, size_type()), my_struct, ns);
      auto query = make_query(s.apply(bar)).as<member_exprt>();
      REQUIRE(query.get().get_component_name() == "field2");
      REQUIRE(
        query[0].as<byte_extract_exprt>().get().offset() ==
        from_integer(7, size_type()));
    }
    THEN(
      "Reverting byte_extract with offset = 20, type = int gives "
      "skeleton `☐` because `☐[2].field2` is equivalent to an offset of 20")
    {
      expr_skeletont s = expr_skeletont::revert_byte_extract(
        skeleton, from_integer(20, size_type()), int_type, ns);
      REQUIRE(s.apply(baz) == baz);
    }
    THEN(
      "Reverting byte_extract with offset = 18, type = int gives "
      "skeleton `byte_extract(☐, 2)`")
    {
      expr_skeletont s = expr_skeletont::revert_byte_extract(
        skeleton, from_integer(18, size_type()), int_type, ns);
      auto query = make_query(s.apply(baz)).as<byte_extract_exprt>();
      REQUIRE(query.get().offset() == from_integer(2, size_type()));
    }
    THEN(
      "Reverting byte_extract with offset = 16, type = int gives "
      "skeleton `byte_extract(☐, 4)`")
    {
      expr_skeletont s = expr_skeletont::revert_byte_extract(
        skeleton, from_integer(16, size_type()), int_type, ns);
      auto query = make_query(s.apply(baz)).as<byte_extract_exprt>();
      REQUIRE(query.get().offset() == from_integer(4, size_type()));
    }
  }
  GIVEN("Skeleton `☐[2].field1`")
  {
    const expr_skeletont skeleton = [&] {
      const exprt skeleton_with_foo = member_exprt{
        index_exprt{foo, from_integer(2, size_type())}, "field1", int_type};
      return expr_skeletont::remove_op0(skeleton_with_foo)
        .compose(expr_skeletont::remove_op0(skeleton_with_foo.op0()));
    }();
    THEN(
      "Reverting byte_extract with offset = 16, type = struct_type gives "
      "skeleton `☐.field1` because `☐[2]` is equivalent to an offset of 16")
    {
      expr_skeletont s = expr_skeletont::revert_byte_extract(
        skeleton, from_integer(16, size_type()), my_struct, ns);
      auto query = make_query(s.apply(bar)).as<member_exprt>();
      REQUIRE(query.get().get_component_name() == "field1");
    }
    THEN(
      "Reverting byte_extract with offset = 16, type = int gives "
      "skeleton `☐` because `☐[2].field1` is also equivalent to an offset "
      "of 16")
    {
      expr_skeletont s = expr_skeletont::revert_byte_extract(
        skeleton, from_integer(16, size_type()), int_type, ns);
      REQUIRE(s.apply(baz) == baz);
    }
  }
}
