/*******************************************************************\

Module: Unit tests for expr_skeleton

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

#include <testing-utils/use_catch.h>

#include <goto-symex/expr_skeleton.h>
#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/std_expr.h>

SCENARIO("expr skeleton", "[core][goto-symex][symex-assign][expr-skeleton]")
{
  const signedbv_typet int_type{32};
  const array_typet array_type{int_type, from_integer(2, size_type())};
  const symbol_exprt foo_a{"foo", array_type};
  const symbol_exprt foo_s{"foo", struct_typet{{{"field1", array_type}}}};

  GIVEN("Skeletons `☐`, `☐[index]` and `☐.field1`")
  {
    const expr_skeletont empty_skeleton;
    const expr_skeletont index_skeleton = expr_skeletont::remove_op0(
      index_exprt{array_exprt{{}, array_type}, from_integer(1, size_type())});
    const expr_skeletont member_skeleton =
      expr_skeletont::remove_op0(member_exprt{
        symbol_exprt{"struct1", struct_typet{{{"field1", array_type}}}},
        "field1",
        array_type});
    THEN(
      "Applying the skeletons to `foo` gives `foo`, `foo[index]` and "
      "`foo.field1` respectively")
    {
      REQUIRE(empty_skeleton.apply(foo_a) == foo_a);
      REQUIRE(
        index_skeleton.apply(foo_a) ==
        index_exprt{foo_a, from_integer(1, size_type()), int_type});
      REQUIRE(
        member_skeleton.apply(foo_s) ==
        member_exprt(foo_s, "field1", array_type));
    }
    THEN(
      "The composition of `☐[index]` with `☐.field1` applied to `foo` gives "
      "`foo.field1[index]`")
    {
      const expr_skeletont composition =
        index_skeleton.compose(member_skeleton);
      REQUIRE(
        composition.apply(foo_s) == index_exprt{
                                      member_exprt(foo_s, "field1", array_type),
                                      from_integer(1, size_type()),
                                      int_type});
    }
    THEN(
      "The composition of `☐[index]` with `☐` applied to `foo` gives "
      "`foo[index]`")
    {
      const expr_skeletont composition = index_skeleton.compose(empty_skeleton);
      REQUIRE(
        composition.apply(foo_a) ==
        index_exprt{foo_a, from_integer(1, size_type()), int_type});
    }
  }
}
