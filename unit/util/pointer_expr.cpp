// Author: Diffblue Ltd.

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/cmdline.h>
#include <util/config.h>
#include <util/pointer_expr.h>
#include <util/pointer_predicates.h>
#include <util/std_expr.h>
#include <util/std_types.h>

#include <testing-utils/empty_namespace.h>
#include <testing-utils/invariant.h>
#include <testing-utils/use_catch.h>

TEST_CASE("pointer_offset_exprt", "[core][util]")
{
  const exprt pointer = symbol_exprt{"foo", pointer_type(void_type())};
  const pointer_offset_exprt pointer_offset{pointer, size_type()};
  SECTION("Is equivalent to free function.")
  {
    CHECK(::pointer_offset(pointer) == pointer_offset);
  }
  SECTION("Result type")
  {
    CHECK(pointer_offset.type() == size_type());
  }
  SECTION("Pointer operand accessor")
  {
    CHECK(pointer_offset.pointer() == pointer);
  }
  SECTION("Downcasting")
  {
    const exprt &upcast = pointer_offset;
    CHECK(expr_try_dynamic_cast<pointer_offset_exprt>(pointer_offset));
    CHECK_FALSE(expr_try_dynamic_cast<pointer_object_exprt>(upcast));
    SECTION("Validation")
    {
      SECTION("Invalid operand")
      {
        unary_exprt invalid_type = pointer_offset;
        invalid_type.op().type() = bool_typet{};
        const cbmc_invariants_should_throwt invariants_throw;
        REQUIRE_THROWS_MATCHES(
          expr_try_dynamic_cast<pointer_offset_exprt>(invalid_type),
          invariant_failedt,
          invariant_failure_containing(
            "pointer_offset must have pointer-typed operand"));
      }
      SECTION("Missing operand")
      {
        exprt missing_operand = pointer_offset;
        missing_operand.operands().clear();
        const cbmc_invariants_should_throwt invariants_throw;
        REQUIRE_THROWS_MATCHES(
          expr_try_dynamic_cast<pointer_offset_exprt>(missing_operand),
          invariant_failedt,
          invariant_failure_containing("pointer_offset must have one operand"));
      }
      SECTION("Too many operands")
      {
        exprt two_operands = pointer_offset;
        two_operands.operands().push_back(pointer);
        const cbmc_invariants_should_throwt invariants_throw;
        REQUIRE_THROWS_MATCHES(
          expr_try_dynamic_cast<pointer_offset_exprt>(two_operands),
          invariant_failedt,
          invariant_failure_containing("pointer_offset must have one operand"));
      }
    }
  }
}

TEST_CASE("pointer_object_exprt", "[core][util]")
{
  const exprt pointer = symbol_exprt{"foo", pointer_type(void_type())};
  const pointer_object_exprt pointer_object{pointer, size_type()};
  SECTION("Is equivalent to free function.")
  {
    CHECK(::pointer_object(pointer) == pointer_object);
  }
  SECTION("Result type")
  {
    CHECK(pointer_object.type() == size_type());
  }
  SECTION("Pointer operand accessor")
  {
    CHECK(pointer_object.pointer() == pointer);
  }
  SECTION("Downcasting")
  {
    const exprt &upcast = pointer_object;
    CHECK(expr_try_dynamic_cast<pointer_object_exprt>(pointer_object));
    CHECK_FALSE(expr_try_dynamic_cast<pointer_offset_exprt>(upcast));
    SECTION("Validation")
    {
      SECTION("Invalid operand")
      {
        unary_exprt invalid_type = pointer_object;
        invalid_type.op().type() = bool_typet{};
        const cbmc_invariants_should_throwt invariants_throw;
        REQUIRE_THROWS_MATCHES(
          expr_try_dynamic_cast<pointer_object_exprt>(invalid_type),
          invariant_failedt,
          invariant_failure_containing(
            "pointer_object must have pointer-typed operand"));
      }
      SECTION("Missing operand")
      {
        exprt missing_operand = pointer_object;
        missing_operand.operands().clear();
        const cbmc_invariants_should_throwt invariants_throw;
        REQUIRE_THROWS_MATCHES(
          expr_try_dynamic_cast<pointer_object_exprt>(missing_operand),
          invariant_failedt,
          invariant_failure_containing("pointer_object must have one operand"));
      }
      SECTION("Too many operands")
      {
        exprt two_operands = pointer_object;
        two_operands.operands().push_back(pointer);
        const cbmc_invariants_should_throwt invariants_throw;
        REQUIRE_THROWS_MATCHES(
          expr_try_dynamic_cast<pointer_object_exprt>(two_operands),
          invariant_failedt,
          invariant_failure_containing("pointer_object must have one operand"));
      }
    }
  }
}

TEST_CASE("object_size_exprt", "[core][util]")
{
  const exprt pointer = symbol_exprt{"foo", pointer_type(void_type())};
  const object_size_exprt object_size{pointer, size_type()};
  SECTION("Is equivalent to free function.")
  {
    CHECK(::object_size(pointer) == object_size);
  }
  SECTION("Result type")
  {
    CHECK(object_size.type() == size_type());
  }
  SECTION("Pointer operand accessor")
  {
    CHECK(object_size.pointer() == pointer);
  }
  SECTION("Downcasting")
  {
    const exprt &upcast = object_size;
    CHECK(expr_try_dynamic_cast<object_size_exprt>(upcast));
    CHECK_FALSE(expr_try_dynamic_cast<pointer_object_exprt>(upcast));
    SECTION("Validation")
    {
      SECTION("Invalid operand")
      {
        unary_exprt invalid_type = object_size;
        invalid_type.op().type() = bool_typet{};
        const cbmc_invariants_should_throwt invariants_throw;
        REQUIRE_THROWS_MATCHES(
          expr_try_dynamic_cast<object_size_exprt>(invalid_type),
          invariant_failedt,
          invariant_failure_containing(
            "Object size expression must have pointer typed operand."));
      }
      SECTION("Missing operand")
      {
        exprt missing_operand = object_size;
        missing_operand.operands().clear();
        const cbmc_invariants_should_throwt invariants_throw;
        REQUIRE_THROWS_MATCHES(
          expr_try_dynamic_cast<object_size_exprt>(missing_operand),
          invariant_failedt,
          invariant_failure_containing(
            "Object size expression must have one operand"));
      }
      SECTION("Too many operands")
      {
        exprt two_operands = object_size;
        two_operands.operands().push_back(pointer);
        const cbmc_invariants_should_throwt invariants_throw;
        REQUIRE_THROWS_MATCHES(
          expr_try_dynamic_cast<object_size_exprt>(two_operands),
          invariant_failedt,
          invariant_failure_containing(
            "Object size expression must have one operand"));
      }
    }
  }
}

TEST_CASE(
  "object_descriptor_exprt::build with uncomputable member offset",
  "[core][util]")
{
  // size_of_expr needs a configured architecture (char width, etc.).
  cmdlinet cmdline;
  config.set(cmdline);

  const signedbv_typet int_type{32};

  // INNER { int a[]; int x; }: the leading member 'a' is an incomplete array,
  // so size_of_expr(a) is empty and member_offset_expr(x) returns nullopt,
  // which is what drives the fallback under test.
  struct_typet inner_type;
  inner_type.components().emplace_back("a", array_typet{int_type, nil_exprt{}});
  inner_type.components().emplace_back("x", int_type);

  // OUTER { int pad; INNER inner; }: the leading 'pad' means descending into
  // o.inner accumulates a non-zero offset before the fallback fires, so this
  // also guards against the offset being double-counted.
  struct_typet outer_type;
  outer_type.components().emplace_back("pad", int_type);
  outer_type.components().emplace_back("inner", inner_type);

  const symbol_exprt o{"o", outer_type};
  const member_exprt inner_access{o, "inner", inner_type};
  const member_exprt x_access{inner_access, "x", int_type};

  object_descriptor_exprt odt;
  odt.build(x_access, empty_namespace);

  // The member access itself becomes the (precise) object, and the offset is
  // reset to zero -- not left at the offset of 'inner' accumulated while
  // descending into the struct operand.
  CHECK(odt.object() == x_access);
  CHECK(odt.offset() == from_integer(0, c_index_type()));
}
