// Author: Diffblue Ltd.

#include <util/c_types.h>
#include <util/pointer_expr.h>
#include <util/pointer_predicates.h>

#include <testing-utils/invariant.h>
#include <testing-utils/use_catch.h>

TEST_CASE("pointer_offset_exprt", "[core][util]")
{
  const exprt pointer = symbol_exprt{"foo", pointer_type(void_type())};
  const pointer_offset_exprt pointer_offset{pointer, signed_size_type()};
  SECTION("Is equivalent to free function.")
  {
    CHECK(::pointer_offset(pointer) == pointer_offset);
  }
  SECTION("Result type")
  {
    CHECK(pointer_offset.type() == signed_size_type());
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
