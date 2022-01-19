/*******************************************************************\

Module: Unit tests for java_trace_validation

Author: Diffblue Ltd.

\*******************************************************************/

#include <goto-programs/goto_trace.h>

#include <java_bytecode/java_trace_validation.h>
#include <java_bytecode/java_types.h>

#include <testing-utils/message.h>
#include <testing-utils/use_catch.h>

#include <util/byte_operators.h>
#include <util/pointer_expr.h>
#include <util/symbol_table.h>

TEST_CASE("java trace validation", "[core][java_trace_validation]")
{
  const exprt plain_expr = exprt();
  const exprt expr_with_data = exprt("id", java_int_type());
  const symbol_exprt valid_symbol_expr = symbol_exprt("id", java_int_type());
  const symbol_exprt invalid_symbol_expr = symbol_exprt(java_int_type());
  const member_exprt valid_member =
    member_exprt(valid_symbol_expr, "member", java_int_type());
  const member_exprt invalid_member =
    member_exprt(plain_expr, "member", java_int_type());
  const constant_exprt invalid_constant = constant_exprt("", java_int_type());
  const constant_exprt valid_constant = constant_exprt("0", java_int_type());
  const index_exprt valid_index = index_exprt(
    symbol_exprt("id", array_typet(typet(), nil_exprt())), valid_constant);
  const index_exprt index_plain =
    index_exprt(exprt(ID_nil, array_typet(typet(), nil_exprt())), exprt());
  const byte_extract_exprt byte_little_endian = byte_extract_exprt(
    ID_byte_extract_little_endian, exprt(), exprt(), typet());
  const byte_extract_exprt byte_big_endian =
    byte_extract_exprt(ID_byte_extract_big_endian, exprt(), exprt(), typet());
  const address_of_exprt valid_address = address_of_exprt(valid_symbol_expr);
  const address_of_exprt invalid_address = address_of_exprt(exprt());
  const struct_exprt struct_plain =
    struct_exprt(std::vector<exprt>(), java_int_type());
  const std::vector<exprt> struct_ops = {valid_constant};
  const struct_exprt valid_struct = struct_exprt(struct_ops, java_int_type());
  const std::vector<exprt> struct_ops_nested = {valid_struct, valid_constant};
  const struct_exprt valid_nested_struct =
    struct_exprt(struct_ops_nested, java_int_type());
  const array_exprt array_plain =
    array_exprt(std::vector<exprt>(), array_typet(java_int_type(), exprt()));
  const array_list_exprt array_list_plain = array_list_exprt(
    std::vector<exprt>(), array_typet(java_int_type(), exprt()));
  const plus_exprt plus_expr = plus_exprt(valid_constant, valid_constant);

  const auto make_test_trace = [](const exprt &lhs, const exprt &rhs) {
    goto_tracet trace;
    goto_trace_stept step;
    step.type = goto_trace_stept::typet::ASSIGNMENT;
    step.full_lhs = lhs;
    step.full_lhs_value = rhs;
    trace.add_step(step);
    return trace;
  };

  SECTION("check_symbol_structure")
  {
    INFO("valid symbol expression")
    REQUIRE(check_symbol_structure(valid_symbol_expr));
    INFO("invalid symbol expression, missing identifier")
    REQUIRE_FALSE(check_symbol_structure(invalid_symbol_expr));
    INFO("invalid symbol expression, not a symbol")
    REQUIRE_FALSE(check_symbol_structure(plain_expr));
  }

  SECTION("get_inner_symbol_expr")
  {
    const exprt inner_symbol = exprt(exprt(valid_symbol_expr));
    const exprt inner_nonsymbol = exprt(exprt(exprt()));
    INFO("expression has an inner symbol")
    REQUIRE(get_inner_symbol_expr(inner_symbol).has_value());
    INFO("expression does not have an inner symbol")
    REQUIRE_FALSE(get_inner_symbol_expr(inner_nonsymbol).has_value());
  }

  SECTION("check_member_structure")
  {
    INFO("valid member structure")
    REQUIRE(check_member_structure(valid_member));
    INFO("invalid member structure, no symbol operand")
    REQUIRE_FALSE(check_member_structure(invalid_member));
  }

  SECTION("can_evaluate_to_constant")
  {
    INFO("symbol_exprts can be evaluated to a constant")
    REQUIRE(can_evaluate_to_constant(valid_symbol_expr));
    INFO("plus_exprts can be evaluated to a constant")
    REQUIRE(can_evaluate_to_constant(plus_expr));
    INFO("constant_exprts can be evaluated to a constant")
    REQUIRE(can_evaluate_to_constant(valid_constant));
    INFO("member_exprts cannot be evaluated to a constant")
    REQUIRE_FALSE(can_evaluate_to_constant(valid_member));
  }

  SECTION("check_index_structure")
  {
    REQUIRE(check_index_structure(valid_index));
    REQUIRE_FALSE(check_index_structure(index_plain));
  }

  SECTION("check_struct_structure")
  {
    REQUIRE_FALSE(check_struct_structure(struct_plain));
    REQUIRE(check_struct_structure(valid_struct));
    REQUIRE(check_struct_structure(valid_nested_struct));
  }

  SECTION("check_address_structure")
  {
    REQUIRE_FALSE(check_address_structure(invalid_address));
    REQUIRE(check_address_structure(valid_address));
  }

  SECTION("check_constant_structure")
  {
    REQUIRE_FALSE(check_constant_structure(invalid_constant));
    REQUIRE(check_constant_structure(valid_constant));
  }

  SECTION("valid_lhs_expr_high_level")
  {
    INFO("member_exprts are valid lhs expressions")
    REQUIRE(valid_lhs_expr_high_level(valid_member));
    INFO("symbol_exprts are valid lhs expressions")
    REQUIRE(valid_lhs_expr_high_level(valid_symbol_expr));
    INFO("index_exprts are valid lhs expressions")
    REQUIRE(valid_lhs_expr_high_level(index_plain));
    INFO("byte_extract_exprts little endian are valid lhs expressions")
    REQUIRE(valid_lhs_expr_high_level(byte_little_endian));
    INFO("byte_extract_exprts big endian are valid lhs expressions")
    REQUIRE(valid_lhs_expr_high_level(byte_big_endian));
    INFO("address_of_exprts are not valid lhs expressions, for example")
    REQUIRE_FALSE(valid_lhs_expr_high_level(valid_address));
  }

  SECTION("valid_rhs_expr_high_level")
  {
    INFO("symbol_exprts are valid rhs expressions")
    REQUIRE(valid_rhs_expr_high_level(valid_symbol_expr));
    INFO("address_of_exprts are valid rhs expressions")
    REQUIRE(valid_rhs_expr_high_level(valid_address));
    INFO("struct_exprts are valid rhs expressions")
    REQUIRE(valid_rhs_expr_high_level(struct_plain));
    INFO("array_exprts are valid rhs expressions")
    REQUIRE(valid_rhs_expr_high_level(array_plain));
    INFO("array_list_exprts are valid rhs expressions")
    REQUIRE(valid_rhs_expr_high_level(array_list_plain));
    INFO("constant_exprts are valid rhs expressions")
    REQUIRE(valid_rhs_expr_high_level(valid_constant));
    INFO("byte_extract_exprts are valid rhs expressions")
    REQUIRE(valid_rhs_expr_high_level(byte_little_endian));
    INFO("byte_extract_exprts are valid rhs expressions")
    REQUIRE(valid_rhs_expr_high_level(byte_big_endian));
    INFO("member_exprts are not valid rhs expressions, for example")
    REQUIRE_FALSE(valid_rhs_expr_high_level(valid_member));
    INFO("index_exprts are not are valid rhs expressions, for example")
    REQUIRE_FALSE(valid_rhs_expr_high_level(index_plain));
  }

  SECTION("check_trace_assumptions pass with a valid step")
  {
    goto_tracet trace = make_test_trace(valid_symbol_expr, valid_constant);
    REQUIRE_NOTHROW(check_trace_assumptions(
      trace,
      namespacet(symbol_tablet()),
      messaget(null_message_handler),
      true,
      validation_modet::EXCEPTION));
  }

  SECTION("check_trace_assumptions fail with an invalid steps - invalid lhs")
  {
    goto_tracet trace = make_test_trace(invalid_symbol_expr, valid_constant);
    REQUIRE_THROWS_AS(
      check_trace_assumptions(
        trace,
        namespacet(symbol_tablet()),
        messaget(null_message_handler),
        true,
        validation_modet::EXCEPTION),
      incorrect_goto_program_exceptiont);
  }

  SECTION(
    "check_trace_assumptions fail with an invalid steps - invalid lhs member")
  {
    goto_tracet trace = make_test_trace(invalid_member, valid_constant);
    REQUIRE_THROWS_AS(
      check_trace_assumptions(
        trace,
        namespacet(symbol_tablet()),
        messaget(null_message_handler),
        true,
        validation_modet::EXCEPTION),
      incorrect_goto_program_exceptiont);
  }

  SECTION(
    "check_trace_assumptions fail with an invalid steps - invalid lhs index")
  {
    goto_tracet trace = make_test_trace(index_plain, valid_constant);
    REQUIRE_THROWS_AS(
      check_trace_assumptions(
        trace,
        namespacet(symbol_tablet()),
        messaget(null_message_handler),
        true,
        validation_modet::EXCEPTION),
      incorrect_goto_program_exceptiont);
  }

  SECTION(
    "check_trace_assumptions fail with an invalid steps - invalid lhs byte "
    "extract")
  {
    goto_tracet trace = make_test_trace(byte_little_endian, valid_constant);
    REQUIRE_THROWS_AS(
      check_trace_assumptions(
        trace,
        namespacet(symbol_tablet()),
        messaget(null_message_handler),
        true,
        validation_modet::EXCEPTION),
      incorrect_goto_program_exceptiont);
  }

  SECTION("check_trace_assumptions fail with an invalid steps - invalid rhs")
  {
    goto_tracet trace = make_test_trace(valid_symbol_expr, valid_member);
    REQUIRE_THROWS_AS(
      check_trace_assumptions(
        trace,
        namespacet(symbol_tablet()),
        messaget(null_message_handler),
        true,
        validation_modet::EXCEPTION),
      incorrect_goto_program_exceptiont);
  }

  SECTION(
    "check_trace_assumptions fail with an invalid steps - invalid rhs "
    "address_of")
  {
    goto_tracet trace = make_test_trace(valid_symbol_expr, invalid_address);
    REQUIRE_THROWS_AS(
      check_trace_assumptions(
        trace,
        namespacet(symbol_tablet()),
        messaget(null_message_handler),
        true,
        validation_modet::EXCEPTION),
      incorrect_goto_program_exceptiont);
  }

  SECTION(
    "check_trace_assumptions fail with an invalid steps - invalid rhs symbol")
  {
    goto_tracet trace = make_test_trace(valid_symbol_expr, invalid_symbol_expr);
    REQUIRE_THROWS_AS(
      check_trace_assumptions(
        trace,
        namespacet(symbol_tablet()),
        messaget(null_message_handler),
        true,
        validation_modet::EXCEPTION),
      incorrect_goto_program_exceptiont);
  }

  SECTION(
    "check_trace_assumptions fail with an invalid steps - invalid rhs struct")
  {
    goto_tracet trace = make_test_trace(valid_symbol_expr, struct_plain);
    REQUIRE_THROWS_AS(
      check_trace_assumptions(
        trace,
        namespacet(symbol_tablet()),
        messaget(null_message_handler),
        true,
        validation_modet::EXCEPTION),
      incorrect_goto_program_exceptiont);
  }

  SECTION(
    "check_trace_assumptions fail with an invalid steps - invalid rhs byte "
    "extract")
  {
    goto_tracet trace = make_test_trace(valid_symbol_expr, byte_little_endian);
    REQUIRE_THROWS_AS(
      check_trace_assumptions(
        trace,
        namespacet(symbol_tablet()),
        messaget(null_message_handler),
        true,
        validation_modet::EXCEPTION),
      incorrect_goto_program_exceptiont);
  }
}
