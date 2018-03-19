/*******************************************************************\

 Module: Unit tests for converting invokedynamic instructions into codet

 Author: Diffblue Ltd.

\*******************************************************************/

#include <testing-utils/catch.hpp>
#include <testing-utils/load_java_class.h>
#include <testing-utils/require_goto_statements.h>
#include <testing-utils/require_expr.h>
#include <testing-utils/require_type.h>
#include <testing-utils/run_test_with_compilers.h>
#include <testing-utils/require_symbol.h>

struct lambda_assignment_test_datat
{
  irep_idt lambda_variable_id;
  irep_idt lambda_interface;
  std::string lambda_interface_method_descriptor;
  irep_idt lambda_function_id;
};

void validate_lamdba_assignement(
  const symbol_tablet &symbol_table,
  const std::vector<codet> &instructions,
  const lambda_assignment_test_datat &test_data)
{
  const auto lambda_assignment =
    require_goto_statements::find_pointer_assignments(
      test_data.lambda_variable_id, instructions);

  REQUIRE(lambda_assignment.non_null_assignments.size() == 1);
  REQUIRE_FALSE(lambda_assignment.null_assignment.has_value());

  const typecast_exprt &rhs_value = require_expr::require_typecast(
    lambda_assignment.non_null_assignments[0].rhs());

  const symbol_exprt &rhs_symbol =
    require_expr::require_symbol(rhs_value.op0());

  const irep_idt &tmp_object_symbol = rhs_symbol.get_identifier();

  const auto tmp_object_assignments =
    require_goto_statements::find_pointer_assignments(
      tmp_object_symbol, instructions);

  REQUIRE(tmp_object_assignments.non_null_assignments.size() == 1);
  REQUIRE_FALSE(tmp_object_assignments.null_assignment.has_value());

  const side_effect_exprt &side_effect_expr =
    require_expr::require_side_effect_expr(
      tmp_object_assignments.non_null_assignments[0].rhs(), ID_java_new);

  const pointer_typet &lambda_temp_type =
    require_type::require_pointer(side_effect_expr.type(), {});

  const symbol_typet &lambda_implementor_type =
    require_type::require_symbol(lambda_temp_type.subtype());

  const irep_idt &tmp_class_identifier =
    lambda_implementor_type.get_identifier();

  const symbolt &lambda_implementor_type_symbol =
    require_symbol::require_symbol_exists(symbol_table, tmp_class_identifier);

  REQUIRE(lambda_implementor_type_symbol.is_type);
  const class_typet &tmp_lambda_class_type =
    require_type::require_complete_class(lambda_implementor_type_symbol.type);

  REQUIRE(tmp_lambda_class_type.has_base(test_data.lambda_interface));

  THEN("The function in the class should call the lambda method")
  {
    const irep_idt method_identifier =
      id2string(tmp_class_identifier) +
      test_data.lambda_interface_method_descriptor;
    const symbolt &method_symbol =
      require_symbol::require_symbol_exists(symbol_table, method_identifier);

    REQUIRE(method_symbol.is_function());

    const std::vector<codet> &assignments =
      require_goto_statements::get_all_statements(method_symbol.value);

    require_goto_statements::require_function_call(
      assignments, test_data.lambda_function_id);
  }
}

SCENARIO(
  "Converting invokedynamic with a local lambda",
  "[core]"
  "[lamdba][java_bytecode][java_bytecode_convert_method][!mayfail]")
{
  // NOLINTNEXTLINE(whitespace/braces)
  run_test_with_compilers([](const std::string &compiler) {
    GIVEN(
      "A class with a static lambda variables from " + compiler + " compiler.")
    {
      symbol_tablet symbol_table = load_java_class(
        "LocalLambdas",
        "./java_bytecode/java_bytecode_parser/lambda_examples/" + compiler +
          "_classes/",
        "LocalLambdas.test");

      WHEN("Inspecting the assignments of the entry function")
      {
        const std::vector<codet> &instructions =
          require_goto_statements::get_all_statements(
            symbol_table.lookup_ref("java::LocalLambdas.test:()V").value);

        const std::string function_prefix = "java::LocalLambdas.test:()V";

        THEN(
          "The local variable should be assigned a temp object implementing "
          "SimpleLambda")
        {
          lambda_assignment_test_datat test_data;
          test_data.lambda_variable_id = function_prefix + "::11::simpleLambda";

          test_data.lambda_interface = "java::SimpleLambda";
          test_data.lambda_interface_method_descriptor = ".Execute:()V";
          test_data.lambda_function_id = "java::LocalLambdas.pretendLambda:()V";
          validate_lamdba_assignement(symbol_table, instructions, test_data);
        }
      }
    }
  });
}
