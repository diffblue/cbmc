/*******************************************************************\

Module: Replace Runtime Checks

Author: diffblue

\*******************************************************************/

/// \file
/// Replace Runtime Checks

#include <util/cprover_prefix.h>
#include <util/prefix.h>
#include <util/string_constant.h>

#include <langapi/language.h>
#include <langapi/mode.h>

#include "replace_runtime_checks.h"

/// A simple pass that replace each call to a function with name:
/// __CPROVER_X_`check-name` with a user-specified sequence of instructions. The
/// language X can also by specified by the user via
/// `--runtime-checks-language`. The function is expected to take one argument
/// (the condition to be checked) and this condition is either asserted or
/// assumed (or both). The `check-name` is then included in the assertion
/// description (via source-location).
struct runtime_checks_replacert
{
public:
  explicit runtime_checks_replacert(
    goto_modelt &goto_model,
    const namespacet &ns,
    const std::string &language_id)
    : goto_model(goto_model),
      ns(ns),
      language_id(language_id),
      common_prefix(std::string{CPROVER_PREFIX} + language_id)
  {
  }

  void replace_with(const std::string &replace_option);

private:
  goto_modelt &goto_model;
  const namespacet &ns;
  const std::string language_id;
  const std::string common_prefix;
  irep_idt mode;

  enum class replace_typet
  {
    assert_only,
    assume_only,
    assert_then_assume
  };

  enum class runtime_check_typet
  {
    overflow,
    range,
    division_by_zero
  };

  void replace_by_option(
    const exprt &condition,
    goto_programt &goto_program,
    goto_programt::targett instruction,
    const std::string &function_name,
    const std::string &replace_option);

  runtime_check_typet get_check_type(const std::string &function_name) const
  {
    if(function_name == common_prefix + "_Overflow_Check")
      return runtime_check_typet::overflow;
    if(function_name == common_prefix + "_Range_Check")
      return runtime_check_typet::range;
    if(function_name == common_prefix + "_Division_Check")
      return runtime_check_typet::division_by_zero;
    throw invalid_source_file_exceptiont{"unsupported " + language_id +
                                         " check: " + function_name};
  }

  replace_typet get_replace_type(const std::string &replace_option) const
  {
    if(replace_option == "assert-first-arg")
      return replace_typet::assert_only;
    if(replace_option == "assume-first-arg")
      return replace_typet::assume_only;
    if(replace_option == "assert-then-assume-first-arg")
      return replace_typet::assert_then_assume;
    throw invalid_command_line_argument_exceptiont{
      "unknown " + language_id + " check replacement option" + replace_option,
      "--replace-runtime-checks"};
  }

  friend std::string to_string(runtime_check_typet type)
  {
    switch(type)
    {
    case runtime_check_typet::overflow:
      return "Overflow";
    case runtime_check_typet::range:
      return "Range";
    case runtime_check_typet::division_by_zero:
      return "Division by zero";
    }
    UNREACHABLE;
  }
};

void runtime_checks_replacert::replace_with(const std::string &replace_option)
{
  auto &goto_functions = goto_model.goto_functions;
  for(auto &goto_function_pair : goto_functions.function_map)
  {
    goto_programt &function_body = goto_function_pair.second.body;
    for(goto_programt::targett instruction = function_body.instructions.begin();
        instruction != function_body.instructions.end();
        ++instruction)
    {
      if(instruction->is_function_call())
      {
        const auto &function_call = instruction->get_function_call();
        const auto &function = function_call.function();

        const auto &function_name =
          id2string(to_symbol_expr(function).get_identifier());
        const auto &function_symbol = ns.lookup(function_name);
        mode = function_symbol.mode;
        if(has_prefix(function_name, common_prefix))
        {
          const auto &function_arguments = function_call.arguments();
          CHECK_RETURN(!function_arguments.empty());

          replace_by_option(
            *function_arguments.begin(),
            function_body,
            instruction,
            function_name,
            replace_option);
        }
      }
    }
  }
}

void runtime_checks_replacert::replace_by_option(
  const exprt &condition,
  goto_programt &goto_program,
  goto_programt::targett instruction,
  const std::string &function_name,
  const std::string &replace_option)
{
  exprt boolean_condition = condition;
  while(boolean_condition.id() == ID_typecast)
    boolean_condition = to_typecast_expr(boolean_condition).op();
  CHECK_RETURN(boolean_condition.type().id() == ID_bool);

  source_locationt commented_source_location = instruction->source_location;
  std::string source_expr_string;
  get_language_from_mode(mode)->from_expr(
    boolean_condition, source_expr_string, ns);
  commented_source_location.set_comment(
    language_id + " " + to_string(get_check_type(function_name)) + " check " +
    source_expr_string);

  switch(get_replace_type(replace_option))
  {
  case replace_typet::assert_then_assume:
  {
    auto after_assert = goto_program.insert_after(
      instruction,
      goto_programt::make_assertion(
        boolean_condition, commented_source_location));
    goto_program.insert_after(
      after_assert,
      goto_programt::make_assumption(
        boolean_condition, commented_source_location));
    break;
  }
  case replace_typet::assert_only:
    goto_program.insert_after(
      instruction,
      goto_programt::make_assertion(
        boolean_condition, commented_source_location));
    break;
  case replace_typet::assume_only:
    goto_program.insert_after(
      instruction,
      goto_programt::make_assumption(
        boolean_condition, commented_source_location));
    break;
  }

  auto skip_instruction = goto_programt::make_skip();
  instruction->swap(skip_instruction);
}

void replace_runtime_checks(
  goto_modelt &goto_model,
  const std::string &replace_option,
  const std::string &language_id)
{
  const namespacet ns{goto_model.symbol_table};
  runtime_checks_replacert runtime_checks{goto_model, ns, language_id};
  runtime_checks.replace_with(replace_option);
  goto_model.goto_functions.update();
}
