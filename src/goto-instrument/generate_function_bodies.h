/*******************************************************************\

Module: Replace bodies of goto functions

Author: Diffblue Ltd.

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_GENERATE_FUNCTION_BODIES_H
#define CPROVER_GOTO_PROGRAMS_GENERATE_FUNCTION_BODIES_H

#include <memory>
#include <regex>

#include <ansi-c/c_object_factory_parameters.h>
#include <goto-programs/goto_function.h>
#include <goto-programs/goto_model.h>
#include <util/cmdline.h>
#include <util/message.h>
#include <util/std_code.h>
#include <util/std_types.h>

/// Base class for replace_function_body implementations
class generate_function_bodiest
{
protected:
  /// Produce a body for the passed function
  /// At this point the body of function is always empty,
  /// and all function parameters have identifiers
  /// \param function: whose body to generate
  /// \param symbol_table: of the current goto program
  /// \param function_name: Identifier of function
  virtual void generate_function_body_impl(
    goto_functiont &function,
    const symbol_tablet &symbol_table,
    const irep_idt &function_name) const = 0;

public:
  virtual ~generate_function_bodiest() = default;

  /// Replace the function body with one based on the replace_function_body
  /// class being used.
  /// \param function: whose body to replace
  /// \param symbol_table: of the current goto program
  /// \param function_name: Identifier of function
  void generate_function_body(
    goto_functiont &function,
    symbol_tablet &symbol_table,
    const irep_idt &function_name) const;

private:
  /// Generate parameter names for unnamed parameters.
  /// CBMC expect functions to have parameter names
  /// if they are called and have a body
  void generate_parameter_names(
    goto_functiont &function,
    symbol_tablet &symbol_table,
    const irep_idt &function_name) const;
};

std::unique_ptr<generate_function_bodiest> generate_function_bodies_factory(
  const std::string &options,
  const c_object_factory_parameterst &object_factory_parameters,
  const symbol_tablet &symbol_table,
  message_handlert &message_handler);

void generate_function_bodies(
  const std::regex &functions_regex,
  const generate_function_bodiest &generate_function_body,
  goto_modelt &model,
  message_handlert &message_handler);

// clang-format off
#define OPT_REPLACE_FUNCTION_BODY \
  "(generate-function-body):" \
  "(generate-function-body-options):"

#define HELP_REPLACE_FUNCTION_BODY \
  " --generate-function-body <regex>\n" \
  /* NOLINTNEXTLINE(whitespace/line_length) */ \
  "                              Generate bodies for functions matching regex\n" \
  " --generate-function-body-options <option>\n" \
  "                              One of assert-false, assume-false,\n" \
  /* NOLINTNEXTLINE(whitespace/line_length) */ \
  "                              nondet-return, assert-false-assume-false and\n" \
  "                              havoc[,params:<regex>][,globals:<regex>]\n" \
  "                              (default: nondet-return)"
// clang-format on

#endif // CPROVER_GOTO_PROGRAMS_GENERATE_FUNCTION_BODIES_H
