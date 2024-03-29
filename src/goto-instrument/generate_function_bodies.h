/*******************************************************************\

Module: Replace bodies of goto functions

Author: Diffblue Ltd.

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_GENERATE_FUNCTION_BODIES_H
#define CPROVER_GOTO_PROGRAMS_GENERATE_FUNCTION_BODIES_H

#include <memory>
#include <regex>

#include <util/irep.h>

class goto_functiont;
class goto_modelt;
class message_handlert;
class symbol_tablet;
struct c_object_factory_parameterst;

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
    symbol_tablet &symbol_table,
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

/// Generate a clone of \p function_name (labelled with \p call_site_id) and
///   instantiate its body with selective havocing of its parameters.
/// \param function_name: The function whose body should be generated
/// \param call_site_id: the number of the call site
/// \param generate_function_body: the previously constructed body generator
/// \param model: the goto-model to be modified
/// \param message_handler: the message-handler
void generate_function_bodies(
  const std::string &function_name,
  const std::string &call_site_id,
  const generate_function_bodiest &generate_function_body,
  goto_modelt &model,
  message_handlert &message_handler);

#define OPT_REPLACE_FUNCTION_BODY \
  "(generate-function-body):" \
  "(generate-havocing-body):" \
  "(generate-function-body-options):"

#define HELP_REPLACE_FUNCTION_BODY                                             \
  " {y--generate-function-body} {uregex} \t "                                  \
  "generate bodies for functions matching {uregex}\n"                          \
  " {y--generate-havocing-body} <option> "                                     \
  "{ufun_name},{yparams}:{up1};{up2};.. \t "                                   \
  "generate havocing body\n"                                                   \
  " {y--generate-havocing-body} <option> "                                     \
  "{ufun_name}[,{ucall-site-id},{yparams}:{up1};{up2};..]+ \t "                \
  "generate havocing body\n"                                                   \
  " {y--generate-function-body-options} {uoption} \t "                         \
  "One of {yassert-false}, {yassume-false}, {ynondet-return}, "                \
  "{yassert-false-assume-false} and "                                          \
  "{yhavoc}[,{yparams}:{uregex}][,{yglobals}:{uregex}]"                        \
  "[,{yparams}:{up1};{up2};..] (default: {ynondet-return})\n"

#endif // CPROVER_GOTO_PROGRAMS_GENERATE_FUNCTION_BODIES_H
