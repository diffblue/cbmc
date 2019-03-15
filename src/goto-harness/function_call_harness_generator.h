/******************************************************************\

Module: harness generator for functions

Author: Diffblue Ltd.

\******************************************************************/

#ifndef CPROVER_GOTO_HARNESS_FUNCTION_CALL_HARNESS_GENERATOR_H
#define CPROVER_GOTO_HARNESS_FUNCTION_CALL_HARNESS_GENERATOR_H

#include <list>
#include <memory>
#include <string>

#include <util/ui_message.h>

#include "goto_harness_generator.h"

/// Function harness generator that for a specified goto-function
/// generates a harness that sets up its arguments and calls it.
class function_call_harness_generatort : public goto_harness_generatort
{
public:
  explicit function_call_harness_generatort(
    ui_message_handlert &message_handler);
  ~function_call_harness_generatort() override;
  void generate(goto_modelt &goto_model, const irep_idt &harness_function_name)
    override;

protected:
  void handle_option(
    const std::string &option,
    const std::list<std::string> &values) override;

  void validate_options(const goto_modelt &goto_model) override;

private:
  std::size_t require_one_size_value(
    const std::string &option,
    const std::list<std::string> &values);
  struct implt;
  std::unique_ptr<implt> p_impl;
};

#endif // CPROVER_GOTO_HARNESS_FUNCTION_CALL_HARNESS_GENERATOR_H
