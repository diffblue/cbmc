/******************************************************************\

Module: goto_harness_generator_factory

Author: Diffblue Ltd.

\******************************************************************/

#ifndef CPROVER_GOTO_HARNESS_GOTO_HARNESS_GENERATOR_FACTORY_H
#define CPROVER_GOTO_HARNESS_GOTO_HARNESS_GENERATOR_FACTORY_H

#include <functional>
#include <map>
#include <memory>
#include <string>

#include "goto_harness_generator.h"

#define GOTO_HARNESS_GENERATOR_TYPE_OPT "harness-type"
#define GOTO_HARNESS_GENERATOR_HARNESS_FUNCTION_NAME_OPT "harness-function-name"

// clang-format off
#define GOTO_HARNESS_FACTORY_OPTIONS                                           \
  "(" GOTO_HARNESS_GENERATOR_TYPE_OPT "):"                                     \
  "(" GOTO_HARNESS_GENERATOR_HARNESS_FUNCTION_NAME_OPT "):"                    \
// end GOTO_HARNESS_FACTORY_OPTIONS

// clang-format on

/// helper to select harness type by name.
class goto_harness_generator_factoryt
{
public:
  /// the type of a function that produces a goto-harness generator.
  using build_generatort =
    std::function<std::unique_ptr<goto_harness_generatort>()>;

  using generator_optionst = std::map<std::string, std::list<std::string>>;

  /// register a new goto-harness generator with the given name.
  /// \param generator_name: name of newly registered generator
  /// \param build_generator: the function that builds the generator
  void register_generator(
    std::string generator_name,
    build_generatort build_generator);

  /// return a generator matching the generator name.
  /// throws if no generator with the supplied name is registered.
  std::unique_ptr<goto_harness_generatort> factory(
    const std::string &generator_name,
    const generator_optionst &generator_options,
    const goto_modelt &goto_model);

private:
  std::map<std::string, build_generatort> generators;
};

#endif // CPROVER_GOTO_HARNESS_GOTO_HARNESS_GENERATOR_FACTORY_H
