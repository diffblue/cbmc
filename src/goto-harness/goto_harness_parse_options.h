/******************************************************************\

Module: goto_harness_parse_options

Author: Diffblue Ltd.

\******************************************************************/

#ifndef CPROVER_GOTO_HARNESS_GOTO_HARNESS_PARSE_OPTIONS_H
#define CPROVER_GOTO_HARNESS_GOTO_HARNESS_PARSE_OPTIONS_H

#include <string>

#include <goto-programs/goto_model.h>
#include <util/parse_options.h>
#include <util/ui_message.h>

#include "function_harness_generator_options.h"
#include "goto_harness_generator_factory.h"
#include "memory_snapshot_harness_generator_options.h"

// clang-format off
#define GOTO_HARNESS_OPTIONS                                                   \
  "(version)"                                                                  \
  GOTO_HARNESS_FACTORY_OPTIONS                                                 \
  COMMON_HARNESS_GENERATOR_OPTIONS                                             \
  FUNCTION_HARNESS_GENERATOR_OPTIONS                                           \
  MEMORY_SNAPSHOT_HARNESS_GENERATOR_OPTIONS                                    \
// end GOTO_HARNESS_OPTIONS

// clang-format on

class goto_harness_parse_optionst : public parse_options_baset
{
public:
  int doit() override;
  void help() override;

  goto_harness_parse_optionst(int argc, const char *argv[]);

private:
  struct goto_harness_configt
  {
    std::string in_file;
    std::string out_file;
    std::string harness_type;
    irep_idt harness_function_name;
  };

  /// Handle command line arguments that are common to all
  /// harness generators.
  goto_harness_configt handle_common_options();

  /// Gather all the options that are not handled by
  /// `handle_common_options()`.
  goto_harness_generator_factoryt::generator_optionst
  collect_generate_factory_options();

  /// Setup the generator factory. This is the function you
  /// need to change when you add a new generator.
  goto_harness_generator_factoryt make_factory();
};

#endif // CPROVER_GOTO_HARNESS_GOTO_HARNESS_PARSE_OPTIONS_H
