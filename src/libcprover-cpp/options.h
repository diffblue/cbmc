// Author: Fotis Koutoulakis for Diffblue Ltd.

#ifndef CPROVER_LIBCPROVER_CPP_OPTIONS_H
#define CPROVER_LIBCPROVER_CPP_OPTIONS_H

#include <memory>

class optionst;

class api_optionst
{
  // Options for the verification engine
  bool simplify_enabled;

  // Option for dropping unused function
  bool drop_unused_functions_enabled;

  // Option for validating the goto model
  bool validate_goto_model_enabled;

  // Private interface methods
  api_optionst() = default;

public:
  static api_optionst create();

  api_optionst &simplify(bool on);

  api_optionst &drop_unused_functions(bool on);

  api_optionst &validate_goto_model(bool on);

  std::unique_ptr<optionst> to_engine_options() const;
};

#endif
