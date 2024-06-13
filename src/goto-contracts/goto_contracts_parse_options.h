/*******************************************************************\

Module: Command Line Parsing

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// Command Line Parsing

#ifndef CPROVER_GOTO_CONTRACTS_GOTO_CONTRACTS_PARSE_OPTIONS_H
#define CPROVER_GOTO_CONTRACTS_GOTO_CONTRACTS_PARSE_OPTIONS_H

#include <util/parse_options.h>

#include <goto-programs/goto_model.h>

// clang-format off
#define GOTO_CONTRACTS_OPTIONS \
  "(verbosity):(version)(xml-ui)(json-ui)" \
  // empty last line

// clang-format on

class goto_contracts_parse_optionst : public parse_options_baset
{
public:
  int doit() override;
  void help() override;

  goto_contracts_parse_optionst(int argc, const char **argv)
    : parse_options_baset(GOTO_CONTRACTS_OPTIONS, argc, argv, "goto-contracts")
  {
  }

protected:
  void register_languages() override;

  void get_goto_program();

  goto_modelt goto_model;
};

#endif // CPROVER_GOTO_CONTRACTS_GOTO_CONTRACTS_PARSE_OPTIONS_H
