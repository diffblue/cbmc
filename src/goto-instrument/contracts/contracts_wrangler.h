/*******************************************************************\

Module: Parse and annotate contracts from configuration files

Author: Qinheping Hu

Date: June 2023

\*******************************************************************/

/// \file
/// Parse and annotate contracts

#ifndef CPROVER_GOTO_INSTRUMENT_CONTRACTS_CONTRACTS_WRANGLER_H
#define CPROVER_GOTO_INSTRUMENT_CONTRACTS_CONTRACTS_WRANGLER_H

#include <util/message.h>
#include <util/namespace.h>
#include <util/replace_symbol.h>
#include <util/string_utils.h>

#include <goto-programs/goto_functions.h>
#include <goto-programs/goto_model.h>

#include <json/json_parser.h>

#include <regex>

struct loop_contracts_clauset
{
  std::string identifier;
  std::string invariants;
  std::string assigns;
  std::string decreases;
  unchecked_replace_symbolt replace_symbol;

  loop_contracts_clauset(
    std::string _identifier,
    std::string _invariants_str,
    std::string _assigns_str,
    std::string _decreases_str,
    unchecked_replace_symbolt _replace_symbol)
    : identifier(std::move(_identifier)),
      invariants(std::move(_invariants_str)),
      assigns(_assigns_str),
      decreases(_decreases_str),
      replace_symbol(_replace_symbol)
  {
  }
};

struct functiont
{
  std::vector<loop_contracts_clauset> loop_contracts;
  std::string regex_str;
};

using functionst = std::list<std::pair<std::regex, functiont>>;

class contracts_wranglert
{
public:
  contracts_wranglert(
    goto_modelt &goto_model,
    const std::string &file_name,
    message_handlert &message_handler);

  namespacet ns;

protected:
  goto_modelt &goto_model;
  symbol_tablet &symbol_table;
  goto_functionst &goto_functions;

  message_handlert &message_handler;

  functionst functions;

  void configure_functions(const jsont &);

  /// @brief Mangle `loop_contracts` in the function with `function_id`
  /// @param loop_contracts The contracts mangled in the function.
  /// @param function_id The function containing the loop we mangle to.
  void mangle(
    const loop_contracts_clauset &loop_contracts,
    const irep_idt &function_id);

  /// @brief Add builtin function symbol with `function_name` into symbol table.
  /// @param function_name Name of the function to add.
  /// @param num_of_args Number of arguments of the added symbol.
  void add_builtin_pointer_function_symbol(
    std::string function_name,
    const std::size_t num_of_args);
};

#endif // CPROVER_GOTO_INSTRUMENT_CONTRACTS_CONTRACTS_WRANGLER_H
