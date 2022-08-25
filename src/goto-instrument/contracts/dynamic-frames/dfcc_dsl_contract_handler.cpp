/*******************************************************************\

Module: Dynamic frame condition checking for function contracts

Author: Remi Delmas, delmasrd@amazon.com
Date: August 2022

\*******************************************************************/

#include "dfcc_dsl_contract_handler.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/expr_util.h>
#include <util/format_expr.h>
#include <util/format_type.h>
#include <util/fresh_symbol.h>
#include <util/invariant.h>
#include <util/mathematical_expr.h>
#include <util/namespace.h>
#include <util/pointer_offset_size.h>
#include <util/std_expr.h>

#include <goto-programs/goto_model.h>
#include <goto-programs/remove_function_pointers.h>

#include <ansi-c/c_expr.h>
#include <goto-instrument/contracts/contracts.h>
#include <goto-instrument/contracts/utils.h>
#include <langapi/language_util.h>

#include "dfcc_dsl_wrapper_program.h"
#include "dfcc_instrument.h"
#include "dfcc_library.h"
#include "dfcc_spec_functions.h"
#include "dfcc_utils.h"

std::map<irep_idt, dfcc_dsl_contract_functionst>
  dfcc_dsl_contract_handlert::contract_cache;

dfcc_dsl_contract_handlert::dfcc_dsl_contract_handlert(
  goto_modelt &goto_model,
  messaget &log,
  dfcc_utilst &utils,
  dfcc_libraryt &library,
  dfcc_instrumentt &instrument,
  dfcc_spec_functionst &spec_functions)
  : goto_model(goto_model),
    log(log),
    message_handler(log.get_message_handler()),
    utils(utils),
    library(library),
    instrument(instrument),
    spec_functions(spec_functions),
    ns(goto_model.symbol_table)
{
}

const dfcc_dsl_contract_functionst &
dfcc_dsl_contract_handlert::get_contract_functions(const irep_idt &contract_id)
{
  auto found = dfcc_dsl_contract_handlert::contract_cache.find(contract_id);
  if(found == dfcc_dsl_contract_handlert::contract_cache.end())
  {
    dfcc_dsl_contract_handlert::contract_cache.insert(
      {contract_id,
       dfcc_dsl_contract_functionst(
         get_pure_contract_symbol(contract_id),
         goto_model,
         log,
         utils,
         library,
         spec_functions)});
  }
  return dfcc_dsl_contract_handlert::contract_cache.at(contract_id);
}

const int
dfcc_dsl_contract_handlert::get_assigns_clause_size(const irep_idt &contract_id)
{
  return get_contract_functions(contract_id).get_nof_assigns_targets();
}

void dfcc_dsl_contract_handlert::add_contract_instructions(
  const dfcc_contract_modet contract_mode,
  const irep_idt &wrapper_id,
  const irep_idt &wrapped_id,
  const irep_idt &contract_id,
  const symbolt &wrapper_write_set_symbol,
  goto_programt &dest,
  std::set<irep_idt> &function_pointer_contracts)
{
  dfcc_dsl_wrapper_programt(
    contract_mode,
    utils.get_function_symbol(wrapper_id),
    utils.get_function_symbol(wrapped_id),
    get_contract_functions(contract_id),
    wrapper_write_set_symbol,
    goto_model,
    log,
    utils,
    library,
    instrument)
    .add_to_dest(dest, function_pointer_contracts);
}

const symbolt *dfcc_dsl_contract_handlert::get_pure_contract_symbol_ptr(
  const irep_idt &contract_id)
{
  const auto &contract_symbol = utils.get_function_symbol(contract_id);
  const symbolt *pure_contract_symbol = nullptr;
  auto pure_contract_id = "contract::" + id2string(contract_id);
  if(!ns.lookup(pure_contract_id, pure_contract_symbol))
  {
    log.debug() << "contract_symbol: " << contract_symbol.name << messaget::eom;
    log.debug() << contract_symbol.type.pretty() << messaget::eom;
    log.debug() << "pure_contract_symbol: " << pure_contract_id
                << messaget::eom;
    log.debug() << pure_contract_symbol->type.pretty() << messaget::eom;

    check_signature_compat(
      contract_id,
      to_code_type(contract_symbol.type),
      pure_contract_id,
      to_code_type(pure_contract_symbol->type));
  }
  else
  {
    // The contract symbol might not have been created if the function had
    // no contract or a contract with all empty clauses (which is equivalent).
    // in that case we create a fresh symbol again with empty clauses
    symbolt new_symbol;
    new_symbol.name = pure_contract_id;
    new_symbol.base_name = pure_contract_id;
    new_symbol.pretty_name = pure_contract_id;
    new_symbol.is_property = true;
    new_symbol.type = contract_symbol.type;
    new_symbol.mode = contract_symbol.mode;
    new_symbol.module = contract_symbol.module;
    new_symbol.location = contract_symbol.location;
    auto entry = goto_model.symbol_table.insert(std::move(new_symbol));
    if(!entry.second)
    {
      log.error().source_location = contract_symbol.location;
      log.error() << "contract '" << contract_symbol.display_name()
                  << "' already set at " << entry.first.location.as_string()
                  << messaget::eom;
      throw 0;
    }
    // this lookup must work, and no need to check for signature compatibility
    ns.lookup(pure_contract_id, pure_contract_symbol);
  }
  return pure_contract_symbol;
}

const symbolt &dfcc_dsl_contract_handlert::get_pure_contract_symbol(
  const irep_idt &contract_id)
{
  auto result = get_pure_contract_symbol_ptr(contract_id);
  if(result != nullptr)
    return *result;

  log.error() << "dfcc_dsl_contract_handlert: pure contract symbol for "
              << contract_id << " was not found, aborting" << messaget::eom;
  throw 0;
}

const bool dfcc_dsl_contract_handlert::pure_contract_symbol_exists(
  const irep_idt &contract_id)
{
  auto result = get_pure_contract_symbol_ptr(contract_id);
  return result != nullptr;
}

void dfcc_dsl_contract_handlert::check_signature_compat(
  const irep_idt &contract_id,
  const code_typet &contract_type,
  const irep_idt &pure_contract_id,
  const code_typet &pure_contract_type)
{
  // we consider that the return value is used if the contract has a return type
  bool compatible = function_is_type_compatible(
    pure_contract_type.return_type().is_not_nil() ||
      contract_type.return_type().is_not_nil(),
    pure_contract_type,
    contract_type,
    ns);

  if(!compatible)
  {
    log.error() << "dfcc_dsl_contract_handlert: function '" << contract_id
                << "' and the corresponding pure contract symbol '"
                << pure_contract_id
                << "' have incompatible type signatures:" << messaget::eom;
    log.error() << "- '" << contract_id << "': " << format(contract_type)
                << messaget::eom;
    log.error() << "- '" << pure_contract_id
                << "': " << format(pure_contract_type) << messaget::eom;
    log.error() << "aborting." << messaget::eom;
    throw 0;
  }
}
