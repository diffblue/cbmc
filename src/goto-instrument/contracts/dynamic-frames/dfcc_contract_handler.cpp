/*******************************************************************\

Module: Dynamic frame condition checking for function contracts

Author: Remi Delmas, delmasrd@amazon.com
Date: August 2022

\*******************************************************************/

#include "dfcc_contract_handler.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/expr_util.h>
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
#include <goto-instrument/contracts/utils.h>
#include <langapi/language_util.h>

#include "dfcc_instrument.h"
#include "dfcc_library.h"
#include "dfcc_spec_functions.h"
#include "dfcc_utils.h"
#include "dfcc_wrapper_program.h"

std::map<irep_idt, dfcc_contract_functionst>
  dfcc_contract_handlert::contract_cache;

dfcc_contract_handlert::dfcc_contract_handlert(
  goto_modelt &goto_model,
  message_handlert &message_handler,
  dfcc_utilst &utils,
  dfcc_libraryt &library,
  dfcc_instrumentt &instrument,
  dfcc_lift_memory_predicatest &memory_predicates,
  dfcc_spec_functionst &spec_functions,
  dfcc_contract_clauses_codegent &contract_clauses_codegen)
  : goto_model(goto_model),
    message_handler(message_handler),
    log(message_handler),
    utils(utils),
    library(library),
    instrument(instrument),
    memory_predicates(memory_predicates),
    spec_functions(spec_functions),
    contract_clauses_codegen(contract_clauses_codegen),
    ns(goto_model.symbol_table)
{
}

const dfcc_contract_functionst &
dfcc_contract_handlert::get_contract_functions(const irep_idt &contract_id)
{
  auto iter = dfcc_contract_handlert::contract_cache.find(contract_id);

  // return existing value
  if(iter != dfcc_contract_handlert::contract_cache.end())
    return iter->second;

  // insert new value
  return dfcc_contract_handlert::contract_cache
    .insert(
      {contract_id,
       dfcc_contract_functionst(
         get_pure_contract_symbol(contract_id),
         goto_model,
         message_handler,
         utils,
         library,
         spec_functions,
         contract_clauses_codegen,
         instrument)})
    .first->second;
}

const std::size_t
dfcc_contract_handlert::get_assigns_clause_size(const irep_idt &contract_id)
{
  return get_contract_functions(contract_id).get_nof_assigns_targets();
}

void dfcc_contract_handlert::add_contract_instructions(
  const dfcc_contract_modet contract_mode,
  const irep_idt &wrapper_id,
  const irep_idt &wrapped_id,
  const irep_idt &contract_id,
  const symbolt &wrapper_write_set_symbol,
  goto_programt &dest,
  std::set<irep_idt> &function_pointer_contracts)
{
  dfcc_wrapper_programt(
    contract_mode,
    utils.get_function_symbol(wrapper_id),
    utils.get_function_symbol(wrapped_id),
    get_contract_functions(contract_id),
    wrapper_write_set_symbol,
    goto_model,
    message_handler,
    utils,
    library,
    instrument,
    memory_predicates)
    .add_to_dest(dest, function_pointer_contracts);
}

const symbolt &dfcc_contract_handlert::get_pure_contract_symbol(
  const irep_idt &contract_id,
  const optionalt<irep_idt> function_id_opt)
{
  auto pure_contract_id = "contract::" + id2string(contract_id);
  const symbolt *pure_contract_symbol = nullptr;
  if(!ns.lookup(pure_contract_id, pure_contract_symbol))
  {
    if(function_id_opt.has_value())
    {
      auto function_id = function_id_opt.value();
      const auto &function_symbol = utils.get_function_symbol(function_id);
      check_signature_compat(
        function_id,
        to_code_type(function_symbol.type),
        pure_contract_id,
        to_code_type(pure_contract_symbol->type));
    }
    return *pure_contract_symbol;
  }
  else
  {
    // The contract symbol might not have been created if the function had
    // no contract or a contract with all empty clauses (which is equivalent).
    // in that case we create a fresh symbol again with empty clauses.
    PRECONDITION_WITH_DIAGNOSTICS(
      function_id_opt.has_value(),
      "Contract '" + pure_contract_id +
        "' not found, the identifier of an existing function must be provided "
        "to derive a default contract");

    auto function_id = function_id_opt.value();
    const auto &function_symbol = utils.get_function_symbol(function_id);

    log.warning() << "Contract '" << contract_id
                  << "' not found, deriving empty pure contract '"
                  << pure_contract_id << "' from function '" << function_id
                  << "'" << messaget::eom;

    symbolt new_symbol{
      pure_contract_id, function_symbol.type, function_symbol.mode};
    new_symbol.base_name = pure_contract_id;
    new_symbol.pretty_name = pure_contract_id;
    new_symbol.is_property = true;
    new_symbol.module = function_symbol.module;
    new_symbol.location = function_symbol.location;
    auto entry = goto_model.symbol_table.insert(std::move(new_symbol));
    INVARIANT(
      entry.second,
      "contract '" + id2string(function_symbol.display_name()) +
        "' already set at " + id2string(entry.first.location.as_string()));
    // this lookup will work and set the pointer
    // no need to check for signature compatibility
    ns.lookup(pure_contract_id, pure_contract_symbol);
    return *pure_contract_symbol;
  }
}

void dfcc_contract_handlert::check_signature_compat(
  const irep_idt &contract_id,
  const code_typet &contract_type,
  const irep_idt &pure_contract_id,
  const code_typet &pure_contract_type)
{
  // can we turn a call to `contract` into a call to `pure_contract` ?
  bool compatible =
    function_is_type_compatible(true, contract_type, pure_contract_type, ns);

  if(!compatible)
  {
    std::ostringstream err_msg;
    err_msg << "dfcc_contract_handlert: function '" << contract_id
            << "' and the corresponding pure contract symbol '"
            << pure_contract_id << "' have incompatible type signatures:\n";

    err_msg << "- contract return type "
            << from_type(ns, contract_id, contract_type.return_type()) << "\n";

    for(const auto &param : contract_type.parameters())
    {
      err_msg << "- contract param type "
              << from_type(ns, contract_id, param.type()) << "\n";
    }

    err_msg << "- pure contract return type "
            << from_type(ns, pure_contract_id, pure_contract_type.return_type())
            << "\n";

    for(const auto &param : pure_contract_type.parameters())
    {
      err_msg << "- pure contract param type "
              << from_type(ns, pure_contract_id, param.type()) << "\n";
    }

    err_msg << "aborting."
            << "\n";
    throw invalid_source_file_exceptiont(
      err_msg.str(), contract_type.source_location());
  }
}
