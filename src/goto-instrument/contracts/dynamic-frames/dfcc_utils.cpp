/*******************************************************************\

Module: Dynamic frame condition checking

Author: Remi Delmas, delmarsd@amazon.com
Date: August 2022

\*******************************************************************/

#include "dfcc_utils.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/format_expr.h>
#include <util/fresh_symbol.h>
#include <util/message.h>
#include <util/pointer_expr.h>
#include <util/pointer_offset_size.h>
#include <util/std_expr.h>
#include <util/std_types.h>

#include <goto-programs/goto_inline.h>
#include <goto-programs/goto_model.h>

#include <ansi-c/goto-conversion/goto_convert_functions.h>
#include <goto-instrument/contracts/inlining_decorator.h>
#include <goto-instrument/contracts/utils.h>
#include <linking/static_lifetime_init.h>

#include <set>

/// Returns true iff the given symbol exists and satisfies requirements.
static bool symbol_exists(
  const goto_modelt &goto_model,
  const irep_idt &name,
  const bool require_has_code_type,
  const bool require_body_available)
{
  const namespacet ns{goto_model.symbol_table};

  const symbolt *sym;
  if(ns.lookup(name, sym))
    return false;

  if(require_has_code_type && sym->type.id() != ID_code)
    return false;

  if(require_body_available)
  {
    const auto found = goto_model.goto_functions.function_map.find(name);

    return found != goto_model.goto_functions.function_map.end() &&
           found->second.body_available();
  }
  return true;
}

bool dfcc_utilst::function_symbol_exists(
  const goto_modelt &goto_model,
  const irep_idt &function_id)
{
  return symbol_exists(goto_model, function_id, true, false);
}

bool dfcc_utilst::function_symbol_with_body_exists(
  const goto_modelt &goto_model,
  const irep_idt &function_id)
{
  return symbol_exists(goto_model, function_id, true, true);
}

symbolt &dfcc_utilst::get_function_symbol(
  symbol_table_baset &symbol_table,
  const irep_idt &function_id)
{
  symbolt &function_symbol = symbol_table.get_writeable_ref(function_id);
  CHECK_RETURN(function_symbol.type.id() == ID_code);
  return function_symbol;
}

symbol_exprt dfcc_utilst::create_symbol(
  symbol_table_baset &symbol_table,
  const typet &type,
  const irep_idt &function_id,
  const std::string &base_name,
  const source_locationt &source_location)
{
  const symbolt &function_symbol =
    get_function_symbol(symbol_table, function_id);

  symbolt &symbol = get_fresh_aux_symbol(
    type,
    id2string(function_id),
    base_name,
    source_location,
    function_symbol.mode,
    symbol_table);
  symbol.module = function_symbol.module;

  return symbol.symbol_expr();
}

const symbolt &dfcc_utilst::create_static_symbol(
  symbol_table_baset &symbol_table,
  const typet &type,
  const std::string &prefix,
  const std::string &base_name,
  const source_locationt &source_location,
  const irep_idt &mode,
  const irep_idt &module,
  const exprt &initial_value,
  const bool no_nondet_initialization)
{
  symbolt &symbol = get_fresh_aux_symbol(
    type, prefix, base_name, source_location, mode, symbol_table);
  symbol.module = module;
  symbol.is_static_lifetime = true;
  symbol.value = initial_value;
  symbol.value.set(ID_C_no_nondet_initialization, no_nondet_initialization);
  symbol.is_parameter = false;
  return symbol;
}

const symbolt &dfcc_utilst::create_new_parameter_symbol(
  symbol_table_baset &symbol_table,
  const irep_idt &function_id,
  const std::string &base_name,
  const typet &type)
{
  const symbolt &function_symbol =
    get_function_symbol(symbol_table, function_id);

  symbolt &symbol = get_fresh_aux_symbol(
    type,
    id2string(function_id),
    base_name,
    function_symbol.location,
    function_symbol.mode,
    symbol_table);
  symbol.is_parameter = true;
  symbol.module = function_symbol.module;
  return symbol;
}

/// \brief Adds the given symbol as parameter to the given code_typet.
static void add_parameter(const symbolt &symbol, code_typet &code_type)
{
  PRECONDITION(symbol.is_parameter);
  code_typet::parametert parameter(symbol.type);
  parameter.set_base_name(symbol.base_name);
  parameter.set_identifier(symbol.name);
  auto &parameters = code_type.parameters();
  parameters.insert(parameters.end(), parameter);
}

void dfcc_utilst::add_parameter(
  goto_modelt &goto_model,
  const symbolt &symbol,
  const irep_idt &function_id)
{
  auto &function_symbol =
    get_function_symbol(goto_model.symbol_table, function_id);
  code_typet &code_type = to_code_type(function_symbol.type);
  ::add_parameter(symbol, code_type);
  auto found = goto_model.goto_functions.function_map.find(function_id);
  if(found != goto_model.goto_functions.function_map.end())
    found->second.set_parameter_identifiers(code_type);
}

const symbolt &dfcc_utilst::add_parameter(
  goto_modelt &goto_model,
  const irep_idt &function_id,
  const std::string &base_name,
  const typet &type)
{
  const symbolt &symbol = create_new_parameter_symbol(
    goto_model.symbol_table, function_id, base_name, type);
  add_parameter(goto_model, symbol, function_id);
  return symbol;
}

/// \brief Clones the old_params into the new_params list, applying the
/// trans_param function to generate the names of the cloned params.
static void clone_parameters(
  symbol_table_baset &symbol_table,
  const code_typet::parameterst &old_params,
  const irep_idt &mode,
  const irep_idt &module,
  const source_locationt &location,
  std::function<const irep_idt(const irep_idt &)> &trans_param,
  const irep_idt &new_function_id,
  code_typet::parameterst &new_params)
{
  // rename function parameters in the wrapper function's code_type
  std::size_t anon_counter = 0;

  // build parameters and symbols
  for(auto &old_param : old_params)
  {
    // new identifier for new_code_type
    const irep_idt &old_base_name = old_param.get_base_name().empty()
                                      ? "#anon" + std::to_string(anon_counter++)
                                      : old_param.get_base_name();
    const irep_idt &new_base_name = trans_param(old_base_name);

    irep_idt new_param_id =
      id2string(new_function_id) + "::" + id2string(new_base_name);

    // build parameter
    code_typet::parametert new_param(old_param.type());
    new_param.set_base_name(new_base_name);
    new_param.set_identifier(new_param_id);
    new_params.push_back(new_param);

    // build symbol
    parameter_symbolt new_param_symbol;
    new_param_symbol.base_name = new_base_name;
    new_param_symbol.name = new_param_id;
    new_param_symbol.pretty_name = new_param_id;
    new_param_symbol.type = old_param.type();
    new_param_symbol.mode = mode;
    new_param_symbol.module = module;
    new_param_symbol.location = location;
    bool add_failed = symbol_table.add(new_param_symbol);
    INVARIANT(
      !add_failed,
      "DFCC: renamed parameter " + id2string(new_base_name) +
        " already exists");
  }
}

/// \brief Creates a new symbol in the `symbol_table` by cloning
/// the given `function_id` function and transforming the existing
/// function's name, parameter names, return type and source location
/// using the given `trans_fun`, `trans_param` and `trans_ret_type` and
/// `trans_loc` functions.
///
/// Also creates a new `goto_function` under the transformed name in
/// the `function_map` with new parameters and an empty body.
/// Returns the new symbol.
///
/// \param goto_model: target goto_model holding the symbol table
/// \param function_id function to clone
/// \param trans_fun transformation function for the function name
/// \param trans_param transformation function for the parameter names
/// \param trans_ret_type transformation function for the return type
/// \param trans_loc transformation function for the source location
/// \return the new function symbol
static const symbolt &clone_and_rename_function(
  goto_modelt &goto_model,
  const irep_idt &function_id,
  std::function<const irep_idt(const irep_idt &)> &trans_fun,
  std::function<const irep_idt(const irep_idt &)> &trans_param,
  std::function<const typet(const typet &)> &trans_ret_type,
  std::function<const source_locationt(const source_locationt &)> &trans_loc)
{
  const symbolt &old_function_symbol =
    dfcc_utilst::get_function_symbol(goto_model.symbol_table, function_id);
  code_typet old_code_type = to_code_type(old_function_symbol.type);

  irep_idt new_function_id = trans_fun(function_id);

  code_typet::parameterst new_params;
  source_locationt new_location = trans_loc(old_function_symbol.location);
  clone_parameters(
    goto_model.symbol_table,
    old_code_type.parameters(),
    old_function_symbol.mode,
    old_function_symbol.mode,
    new_location,
    trans_param,
    new_function_id,
    new_params);

  code_typet new_code_type(
    new_params, trans_ret_type(old_code_type.return_type()));

  // create new goto_function
  goto_functiont new_goto_function;
  new_goto_function.set_parameter_identifiers(new_code_type);
  goto_model.goto_functions.function_map[new_function_id].copy_from(
    new_goto_function);

  // build new function symbol
  symbolt new_function_symbol{
    new_function_id, std::move(new_code_type), old_function_symbol.mode};
  new_function_symbol.base_name = new_function_id;
  new_function_symbol.pretty_name = new_function_id;
  new_function_symbol.module = old_function_symbol.module;
  new_function_symbol.location = trans_loc(old_function_symbol.location);
  new_function_symbol.set_compiled();

  INVARIANT(
    !goto_model.symbol_table.add(new_function_symbol),
    "DFCC: renamed function " + id2string(new_function_id) + " already exists");

  return goto_model.symbol_table.lookup_ref(new_function_id);
}

const symbolt &dfcc_utilst::clone_and_rename_function(
  goto_modelt &goto_model,
  const irep_idt &function_id,
  const irep_idt &new_function_id,
  std::optional<typet> new_return_type = {})
{
  std::function<const irep_idt(const irep_idt &)> trans_fun =
    [&](const irep_idt &old_name) { return new_function_id; };

  std::function<const irep_idt(const irep_idt &)> trans_param =
    [&](const irep_idt &old_name) { return old_name; };

  std::function<const typet(const typet &)> trans_ret_type =
    [&](const typet &old_type) {
      return new_return_type.has_value() ? new_return_type.value() : old_type;
    };

  std::function<const source_locationt(const source_locationt &)> trans_loc =
    [&](const source_locationt &old_location) { return old_location; };

  return ::clone_and_rename_function(
    goto_model, function_id, trans_fun, trans_param, trans_ret_type, trans_loc);
}

void dfcc_utilst::wrap_function(
  goto_modelt &goto_model,
  const irep_idt &function_id,
  const irep_idt &wrapped_function_id)
{
  auto &goto_functions = goto_model.goto_functions;
  auto &symbol_table = goto_model.symbol_table;

  auto old_function = goto_functions.function_map.find(function_id);
  INVARIANT(
    old_function != goto_functions.function_map.end(),
    "DFCC: function to wrap " + id2string(function_id) +
      " must exist in the program");

  // Register the wrapped function under the new name
  std::swap(
    goto_functions.function_map[wrapped_function_id], old_function->second);

  // Remove previous entry
  goto_functions.function_map.erase(old_function);

  // Add new symbol for the wrapped function in the symbol table
  const symbolt *old_sym = symbol_table.lookup(function_id);
  source_locationt sl(old_sym->location);
  sl.set_file("wrapped functions for code contracts");
  sl.set_line("0");
  symbolt wrapped_sym = *old_sym;
  wrapped_sym.name = wrapped_function_id;
  wrapped_sym.base_name = wrapped_function_id;
  wrapped_sym.location = sl;
  const auto wrapped_found = symbol_table.insert(std::move(wrapped_sym));
  INVARIANT(
    wrapped_found.second,
    "DFCC: wrapped function symbol " + id2string(wrapped_function_id) +
      " already exists in the symbol table");

  // Re-insert a symbol for `function_id` which is now the wrapper function
  symbolt wrapper_sym = *old_sym;

  std::function<const irep_idt(const irep_idt &)> trans_param =
    [&](const irep_idt &old_param) {
      return id2string(old_param) + "_wrapper";
    };

  // create new code_type with renamed parameters for the wrapper
  const auto &old_code_type = to_code_type(old_sym->type);
  code_typet::parameterst new_params;
  clone_parameters(
    symbol_table,
    old_code_type.parameters(),
    wrapper_sym.mode,
    wrapper_sym.module,
    wrapper_sym.location,
    // the naming scheme is `function_id::param` + `param_suffix`
    trans_param,
    function_id,
    new_params);

  code_typet new_code_type(new_params, old_code_type.return_type());

  wrapper_sym.type = new_code_type;

  // Remove original symbol from the symbol_table
  bool remove_failed = goto_model.symbol_table.remove(function_id);
  INVARIANT(
    !remove_failed,
    "DFCC: could not remove wrapped function '" + id2string(function_id) +
      "' from the symbol table");

  // Insert update symbol in the symbol_table
  const auto wrapper_sym_found = symbol_table.insert(std::move(wrapper_sym));
  INVARIANT(
    wrapper_sym_found.second,
    "DFCC: could not insert wrapper symbol '" + id2string(function_id) +
      "' in the symbol table");

  // Insert wrapper function in the function_map
  goto_functiont &wrapper_fun = goto_functions.function_map[function_id];
  wrapper_fun.set_parameter_identifiers(new_code_type);
  wrapper_fun.body.add(goto_programt::make_end_function(sl));
}

const exprt dfcc_utilst::make_null_check_expr(const exprt &ptr)
{
  return equal_exprt(ptr, null_pointer_exprt(to_pointer_type(ptr.type())));
}

exprt dfcc_utilst::make_sizeof_expr(const exprt &expr, const namespacet &ns)
{
  const auto &size = size_of_expr(expr.type(), ns);

  if(!size.has_value())
  {
    throw invalid_source_file_exceptiont(
      "DFCC: no definite size for lvalue target" + format_to_string(expr),
      expr.source_location());
  }
  return size.value();
}

static inlining_decoratort inline_function(
  goto_modelt &goto_model,
  const irep_idt &function_id,
  message_handlert &message_handler)
{
  auto &goto_function = goto_model.goto_functions.function_map.at(function_id);

  PRECONDITION_WITH_DIAGNOSTICS(
    goto_function.body_available(),
    "dfcc_utilst::inline_function: '" + id2string(function_id) +
      "' must have a body");

  const namespacet ns{goto_model.symbol_table};
  inlining_decoratort decorated(message_handler);
  goto_function_inline(goto_model.goto_functions, function_id, ns, decorated);

  return decorated;
}

void dfcc_utilst::inline_function(
  goto_modelt &goto_model,
  const irep_idt &function_id,
  message_handlert &message_handler)
{
  inlining_decoratort decorated =
    ::inline_function(goto_model, function_id, message_handler);

  messaget log{message_handler};
  decorated.throw_on_recursive_calls(log, 0);
  decorated.throw_on_no_body(log, 0);
  decorated.throw_on_missing_function(log, 0);
  decorated.throw_on_not_enough_arguments(log, 0);

  goto_model.goto_functions.update();
}

void dfcc_utilst::inline_function(
  goto_modelt &goto_model,
  const irep_idt &function_id,
  std::set<irep_idt> &no_body,
  std::set<irep_idt> &recursive_call,
  std::set<irep_idt> &missing_function,
  std::set<irep_idt> &not_enough_arguments,
  message_handlert &message_handler)
{
  inlining_decoratort decorated =
    ::inline_function(goto_model, function_id, message_handler);

  no_body.insert(
    decorated.get_no_body_set().begin(), decorated.get_no_body_set().end());
  recursive_call.insert(
    decorated.get_recursive_call_set().begin(),
    decorated.get_recursive_call_set().end());
  missing_function.insert(
    decorated.get_missing_function_set().begin(),
    decorated.get_missing_function_set().end());
  not_enough_arguments.insert(
    decorated.get_not_enough_arguments_set().begin(),
    decorated.get_not_enough_arguments_set().end());

  goto_model.goto_functions.update();
}

void dfcc_utilst::inline_program(
  goto_modelt &goto_model,
  goto_programt &goto_program,
  std::set<irep_idt> &no_body,
  std::set<irep_idt> &recursive_call,
  std::set<irep_idt> &missing_function,
  std::set<irep_idt> &not_enough_arguments,
  message_handlert &message_handler)
{
  const namespacet ns{goto_model.symbol_table};
  inlining_decoratort decorated(message_handler);
  goto_program_inline(goto_model.goto_functions, goto_program, ns, decorated);
  no_body.insert(
    decorated.get_no_body_set().begin(), decorated.get_no_body_set().end());
  recursive_call.insert(
    decorated.get_recursive_call_set().begin(),
    decorated.get_recursive_call_set().end());
  missing_function.insert(
    decorated.get_missing_function_set().begin(),
    decorated.get_missing_function_set().end());
  not_enough_arguments.insert(
    decorated.get_not_enough_arguments_set().begin(),
    decorated.get_not_enough_arguments_set().end());
  goto_model.goto_functions.update();
}
