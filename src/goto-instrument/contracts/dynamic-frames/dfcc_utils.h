/*******************************************************************\

Module: Dynamic frame condition checking for function contracts

Author: Remi Delmas, delmasrd@amazon.com
Date: August 2022

\*******************************************************************/

/// \file
/// Dynamic frame condition checking utility functions

#ifndef CPROVER_GOTO_INSTRUMENT_CONTRACTS_DYNAMIC_FRAMES_DFCC_UTILS_H
#define CPROVER_GOTO_INSTRUMENT_CONTRACTS_DYNAMIC_FRAMES_DFCC_UTILS_H

#include <util/namespace.h>
#include <util/std_expr.h>

#include <set>

class goto_modelt;
class messaget;
class message_handlert;
class symbolt;

class dfcc_utilst
{
public:
  dfcc_utilst(goto_modelt &goto_model, messaget &log);

protected:
  goto_modelt &goto_model;
  messaget &log;
  message_handlert &message_handler;
  namespacet ns;

public:
  /// Returns true iff the given symbol exists and satisfies requirements.
  const bool symbol_exists(
    const std::string &function_id,
    const bool require_has_code_type = false,
    const bool require_body_available = false);

  const bool function_symbol_exists(const std::string &function_id);
  const bool function_symbol_with_body_exists(const std::string &function_id);

  /// Returns the `symbolt` for `function_id`.
  symbolt &get_function_symbol(const irep_idt &function_id);

  /// Adds a new symbol named `prefix::base_name` of type `type`
  /// with given attributes in the symbol table, and returns the created symbol.
  /// If a symbol of the same name already exists the name will be decorated
  /// with a unique suffix.
  const symbolt &create_symbol(
    const typet &type,
    const std::string &prefix,
    const std::string &base_name,
    const source_locationt &source_location,
    const irep_idt &mode,
    const irep_idt &module,
    bool is_parameter);

  /// Adds a new static symbol named `prefix::base_name` of type `type` with
  /// value `initial_value` in the symbol table, returns the created symbol.
  /// If a symbol of the same name already exists the name will be decorated
  /// with a unique suffix.
  const symbolt &create_static_symbol(
    const typet &type,
    const std::string &prefix,
    const std::string &base_name,
    const source_locationt &source_location,
    const irep_idt &mode,
    const irep_idt &module,
    const exprt &initial_value);

  /// Regenerates the CPROVER_INITIALIZE function which defines all global
  /// statics of the goto model.
  void create_initialize_function();

  /// Creates a new parameter symbol for the given function_id
  const symbolt &create_new_parameter_symbol(
    const irep_idt &function_id,
    const std::string &base_name,
    const typet &type);

  /// \brief Adds the given symbol as parameter to the function symbol's
  /// code_type. Also adds the corresponding parameter to its goto_function if
  /// it exists in the function map of the goto model.
  void add_parameter(const symbolt &symbol, const irep_idt &function_id);

  /// \brief Adds the given symbol as parameter to the given code_typet.
  void add_parameter(const symbolt &symbol, code_typet &code_type);

  /// \brief Adds a parameter with given `base_name` and `type` to the given
  /// `function_id`. Both the symbol and the goto_function are updated.
  const symbolt &add_parameter(
    const irep_idt &function_id,
    const std::string &base_name,
    const typet &type);

  /// \brief Creates a new symbol in the `symbol_table` by cloning
  /// the given `function_id` function and transforming the existing's
  /// function's name, parameter names, return type and source location
  /// using the given `trans_fun`, `trans_param` and `trans_ret_type` and
  /// `trans_loc` functions.
  ///
  /// Also creates a new `goto_function` under the transformed name in
  /// the `function_map` with new parameters and an empty body.
  /// Returns the new symbol.
  ///
  /// \param function_id function to clone
  /// \param trans_fun transformation function for the function name
  /// \param trans_param transformation function for the parameter names
  /// \param trans_ret_type transformation function for the return type
  /// \param trans_loc transformation function for the source location
  /// \return the new function symbol
  const symbolt &clone_and_rename_function(
    const irep_idt &function_id,
    std::function<const irep_idt(const irep_idt &)> &trans_fun,
    std::function<const irep_idt(const irep_idt &)> &trans_param,
    std::function<const typet(const typet &)> &trans_ret_type,
    std::function<const source_locationt(const source_locationt &)> &trans_loc);

  /// \brief Clones the old_params into the new_params list, applying the
  /// trans_param function to generate the names of the cloned params.
  void clone_parameters(
    const code_typet::parameterst &old_params,
    const irep_idt &mode,
    const irep_idt &module,
    const source_locationt &location,
    std::function<const irep_idt(const irep_idt &)> &trans_param,
    const irep_idt &new_function_id,
    code_typet::parameterst &new_params);

  /// \brief Creates names for anonymous parameters and declares them
  /// in the symbol table if needed (using goto_convert requires all function
  /// parameters to have names).
  void fix_parameters_symbols(const irep_idt &function_id);

  /// \brief Creates a new function symbol and and goto_function
  /// entry in the `goto_functions_map` by cloning the given `function_id`.
  ///
  /// The cloned function symbol has `new_function_id` as name
  /// The cloned parameters symbols have `new_function_id::name` as name
  /// Returns the new function symbol
  const symbolt &clone_and_rename_function(
    const irep_idt &function_id,
    const irep_idt &new_function_id,
    optionalt<typet> new_return_type);

  /// Given a function to wrap `foo` and a new name `wrapped_foo`
  ///
  /// ```
  /// ret_t foo(x_t foo::x, y_t foo::y) { foo_body; }
  /// ```
  ///
  /// This method creates a new entry in the symbol_table for
  /// `wrapped_foo` and moves the body of the original function, `foo_body`,
  /// under `wrapped_foo` in `function_map`.
  ///
  /// The parameter symbols of `wrapped_foo` remain the same as in `foo`:
  /// ```
  /// ret_t wrapped_foo(x_t foo::x, y_t foo::y) { foo_body; }
  /// ```
  ///
  /// The parameters of the original `foo` get renamed to
  /// make sure they are distinct from that of `wrapped_foo`, and a new
  /// empty body is generated for `foo`:
  ///
  /// ```
  /// ret_t foo(x_t foo::x_wrapped, y_t foo::y_wrapped) { };
  /// ```
  ///
  /// Any other goto_function calling `foo` still calls `foo` which has become
  /// a wrapper for `wrapped_foo`.
  ///
  /// By generating a new body for `foo`, one can implement contract
  /// checking logic, contract replacement logic, etc.
  void wrap_function(
    const irep_idt &function_id,
    const irep_idt &wrapped_function_id);

  /// \brief Returns the expression `expr == NULL`.
  const exprt make_null_check_expr(const exprt &ptr);

  /// \brief Returns the expression `sizeof(expr)`.
  exprt make_sizeof_expr(const exprt &expr);

  /// \brief Returns the expression `&expr[0]`
  exprt make_map_start_address(const exprt &expr);

  /// \brief Inlines the given function, aborts on recursive calls during
  /// inlining.
  void inline_function(const irep_idt &function_id);

  /// \brief Inlines the given function, and returns function symbols that
  /// caused warnings.
  void inline_function(
    const irep_idt &function_id,
    std::set<irep_idt> &no_body,
    std::set<irep_idt> &recursive_call,
    std::set<irep_idt> &missing_function,
    std::set<irep_idt> &not_enough_arguments);

  /// \brief Checks if the function is loop free. The function must exist
  /// and have a body. Prints `msg` and throws `err` on failure.
  void
  check_loop_freeness(const irep_idt &function_id, std::string msg, int err);

  /// \brief Sets the given hide flag on all instructions of the function if it
  /// exists.
  void set_hide(const irep_idt &function_id, bool hide);
};

#endif
