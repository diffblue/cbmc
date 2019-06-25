/*******************************************************************\

Module: Create function stubs in C from code contracts

Author: Konstantinos Kallas

Date: July 2019

\*******************************************************************/

/// \file
/// Create function stubs in C from code contracts

#include "stub_function.h"

#include <fstream>

#include <util/expr_util.h>
#include <util/fresh_symbol.h>
#include <util/replace_symbol.h>

#include <goto-programs/remove_skip.h>

#include <analyses/local_may_alias.h>

#include <linking/static_lifetime_init.h>

#include "loop_utils.h"

class stub_functiont
{
public:
  stub_functiont(
    symbol_tablet &_symbol_table,
    goto_functionst &_goto_functions,
    irep_idt _function_name,
    messaget &_log)
    : ns(_symbol_table),
      symbol_table(_symbol_table),
      goto_functions(_goto_functions),
      function_name(_function_name),
      log(_log),
      temporary_counter(0)
  {
  }

  bool operator()();

protected:
  namespacet ns;
  symbol_tablet &symbol_table;
  goto_functionst &goto_functions;
  const irep_idt function_name;
  messaget &log;

  unsigned temporary_counter;

  void stub_function(
    const irep_idt &function_id,
    goto_functionst::goto_functiont &goto_function);

  const symbolt &new_tmp_symbol(
    const typet &type,
    const source_locationt &source_location,
    const irep_idt &function_id,
    const irep_idt &mode);
};

///
/// Creates a stub for each function based on the associated
/// `requires` and `ensures` statements in the function's contract.
///
/// Example:
/// The following function:
///
/// ```c
/// int foo(int *arg)
///   requires(*arg == 1)
///   ensures(*arg == 2)
/// { ... }
/// ```
///
/// would produce the following stub
///
/// ```c
/// int foo(int *arg)
/// {
///   assert(*arg == 1);
///   int rval = __stub_foo_impl(arg);
///   assume(*arg == 2);
///   return rval;
/// }
/// ```
///
/// where the user can implement `__stub_foo_impl` to get some custom
/// behaviour out of the stub. If `__stub_foo_impl` is not
/// implemented, the default behaviour of CBMC is that a
/// non-deterministic value is returned, in this example `rval`.
///
void stub_functiont::stub_function(
  const irep_idt &function_id,
  goto_functionst::goto_functiont &goto_function)
{
  // Get the function requires and ensures
  const symbolt &f_sym = ns.lookup(function_id);
  const code_typet &type = to_code_type(f_sym.type);

  const exprt &requires =
    static_cast<const exprt &>(type.find(ID_C_spec_requires));
  const exprt &ensures =
    static_cast<const exprt &>(type.find(ID_C_spec_ensures));

  // Clear the function body
  goto_function.body.clear();

  // Add an assertion, that checks the contract requirements, in the
  // function body
  if(requires.is_not_nil())
    goto_function.body.add(
      goto_programt::make_assertion(requires, requires.source_location()));

  // Get the stub implementation function symbol. The stub
  // implementation function is called from the stub and can be
  // implemented by the user to give the stub some custom specific
  // behaviour. If the stub implementation function is left without a
  // body, CBMC by default treats it as returning a non-deterministic
  // return value.
  const symbolt &stub_implementation_symbol =
    symbol_table.lookup_ref(stub_name_of_function(function_id));

  // Make the function call to the implementation function
  code_function_callt internal_implementation_call(
    stub_implementation_symbol.symbol_expr());

  // Declare a variable to store the return value from the internal call
  symbol_exprt return_value_symbol = get_fresh_aux_symbol(
                                       type.return_type(),
                                       id2string(function_id) + "::ret_val",
                                       "ret_val",
                                       source_locationt(),
                                       stub_implementation_symbol.mode,
                                       symbol_table)
                                       .symbol_expr();

  replace_symbolt replace_return_value_symbol;

  if(type.return_type() != empty_typet())
  {
    // Declare the return variable and assign to it the return value
    // of the call
    goto_function.body.add(goto_programt::make_decl(return_value_symbol));
    internal_implementation_call.lhs() = return_value_symbol;

    // Replace the return_value with r
    symbol_exprt ret_val(CPROVER_PREFIX "return_value", type.return_type());
    replace_return_value_symbol.insert(ret_val, return_value_symbol);
  }

  // Add the parameters as arguments to the call
  for(const auto &parameter_identifier : type.parameter_identifiers())
  {
    const symbolt &parameter_symbol = ns.lookup(parameter_identifier);
    internal_implementation_call.arguments().push_back(
      parameter_symbol.symbol_expr());
  }

  goto_function.body.add(goto_programt::make_function_call(
    code_function_callt(internal_implementation_call)));
  // Maybe: Add location/comments maybe?

  // Add the postcondition assumption
  if(ensures.is_not_nil())
  {
    exprt ensures_replaced = ensures;
    replace_return_value_symbol(ensures_replaced);
    goto_function.body.add(goto_programt::make_assumption(
      ensures_replaced, ensures.source_location()));
  }

  if(type.return_type() != empty_typet())
  {
    code_returnt return_expr(return_value_symbol);
    goto_function.body.add(goto_programt::make_return(return_expr));
  }

  // Append the end of function instruction
  goto_function.body.add(
    goto_programt::make_end_function(ensures.source_location()));
}

bool stub_functiont::operator()()
{
  // Get the body of the requested function to stub
  goto_functiont function_body;
  auto requested_function_body =
    goto_functions.function_map.find(function_name);
  if(requested_function_body == goto_functions.function_map.end())
  {
    log.error() << "The body of function: " << function_name
                << "doesn't exist in the goto_model\n";
    return true;
  }
  function_body.copy_from(requested_function_body->second);

  log.debug() << "Stubbing function: " << function_name << "\n";

  // Add a declaration of the impl function, that will be called in
  // the function body. Create a new function symbol for the internal
  // implementation function
  if(!symbol_table.has_symbol(function_name))
  {
    log.error() << "Function: " << function_name
                << "doesn't exist in the symbol table\n";
    return true;
  }
  symbolt function_symbol = symbol_table.lookup_ref(function_name);
  const irep_idt stub_function_name = stub_name_of_function(function_name);
  function_symbol.name = stub_function_name;
  function_symbol.location = source_locationt();

  // Question: Maybe I should also change the symbol module?
  function_symbol.base_name = stub_function_name;
  function_symbol.pretty_name = stub_function_name;

  if(symbol_table.has_symbol(function_symbol.name))
  {
    log.error() << "The internal stub implementation name: "
                << function_symbol.name
                << "already exists in the symbol table\n";
    return true;
  }
  symbol_table.add(function_symbol);
  stub_function(function_name, function_body);

  // Delete all other functions and just keep the stub so that we can
  // output it in C
  goto_functions.function_map[function_name].copy_from(function_body);
  goto_functions.update();
  return false;
}

// This is copied from code_contracts.cpp
//
// Question: Probably something like that exists in some utils library
const symbolt &stub_functiont::new_tmp_symbol(
  const typet &type,
  const source_locationt &source_location,
  const irep_idt &function_id,
  const irep_idt &mode)
{
  return get_fresh_aux_symbol(
    type,
    id2string(function_id) + "::tmp_cc",
    "tmp_cc",
    source_location,
    mode,
    symbol_table);
}

bool stub_function(
  goto_modelt &goto_model,
  const std::string &function_name,
  messaget &log)
{
  return stub_functiont(
    goto_model.symbol_table, goto_model.goto_functions, function_name, log)();
}

const std::string stub_name_of_function(const irep_idt &function_name)
{
  std::stringstream ss;
  ss << "__stub_" << function_name << "_impl";
  return ss.str();
}
