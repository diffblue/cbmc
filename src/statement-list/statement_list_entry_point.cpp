/*******************************************************************\

Module: Statement List Language Entry Point

Author: Matthias Weiss, matthias.weiss@diffblue.com

\*******************************************************************/

/// \file
/// Statement List Language Entry Point

#include "statement_list_entry_point.h"

#include <goto-programs/adjust_float_expressions.h>
#include <goto-programs/goto_functions.h>

#include <linking/static_lifetime_init.h>

#include <util/c_types.h>
#include <util/config.h>
#include <util/message.h>
#include <util/pointer_expr.h>
#include <util/std_code.h>
#include <util/symbol_table.h>

/// Postfix for the artificial data block that is created when calling a main
/// symbol that is a function block.
#define DB_ENTRY_POINT_POSTFIX "_entry_point"

/// Name of the CPROVER-specific hide label.
#define CPROVER_HIDE CPROVER_PREFIX "HIDE"

/// Searches for symbols with the given name (which is considered to be the
/// name of the main symbol) and returns false if there is exactly one symbol
/// with that name in the given symbol table. Prints an error message and
/// returns true if there are multiple or no matches.
/// \param symbol_table: Symbol table to search through.
/// \param message_handler: Used for printing error messages.
/// \param main_symbol_name: Name of the symbol to look for.
/// \return False if there is exactly one match, true otherwise.
static bool is_main_symbol_invalid(
  const symbol_tablet &symbol_table,
  message_handlert &message_handler,
  const irep_idt &main_symbol_name)
{
  bool found = false;

  for(const std::pair<const irep_idt, symbolt> &pair : symbol_table)
  {
    if(pair.first == main_symbol_name && pair.second.type.id() == ID_code)
    {
      if(found)
      {
        messaget message(message_handler);
        message.error() << "main symbol `" << main_symbol_name
                        << "' is ambiguous" << messaget::eom;
        return true;
      }
      else
        found = true;
    }
  }

  if(found)
    return false;
  else
  {
    messaget message(message_handler);
    message.error() << "main symbol `" << main_symbol_name << "' not found"
                    << messaget::eom;
    return true;
  }
}

/// Creates a call to __CPROVER_initialize and adds it to the start function's
/// body.
/// \param [out] function_body: Body of the start function.
/// \param symbol_table: Symbol table, containing the symbol for
///   __CPROVER_initialize.
/// \param main_symbol_location: Source location of the main symbol.
static void add_initialize_call(
  code_blockt &function_body,
  const symbol_tablet &symbol_table,
  const source_locationt &main_symbol_location)
{
  symbolt init = symbol_table.lookup_ref(INITIALIZE_FUNCTION);
  code_function_callt call_init{init.symbol_expr()};
  call_init.add_source_location() = main_symbol_location;
  function_body.add(call_init);
}

/// Creates a call to the main function block and adds it to the start
/// function's body.
/// \param [out] function_body: Body of the start function.
/// \param symbol_table: Symbol table, containing the main symbol.
/// \param main_function_block: Main symbol of this application.
static void add_main_function_block_call(
  code_blockt &function_body,
  symbol_tablet &symbol_table,
  const symbolt &main_function_block)
{
  const code_typet &function_type = to_code_type(main_function_block.type);
  PRECONDITION(1u == function_type.parameters().size());
  const code_typet::parametert &data_block_interface =
    function_type.parameters().front();
  symbolt instance_data_block;
  instance_data_block.name =
    id2string(data_block_interface.get_base_name()) + DB_ENTRY_POINT_POSTFIX;
  instance_data_block.type =
    to_type_with_subtype(data_block_interface.type()).subtype();
  instance_data_block.is_static_lifetime = true;
  instance_data_block.mode = ID_statement_list;
  symbol_table.add(instance_data_block);
  const address_of_exprt data_block_ref{instance_data_block.symbol_expr()};

  code_function_callt::argumentst args{data_block_ref};
  code_function_callt call_main{main_function_block.symbol_expr(), args};
  call_main.add_source_location() = main_function_block.location;
  function_body.add(call_main);
}

/// Creates __CPROVER_initialize and adds it to the symbol table.
/// \param [out] symbol_table: Symbol table that should contain the function.
static void generate_statement_list_init_function(symbol_tablet &symbol_table)
{
  symbolt init;
  init.name = INITIALIZE_FUNCTION;
  init.mode = ID_statement_list;
  init.type = code_typet({}, empty_typet{});

  code_blockt dest;
  dest.add(code_labelt(CPROVER_HIDE, code_skipt()));

  for(const std::pair<const irep_idt, symbolt> &pair : symbol_table)
  {
    const symbolt &symbol = pair.second;
    if(symbol.is_static_lifetime && symbol.value.is_not_nil())
      dest.add(code_assignt{pair.second.symbol_expr(), pair.second.value});
  }
  init.value = std::move(dest);
  symbol_table.add(init);
}

/// Creates __CPROVER_rounding_mode and adds it to the symbol table.
/// \param [out] symbol_table: Symbol table that should contain the symbol.
static void generate_rounding_mode(symbol_tablet &symbol_table)
{
  symbolt rounding_mode;
  rounding_mode.name = rounding_mode_identifier();
  rounding_mode.type = signed_int_type();
  rounding_mode.is_thread_local = true;
  rounding_mode.is_static_lifetime = true;
  const constant_exprt rounding_val{
    std::to_string(ieee_floatt::rounding_modet::ROUND_TO_EVEN),
    signed_int_type()};
  rounding_mode.value = rounding_val;
  symbol_table.add(rounding_mode);
}

/// Creates a start function and adds it to the symbol table. This start
/// function contains calls to __CPROVER_initialize and the main symbol.
/// \param main: Main symbol of this application.
/// \param [out] symbol_table: Symbol table that should contain the function.
/// \param message_handler: Handler that is responsible for error messages.
bool generate_statement_list_start_function(
  const symbolt &main,
  symbol_tablet &symbol_table,
  message_handlert &message_handler)
{
  PRECONDITION(!main.value.is_nil());
  code_blockt start_function_body;
  start_function_body.add(code_labelt(CPROVER_HIDE, code_skipt()));

  add_initialize_call(start_function_body, symbol_table, main.location);
  // TODO: Support calls to STL functions.
  // Since STL function calls do not involve a data block, pass all arguments
  // as normal parameters.
  add_main_function_block_call(start_function_body, symbol_table, main);

  // Add the start symbol.
  symbolt start_symbol;
  start_symbol.name = goto_functionst::entry_point();
  start_symbol.type = code_typet({}, empty_typet{});
  start_symbol.value.swap(start_function_body);
  start_symbol.mode = main.mode;

  if(!symbol_table.insert(std::move(start_symbol)).second)
  {
    messaget message(message_handler);
    message.error() << "failed to insert start symbol" << messaget::eom;
    return true;
  }

  return false;
}

bool statement_list_entry_point(
  symbol_tablet &symbol_table,
  message_handlert &message_handler)
{
  // Check if the entry point is already present and return if it is.
  if(
    symbol_table.symbols.find(goto_functionst::entry_point()) !=
    symbol_table.symbols.end())
    return false;

  irep_idt main_symbol_name;

  // Find main symbol given by the user.
  if(config.main.has_value())
  {
    if(is_main_symbol_invalid(
         symbol_table, message_handler, config.main.value()))
      return true;
    main_symbol_name = config.main.value();
  }
  // Fallback: Search for block with TIA main standard name.
  // TODO: Support the standard entry point of STL (organisation blocks).
  // This also requires to expand the grammar and typecheck.
  else
  {
    if(is_main_symbol_invalid(
         symbol_table, message_handler, ID_statement_list_main_function))
      return true;
    main_symbol_name = ID_statement_list_main_function;
  }

  const symbolt &main = symbol_table.lookup_ref(main_symbol_name);

  // Check if the symbol has a body.
  if(main.value.is_nil())
  {
    messaget message(message_handler);
    message.error() << "main symbol `" << id2string(main_symbol_name)
                    << "' has no body" << messaget::eom;
    return true;
  }

  generate_rounding_mode(symbol_table);
  generate_statement_list_init_function(symbol_table);
  return generate_statement_list_start_function(
    main, symbol_table, message_handler);
}
