/*******************************************************************\

Module: Symex Shadow Memory Instrumentation

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Symex Shadow Memory Instrumentation

#include "shadow_memory.h"

#include <util/fresh_symbol.h>

#include <langapi/language_util.h>

#include "goto_symex_state.h"

void shadow_memoryt::initialize_shadow_memory(
  goto_symex_statet &state,
  const exprt &expr,
  const shadow_memory_field_definitionst::field_definitiont &fields)
{
  // To be implemented
}

symbol_exprt shadow_memoryt::add_field(
  goto_symex_statet &state,
  const exprt &expr,
  const irep_idt &field_name,
  const typet &field_type)
{
  // To be completed

  const auto &function_symbol = ns.lookup(state.source.function_id);

  symbolt &new_symbol = get_fresh_aux_symbol(
    field_type,
    id2string(state.source.function_id),
    SHADOW_MEMORY_PREFIX + from_expr(expr) + "__" + id2string(field_name),
    state.source.pc->source_location(),
    function_symbol.mode,
    state.symbol_table);

  // Call some function on ns to silence the compiler in the meanwhile.
  ns.get_symbol_table();

  return new_symbol.symbol_expr();
}

void shadow_memoryt::symex_set_field(
  goto_symex_statet &state,
  const exprt::operandst &arguments)
{
  // To be implemented
}

void shadow_memoryt::symex_get_field(
  goto_symex_statet &state,
  const exprt &lhs,
  const exprt::operandst &arguments)
{
  // To be implemented
}

void shadow_memoryt::symex_field_static_init(
  goto_symex_statet &state,
  const ssa_exprt &lhs)
{
  // To be implemented
}

void shadow_memoryt::symex_field_static_init_string_constant(
  goto_symex_statet &state,
  const ssa_exprt &expr,
  const exprt &rhs)
{
  // To be implemented
}

void shadow_memoryt::symex_field_local_init(
  goto_symex_statet &state,
  const ssa_exprt &expr)
{
  // To be implemented
}

void shadow_memoryt::symex_field_dynamic_init(
  goto_symex_statet &state,
  const exprt &expr,
  const side_effect_exprt &code)
{
  // To be implemented
}

shadow_memory_field_definitionst shadow_memoryt::gather_field_declarations(
  abstract_goto_modelt &goto_model,
  message_handlert &message_handler)
{
  // To be implemented

  return shadow_memory_field_definitionst();
}

void shadow_memoryt::convert_field_declaration(
  const code_function_callt &code_function_call,
  shadow_memory_field_definitionst::field_definitiont &fields)
{
  // To be implemented
}
