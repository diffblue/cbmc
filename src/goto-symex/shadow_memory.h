/*******************************************************************\

Module: Symex Shadow Memory Instrumentation

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Symex Shadow Memory Instrumentation

#ifndef CPROVER_GOTO_SYMEX_SHADOW_MEMORY_H
#define CPROVER_GOTO_SYMEX_SHADOW_MEMORY_H

#include <util/expr.h>
#include <util/message.h>
#include <util/std_expr.h>

#include "shadow_memory_field_definitions.h"

#define SHADOW_MEMORY_PREFIX "SM__"
#define SHADOW_MEMORY_FIELD_DECL "field_decl"
#define SHADOW_MEMORY_GLOBAL_SCOPE "_global"
#define SHADOW_MEMORY_LOCAL_SCOPE "_local"
#define SHADOW_MEMORY_GET_FIELD "get_field"
#define SHADOW_MEMORY_SET_FIELD "set_field"

class code_function_callt;
class abstract_goto_modelt;
class goto_symex_statet;
class side_effect_exprt;
class ssa_exprt;

/// \brief The shadow memory instrumentation performed during symbolic execution
class shadow_memoryt
{
public:
  shadow_memoryt(
    const std::function<void(goto_symex_statet &, const exprt &, const exprt &)>
      symex_assign,
    const namespacet &ns,
    message_handlert &message_handler)
    : symex_assign(symex_assign), ns(ns), log(message_handler)
  {
  }

  /// Gathers the available shadow memory field definitions
  /// (__CPROVER_field_decl calls) from the goto model.
  /// \param goto_model The goto model
  /// \param message_handler For logging
  /// \return The field definitions
  static shadow_memory_field_definitionst gather_field_declarations(
    abstract_goto_modelt &goto_model,
    message_handlert &message_handler);

  /// Initialize global-scope shadow memory for global/static variables.
  /// \param state The symex state
  /// \param lhs The LHS expression of the initializer assignment
  void symex_field_static_init(goto_symex_statet &state, const ssa_exprt &lhs);

  /// Initialize global-scope shadow memory for string constants.
  /// \param state The symex state
  /// \param expr The defined symbol expression
  /// \param rhs The RHS expression of the initializer assignment
  void symex_field_static_init_string_constant(
    goto_symex_statet &state,
    const ssa_exprt &expr,
    const exprt &rhs);

  /// Initialize local-scope shadow memory for local variables and parameters.
  /// \param state The symex state
  /// \param expr The declared symbol expression
  void symex_field_local_init(goto_symex_statet &state, const ssa_exprt &expr);

  /// Initialize global-scope shadow memory for dynamically allocated memory.
  /// \param state The symex state
  /// \param expr The dynamic object symbol expression
  /// \param code The allocation side effect code
  void symex_field_dynamic_init(
    goto_symex_statet &state,
    const exprt &expr,
    const side_effect_exprt &code);

  /// Symbolically executes a __CPROVER_get_field call
  /// \param state The symex state
  /// \param lhs The LHS of the call
  /// \param arguments The call arguments
  void symex_get_field(
    goto_symex_statet &state,
    const exprt &lhs,
    const exprt::operandst &arguments);

  /// Symbolically executes a __CPROVER_set_field call
  /// \param state The symex state
  /// \param arguments The call arguments
  void
  symex_set_field(goto_symex_statet &state, const exprt::operandst &arguments);

private:
  /// Converts a field declaration
  /// \param code_function_call The __CPROVER_field_decl_* call
  /// \param fields The field declaration to be extended
  void convert_field_declaration(
    const code_function_callt &code_function_call,
    shadow_memory_field_definitionst::field_definitiont &fields);

  /// Allocates and initializes a shadow memory field for the given original
  /// memory.
  /// \param state The symex state
  /// \param expr The expression for which shadow memory should be allocated
  /// \param fields The field definition to be used
  void initialize_shadow_memory(
    goto_symex_statet &state,
    const exprt &expr,
    const shadow_memory_field_definitionst::field_definitiont &fields);

  /// Registers a shadow memory field for the given original memory
  /// \param state The symex state
  /// \param expr The expression for which shadow memory should be allocated
  /// \param field_name The field name
  /// \param field_type The field type
  /// \return The resulting shadow memory symbol expression
  symbol_exprt add_field(
    goto_symex_statet &state,
    const exprt &expr,
    const irep_idt &field_name,
    const typet &field_type);

private:
  const std::function<void(goto_symex_statet &, const exprt &, const exprt)>
    symex_assign;
  const namespacet &ns;
  messaget log;
};

#endif // CPROVER_GOTO_SYMEX_SHADOW_MEMORY_H
