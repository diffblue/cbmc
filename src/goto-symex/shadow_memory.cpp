/*******************************************************************\

Module: Symex Shadow Memory Instrumentation

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Symex Shadow Memory Instrumentation

#include "shadow_memory.h"

#include <util/bitvector_types.h>
#include <util/expr_initializer.h>
#include <util/format_expr.h>
#include <util/format_type.h>
#include <util/fresh_symbol.h>

#include <langapi/language_util.h>

#include "goto_symex_state.h"
#include "shadow_memory_util.h"

void shadow_memoryt::initialize_shadow_memory(
  goto_symex_statet &state,
  exprt expr,
  const shadow_memory_field_definitionst::field_definitiont &fields)
{
  typet type = ns.follow(expr.type());
  clean_pointer_expr(expr, type);
  for(const auto &field_pair : fields)
  {
    const symbol_exprt &shadow = add_field(state, expr, field_pair.first, type);

    if(
      field_pair.second.id() == ID_typecast &&
      to_typecast_expr(field_pair.second).op().is_zero())
    {
      const auto zero_value =
        zero_initializer(type, expr.source_location(), ns);
      CHECK_RETURN(zero_value.has_value());

      symex_assign(state, shadow, *zero_value);
    }
    else
    {
      exprt init_expr = field_pair.second;
      if(init_expr.id() == ID_typecast)
        init_expr = to_typecast_expr(field_pair.second).op();
      const auto init_value =
        expr_initializer(type, expr.source_location(), ns, init_expr);
      CHECK_RETURN(init_value.has_value());

      symex_assign(state, shadow, *init_value);
    }

    log.debug() << "Shadow memory: initialize field "
                << id2string(shadow.get_identifier()) << " for " << format(expr)
                << " with initial value " << format(field_pair.second)
                << messaget::eom;
  }
}

const symbol_exprt &shadow_memoryt::add_field(
  goto_symex_statet &state,
  const exprt &expr,
  const irep_idt &field_name,
  const typet &field_type)
{
  const auto &function_symbol = ns.lookup(state.source.function_id);
  const symbolt &new_symbol = get_fresh_aux_symbol(
    field_type,
    id2string(state.source.function_id),
    SHADOW_MEMORY_PREFIX + from_expr(expr) + "__" + id2string(field_name),
    state.source.pc->source_location(),
    function_symbol.mode,
    state.symbol_table);

  auto &addresses = state.shadow_memory.address_fields[field_name];
  addresses.push_back(
    shadow_memory_statet::shadowed_addresst{expr, new_symbol.symbol_expr()});

  return addresses.back().shadow;
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
  const abstract_goto_modelt &goto_model,
  message_handlert &message_handler)
{
  shadow_memory_field_definitionst field_definitions;

  // Gather shadow memory declarations from goto model
  for(const auto &goto_function : goto_model.get_goto_functions().function_map)
  {
    const auto &goto_program = goto_function.second.body;
    forall_goto_program_instructions(target, goto_program)
    {
      if(!target->is_function_call())
        continue;

      const auto &code_function_call = to_code_function_call(target->code());
      const exprt &function = code_function_call.function();

      if(function.id() != ID_symbol)
        continue;

      const irep_idt &identifier = to_symbol_expr(function).get_identifier();

      if(
        identifier ==
        CPROVER_PREFIX SHADOW_MEMORY_FIELD_DECL SHADOW_MEMORY_GLOBAL_SCOPE)
      {
        convert_field_declaration(
          code_function_call,
          field_definitions.global_fields,
          true,
          message_handler);
      }
      else if(
        identifier ==
        CPROVER_PREFIX SHADOW_MEMORY_FIELD_DECL SHADOW_MEMORY_LOCAL_SCOPE)
      {
        convert_field_declaration(
          code_function_call,
          field_definitions.local_fields,
          false,
          message_handler);
      }
    }
  }
  return field_definitions;
}

void shadow_memoryt::convert_field_declaration(
  const code_function_callt &code_function_call,
  shadow_memory_field_definitionst::field_definitiont &fields,
  bool is_global,
  message_handlert &message_handler)
{
  INVARIANT(
    code_function_call.arguments().size() == 2,
    std::string(CPROVER_PREFIX) + SHADOW_MEMORY_FIELD_DECL +
      (is_global ? SHADOW_MEMORY_GLOBAL_SCOPE : SHADOW_MEMORY_LOCAL_SCOPE) +
      " requires 2 arguments");
  irep_idt field_name = extract_field_name(code_function_call.arguments()[0]);

  exprt expr = code_function_call.arguments()[1];

  messaget log(message_handler);
  log.debug() << "Shadow memory: declare " << (is_global ? "global " : "local ")
              << "field " << id2string(field_name) << " of type "
              << format(expr.type()) << messaget::eom;
  if(!can_cast_type<bitvector_typet>(expr.type()))
  {
    throw unsupported_operation_exceptiont(
      "A shadow memory field must be of a bitvector type.");
  }
  if(to_bitvector_type(expr.type()).get_width() > 8)
  {
    throw unsupported_operation_exceptiont(
      "A shadow memory field must not be larger than 8 bits.");
  }

  // record the field's initial value (and type)
  fields[field_name] = expr;
}
