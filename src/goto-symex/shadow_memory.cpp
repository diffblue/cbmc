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
#include <util/pointer_expr.h>
#include <util/prefix.h>
#include <util/string_constant.h>

#include <langapi/language_util.h>
#include <linking/static_lifetime_init.h>

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

// TODO: the following 4 functions (`symex_field_static_init`,
//                                  `symex_field_static_init_string_constant`,
//                                  `symex_field_local_init`,
//                                  `symex_field_dynamic_init`) do filtering on
//  the input symbol name and then call `initialize_shadow_memory` accordingly.
//  We want to refactor and improve the way the filtering is done, but given
//  that we don't have an easy mechanism to validate that we haven't changed the
//  behaviour, we want to postpone changing this until the full shadow memory
//  functionalities are integrated and we have good regression/unit testing.

void shadow_memoryt::symex_field_static_init(
  goto_symex_statet &state,
  const ssa_exprt &lhs)
{
  if(lhs.get_original_expr().id() != ID_symbol)
    return;

  const irep_idt &identifier =
    to_symbol_expr(lhs.get_original_expr()).get_identifier();

  if(state.source.function_id != INITIALIZE_FUNCTION)
    return;

  if(
    has_prefix(id2string(identifier), CPROVER_PREFIX) &&
    !has_prefix(id2string(identifier), CPROVER_PREFIX "errno"))
  {
    return;
  }

  const symbolt &symbol = ns.lookup(identifier);

  if(
    (id2string(symbol.name).find("::return_value") == std::string::npos &&
     symbol.is_auxiliary) ||
    !symbol.is_static_lifetime)
    return;
  if(id2string(symbol.name).find("__cs_") != std::string::npos)
    return;

  const typet &type = symbol.type;
  log.debug() << "Shadow memory: global memory " << id2string(identifier)
              << " of type " << from_type(ns, "", type) << messaget::eom;

  initialize_shadow_memory(
    state, lhs, state.shadow_memory.fields.global_fields);
}

void shadow_memoryt::symex_field_static_init_string_constant(
  goto_symex_statet &state,
  const ssa_exprt &expr,
  const exprt &rhs)
{
  if(
    expr.get_original_expr().id() == ID_symbol &&
    has_prefix(
      id2string(to_symbol_expr(expr.get_original_expr()).get_identifier()),
      CPROVER_PREFIX))
  {
    return;
  }
  const index_exprt &index_expr =
    to_index_expr(to_address_of_expr(rhs).object());

  const typet &type = index_expr.array().type();
  log.debug() << "Shadow memory: global memory "
              << id2string(to_string_constant(index_expr.array()).get_value())
              << " of type " << from_type(ns, "", type) << messaget::eom;

  initialize_shadow_memory(
    state, index_expr.array(), state.shadow_memory.fields.global_fields);
}

void shadow_memoryt::symex_field_local_init(
  goto_symex_statet &state,
  const ssa_exprt &expr)
{
  const symbolt &symbol =
    ns.lookup(to_symbol_expr(expr.get_original_expr()).get_identifier());

  const std::string symbol_name = id2string(symbol.name);
  if(
    symbol.is_auxiliary &&
    symbol_name.find("::return_value") == std::string::npos)
    return;
  if(
    symbol_name.find("malloc::") != std::string::npos &&
    (symbol_name.find("malloc_size") != std::string::npos ||
     symbol_name.find("malloc_res") != std::string::npos ||
     symbol_name.find("record_malloc") != std::string::npos ||
     symbol_name.find("record_may_leak") != std::string::npos))
  {
    return;
  }
  if(
    symbol_name.find("__builtin_alloca::") != std::string::npos &&
    (symbol_name.find("alloca_size") != std::string::npos ||
     symbol_name.find("record_malloc") != std::string::npos ||
     symbol_name.find("record_alloca") != std::string::npos ||
     symbol_name.find("res") != std::string::npos))
  {
    return;
  }
  if(symbol_name.find("__cs_") != std::string::npos)
    return;

  const typet &type = expr.type();
  ssa_exprt expr_l1 = remove_level_2(expr);
  log.debug() << "Shadow memory: local memory "
              << id2string(expr_l1.get_identifier()) << " of type "
              << from_type(ns, "", type) << messaget::eom;

  initialize_shadow_memory(
    state, expr_l1, state.shadow_memory.fields.local_fields);
}

void shadow_memoryt::symex_field_dynamic_init(
  goto_symex_statet &state,
  const exprt &expr,
  const side_effect_exprt &code)
{
  log.debug() << "Shadow memory: dynamic memory of type "
              << from_type(ns, "", expr.type()) << messaget::eom;

  initialize_shadow_memory(
    state, expr, state.shadow_memory.fields.global_fields);
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
