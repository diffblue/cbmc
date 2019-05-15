/*******************************************************************\

Module: Program Transformation

Author: diffblue

\*******************************************************************/

/// \file
/// Program Transformation

#include "collect_function_pointer_targets.h"

#include <analyses/does_remove_const.h>

collect_function_pointer_targetst::collect_function_pointer_targetst(
  message_handlert &message_handler,
  const symbol_tablet &symbol_table,
  bool only_resolve_const_fps)
  : log(message_handler),
    ns(symbol_table),
    symbol_table(symbol_table),
    only_resolve_const_fps(only_resolve_const_fps),
    initialised(false)
{
}

void collect_function_pointer_targetst::initialise_taken_addresses(
  const goto_functionst &goto_functions)
{
  for(const auto &s : symbol_table.symbols)
    compute_address_taken_functions(s.second.value, address_taken);

  compute_address_taken_functions(goto_functions, address_taken);
}

void collect_function_pointer_targetst::initialise_type_map(
  const goto_functionst &goto_functions)
{
  for(const auto &fmap_pair : goto_functions.function_map)
    type_map.emplace(fmap_pair.first, fmap_pair.second.type);
}

possible_fp_targets_mapt collect_function_pointer_targetst::
operator()(const goto_functionst &goto_functions)
{
  if(!initialised)
  {
    initialise_taken_addresses(goto_functions);
    initialise_type_map(goto_functions);
    initialised = true;
  }

  possible_fp_targets_mapt target_map;
  for(const auto &function_pair : goto_functions.function_map)
  {
    const auto &instructions = function_pair.second.body.instructions;
    for(auto target = instructions.begin(); target != instructions.end();
        target++)
    {
      if(
        target->is_function_call() &&
        target->get_function_call().function().id() == ID_dereference)
      {
        const auto &function = target->get_function_call().function();
        irep_idt callee_id = get_callee_id(function);
        CHECK_RETURN(!callee_id.empty());
        if(target_map.count(callee_id) == 0)
        {
          target_map.emplace(
            callee_id, get_function_pointer_targets(goto_functions, target));
        }
      }
    }
  }
  return target_map;
}

fp_state_targetst
collect_function_pointer_targetst::get_function_pointer_targets(
  const goto_functionst &goto_functions,
  goto_programt::const_targett &call_site)
{
  PRECONDITION(initialised);

  fp_state_targetst stateful_targets;
  auto &fp_state = stateful_targets.first;
  auto &functions = stateful_targets.second;

  for(const auto &function_pair : goto_functions.function_map)
  {
    const auto &function_body = function_pair.second.body;
    const auto &candidates =
      get_function_pointer_targets(function_body, call_site);

    functions.insert(candidates.second.begin(), candidates.second.end());
    fp_state.merge(candidates.first);
  }
  return stateful_targets;
}

fp_state_targetst
collect_function_pointer_targetst::get_function_pointer_targets(
  const goto_programt &goto_program,
  goto_programt::const_targett &call_site)
{
  PRECONDITION(call_site->is_function_call());

  const code_function_callt &code = call_site->get_function_call();
  const auto &function = to_dereference_expr(code.function());
  const auto &refined_call_type = refine_call_type(function.type(), code);

  auto stateful_targets = try_remove_const_fp(goto_program, function.pointer());
  auto &fp_state = stateful_targets.first;
  auto &functions = stateful_targets.second;

  fp_state.precise_const_removal =
    !fp_state.code_removes_const && functions.size() == 1;

  if(
    !fp_state.precise_const_removal && !fp_state.remove_const_found_functions &&
    !only_resolve_const_fps)
  {
    // get all type-compatible functions
    // whose address is ever taken
    for(const auto &type_pair : type_map)
    {
      const auto &candidate_function_name = type_pair.first;
      const auto &candidate_function_type = type_pair.second;

      // only accept as candidate functions such that:
      // 1. their address was taken
      // 2. their type is compatible with the call-site-function type
      // 3. they're not pthread mutex clean-up
      if(
        address_taken.find(candidate_function_name) != address_taken.end() &&
        is_type_compatible(
          code.lhs().is_not_nil(),
          refined_call_type,
          candidate_function_type,
          ns) &&
        candidate_function_name != "pthread_mutex_cleanup")
      {
        functions.insert(
          symbol_exprt{candidate_function_name, candidate_function_type});
      }
    }
  }
  return stateful_targets;
}

fp_state_targetst collect_function_pointer_targetst::try_remove_const_fp(
  const goto_programt &goto_program,
  const exprt &pointer)
{
  fp_state_targetst stateful_targets;
  auto &fp_state = stateful_targets.first;
  auto &functions = stateful_targets.second;

  does_remove_constt const_removal_check(goto_program, ns);
  fp_state.code_removes_const = const_removal_check().first;

  if(fp_state.code_removes_const)
  {
    fp_state.remove_const_found_functions = false;
  }
  else
  {
    remove_const_function_pointerst fpr(
      log.get_message_handler(), ns, symbol_table);
    fp_state.remove_const_found_functions = fpr(pointer, functions);
    CHECK_RETURN(fp_state.remove_const_found_functions || functions.empty());
  }
  return stateful_targets;
}

code_typet collect_function_pointer_targetst::refine_call_type(
  const typet &type,
  const code_function_callt &code)
{
  PRECONDITION(can_cast_type<code_typet>(type));
  code_typet call_type = to_code_type(type);

  if(call_type.has_ellipsis() && call_type.parameters().empty())
  {
    call_type.remove_ellipsis();
    for(const auto &argument : code.arguments())
      call_type.parameters().push_back(code_typet::parametert{argument.type()});
  }
  return call_type;
}

irep_idt
collect_function_pointer_targetst::get_callee_id(const exprt &called_function)
{
  irep_idt callee_id;
  bool contains_code = false;
  auto type_contains_code = [&contains_code](const typet &t) {
    if(t.id() == ID_code)
      contains_code = true;
  };

  called_function.visit_post(
    [&callee_id, &type_contains_code, &contains_code](const exprt &e) {
      if(e.id() == ID_symbol)
      {
        e.type().visit(type_contains_code);
        if(contains_code)
        {
          callee_id = to_symbol_expr(e).get_identifier();
          return;
        }
      }
      if(e.id() == ID_dereference)
      {
        const auto &pointer = to_dereference_expr(e).pointer();
        if(pointer.id() == ID_symbol)
          callee_id = to_symbol_expr(pointer).get_identifier();
        if(pointer.id() == ID_member)
        {
          pointer.type().visit(type_contains_code);
          if(contains_code)
            callee_id = to_member_expr(pointer).get_component_name();
        }
      }
    });
  return callee_id;
}

bool collect_function_pointer_targetst::arg_is_type_compatible(
  const typet &call_type,
  const typet &function_type,
  const namespacet &name_space)
{
  if(call_type == function_type)
    return true;

  // any integer-vs-enum-vs-pointer is ok
  if(
    call_type.id() == ID_signedbv || call_type.id() == ID_unsigned ||
    call_type.id() == ID_bool || call_type.id() == ID_c_bool ||
    call_type.id() == ID_c_enum_tag || call_type.id() == ID_c_enum ||
    call_type.id() == ID_pointer)
  {
    return function_type.id() == ID_signedbv ||
           function_type.id() == ID_unsigned || function_type.id() == ID_bool ||
           function_type.id() == ID_c_bool ||
           function_type.id() == ID_pointer ||
           function_type.id() == ID_c_enum ||
           function_type.id() == ID_c_enum_tag;
  }

  return pointer_offset_bits(call_type, name_space) ==
         pointer_offset_bits(function_type, name_space);
}

bool collect_function_pointer_targetst::is_type_compatible(
  bool return_value_used,
  const code_typet &call_type,
  const code_typet &function_type,
  const namespacet &name_space)
{
  // we are willing to ignore anything that's returned
  // if we call with 'void'
  if(
    return_value_used && call_type.return_type() != empty_typet() &&
    !arg_is_type_compatible(
      call_type.return_type(), function_type.return_type(), name_space))
    return false;

  // let's look at the parameters
  const auto &call_parameters = call_type.parameters();
  const auto &function_parameters = function_type.parameters();

  if(function_type.has_ellipsis() && function_parameters.empty())
    return true;
  if(call_type.has_ellipsis() && call_parameters.empty())
    return true;

  // we are quite strict here, could be much more generous
  if(call_parameters.size() != function_parameters.size())
    return false;

  for(std::size_t i = 0; i < call_parameters.size(); i++)
    if(!arg_is_type_compatible(
         call_parameters[i].type(), function_parameters[i].type(), name_space))
      return false;
  return true;
}

possible_fp_targets_mapt get_function_pointer_targets(
  message_handlert &message_handler,
  const goto_functionst &goto_functions,
  const symbol_tablet &symbol_table,
  bool only_resolve_const_fps)
{
  collect_function_pointer_targetst collector(
    message_handler, symbol_table, only_resolve_const_fps);

  return collector(goto_functions);
}
