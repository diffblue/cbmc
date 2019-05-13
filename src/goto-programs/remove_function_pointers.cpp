/*******************************************************************\

Module: Program Transformation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Program Transformation

#include "remove_function_pointers.h"

#include <cassert>

#include <util/c_types.h>
#include <util/fresh_symbol.h>
#include <util/invariant.h>
#include <util/message.h>
#include <util/pointer_offset_size.h>
#include <util/replace_expr.h>
#include <util/source_location.h>
#include <util/std_expr.h>

#include <analyses/does_remove_const.h>

#include "remove_skip.h"
#include "compute_called_functions.h"
#include "remove_const_function_pointers.h"

class remove_function_pointerst
{
public:
  remove_function_pointerst(
    message_handlert &_message_handler,
    symbol_tablet &_symbol_table,
    bool _add_safety_assertion,
    bool only_resolve_const_fps,
    const goto_functionst &goto_functions);

  /// Call the function pointer removal via an operator
  /// \param goto_functions: functions to modify
  /// \param target_map: candidate functions
  void operator()(
    goto_functionst &goto_functions,
    const possible_fp_targets_mapt &target_map);

  // a set of function symbols
  using functionst = remove_const_function_pointerst::functionst;
  /// Call the function pointer removal within the \p goto_program
  /// \param goto_program: program to modify
  /// \param function_id: identifier of the function pointer to be removed
  /// \param target_map: candidate functions
  bool remove_function_pointers(
    goto_programt &goto_program,
    const irep_idt &function_id,
    const possible_fp_targets_mapt &target_map);


protected:
  messaget log;
  const namespacet ns;
  symbol_tablet &symbol_table;
  bool add_safety_assertion;

  // We can optionally halt the FP removal if we aren't able to use
  // remove_const_function_pointerst to successfully narrow to a small
  // subset of possible functions and just leave the function pointer
  // as it is.
  // This can be activated in goto-instrument using
  // --remove-const-function-pointers instead of --remove-function-pointers
  bool only_resolve_const_fps;

  /// Replace a call to a dynamic function at location
  /// \p target in the given goto-program by a case-split
  /// over a given set of functions
  /// \param goto_program: The goto program that contains target
  /// \param function_id: Name of function containing the target
  /// \param target: location with function call with function pointer
  /// \param functions: the set of functions to consider
  void remove_function_pointer(
    goto_programt &goto_program,
    const irep_idt &function_id,
    goto_programt::targett target,
    const possible_fp_targetst &functions);

  /// Replace a call to a dynamic function at location
  /// target in the given goto-program by determining
  /// functions that have a compatible signature
  /// \param goto_program: The goto program that contains target
  /// \param function_id: Name of function containing the target
  /// \param target: location with function call with function pointer
  /// \param stateful_targets: the set of functions to consider
  void remove_function_pointer(
    goto_programt &goto_program,
    const irep_idt &function_id,

    goto_programt::targett target,
    const fp_state_targetst &stateful_targets);

  void fix_argument_types(code_function_callt &function_call);
  void fix_return_type(
    const irep_idt &in_function_id,
    code_function_callt &function_call,
    goto_programt &dest);

  /// From *fp() build the following sequence of instructions:
  ///
  /// if (fp=&f1) then goto loc1
  /// if (fp=&f2) then goto loc2
  /// ..
  /// if (fp=&fn) then goto locN
  /// loc1:  f1(); goto N+1;
  /// loc2:  f2(); goto N+1;
  /// ..
  /// locN:  fn(); goto N+1;
  /// locN+1:
  ///
  /// \param functions: set of function candidates
  /// \param code: the original function call
  /// \param function_id: name of the function
  /// \param target: iterator to the target call-site
  /// \return the GOTO program for the new code
  goto_programt build_new_code(
    const functionst &functions,
    const code_function_callt &code,
    const irep_idt &function_id,
    goto_programt::targett target);

  /// Log the statistics collected during this analysis
  /// \param target: iterator to the target call-site
  /// \param functions: the set of function candidates
  void remove_function_pointer_log(
    goto_programt::targett target,
    const functionst &functions) const;

};

remove_function_pointerst::remove_function_pointerst(
  message_handlert &_message_handler,
  symbol_tablet &_symbol_table,
  bool _add_safety_assertion,
  bool only_resolve_const_fps,
  const goto_functionst &goto_functions)
  : log(_message_handler),
    ns(_symbol_table),
    symbol_table(_symbol_table),
    add_safety_assertion(_add_safety_assertion),
    only_resolve_const_fps(only_resolve_const_fps)
{
}

void remove_function_pointerst::fix_argument_types(
  code_function_callt &function_call)
{
  const code_typet &code_type = to_code_type(function_call.function().type());

  const code_typet::parameterst &function_parameters=
    code_type.parameters();

  code_function_callt::argumentst &call_arguments=
    function_call.arguments();

  for(std::size_t i=0; i<function_parameters.size(); i++)
  {
    if(i<call_arguments.size())
    {
      if(call_arguments[i].type() != function_parameters[i].type())
      {
        call_arguments[i] =
          typecast_exprt(call_arguments[i], function_parameters[i].type());
      }
    }
  }
}

void remove_function_pointerst::fix_return_type(
  const irep_idt &in_function_id,
  code_function_callt &function_call,
  goto_programt &dest)
{
  // are we returning anything at all?
  if(function_call.lhs().is_nil())
    return;

  const code_typet &code_type = to_code_type(function_call.function().type());

  // type already ok?
  if(function_call.lhs().type() == code_type.return_type())
    return;

  const symbolt &function_symbol =
    ns.lookup(to_symbol_expr(function_call.function()).get_identifier());

  symbolt &tmp_symbol = get_fresh_aux_symbol(
    code_type.return_type(),
    id2string(in_function_id),
    "tmp_return_val_" + id2string(function_symbol.base_name),
    function_call.source_location(),
    function_symbol.mode,
    symbol_table);

  const symbol_exprt tmp_symbol_expr = tmp_symbol.symbol_expr();

  exprt old_lhs=function_call.lhs();
  function_call.lhs()=tmp_symbol_expr;

  dest.add(goto_programt::make_assignment(
    code_assignt(old_lhs, typecast_exprt(tmp_symbol_expr, old_lhs.type()))));
}

void remove_function_pointerst::remove_function_pointer(
  goto_programt &goto_program,
  const irep_idt &function_id,
  goto_programt::targett target,
  const fp_state_targetst &stateful_targets)
{
  const auto &fp_state = stateful_targets.first;
  const auto &functions = stateful_targets.second;
  if(fp_state.precise_const_removal)
  {
    auto call = target->get_function_call();
    call.function() = *functions.cbegin();
    target->set_function_call(call);
  }
  else if(fp_state.remove_const_found_functions || !only_resolve_const_fps)
  {
    // If this mode is enabled, we only remove function pointers
    // that we can resolve either to an exact function, or an exact subset
    // (e.g. a variable index in a constant array).
    // Since we haven't found functions, we would now resort to
    // replacing the function pointer with any function with a valid signature
    // Since we don't want to do that, we abort.
    remove_function_pointer(goto_program, function_id, target, functions);
  }
}

void remove_function_pointerst::remove_function_pointer(
  goto_programt &goto_program,
  const irep_idt &function_id,
  goto_programt::targett target,
  const possible_fp_targetst &functions)
{
  const code_function_callt &code = target->get_function_call();
  const exprt &function = code.function();

  goto_programt::targett next_target=target;
  next_target++;

  goto_program.destructive_insert(next_target, new_code);

  // We preserve the original dereferencing to possibly catch
  // further pointer-related errors.
  code_expressiont code_expression(function);
  code_expression.add_source_location()=function.source_location();
  target->code.swap(code_expression);
  target->type=OTHER;

  // report statistics
  remove_function_pointer_log(target, functions);
}

bool remove_function_pointerst::remove_function_pointers(
  goto_programt &goto_program,
  const irep_idt &function_id,
  const possible_fp_targets_mapt &target_map)
{
  bool did_something=false;

  Forall_goto_program_instructions(target, goto_program)
    if(target->is_function_call())
    {
      const code_function_callt &code = target->get_function_call();
      const auto &callee = code.function();

      if(code.function().id()==ID_dereference)
      {
        auto callee_id =
          collect_function_pointer_targetst::get_callee_id(callee);
        CHECK_RETURN(target_map.count(callee_id) > 0);
        remove_function_pointer(
          goto_program, function_id, target, target_map.at(callee_id));
        did_something = true;
      }
    }

  if(did_something)
    remove_skip(goto_program);

  return did_something;
}

void remove_function_pointerst::operator()(
  goto_functionst &functions,
  const possible_fp_targets_mapt &target_map)
{
  bool did_something=false;

  for(goto_functionst::function_mapt::iterator f_it=
      functions.function_map.begin();
      f_it!=functions.function_map.end();
      f_it++)
  {
    goto_programt &goto_program=f_it->second.body;

    if(remove_function_pointers(goto_program, f_it->first, target_map))
      did_something=true;
  }

  if(did_something)
    functions.compute_location_numbers();
}

bool remove_function_pointers(
  message_handlert &_message_handler,
  symbol_tablet &symbol_table,
  const goto_functionst &goto_functions,
  goto_programt &goto_program,
  const irep_idt &function_id,
  bool add_safety_assertion,
  bool only_remove_const_fps)
{
  remove_function_pointerst
    rfp(
      _message_handler,
      symbol_table,
      add_safety_assertion,
      only_remove_const_fps,
      goto_functions);

  return rfp.remove_function_pointers(goto_program, function_id);
}

void remove_function_pointers(
  message_handlert &_message_handler,
  symbol_tablet &symbol_table,
  goto_functionst &goto_functions,
  bool add_safety_assertion,
  bool only_remove_const_fps)
{
  remove_function_pointerst
    rfp(
      _message_handler,
      symbol_table,
      add_safety_assertion,
      only_remove_const_fps,
      goto_functions);

  rfp(goto_functions);
}

void remove_function_pointers(message_handlert &_message_handler,
  goto_modelt &goto_model,
  bool add_safety_assertion,
  bool only_remove_const_fps)
{
  remove_function_pointers(
    _message_handler,
    goto_model.symbol_table,
    goto_model.goto_functions,
    add_safety_assertion,
    only_remove_const_fps);
}

void remove_function_pointers(
  message_handlert &_message_handler,
  goto_modelt &goto_model,
  const possible_fp_targets_mapt &target_map,
  bool add_safety_assertion,
  bool only_remove_const_fps)
{
  remove_function_pointerst rfp(
    _message_handler,
    goto_model.symbol_table,
    add_safety_assertion,
    only_remove_const_fps,
    goto_model.goto_functions);

  rfp(goto_model.goto_functions, target_map);
}

{
  remove_function_pointerst rfp(
    message_handler,
    goto_model.symbol_table,
    false,
    false,
    goto_model.goto_functions);

}

goto_programt remove_function_pointerst::build_new_code(
  const functionst &functions,
  const code_function_callt &code,
  const irep_idt &function_id,
  goto_programt::targett target)
{
  // the final target is a skip
  goto_programt final_skip;
  const exprt &pointer = to_dereference_expr(code.function()).pointer();
  goto_programt::targett t_final = final_skip.add(goto_programt::make_skip());

  goto_programt new_code_calls;
  goto_programt new_code_gotos;
  for(const auto &function : functions)
  {
    // call function
    auto new_call = code;

    new_call.function() = function;

    // the signature of the function might not match precisely
    fix_argument_types(new_call);

    goto_programt tmp;
    fix_return_type(function_id, new_call, tmp);

    auto call = new_code_calls.add(goto_programt::make_function_call(new_call));
    new_code_calls.destructive_append(tmp);

    // goto final
    new_code_calls.add(goto_programt::make_goto(t_final, true_exprt{}));

    // goto to call
    const auto casted_address = typecast_exprt::conditional_cast(
      address_of_exprt{function, pointer_type(function.type())},
      pointer.type());

    const auto goto_it = new_code_gotos.add(
      goto_programt::make_goto(call, equal_exprt{pointer, casted_address}));

    // set locations for the above goto
    irep_idt property_class = goto_it->source_location.get_property_class();
    irep_idt comment = goto_it->source_location.get_comment();
    goto_it->source_location = target->source_location;
    if(!property_class.empty())
      goto_it->source_location.set_property_class(property_class);
    if(!comment.empty())
      goto_it->source_location.set_comment(comment);
  }

  // fall-through
  if(add_safety_assertion)
  {
    goto_programt::targett t =
      new_code_gotos.add(goto_programt::make_assertion(false_exprt{}));
    t->source_location.set_property_class("pointer dereference");
    t->source_location.set_comment("invalid function pointer");
  }
  new_code_gotos.add(goto_programt::make_assumption(false_exprt{}));

  goto_programt new_code;

  // patch them all together
  new_code.destructive_append(new_code_gotos);
  new_code.destructive_append(new_code_calls);
  new_code.destructive_append(final_skip);

  return new_code;
}

void remove_function_pointerst::remove_function_pointer_log(
  goto_programt::targett target,
  const functionst &functions) const
{
  log.statistics().source_location = target->source_location;
  log.statistics() << "replacing function pointer by " << functions.size()
                   << " possible targets" << messaget::eom;

  // list the names of functions when verbosity is at debug level
  log.conditional_output(
    log.debug(), [&functions](messaget::mstreamt &mstream) {
      mstream << "targets: ";

      bool first = true;
      for(const auto &function : functions)
      {
        if(!first)
          mstream << ", ";

        mstream << function.get_identifier();
        first = false;
      }

      mstream << messaget::eom;
    });
}
