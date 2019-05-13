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

  void operator()(goto_functionst &goto_functions);

  bool remove_function_pointers(
    goto_programt &goto_program,
    const irep_idt &function_id);

  // a set of function symbols
  using functionst = remove_const_function_pointerst::functionst;

  /// Replace a call to a dynamic function at location
  /// target in the given goto-program by a case-split
  /// over a given set of functions
  /// \param goto_program: The goto program that contains target
  /// \param function_id: Name of function containing the target
  /// \param target: location with function call with function pointer
  /// \param functions: The set of functions to consider
  void remove_function_pointer(
    goto_programt &goto_program,
    const irep_idt &function_id,
    goto_programt::targett target,
    const functionst &functions);

  /// Go through the whole model and find all potential function the pointer at
  ///   \p call site may point to
  /// \param goto_model: model to search for potential functions
  /// \param call_site: the call site of the function pointer under analysis
  /// \return the set of the potential functions
  functionst get_function_pointer_targets(
    const goto_modelt &goto_model,
    goto_programt::const_targett &call_site);

  /// Go through a single function body and find all potential function the
  ///   pointer at \p call site may point to
  /// \param goto_program: function body to search for potential functions
  /// \param call_site: the call site of the function pointer under analysis
  /// \return the set of the potential functions
  functionst get_function_pointer_targets(
    const goto_programt &goto_program,
    goto_programt::const_targett &call_site);

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

  // Internal variables for communication between function pointer collection
  //   and the call modification.
  bool remove_const_found_functions;
  bool does_remove_const_success;
  bool only_remove_const_function_pointers_called;

  /// Replace a call to a dynamic function at location
  /// target in the given goto-program by determining
  /// functions that have a compatible signature
  /// \param goto_program: The goto program that contains target
  /// \param function_id: Name of function containing the target
  /// \param target: location with function call with function pointer
  void remove_function_pointer(
    goto_programt &goto_program,
    const irep_idt &function_id,
    goto_programt::targett target);

  bool is_type_compatible(
    bool return_value_used,
    const code_typet &call_type,
    const code_typet &function_type);

  bool arg_is_type_compatible(
    const typet &call_type,
    const typet &function_type);

  void fix_argument_types(code_function_callt &function_call);
  void fix_return_type(
    const irep_idt &in_function_id,
    code_function_callt &function_call,
    goto_programt &dest);

  /// Refine the \p type in case the forward declaration was incomplete
  /// \param type: the type to be refined
  /// \param code: the function call code to get the arguments from
  /// \return the refined call type
  static code_typet
  refine_call_type(const typet &type, const code_function_callt &code);

  /// Try to remove the const function pointers
  /// \param goto_program: the function body to run the const_removal_check on
  /// \param functions: the list of functions the const removal found
  /// \param pointer: the pointer to be resolved
  void try_remove_const_fp(
    const goto_programt &goto_program,
    functionst &functions,
    const exprt &pointer);

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

  /// Extract function name from \p called_functions
  /// \param: called_function: the function call expression
  /// \return function identifier
  irep_idt get_callee_id(const exprt &called_function) const;
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

bool remove_function_pointerst::arg_is_type_compatible(
  const typet &call_type,
  const typet &function_type)
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

  return pointer_offset_bits(call_type, ns) ==
         pointer_offset_bits(function_type, ns);
}

bool remove_function_pointerst::is_type_compatible(
  bool return_value_used,
  const code_typet &call_type,
  const code_typet &function_type)
{
  // we are willing to ignore anything that's returned
  // if we call with 'void'
  if(!return_value_used)
  {
  }
  else if(call_type.return_type() == empty_typet())
  {
    // ok
  }
  else
  {
    if(!arg_is_type_compatible(call_type.return_type(),
                               function_type.return_type()))
      return false;
  }

  // let's look at the parameters
  const code_typet::parameterst &call_parameters=call_type.parameters();
  const code_typet::parameterst &function_parameters=function_type.parameters();

  if(function_type.has_ellipsis() &&
     function_parameters.empty())
  {
    // always ok
  }
  else if(call_type.has_ellipsis() &&
          call_parameters.empty())
  {
    // always ok
  }
  else
  {
    // we are quite strict here, could be much more generous
    if(call_parameters.size()!=function_parameters.size())
      return false;

    for(std::size_t i=0; i<call_parameters.size(); i++)
      if(!arg_is_type_compatible(call_parameters[i].type(),
                                 function_parameters[i].type()))
        return false;
  }

  return true;
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

code_typet remove_function_pointerst::refine_call_type(
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

void remove_function_pointerst::try_remove_const_fp(
  const goto_programt &goto_program,
  functionst &functions,
  const exprt &pointer)
{
  PRECONDITION(functions.empty());

  does_remove_constt const_removal_check(goto_program, ns);
  const auto does_remove_const = const_removal_check();
  does_remove_const_success = does_remove_const.first;

  if(does_remove_const_success)
  {
    log.warning().source_location = does_remove_const.second;
    log.warning() << "cast from const to non-const pointer found, "
                  << "only worst case function pointer removal will be done."
                  << messaget::eom;
    remove_const_found_functions = false;
  }
  else
  {
    remove_const_function_pointerst fpr(
      log.get_message_handler(), ns, symbol_table);

    // if remove_const_function fails, functions should be empty
    // however, it is possible for found_functions to be true and functions
    // to be empty (this happens if the pointer can only resolve to the null
    // pointer)
    remove_const_found_functions = fpr(pointer, functions);
    CHECK_RETURN(remove_const_found_functions || functions.empty());
  }
}

remove_function_pointerst::functionst
remove_function_pointerst::get_function_pointer_targets(
  const goto_modelt &goto_model,
  goto_programt::const_targett &call_site)
{
  functionst functions;
  for(const auto &function_pair : goto_model.goto_functions.function_map)
  {
    const auto &function_body = function_pair.second.body;
    const auto &candidates =
      get_function_pointer_targets(function_body, call_site);
    functions.insert(candidates.begin(), candidates.end());
  }
  return functions;
}

remove_function_pointerst::functionst
remove_function_pointerst::get_function_pointer_targets(
  const goto_programt &goto_program,
  goto_programt::const_targett &call_site)
{
  PRECONDITION(call_site->is_function_call());

  const code_function_callt &code = call_site->get_function_call();
  const auto &function = to_dereference_expr(code.function());
  const auto &refined_call_type = refine_call_type(function.type(), code);

  functionst functions;
  try_remove_const_fp(goto_program, functions, function.pointer());

  only_remove_const_function_pointers_called =
    !does_remove_const_success && functions.size() == 1;
  if(
    !only_remove_const_function_pointers_called &&
    !remove_const_found_functions && !only_resolve_const_fps)
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
          candidate_function_type) &&
        candidate_function_name != "pthread_mutex_cleanup")
      {
        functions.insert(
          symbol_exprt{candidate_function_name, candidate_function_type});
      }
    }
  }
  return functions;
}

void remove_function_pointerst::remove_function_pointer(
  goto_programt &goto_program,
  const irep_idt &function_id,
  goto_programt::targett target)
{
  goto_programt::const_targett const_target = target;
  const auto functions =
    get_function_pointer_targets(goto_program, const_target);

  if(only_remove_const_function_pointers_called)
  {
    auto call = target->get_function_call();
    call.function() = *functions.cbegin();
    target->set_function_call(call);
  }
  else if(remove_const_found_functions || !only_resolve_const_fps)
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
  const functionst &functions)
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
  const irep_idt &function_id)
{
  bool did_something=false;

  Forall_goto_program_instructions(target, goto_program)
    if(target->is_function_call())
    {
      const code_function_callt &code = target->get_function_call();

      if(code.function().id()==ID_dereference)
      {
        remove_function_pointer(goto_program, function_id, target);
        did_something=true;
      }
    }

  if(did_something)
    remove_skip(goto_program);

  return did_something;
}

void remove_function_pointerst::operator()(goto_functionst &functions)
{
  bool did_something=false;

  for(goto_functionst::function_mapt::iterator f_it=
      functions.function_map.begin();
      f_it!=functions.function_map.end();
      f_it++)
  {
    goto_programt &goto_program=f_it->second.body;

    if(remove_function_pointers(goto_program, f_it->first))
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

possible_fp_targets_mapt get_function_pointer_targets(
  message_handlert &message_handler,
  goto_modelt &goto_model)
{
  remove_function_pointerst rfp(
    message_handler,
    goto_model.symbol_table,
    false,
    false,
    goto_model.goto_functions);

  possible_fp_targets_mapt target_map;
  const auto &goto_functions = goto_model.goto_functions;
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
        const auto &function_id =
          to_symbol_expr(
            to_dereference_expr(target->get_function_call().function())
              .pointer())
            .get_identifier();
        target_map.emplace(
          function_id, rfp.get_function_pointer_targets(goto_model, target));
      }
    }
  }
  return target_map;
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

irep_idt
remove_function_pointerst::get_callee_id(const exprt &called_function) const
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
