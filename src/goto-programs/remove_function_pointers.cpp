/*******************************************************************\

Module: Program Transformation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Program Transformation

#include "remove_function_pointers.h"

#include <util/c_types.h>
#include <util/fresh_symbol.h>
#include <util/invariant.h>
#include <util/message.h>
#include <util/pointer_expr.h>
#include <util/pointer_offset_size.h>
#include <util/source_location.h>
#include <util/std_code.h>
#include <util/std_expr.h>

#include <analyses/does_remove_const.h>

#include "compute_called_functions.h"
#include "goto_model.h"
#include "remove_const_function_pointers.h"
#include "remove_skip.h"

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
  /// target in the given goto-program by determining
  /// functions that have a compatible signature
  /// \param goto_program: The goto program that contains target
  /// \param function_id: Name of function containing the target
  /// \param target: location with function call with function pointer
  void remove_function_pointer(
    goto_programt &goto_program,
    const irep_idt &function_id,
    goto_programt::targett target);

  std::unordered_set<irep_idt> address_taken;

  typedef std::map<irep_idt, code_typet> type_mapt;
  type_mapt type_map;

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
  for(const auto &s : symbol_table.symbols)
    compute_address_taken_functions(s.second.value, address_taken);

  compute_address_taken_functions(goto_functions, address_taken);

  // build type map
  for(const auto &gf_entry : goto_functions.function_map)
  {
    type_map.emplace(
      gf_entry.first, to_code_type(ns.lookup(gf_entry.first).type));
  }
}

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

void remove_function_pointerst::remove_function_pointer(
  goto_programt &goto_program,
  const irep_idt &function_id,
  goto_programt::targett target)
{
  const auto &function = to_dereference_expr(as_const(*target).call_function());

  // this better have the right type
  code_typet call_type=to_code_type(function.type());

  // refine the type in case the forward declaration was incomplete
  if(call_type.has_ellipsis() &&
     call_type.parameters().empty())
  {
    call_type.remove_ellipsis();
    for(const auto &argument : as_const(*target).call_arguments())
    {
      call_type.parameters().push_back(code_typet::parametert(argument.type()));
    }
  }

  bool found_functions;

  const exprt &pointer = function.pointer();
  remove_const_function_pointerst::functionst functions;
  does_remove_constt const_removal_check(goto_program, ns);
  const auto does_remove_const = const_removal_check();
  if(does_remove_const.first)
  {
    log.warning().source_location = does_remove_const.second;
    log.warning() << "cast from const to non-const pointer found, "
                  << "only worst case function pointer removal will be done."
                  << messaget::eom;
    found_functions=false;
  }
  else
  {
    remove_const_function_pointerst fpr(
      log.get_message_handler(), ns, symbol_table);

    found_functions=fpr(pointer, functions);

    // if found_functions is false, functions should be empty
    // however, it is possible for found_functions to be true and functions
    // to be empty (this happens if the pointer can only resolve to the null
    // pointer)
    CHECK_RETURN(found_functions || functions.empty());

    if(functions.size()==1)
    {
      target->call_function() = *functions.cbegin();
      return;
    }
  }

  if(!found_functions)
  {
    if(only_resolve_const_fps)
    {
      // If this mode is enabled, we only remove function pointers
      // that we can resolve either to an exact function, or an exact subset
      // (e.g. a variable index in a constant array).
      // Since we haven't found functions, we would now resort to
      // replacing the function pointer with any function with a valid signature
      // Since we don't want to do that, we abort.
      return;
    }

    bool return_value_used = as_const(*target).call_lhs().is_not_nil();

    // get all type-compatible functions
    // whose address is ever taken
    for(const auto &t : type_map)
    {
      // address taken?
      if(address_taken.find(t.first)==address_taken.end())
        continue;

      // type-compatible?
      if(!is_type_compatible(return_value_used, call_type, t.second))
        continue;

      if(t.first=="pthread_mutex_cleanup")
        continue;

      symbol_exprt expr(t.first, t.second);
      functions.insert(expr);
    }
  }

  remove_function_pointer(goto_program, function_id, target, functions);
}

void remove_function_pointerst::remove_function_pointer(
  goto_programt &goto_program,
  const irep_idt &function_id,
  goto_programt::targett target,
  const functionst &functions)
{
  const exprt &function = target->call_function();
  const exprt &pointer = to_dereference_expr(function).pointer();

  // the final target is a skip
  goto_programt final_skip;

  goto_programt::targett t_final = final_skip.add(goto_programt::make_skip());

  // build the calls and gotos

  goto_programt new_code_calls;
  goto_programt new_code_gotos;

  for(const auto &fun : functions)
  {
    // call function
    auto new_call =
      code_function_callt(target->call_lhs(), fun, target->call_arguments());

    // the signature of the function might not match precisely
    fix_argument_types(new_call);

    goto_programt tmp;
    fix_return_type(function_id, new_call, tmp);

    auto call = new_code_calls.add(goto_programt::make_function_call(new_call));
    new_code_calls.destructive_append(tmp);

    // goto final
    new_code_calls.add(goto_programt::make_goto(t_final, true_exprt()));

    // goto to call
    const address_of_exprt address_of(fun, pointer_type(fun.type()));

    const auto casted_address =
      typecast_exprt::conditional_cast(address_of, pointer.type());

    new_code_gotos.add(
      goto_programt::make_goto(call, equal_exprt(pointer, casted_address)));
  }

  // fall-through
  if(add_safety_assertion)
  {
    goto_programt::targett t =
      new_code_gotos.add(goto_programt::make_assertion(false_exprt()));
    t->source_location_nonconst().set_property_class("pointer dereference");
    t->source_location_nonconst().set_comment("invalid function pointer");
  }
  new_code_gotos.add(goto_programt::make_assumption(false_exprt()));

  goto_programt new_code;

  // patch them all together
  new_code.destructive_append(new_code_gotos);
  new_code.destructive_append(new_code_calls);
  new_code.destructive_append(final_skip);

  // set locations
  for(auto &instruction : new_code.instructions)
  {
    source_locationt &source_location = instruction.source_location_nonconst();

    irep_idt property_class = source_location.get_property_class();
    irep_idt comment = source_location.get_comment();
    source_location = target->source_location();
    if(!property_class.empty())
      source_location.set_property_class(property_class);
    if(!comment.empty())
      source_location.set_comment(comment);
  }

  goto_programt::targett next_target=target;
  next_target++;

  goto_program.destructive_insert(next_target, new_code);

  // We preserve the original dereferencing to possibly catch
  // further pointer-related errors.
  code_expressiont code_expression(function);
  code_expression.add_source_location()=function.source_location();
  *target =
    goto_programt::make_other(code_expression, target->source_location());

  // report statistics
  log.statistics().source_location = target->source_location();
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

bool remove_function_pointerst::remove_function_pointers(
  goto_programt &goto_program,
  const irep_idt &function_id)
{
  bool did_something=false;

  Forall_goto_program_instructions(target, goto_program)
    if(target->is_function_call())
    {
      if(target->call_function().id() == ID_dereference)
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
