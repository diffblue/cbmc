/*******************************************************************\

Module: Remove calls to functions without a body

Author: Daniel Poetzl

\*******************************************************************/

/// \file
/// Remove calls to functions without a body

#include "remove_calls_no_body.h"

#include <util/invariant.h>
#include <util/message.h>
#include <util/std_code.h>

#include "goto_functions.h"

/// Remove a single call
/// \param goto_program: goto program to modify
/// \param target: iterator pointing to the call
/// \param lhs: lhs of the call to which the return value is assigned
/// \param arguments: arguments of the call
void remove_calls_no_bodyt::remove_call_no_body(
  goto_programt &goto_program,
  goto_programt::targett target,
  const exprt &lhs,
  const exprt::operandst &arguments)
{
  PRECONDITION(target->is_function_call());
  PRECONDITION(!goto_program.empty());

  goto_programt tmp;

  // evaluate function arguments -- they might have
  // pointer dereferencing or the like
  for(const exprt &argument : arguments)
  {
    tmp.add(goto_programt::make_other(
      code_expressiont(argument), target->source_location()));
  }

  // return value
  if(lhs.is_not_nil())
  {
    side_effect_expr_nondett rhs(lhs.type(), target->source_location());

    code_assignt code(lhs, rhs);
    code.add_source_location() = target->source_location();

    tmp.add(goto_programt::make_assignment(code, target->source_location()));
  }

  // kill call
  *target = goto_programt::make_location(target->source_location());
  target++;

  goto_program.destructive_insert(target, tmp);
}

/// Check if instruction is a call to an opaque function through an ordinary
/// (non-function pointer) call.
/// \param target: iterator pointing to the instruction to check
/// \param goto_functions: all goto function to look up call target
bool remove_calls_no_bodyt::is_opaque_function_call(
  const goto_programt::const_targett target,
  const goto_functionst &goto_functions)
{
  if(!target->is_function_call())
    return false;

  const exprt &f = target->call_function();

  if(f.id() != ID_symbol)
    return false;

  const symbol_exprt &se = to_symbol_expr(f);
  const irep_idt id = se.get_identifier();

  goto_functionst::function_mapt::const_iterator f_it =
    goto_functions.function_map.find(id);

  if(f_it != goto_functions.function_map.end())
  {
    return !f_it->second.body_available();
  }

  return false;
}

/// Remove calls to functions without a body and replace them with evaluations
/// of the arguments of the call and a nondet assignment to the variable taking
/// the return value.
/// \param goto_program: goto program to operate on
/// \param goto_functions: all goto functions; for looking up functions which
///   the goto program may call
/// \param message_handler: message handler
void remove_calls_no_bodyt::operator()(
  goto_programt &goto_program,
  const goto_functionst &goto_functions,
  message_handlert &message_handler)
{
  for(goto_programt::targett it = goto_program.instructions.begin();
      it != goto_program.instructions.end();) // no it++
  {
    if(is_opaque_function_call(it, goto_functions))
    {
      messaget log{message_handler};
      log.status() << "Removing call to "
                   << to_symbol_expr(it->call_function()).get_identifier()
                   << ", which has no body" << messaget::eom;
      remove_call_no_body(
        goto_program, it, it->call_lhs(), it->call_arguments());
    }
    else
    {
      it++;
    }
  }
}

/// Remove calls to functions without a body and replace them with evaluations
/// of the arguments of the call and a nondet assignment to the variable taking
/// the return value.
/// \param goto_functions: goto functions to operate on
/// \param message_handler: message handler
void remove_calls_no_bodyt::operator()(
  goto_functionst &goto_functions,
  message_handlert &message_handler)
{
  for(auto &gf_entry : goto_functions.function_map)
  {
    (*this)(gf_entry.second.body, goto_functions, message_handler);
  }
}
