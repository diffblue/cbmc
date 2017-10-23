/*******************************************************************\

Module: Make function assume false

Author: Elizabeth Polgreen

Date: November 2017

\*******************************************************************/

/// \file
/// Make function assume false

#include "make_function_assume_false.h"

#include <util/message.h>

#include <goto-programs/goto_model.h>

/// \brief Replace calls to the function with assume(false).
/// This effectively blocks any paths through the function
/// or depending on return values from the function.
/// \param goto_model  input program to be modifier
/// \param identifier  name of function to block
/// \param message_handler  Error/status output
void make_function_assume_false(
  goto_modelt &goto_model,
  const irep_idt &identifier,
  message_handlert &message_handler)
{
  messaget message(message_handler);

  goto_functionst::function_mapt::iterator entry =
    goto_model.goto_functions.function_map.find(identifier);

  if(entry==goto_model.goto_functions.function_map.end())
  {
    message.error() << "No function " << identifier
                    << " in goto program" << messaget::eom;
    return;
  }
  else if(entry->second.is_inlined())
  {
    message.warning() << "Function " << identifier << " is inlined, "
                      << "instantiations will not be blocked"
                      << messaget::eom;
  }
  else
  {
    message.status() << "Blocking all calls to " << identifier << messaget::eom;

    Forall_goto_functions(it, goto_model.goto_functions)
    {
      Forall_goto_program_instructions(iit, it->second.body)
      {
        goto_programt::instructiont &ins = *iit;

        if(!ins.is_function_call())
          continue;

        const code_function_callt &call = to_code_function_call(ins.code);

        if(call.function().id() != ID_symbol)
          continue;

        if(to_symbol_expr(call.function()).get_identifier() == identifier)
        {
          ins.make_assumption(false_exprt());
          ins.source_location.set_comment(
              "`"+id2string(identifier)+"'"
                  " is marked unusable by --make-function-assume-false");
        }
      }
    }
  }
}

/// \brief Replace calls to any functions in the list
/// "functions" with assume(false).
/// This effectively blocks any paths through the function
/// or depending on return values from the function.
/// \param functions   list of function names to block
/// \param goto_model  input program to be modifier
/// \param message_handler  Error/status output
void make_functions_assume_false(
    goto_modelt &goto_model,
    const std::list<std::string> &functions,
    message_handlert &message_handler)
{
  messaget message(message_handler);
  for(const auto &func : functions)
  {
    make_function_assume_false(goto_model, func, message_handler);
  }
}




