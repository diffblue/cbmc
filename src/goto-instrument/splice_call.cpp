/*******************************************************************\

Module: Prepend/ splice a 0-ary function call in the beginning of a function 
e.g. for setting/ modelling the global environment

Author: Konstantinos Pouliasis

Date: July 2017

\*******************************************************************/

/// \file
/// Prepend a nullary call to another function
/// useful for context/ environment setting in arbitrary nodes

#include "splice_call.h"

#include <util/message.h>
#include <util/string2int.h>
#include <util/string_utils.h>

#include <langapi/language.h>

#include <goto-programs/goto_functions.h>

#include <algorithm>

// split the argument in caller/ callee two-position vector
// expect input as a string of two names glued with comma: "caller,callee"
static bool parse_caller_callee(
  const std::string &callercallee,
  std::vector<std::string> &result)
{
  split_string(callercallee, ',', result);
  return (result.size()!= 2);
}

bool splice_call(
  goto_functionst &goto_functions,
  const std::string &callercallee,
  const symbol_tablet &symbol_table,
  message_handlert &message_handler)
{
  messaget message(message_handler);
  const namespacet ns(symbol_table);
  std::vector<std::string> caller_callee;
  if(parse_caller_callee(callercallee, caller_callee))
  {
    message.error() << "Expecting two function names separated by a comma"
                    << messaget::eom;
    return true;
  }
  goto_functionst::function_mapt::iterator caller_fun=
    goto_functions.function_map.find(caller_callee[0]);
  goto_functionst::function_mapt::const_iterator callee_fun=
    goto_functions.function_map.find(caller_callee[1]);
  if(caller_fun==goto_functions.function_map.end())
  {
    message.error() << "Caller function does not exist" << messaget::eom;
    return true;
  }
  if(!caller_fun->second.body_available())
  {
    message.error() << "Caller function has no available body" << messaget::eom;
    return true;
  }
  if(callee_fun==goto_functions.function_map.end())
  {
    message.error() << "Callee function does not exist" << messaget::eom;
    return true;
  }
  goto_programt::const_targett start=
    caller_fun->second.body.instructions.begin();
  goto_programt::targett g=
    caller_fun->second.body.insert_before(start);
  const code_function_callt splice_call(
    ns.lookup(callee_fun->first).symbol_expr());
  g->make_function_call(splice_call);

  // update counters etc.
  goto_functions.update();
  return false;
}
