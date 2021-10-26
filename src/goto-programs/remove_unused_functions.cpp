/*******************************************************************\

Module: Unused function removal

Author: CM Wintersteiger

\*******************************************************************/

/// \file
/// Unused function removal

#include "remove_unused_functions.h"

#include <util/message.h>

#include "goto_model.h"

void remove_unused_functions(
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  remove_unused_functions(goto_model.goto_functions, message_handler);
}

void remove_unused_functions(
  goto_functionst &functions,
  message_handlert &message_handler)
{
  std::set<irep_idt> used_functions;
  std::list<goto_functionst::function_mapt::iterator> unused_functions;
  find_used_functions(
    goto_functionst::entry_point(), functions, used_functions);

  for(goto_functionst::function_mapt::iterator it=
        functions.function_map.begin();
      it!=functions.function_map.end();
      it++)
  {
    if(used_functions.find(it->first)==used_functions.end())
      unused_functions.push_back(it);
  }

  messaget message(message_handler);

  if(!unused_functions.empty())
  {
    message.statistics()
      << "Dropping " << unused_functions.size() << " of " <<
      functions.function_map.size() << " functions (" <<
      used_functions.size() << " used)" << messaget::eom;
  }

  for(const auto &f : unused_functions)
    functions.function_map.erase(f);
}

void find_used_functions(
  const irep_idt &start,
  goto_functionst &functions,
  std::set<irep_idt> &seen)
{
  std::pair<std::set<irep_idt>::const_iterator, bool> res =
    seen.insert(start);

  if(!res.second)
    return;
  else
  {
    goto_functionst::function_mapt::const_iterator f_it =
      functions.function_map.find(start);

    if(f_it!=functions.function_map.end())
    {
      for(const auto &instruction : f_it->second.body.instructions)
      {
        if(instruction.is_function_call())
        {
          const auto &function = instruction.call_function();

          const irep_idt &identifier =
            to_symbol_expr(function).get_identifier();

          find_used_functions(identifier, functions, seen);
        }
      }
    }
  }
}
