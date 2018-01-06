/*******************************************************************\

Module: Syntactic GOTO-DIFF

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Syntactic GOTO-DIFF

#include "syntactic_diff.h"

bool syntactic_difft::operator()()
{
  forall_goto_functions(it, goto_model1.goto_functions)
  {
    if(!it->second.body_available())
      continue;

    goto_functionst::function_mapt::const_iterator f_it=
      goto_model2.goto_functions.function_map.find(it->first);
    if(f_it==goto_model2.goto_functions.function_map.end() ||
       !f_it->second.body_available())
    {
      deleted_functions.insert(it->first);
      continue;
    }

    if(it->second.body.instructions.size() !=
       f_it->second.body.instructions.size())
    {
      modified_functions.insert(it->first);
      continue;
    }

    goto_programt::instructionst::const_iterator
      i_it1=it->second.body.instructions.begin();
    for(goto_programt::instructionst::const_iterator
        i_it2=f_it->second.body.instructions.begin();
        i_it1!=it->second.body.instructions.end() &&
        i_it2!=f_it->second.body.instructions.end();
        ++i_it1, ++i_it2)
    {
      long jump_difference1 = 0;
      if(!i_it1->targets.empty())
      {
        jump_difference1 =
          i_it1->get_target()->location_number - i_it1->location_number;
      }
      long jump_difference2 = 0;
      if(!i_it2->targets.empty())
      {
        jump_difference2 =
          i_it2->get_target()->location_number - i_it2->location_number;
      }
      if(
        i_it1->code != i_it2->code || i_it1->function != i_it2->function ||
        i_it1->type != i_it2->type || i_it1->guard != i_it2->guard ||
        jump_difference1 != jump_difference2)
      {
        modified_functions.insert(it->first);
        break;
      }
    }
  }
  forall_goto_functions(it, goto_model2.goto_functions)
  {
    if(!it->second.body_available())
      continue;

    total_functions_count++;

    goto_functionst::function_mapt::const_iterator f_it=
      goto_model1.goto_functions.function_map.find(it->first);
    if(f_it==goto_model1.goto_functions.function_map.end() ||
       !f_it->second.body_available())
      new_functions.insert(it->first);
  }

  return !(new_functions.empty() &&
           modified_functions.empty() &&
           deleted_functions.empty());
}
