/*******************************************************************\

Module: Syntactic GOTO-DIFF

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Syntactic GOTO-DIFF

#include "syntactic_diff.h"

#include <goto-programs/goto_model.h>

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

    // check access qualifiers
    const symbolt *fun1 = goto_model1.symbol_table.lookup(it->first);
    CHECK_RETURN(fun1 != nullptr);
    const symbolt *fun2 = goto_model2.symbol_table.lookup(it->first);
    CHECK_RETURN(fun2 != nullptr);
    const irep_idt &class_name = fun1->type.get(ID_C_class);
    bool function_access_changed =
      fun1->type.get(ID_access) != fun2->type.get(ID_access);
    bool class_access_changed = false;
    bool field_access_changed = false;
    if(!class_name.empty())
    {
      const symbolt *class1 = goto_model1.symbol_table.lookup(class_name);
      CHECK_RETURN(class1 != nullptr);
      const symbolt *class2 = goto_model2.symbol_table.lookup(class_name);
      CHECK_RETURN(class2 != nullptr);
      class_access_changed =
        class1->type.get(ID_access) != class2->type.get(ID_access);
      const class_typet &class_type1 = to_class_type(class1->type);
      const class_typet &class_type2 = to_class_type(class2->type);
      for(const auto &field1 : class_type1.components())
      {
        for(const auto &field2 : class_type2.components())
        {
          if(field1.get_name() == field2.get_name())
          {
            field_access_changed = field1.get_access() != field2.get_access();
            break;
          }
        }
        if(field_access_changed)
          break;
      }
    }
    if(function_access_changed || class_access_changed || field_access_changed)
    {
      modified_functions.insert(it->first);
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
