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
  for(const auto &gf_entry : goto_model1.goto_functions.function_map)
  {
    if(!gf_entry.second.body_available())
      continue;

    goto_functionst::function_mapt::const_iterator f_it =
      goto_model2.goto_functions.function_map.find(gf_entry.first);
    if(f_it==goto_model2.goto_functions.function_map.end() ||
       !f_it->second.body_available())
    {
      deleted_functions.insert(gf_entry.first);
      continue;
    }

    // check access qualifiers
    const symbolt *fun1 = goto_model1.symbol_table.lookup(gf_entry.first);
    CHECK_RETURN(fun1 != nullptr);
    const symbolt *fun2 = goto_model2.symbol_table.lookup(gf_entry.first);
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
      modified_functions.insert(gf_entry.first);
      continue;
    }

    if(!gf_entry.second.body.equals(f_it->second.body))
    {
      modified_functions.insert(gf_entry.first);
      continue;
    }
  }
  for(const auto &gf_entry : goto_model2.goto_functions.function_map)
  {
    if(!gf_entry.second.body_available())
      continue;

    total_functions_count++;

    goto_functionst::function_mapt::const_iterator f_it =
      goto_model1.goto_functions.function_map.find(gf_entry.first);
    if(f_it==goto_model1.goto_functions.function_map.end() ||
       !f_it->second.body_available())
    {
      new_functions.insert(gf_entry.first);
    }
  }

  return !(new_functions.empty() &&
           modified_functions.empty() &&
           deleted_functions.empty());
}
