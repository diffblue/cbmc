/*******************************************************************\

Module: Syntactic GOTO-DIFF for Java

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Syntactic GOTO-DIFF for Java

#include "java_syntactic_diff.h"

#include <goto-programs/goto_model.h>
#include <java_bytecode/java_utils.h>

bool java_syntactic_difft::operator()()
{
  forall_goto_functions(it, goto_model1.goto_functions)
  {
    if(!it->second.body_available())
      continue;

    goto_functionst::function_mapt::const_iterator f_it =
      goto_model2.goto_functions.function_map.find(it->first);
    if(
      f_it == goto_model2.goto_functions.function_map.end() ||
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
    const optionalt<irep_idt> class_name = declaring_class(*fun1);
    bool function_access_changed =
      fun1->type.get(ID_access) != fun2->type.get(ID_access);
    bool class_access_changed = false;
    bool field_access_changed = false;
    if(class_name)
    {
      const symbolt *class1 = goto_model1.symbol_table.lookup(*class_name);
      CHECK_RETURN(class1 != nullptr);
      const symbolt *class2 = goto_model2.symbol_table.lookup(*class_name);
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

    if(!it->second.body.equals(f_it->second.body))
    {
      modified_functions.insert(it->first);
      continue;
    }
  }
  forall_goto_functions(it, goto_model2.goto_functions)
  {
    if(!it->second.body_available())
      continue;

    total_functions_count++;

    goto_functionst::function_mapt::const_iterator f_it =
      goto_model1.goto_functions.function_map.find(it->first);
    if(
      f_it == goto_model1.goto_functions.function_map.end() ||
      !f_it->second.body_available())
      new_functions.insert(it->first);
  }

  return !(
    new_functions.empty() && modified_functions.empty() &&
    deleted_functions.empty());
}
