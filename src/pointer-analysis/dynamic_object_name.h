/*******************************************************************\

Module: Dynamic object name

Author: Marius-Constantin Melemciuc

Date: April 2017

@ Copyright Diffblue, Ltd.

\*******************************************************************/

#ifndef CPROVER_POINTER_ANALYSIS_DYNAMIC_OBJECT_NAME_H
#define CPROVER_POINTER_ANALYSIS_DYNAMIC_OBJECT_NAME_H

#include <string>

#include <util/std_expr.h>

extern const std::string prefix_dynamic_object;

/*******************************************************************\

Function: get_dynamic_object_name

  Inputs: dynamic_object: The dynamic-object.

 Outputs: The name of the dynamic-object, composed of the
          "value_set::dynamic_object",
          it's instance,
          and the keyword "most_recent_allocation" or
          "any_allocation".

 Purpose: To generate a name for dynamic-objects suitable for use
          in the LHS of value-set maps.

\*******************************************************************/

inline std::string get_dynamic_object_name(
  const dynamic_object_exprt &dynamic_object)
{
  std::string name=
    "value_set::dynamic_object"+
    std::to_string(dynamic_object.get_instance());

  if(dynamic_object.get_recency()==
    dynamic_object_exprt::recencyt::MOST_RECENT_ALLOCATION)
  {
    name+=as_string(ID_most_recent_allocation);
  }
  else if(dynamic_object.get_recency()==
    dynamic_object_exprt::recencyt::ANY_ALLOCATION)
  {
    name+=as_string(ID_any_allocation);
  }

  return name;
}

#endif // CPROVER_POINTER_ANALYSIS_DYNAMIC_OBJECT_NAME_H
