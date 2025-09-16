/*******************************************************************\

Module: JSON goto_functions deserialization

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// JSON goto_functions deserialization

#include "json_goto_functions.h"

#include <util/exception_utils.h>
#include <util/json.h>

#include <goto-programs/goto_functions.h>

#include "json_goto_function.h"

void goto_functions_from_json(
  const jsont &json,
  goto_functionst &goto_functions)
{
  if(!json.is_object())
  {
    throw deserialization_exceptiont{
      "goto_functions_from_json: JSON input must be an object"};
  }

  const json_objectt &json_object = to_json_object(json);
  const auto it = json_object.find("functions");

  if(it == json_object.end())
  {
    throw deserialization_exceptiont{
      "goto_functions_from_json: JSON object must have key 'functions'"};
  }

  if(!it->second.is_array())
  {
    throw deserialization_exceptiont{
      "goto_functions_from_json: JSON functions must be an array"};
  }

  const json_arrayt &json_functions = to_json_array(it->second);

  for(const auto &function : json_functions)
  {
    if(!function.is_object())
    {
      throw deserialization_exceptiont{
        "goto_functions_from_json: JSON function must be an object"};
    }

    const json_objectt &json_function = to_json_object(function);
    auto name_it = json_function.find("name");

    if(name_it == json_function.end() || !name_it->second.is_string())
    {
      throw deserialization_exceptiont{
        "goto_functions_from_json: JSON function object must have key 'name' "
        "mapping to a string"};
    }
    const auto function_name = name_it->second.value;

    goto_functiont goto_function = goto_function_from_json(json_function);
    goto_functions.function_map[function_name] = std::move(goto_function);
  }

  goto_functions.update();
}
