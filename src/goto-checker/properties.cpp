/*******************************************************************\

Module: Goto Checker Interface

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Property Map

#include "properties.h"

#include <util/invariant.h>

std::string as_string(resultt result)
{
  switch(result)
  {
  case resultt::PASS:
    return "PASS";
  case resultt::FAIL:
    return "FAIL";
  case resultt::ERROR:
    return "ERROR";
  case resultt::UNKNOWN:
    return "UNKNOWN";
  }

  UNREACHABLE;
}

/// Returns the properties in the goto model
propertiest initialize_properties(const goto_modelt &goto_model)
{
  propertiest properties;
  forall_goto_functions(it, goto_model.goto_functions)
  {
    if(
      !it->second.is_inlined() ||
      it->first == goto_model.goto_functions.entry_point())
    {
      const goto_programt &goto_program = it->second.body;

      forall_goto_program_instructions(i_it, goto_program)
      {
        if(!i_it->is_assert())
          continue;

        const source_locationt &source_location = i_it->source_location;

        irep_idt property_id = source_location.get_property_id();

        property_infot &property = properties[property_id];
        property.result = resultt::UNKNOWN;
        property.location = i_it;
      }
    }
  }
  return properties;
}

/// Update with the preference order
/// 1. old non-UNKNOWN result
/// 2. new non-UNKNOWN result
/// 3. UNKNOWN
/// Suitable for updating property results
resultt &operator|=(resultt &a, resultt const &b)
{
  PRECONDITION(a == resultt::UNKNOWN || a == b);
  switch(a)
  {
  case resultt::UNKNOWN:
    a = b;
    return a;
  case resultt::ERROR:
  case resultt::PASS:
  case resultt::FAIL:
    return a;
  }
  UNREACHABLE;
}

/// Update with the preference order
/// 1. ERROR
/// 2. FAIL
/// 3. UNKNOWN
/// 4. PASS
/// Suitable for computing overall results
resultt &operator&=(resultt &a, resultt const &b)
{
  switch(a)
  {
  case resultt::UNKNOWN:
    a = b;
    return a;
  case resultt::PASS:
    a = (b == resultt::PASS ? a : b);
    return a;
  case resultt::ERROR:
    a = b;
    return a;
  case resultt::FAIL:
    a = (b == resultt::ERROR ? b : a);
    return a;
  }
  UNREACHABLE;
}

/// Determines the overall result corresponding from the given properties
/// That is PASS if all properties are PASS,
///         FAIL if at least one property is FAIL and no property is ERROR,
///         UNKNOWN if no property is FAIL or ERROR and
///           at least one property is UNKNOWN,
///         ERROR if at least one property is error.
resultt determine_result(const propertiest &properties)
{
  resultt result = resultt::UNKNOWN;
  for(const auto &property_pair : properties)
  {
    result &= property_pair.second.result;
  }
  return result;
}

/// Merges a set of properties into a given set of properties,
/// updating its results and adding new properties.
void merge_properties(
  propertiest &properties,
  const propertiest &updated_properties)
{
  for(const auto &property_pair : updated_properties)
  {
    auto found_property = properties.insert(property_pair);
    if(!found_property.second)
      found_property.first->second.result |= property_pair.second.result;
  }
}
