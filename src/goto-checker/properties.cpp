/*******************************************************************\

Module: Properties

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Properties

#include "properties.h"

#include <util/exit_codes.h>
#include <util/invariant.h>
#include <util/json.h>
#include <util/json_irep.h>
#include <util/json_stream.h>
#include <util/xml.h>
#include <util/xml_irep.h>

#include <goto-programs/abstract_goto_model.h>

std::string as_string(resultt result)
{
  switch(result)
  {
  case resultt::UNKNOWN:
    return "UNKNOWN";
  case resultt::PASS:
    return "PASS";
  case resultt::FAIL:
    return "FAIL";
  case resultt::ERROR:
    return "ERROR";
  }

  UNREACHABLE;
}

std::string as_string(property_statust status)
{
  switch(status)
  {
  case property_statust::NOT_CHECKED:
    return "NOT CHECKED";
  case property_statust::UNKNOWN:
    return "UNKNOWN";
  case property_statust::NOT_REACHABLE:
    return "UNREACHABLE";
  case property_statust::PASS:
    return "SUCCESS";
  case property_statust::FAIL:
    return "FAILURE";
  case property_statust::ERROR:
    return "ERROR";
  }

  UNREACHABLE;
}

property_infot::property_infot(
  goto_programt::const_targett pc,
  std::string description,
  property_statust status)
  : pc(pc), description(std::move(description)), status(status)
{
}

propertiest initialize_properties(const abstract_goto_modelt &goto_model)
{
  propertiest properties;
  update_properties_from_goto_model(properties, goto_model);
  return properties;
}

void update_properties_from_goto_model(
  propertiest &properties,
  const abstract_goto_modelt &goto_model)
{
  const auto &goto_functions = goto_model.get_goto_functions();
  for(const auto &function_pair : goto_functions.function_map)
  {
    const goto_programt &goto_program = function_pair.second.body;

    // need pointer to goto instruction
    forall_goto_program_instructions(i_it, goto_program)
    {
      if(!i_it->is_assert())
        continue;

      std::string description =
        id2string(i_it->source_location().get_comment());
      if(description.empty())
        description = "assertion";
      properties.emplace(
        i_it->source_location().get_property_id(),
        property_infot{i_it, description, property_statust::NOT_CHECKED});
    }
  }
}

std::string
as_string(const irep_idt &property_id, const property_infot &property_info)
{
  return "[" + id2string(property_id) + "] " + property_info.description +
         ": " + as_string(property_info.status);
}

xmlt xml(const irep_idt &property_id, const property_infot &property_info)
{
  xmlt xml_result("result");
  xml_result.set_attribute("property", id2string(property_id));
  xml_result.set_attribute("status", as_string(property_info.status));
  xml_result.new_element(xml(property_info.pc->source_location()));
  return xml_result;
}

template <class json_objectT>
static void json(
  json_objectT &result,
  const irep_idt &property_id,
  const property_infot &property_info)
{
  result["property"] = json_stringt(property_id);
  result["description"] = json_stringt(property_info.description);
  result["status"] = json_stringt(as_string(property_info.status));
  result["sourceLocation"] = json(property_info.pc->source_location());
}

json_objectt
json(const irep_idt &property_id, const property_infot &property_info)
{
  json_objectt result;
  json<json_objectt>(result, property_id, property_info);
  return result;
}

void json(
  json_stream_objectt &result,
  const irep_idt &property_id,
  const property_infot &property_info)
{
  json<json_stream_objectt>(result, property_id, property_info);
}

int result_to_exit_code(resultt result)
{
  switch(result)
  {
  case resultt::PASS:
    return CPROVER_EXIT_VERIFICATION_SAFE;
  case resultt::FAIL:
    return CPROVER_EXIT_VERIFICATION_UNSAFE;
  case resultt::ERROR:
    return CPROVER_EXIT_INTERNAL_ERROR;
  case resultt::UNKNOWN:
    return CPROVER_EXIT_VERIFICATION_INCONCLUSIVE;
  }
  UNREACHABLE;
}

std::size_t
count_properties(const propertiest &properties, property_statust status)
{
  std::size_t count = 0;
  for(const auto &property_pair : properties)
  {
    if(property_pair.second.status == status)
      ++count;
  }
  return count;
}

bool is_property_to_check(property_statust status)
{
  return status == property_statust::NOT_CHECKED ||
         status == property_statust::UNKNOWN;
}

bool has_properties_to_check(const propertiest &properties)
{
  for(const auto &property_pair : properties)
  {
    if(is_property_to_check(property_pair.second.status))
      return true;
  }
  return false;
}

/// Update with the preference order
/// 1. old non-UNKNOWN/non-NOT_CHECKED status
/// 2. new non-UNKNOWN/non-NOT_CHECKED status
/// 3. UNKNOWN
/// 4. NOT_CHECKED
/// Suitable for updating property status
property_statust &operator|=(property_statust &a, property_statust const &b)
{
  // non-monotonic use is likely a bug
  // UNKNOWN is neutral element w.r.t. ERROR/PASS/NOT_REACHABLE/FAIL
  // clang-format off
  PRECONDITION(
    a == property_statust::NOT_CHECKED ||
    (a == property_statust::UNKNOWN && b != property_statust::NOT_CHECKED) ||
    b == property_statust::UNKNOWN ||
    a == b);
  // clang-format on
  switch(a)
  {
  case property_statust::NOT_CHECKED:
  case property_statust::UNKNOWN:
    a = b;
    return a;
  case property_statust::ERROR:
  case property_statust::PASS:
  case property_statust::NOT_REACHABLE:
  case property_statust::FAIL:
    return a;
  }
  UNREACHABLE;
}

/// Update with the preference order
/// 1. ERROR
/// 2. FAIL
/// 3. UNKNOWN
/// 4. NOT_CHECKED
/// 5. NOT_REACHABLE
/// 6. PASS
/// Suitable for computing overall results
property_statust &operator&=(property_statust &a, property_statust const &b)
{
  switch(a)
  {
  case property_statust::ERROR:
    return a;
  case property_statust::FAIL:
    a = (b == property_statust::ERROR ? b : a);
    return a;
  case property_statust::UNKNOWN:
    a = (b == property_statust::ERROR || b == property_statust::FAIL ? b : a);
    return a;
  case property_statust::NOT_CHECKED:
    a =
      (b != property_statust::PASS && b != property_statust::NOT_REACHABLE ? b
                                                                           : a);
    return a;
  case property_statust::NOT_REACHABLE:
    a = (b != property_statust::PASS ? b : a);
    return a;
  case property_statust::PASS:
    a = (b == property_statust::PASS ? a : b);
    return a;
  }
  UNREACHABLE;
}

/// Determines the overall result corresponding from the given properties
/// That is PASS if all properties are PASS or NOT_CHECKED,
///         FAIL if at least one property is FAIL and no property is ERROR,
///         UNKNOWN if no property is FAIL or ERROR and
///           at least one property is UNKNOWN,
///         ERROR if at least one property is error.
resultt determine_result(const propertiest &properties)
{
  property_statust status = property_statust::PASS;
  for(const auto &property_pair : properties)
  {
    status &= property_pair.second.status;
  }
  switch(status)
  {
  case property_statust::NOT_CHECKED:
    // If we have unchecked properties then we don't know.
    return resultt::UNKNOWN;
  case property_statust::UNKNOWN:
    return resultt::UNKNOWN;
  case property_statust::NOT_REACHABLE:
    // If a property is not reachable then overall it's still a PASS.
    return resultt::PASS;
  case property_statust::PASS:
    return resultt::PASS;
  case property_statust::FAIL:
    return resultt::FAIL;
  case property_statust::ERROR:
    return resultt::ERROR;
  }
  UNREACHABLE;
}
