// Author Fotis Koutoulakis for Diffblue Ltd 2022.

// NOLINTNEXTLINE(build/include)
#include "include/c_api.h"

// clang-format off
#include <api.h>
// clang-format on

#include <algorithm>
#include <cassert>
#include <iostream>
#include <iterator>
#include <string>
#include <vector>

std::vector<std::string> output;

extern bool cbmc_invariants_should_throw;

std::vector<std::string> const &
_translate_vector_of_string(rust::Vec<rust::String> elements)
{
  std::vector<std::string> *stdv = new std::vector<std::string>{};
  std::transform(
    elements.begin(),
    elements.end(),
    std::back_inserter(*stdv),
    [](rust::String elem) { return std::string(elem); });

  // NOLINTNEXTLINE(build/deprecated)
  assert(elements.size() == stdv->size());
  return *stdv;
}

std::unique_ptr<api_sessiont> new_api_session()
{
  // Create a new API session and register the default API callback for that.
  api_sessiont *api{new api_sessiont()};
  // We need to configure invariants to be throwing exceptions instead of
  // reporting to stderr and calling abort()
  cbmc_invariants_should_throw = true;

  // This lambda needs to be non-capturing in order for it to be convertible
  // to a function pointer, to pass to the API.
  const auto write_output =
    [](const api_messaget &message, api_call_back_contextt context) {
      std::vector<std::string> &output =
        *static_cast<std::vector<std::string> *>(context);
      output.emplace_back(api_message_get_string(message));
    };

  api->set_message_callback(write_output, &output);

  return std::unique_ptr<api_sessiont>(api);
}

std::vector<std::string> const &get_messages()
{
  return output;
}

verifier_resultt get_verification_result(
  const std::unique_ptr<verification_resultt> &verifier_result)
{
  return verifier_result->final_result();
}

std::vector<std::string> const &
get_property_ids(const std::unique_ptr<verification_resultt> &verifier_result)
{
  std::vector<std::string> *property_ids = new std::vector<std::string>();
  *property_ids = verifier_result->get_property_ids();
  return *property_ids;
}

std::string const &get_property_description(
  const std::unique_ptr<verification_resultt> &verifier_result,
  const std::string &property_id)
{
  std::string *description = new std::string();
  *description = verifier_result->get_property_description(property_id);
  return *description;
}

prop_statust get_property_status(
  const std::unique_ptr<verification_resultt> &verifier_result,
  const std::string &property_id)
{
  return verifier_result->get_property_status(property_id);
}
