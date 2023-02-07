// Copyright (c) 2023 Fotis Koutoulakis for Diffblue Ltd.

/// \file
/// Interface for the various verification engines providing results
//  in a structured form.

#include "verification_result.h"

#include <util/invariant.h>
#include <util/make_unique.h>

#include <goto-checker/properties.h>

#include <algorithm>
#include <string>
#include <vector>

class verification_resultt::verification_result_implt
{
  propertiest _properties;
  resultt _verifier_result;

public:
  verification_result_implt() = default;
  verification_result_implt(const verification_result_implt &other) = default;
  ~verification_result_implt() = default;

  void set_properties(propertiest &properties);
  void set_result(resultt &verification_result);

  resultt get_result();
  const propertiest &get_properties();
};

// Impl

void verification_resultt::verification_result_implt::set_properties(
  propertiest &properties)
{
  _properties = properties;
}

void verification_resultt::verification_result_implt::set_result(
  resultt &result)
{
  _verifier_result = result;
}

resultt verification_resultt::verification_result_implt::get_result()
{
  return _verifier_result;
}

const propertiest &
verification_resultt::verification_result_implt::get_properties()
{
  return _properties;
}

// Verification_result

verification_resultt::verification_resultt()
  : _impl(util_make_unique<verification_resultt::verification_result_implt>())
{
}

verification_resultt::~verification_resultt()
{
}

verification_resultt::verification_resultt(const verification_resultt &other)
  : _impl(util_make_unique<verification_result_implt>(*other._impl))
{
}

verification_resultt &
verification_resultt::operator=(verification_resultt &&) = default;
verification_resultt &
verification_resultt::operator=(const verification_resultt &other)
{
  *_impl = *other._impl;
  return *this;
}

void verification_resultt::set_properties(propertiest &properties)
{
  _impl->set_properties(properties);
}

void verification_resultt::set_result(resultt &result)
{
  _impl->set_result(result);
}

verifier_resultt verification_resultt::final_result() const
{
  switch(_impl->get_result())
  {
  case resultt::ERROR:
    return verifier_resultt::ERROR;
  case resultt::FAIL:
    return verifier_resultt::FAIL;
  case resultt::PASS:
    return verifier_resultt::PASS;
  case resultt::UNKNOWN:
    return verifier_resultt::UNKNOWN;
  }
  // Required to silence compiler warnings that are promoted as errors!
  UNREACHABLE;
}

std::vector<std::string> verification_resultt::get_property_ids() const
{
  std::vector<std::string> result;
  for(const auto &props : _impl->get_properties())
  {
    result.push_back(as_string(props.first));
  }
  return result;
}

std::string verification_resultt::get_property_description(
  const std::string &property_id) const
{
  auto irepidt_property = irep_idt(property_id);
  const auto description =
    _impl->get_properties().at(irepidt_property).description;
  return description;
}

prop_statust
verification_resultt::get_property_status(const std::string &property_id) const
{
  auto irepidt_property = irep_idt(property_id);
  switch(_impl->get_properties().at(irepidt_property).status)
  {
  case property_statust::ERROR:
    return prop_statust::ERROR;
  case property_statust::FAIL:
    return prop_statust::FAIL;
  case property_statust::NOT_CHECKED:
    return prop_statust::NOT_CHECKED;
  case property_statust::NOT_REACHABLE:
    return prop_statust::NOT_REACHABLE;
  case property_statust::PASS:
    return prop_statust::PASS;
  case property_statust::UNKNOWN:
    return prop_statust::UNKNOWN;
  }
  UNREACHABLE;
}
