// Author: Fotis Koutoulakis for Diffblue Ltd.

#include "api_options.h"

#include <util/make_unique.h>

struct api_optionst::implementationt
{
  // Options for the verification engine
  bool simplify_enabled;

  // Option for dropping unused function
  bool drop_unused_functions_enabled;

  // Option for validating the goto model
  bool validate_goto_model_enabled;
};

api_optionst::api_optionst(
  std::unique_ptr<const implementationt> implementation)
  : implementation{std::move(implementation)}
{
}

bool api_optionst::simplify() const
{
  return implementation->simplify_enabled;
}

bool api_optionst::drop_unused_functions() const
{
  return implementation->drop_unused_functions_enabled;
}

bool api_optionst::validate_goto_model() const
{
  return implementation->validate_goto_model_enabled;
}

api_optionst::api_optionst(api_optionst &&api_options) noexcept = default;
api_optionst &api_optionst::operator=(api_optionst &&) noexcept = default;
api_optionst::~api_optionst() = default;

api_optionst::buildert &api_optionst::buildert::simplify(bool on)
{
  implementation->simplify_enabled = on;
  return *this;
}

api_optionst::buildert &api_optionst::buildert::drop_unused_functions(bool on)
{
  implementation->drop_unused_functions_enabled = on;
  return *this;
}

api_optionst::buildert &api_optionst::buildert::validate_goto_model(bool on)
{
  implementation->validate_goto_model_enabled = on;
  return *this;
}

api_optionst api_optionst::buildert::build()
{
  auto impl = util_make_unique<implementationt>(*implementation);
  api_optionst api_options{std::move(impl)};
  return api_options;
}

api_optionst::buildert::buildert() = default;
api_optionst::buildert::buildert(api_optionst::buildert &&builder) noexcept =
  default;
api_optionst::buildert::~buildert() = default;
