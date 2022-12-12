// Author: Fotis Koutoulakis for Diffblue Ltd.

#include "options.h"

#include <util/make_unique.h>
#include <util/options.h>

api_optionst api_optionst::create()
{
  return api_optionst{};
}

api_optionst &api_optionst::simplify(bool on)
{
  simplify_enabled = on;
  return *this;
}

std::unique_ptr<optionst> api_optionst::to_engine_options() const
{
  optionst engine_options;
  engine_options.set_option("simplify", simplify_enabled);
  return util_make_unique<optionst>(engine_options);
}
