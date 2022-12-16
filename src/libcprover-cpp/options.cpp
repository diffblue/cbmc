// Author: Fotis Koutoulakis for Diffblue Ltd.

#include "options.h"

#include <util/cmdline.h>
#include <util/make_unique.h>
#include <util/options.h>

#include <ansi-c/goto_check_c.h>
#include <goto-checker/solver_factory.h>

api_optionst api_optionst::create()
{
  return api_optionst{};
}

api_optionst &api_optionst::simplify(bool on)
{
  simplify_enabled = on;
  return *this;
}

static std::unique_ptr<optionst> make_internal_default_options()
{
  std::unique_ptr<optionst> options = util_make_unique<optionst>();
  cmdlinet command_line;
  PARSE_OPTIONS_GOTO_CHECK(command_line, (*options));
  parse_solver_options(command_line, *options);
  options->set_option("built-in-assertions", true);
  options->set_option("arrays-uf", "auto");
  options->set_option("depth", UINT32_MAX);
  options->set_option("sat-preprocessor", true);
  return options;
}

std::unique_ptr<optionst> api_optionst::to_engine_options() const
{
  auto engine_options = make_internal_default_options();
  engine_options->set_option("simplify", simplify_enabled);
  return engine_options;
}
