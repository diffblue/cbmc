#include <cegis/cegis-util/string_helper.h>
#include <cegis/cegis-util/inline_user_program.h>
#include <cegis/cegis-util/counterexample_vars.h>
#include <cegis/cegis-util/program_helper.h>
#include <cegis/control/preprocessing/control_preprocessing.h>

control_preprocessingt::control_preprocessingt(const symbol_tablet &st,
    const goto_functionst &gf) :
    control_program(st, gf)
{
}

namespace
{
const char * const excluded_functions[]= {
    "verify_stability_closedloop_using_dslib", "check_stability_closedloop",
    "fxp_double_to_fxp", "fxp_to_double", "ft_closedloop_series", "poly_mult",
    "poly_sum", "internal_pow" };

bool is_meta(const goto_programt::const_targett pos)
{
  if (default_cegis_meta_criterion(pos)) return true;
  const source_locationt &loc=pos->code.source_location();
  const std::string &func=id2string(loc.get_function());
  for (const char * const excluded : excluded_functions)
    if (contains(func, excluded)) return true;
  return false;
}
}

void control_preprocessingt::operator ()()
{
  goto_functionst &gf=control_program.gf;
  inline_user_program(control_program.st, gf);
  goto_programt::targetst &locs=control_program.counterexample_locations;
  goto_programt &body=get_entry_body(gf);
  collect_counterexample_locations(locs, body, is_meta);
}

void control_preprocessingt::operator ()(const size_t max_length) const
{
}

size_t control_preprocessingt::get_min_solution_size() const
{
  return 1u;
}

const control_programt &control_preprocessingt::get_program() const
{
  return control_program;
}
