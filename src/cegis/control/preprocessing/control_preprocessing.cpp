#include <cegis/cegis-util/inline_user_program.h>
#include <cegis/cegis-util/counterexample_vars.h>
#include <cegis/cegis-util/program_helper.h>
#include <cegis/control/preprocessing/control_preprocessing.h>

control_preprocessingt::control_preprocessingt(const symbol_tablet &st,
    const goto_functionst &gf) :
    control_program(st, gf)
{
}

void control_preprocessingt::operator ()()
{
  goto_functionst &gf=control_program.gf;
  inline_user_program(control_program.st, gf);
  goto_programt::targetst &locs=control_program.counterexample_locations;
  goto_programt &body=get_entry_body(gf);
  collect_counterexample_locations(locs, body);
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
