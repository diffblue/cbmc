/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <algorithm>

#include <cegis/cegis-util/program_helper.h>
#include <cegis/instrument/meta_variables.h>
#include <cegis/invariant/util/invariant_program_helper.h>
#include <cegis/danger/meta/literals.h>
#include <cegis/danger/meta/meta_variable_names.h>
#include <cegis/danger/value/danger_goto_solution.h>
#include <cegis/danger/options/danger_program.h>
#include <cegis/invariant/util/copy_instructions.h>
#include <cegis/invariant/symex/verify/insert_program.h>
#include <cegis/danger/symex/verify/insert_candidate.h>

namespace
{
class assign_x0t
{
  const symbol_tablet &st;
  goto_functionst &gf;
  goto_programt::targetst::const_iterator current_choice;
public:
  explicit assign_x0t(danger_programt &prog) :
      st(prog.st), gf(prog.gf), current_choice(prog.x0_choices.begin())
  {
  }

  ~assign_x0t()
  {
  }

  void operator()(const exprt &x0_value)
  {
    const goto_programt::targett pos=*current_choice++;
    const irep_idt &var_name=get_affected_variable(*pos);
    cegis_assign_user_variable(st, gf, pos, var_name, x0_value);
  }
};

void assign_x0(danger_programt &prog, const candidatet &candidate)
{
  const candidatet::nondet_choicest &x0_values=candidate.x0_choices;
  const goto_programt::targetst &x0_choices=prog.x0_choices;
  assert(x0_values.size() <= x0_choices.size());
  const assign_x0t assign(prog);
  std::for_each(x0_values.begin(), x0_values.end(), assign);
}

class insert_danger_programt
{
  const danger_programt::loopst &loops;
  goto_programt &body;
  size_t loop_id;
public:
  insert_danger_programt(danger_programt &prog, goto_programt &body) :
      loops(prog.loops), body(body), loop_id(0u)
  {
  }

  void operator()(const candidatet::danger_programt &solution)
  {
    const danger_programt::loopt &loop=loops.at(loop_id);
    const invariant_programt::meta_vars_positionst &im=loop.meta_variables;
    const danger_programt::danger_meta_vars_positionst &dm=
        loop.danger_meta_variables;
    insert_program(body, im.Ix, solution.invariant);
    const irep_idt &Dx=get_affected_variable(*im.Ix);
    const irep_idt &Dx_prime=get_affected_variable(*im.Ix_prime);
    insert_program(body, im.Ix_prime, solution.invariant, Dx, Dx_prime);
    if(!dm.Rx.empty() && !dm.Rx_prime.empty())
    {
      const goto_programt::targett Rx=*dm.Rx.rbegin();
      insert_program(body, *dm.Rx.rbegin(), solution.ranking);
      const irep_idt &Rx_n=get_affected_variable(*Rx);
      const goto_programt::targett Rx_prime=*dm.Rx_prime.rbegin();
      const irep_idt &Rx_pn=get_affected_variable(*Rx_prime);
      insert_program(body, Rx_prime, solution.ranking, Rx_n, Rx_pn); // XXX: Lexicographical ranking?
    }
    if(!dm.Sx.empty()) insert_program(body, *dm.Sx.rbegin(), solution.skolem);
  }
};

void insert_programs(danger_programt &prog, const candidatet &candidate)
{
  const candidatet::danger_programst &progs=candidate.danger_programs;
  if(progs.empty()) return;
  goto_programt &body=get_entry_body(prog.gf);
  const goto_programt::instructionst &first_inv=progs.begin()->invariant;
  const std::string D0x(get_cegis_meta_name(get_Dx(0)));
  const std::string Dx0(get_cegis_meta_name(get_Dx0()));
  insert_program(body, prog.Ix0, first_inv, D0x, Dx0);
  const insert_danger_programt insert(prog, body);
  std::for_each(progs.begin(), progs.end(), insert);
}
}

void danger_insert_candidate(danger_programt &program,
    const candidatet &candidate)
{
  assign_x0(program, candidate);
  insert_programs(program, candidate);
}
