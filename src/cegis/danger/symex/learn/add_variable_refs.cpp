/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <algorithm>

#include <util/cprover_prefix.h>
#include <util/arith_tools.h>

#include <ansi-c/c_types.h>

#include <cegis/cegis-util/program_helper.h>
#include <cegis/instrument/meta_variables.h>
#include <cegis/instrument/instrument_var_ops.h>
#include <cegis/invariant/util/invariant_program_helper.h>
#include <cegis/instrument/literals.h>
#include <cegis/invariant/meta/meta_variable_names.h>
#include <cegis/danger/options/danger_program.h>
#include <cegis/danger/symex/learn/add_variable_refs.h>

namespace
{
void link_skolem(danger_programt &prog, const size_t num_user_vars,
    const size_t user_vars, const size_t max_solution_size,
    const danger_programt::loopt &loop)
{
  const goto_programt::targetst &sklm=loop.danger_meta_variables.Sx;
  if(sklm.empty()) return;
  const symbol_tablet &st=prog.st;
  goto_programt &body=get_entry_body(prog.gf);
  goto_programt::targett pos=sklm.front();
  const size_t num_skolem=sklm.size();
  const size_t num_tmp=max_solution_size - num_skolem;
  link_temp_vars(st, body, --pos, num_tmp, user_vars);
  goto_programt::targetst::const_iterator it=sklm.begin();
  for(size_t i=0; i < num_skolem - 1; ++i, ++it)
  {
    pos=*it;
    const goto_programt::instructiont &instr=*pos;
    const size_t id=num_tmp + i;
    const irep_idt &variable=get_affected_variable(instr);
    pos=set_rops_reference(st, body, pos, variable, id);
    pos=set_ops_reference(st, body, pos, variable, id + num_user_vars);
  }
  pos=sklm.back();
  const size_t final_id=max_solution_size - 1;
  set_rops_reference(st, body, pos, get_affected_variable(*pos), final_id);
}

class link_meta_variablest
{
  danger_programt &prog;
  const size_t user_vars;
  const size_t max_size;
public:
  link_meta_variablest(danger_programt &prog, const size_t num_user_vars,
      const size_t max_solution_size) :
      prog(prog), user_vars(num_user_vars), max_size(max_solution_size)
  {
  }

  void operator()(const invariant_programt::invariant_loopt &loop) const
  {
    const invariant_programt::meta_vars_positionst &im=loop.meta_variables;
    link_result_var(prog.st, prog.gf, user_vars, max_size, im.Ix);
    link_result_var(prog.st, prog.gf, user_vars, max_size, im.Ix_prime);
  }

  void operator()(const danger_programt::loopt &loop) const
  {
    operator()(static_cast<const invariant_programt::invariant_loopt &>(loop));
    const danger_programt::danger_meta_vars_positionst &dm=
        loop.danger_meta_variables;
    auto inv=[this](const goto_programt::targett &pos)
    { link_result_var(prog.st, prog.gf, user_vars, max_size, pos);};
    std::for_each(dm.Rx.begin(), dm.Rx.end(), inv);
    std::for_each(dm.Rx_prime.begin(), dm.Rx_prime.end(), inv);
    link_skolem(prog, user_vars, user_vars, max_size, loop);
  }
};
}

void link_meta_variables(danger_programt &prog, const size_t user_vars,
    const size_t max_solution_size)
{
  const symbol_tablet &st=prog.st;
  goto_functionst &gf=prog.gf;
  link_result_var(st, gf, user_vars, max_solution_size, prog.Ix0);
  const danger_programt::loopst &loops=prog.loops;
  const link_meta_variablest link(prog, user_vars, max_solution_size);
  std::for_each(loops.begin(), loops.end(), link);
}
