/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <algorithm>

#include <ansi-c/c_types.h>

#include <util/arith_tools.h>

#include <cegis/cegis-util/program_helper.h>
#include <cegis/instrument/literals.h>
#include <cegis/instrument/meta_variables.h>
#include <cegis/invariant/util/invariant_program_helper.h>
#include <cegis/invariant/symex/learn/add_invariant_programs_to_learn.h>
#include <cegis/danger/meta/literals.h>
#include <cegis/danger/options/danger_program.h>

namespace
{
class declare_danger_programst
{
  danger_programt &prog;
  const size_t max_sol_sz;
  goto_programt::targett pos;
public:
  declare_danger_programst(danger_programt &prog,
      const size_t max_solution_size, const goto_programt::targett &pos) :
      prog(prog), max_sol_sz(max_solution_size), pos(pos)
  {
  }

  void operator()(const danger_programt::loopt &loop)
  {
    const symbol_tablet &st=prog.st;
    goto_functionst &gf=prog.gf;
    const danger_programt::danger_meta_vars_positionst &dm=
        loop.danger_meta_variables;
    const goto_programt::targetst &rx=dm.Rx;
    const goto_programt::targetst &rx_prime=dm.Rx_prime;
    if(!rx.empty() && !rx_prime.empty())
    {
      const goto_programt::targett rx_prog=*rx.rbegin();
      pos=add_inv_prog(prog, pos, max_sol_sz, rx_prog);
      const std::string rx_prog_name=get_prog_var_name(st, rx_prog);
      execute_inv_prog(st, gf, max_sol_sz, *rx_prime.rbegin(), rx_prog_name);
    }
    const goto_programt::targetst &sx=dm.Sx;
    if(!sx.empty()) pos=add_inv_prog(prog, pos, max_sol_sz, *sx.rbegin());
  }
};
}

void danger_add_programs_to_learn(danger_programt &prog, const size_t max_sz)
{
  const danger_programt::loopst &loops=prog.loops;
  if(loops.empty()) return;
  const goto_programt::targett pos=add_invariant_progs_to_learn(prog, max_sz);
  const declare_danger_programst declare_danger_progs(prog, max_sz, pos);
  std::for_each(loops.begin(), loops.end(), declare_danger_progs);
  const danger_programt::loopt first_loop=*loops.begin();
  const symbol_tablet &st=prog.st;
  const std::string D0=get_prog_var_name(st, first_loop.meta_variables.Ix);
  execute_inv_prog(st, prog.gf, max_sz, prog.Ix0, D0);
}
