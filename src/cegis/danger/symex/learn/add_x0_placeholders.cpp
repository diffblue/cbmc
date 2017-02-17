/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <algorithm>

#include <cegis/cegis-util/program_helper.h>
#include <cegis/instrument/meta_variables.h>
#include <cegis/danger/options/danger_program.h>
#include <cegis/danger/meta/literals.h>
#include <cegis/danger/symex/learn/add_x0_placeholders.h>

namespace
{
const typet &get_type(const goto_programt::targett &target)
{
  const goto_programt::instructiont &instr=*target;
  switch (instr.type)
  {
  case goto_program_instruction_typet::DECL:
    return to_code_decl(instr.code).symbol().type();
  case goto_program_instruction_typet::ASSIGN:
    return to_code_assign(instr.code).lhs().type();
  default:
    assert(!"Only DECL or ASSIGN supported.");
  }
}

class add_x0_placeholdert
{
  danger_programt &prog;
  symbol_tablet &st;
  goto_functionst &gf;
public:
  explicit add_x0_placeholdert(danger_programt &prog) :
      prog(prog), st(prog.st), gf(prog.gf)
  {
  }

  void operator()(const goto_programt::targett &target) const
  {
    const irep_idt &x0_name=get_affected_variable(*target);
    std::string base_name(DANGER_X0_PLACEHOLDER_PREFIX);
    base_name+=id2string(x0_name);
    goto_programt::targett pos=prog.invariant_range.begin;
    const typet &type=get_type(target);
    declare_cegis_meta_variable(st, gf, --pos, base_name, type);
    const std::string full_name(get_cegis_meta_name(base_name));
    const symbol_exprt placeholder(full_name, type);
    cegis_assign_user_variable(st, gf, target, x0_name, placeholder);
  }
};
}

void danger_add_x0_placeholders(danger_programt &prog)
{
  const goto_programt::targetst &x0=prog.x0_choices;
  const add_x0_placeholdert add_placeholder(prog);
  std::for_each(x0.begin(), x0.end(), add_placeholder);
}
