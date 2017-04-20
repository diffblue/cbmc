/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <algorithm>

#include <cegis/cegis-util/program_helper.h>
#include <cegis/instrument/meta_variables.h>
#include <cegis/invariant/meta/meta_variable_names.h>
#include <cegis/invariant/util/invariant_program_helper.h>
#include <cegis/danger/options/danger_program.h>
#include <cegis/danger/meta/meta_variable_names.h>

namespace
{
class create_skolem_meta_variablest
{
  symbol_tablet &st;
  goto_functionst &gf;
  const size_t loop_id;
  const typet type;
  danger_programt::danger_meta_vars_positionst &meta;
  goto_programt::targett pos;
  size_t skid;
public:
  create_skolem_meta_variablest(symbol_tablet &st, goto_functionst &gf,
      const size_t loop_id, danger_programt::danger_meta_vars_positionst &meta,
      const goto_programt::targett &pos) :
      st(st), gf(gf), loop_id(loop_id), type(cegis_default_integer_type()), meta(meta), pos(
          pos), skid(0)
  {
  }

  void operator()(const goto_programt::targett &sklm)
  {
    const std::string meta_name=get_Sx(loop_id, skid++);
    pos=declare_cegis_meta_variable(st, gf, pos, meta_name, type);
    const std::string full_meta_name(get_cegis_meta_name(meta_name));
    const symbol_exprt meta_var(st.lookup(full_meta_name).symbol_expr());
    const irep_idt &sklm_name=get_affected_variable(*sklm);
    cegis_assign_user_variable(st, gf, sklm, sklm_name, meta_var);
    meta.Sx.push_back(pos);
  }
};

class create_danger_meta_variables_for_loopt
{
  symbol_tablet &st;
  goto_functionst &gf;
  size_t loop_id;
  const bool use_ranking;
public:
  explicit create_danger_meta_variables_for_loopt(danger_programt &prog) :
      st(prog.st), gf(prog.gf), loop_id(0u), use_ranking(prog.use_ranking)
  {
  }

  void operator()(danger_programt::loopt &loop)
  {
    const typet type(cegis_default_integer_type());
    invariant_programt::meta_vars_positionst &im=loop.meta_variables;
    danger_programt::danger_meta_vars_positionst &dm=loop.danger_meta_variables;
    goto_programt::targett pos=im.Gx;
    ++pos;
    const size_t ranking_count=1; // XXX: Lexicographical ranking?
    if(use_ranking) for(size_t i=0; i < ranking_count; ++i)
    {
      pos=declare_cegis_meta_variable(st, gf, pos, get_Rx(loop_id, i), type);
      dm.Rx.push_back(pos);
    }
    const goto_programt::targetst &sklm=loop.skolem_choices;
    const create_skolem_meta_variablest create_sklm(st, gf, loop_id, dm, pos);
    std::for_each(sklm.begin(), sklm.end(), create_sklm);
    pos=im.Ix_prime;
    if(use_ranking) for(size_t i=0; i < ranking_count; ++i)
    {
      const std::string rx_prime(get_Rx_prime(loop_id, i));
      pos=declare_cegis_meta_variable(st, gf, pos, rx_prime, type);
      dm.Rx_prime.push_back(pos);
    }
    ++loop_id;
  }
};
}

void add_ranking_and_skolem_variables(danger_programt &program,
    const size_t max_program_length)
{
  danger_programt::loopst &loops=program.loops;
  const create_danger_meta_variables_for_loopt create_meta(program);
  std::for_each(loops.begin(), loops.end(), create_meta);
}
