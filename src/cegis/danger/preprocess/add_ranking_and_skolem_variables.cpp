#include <algorithm>

#include <cegis/invariant/meta/meta_variable_names.h>
#include <cegis/invariant/instrument/meta_variables.h>
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
      st(st), gf(gf), loop_id(loop_id), type(invariant_meta_type()), meta(meta), pos(
          pos), skid(0)
  {
  }

  void operator()(const goto_programt::targett &sklm)
  {
    const std::string meta_name=get_Sx(loop_id, skid++);
    pos=declare_invariant_variable(st, gf, pos, meta_name, type);
    const std::string full_meta_name(get_invariant_meta_name(meta_name));
    const symbol_exprt meta_var(st.lookup(full_meta_name).symbol_expr());
    const irep_idt &sklm_name=get_affected_variable(*sklm);
    invariant_assign_user_variable(st, gf, sklm, sklm_name, meta_var);
    meta.Sx.push_back(pos);
  }
};

class create_danger_meta_variables_for_loopt
{
  symbol_tablet &st;
  goto_functionst &gf;
  size_t loop_id;
public:
  create_danger_meta_variables_for_loopt(danger_programt &prog) :
      st(prog.st), gf(prog.gf), loop_id(0u)
  {
  }

  void operator()(danger_programt::loopt &loop)
  {
    const typet type(invariant_meta_type());
    invariant_programt::meta_vars_positionst &im=loop.meta_variables;
    danger_programt::danger_meta_vars_positionst &dm=loop.danger_meta_variables;
    goto_programt::targett pos=im.Gx;
    ++pos;
    const size_t ranking_count=1; // XXX: Lexicographical ranking?
    for (size_t i=0; i < ranking_count; ++i)
    {
      pos=declare_invariant_variable(st, gf, pos, get_Rx(loop_id, i), type);
      dm.Rx.push_back(pos);
    }
    const goto_programt::targetst &sklm=loop.skolem_choices;
    const create_skolem_meta_variablest create_sklm(st, gf, loop_id, dm, pos);
    std::for_each(sklm.begin(), sklm.end(), create_sklm);
    pos=im.Ix_prime;
    for (size_t i=0; i < ranking_count; ++i)
    {
      const std::string rx_prime(get_Rx_prime(loop_id, i));
      pos=declare_invariant_variable(st, gf, pos, rx_prime, type);
      dm.Rx_prime.push_back(pos);
    }
    ++loop_id;
  }
};

#if 0
void createAx(invariant_programt &program)
{
  symbol_tablet &st=program.st;
  goto_functionst &gf=program.gf;
  goto_programt::targett pos=program.get_loops().back()->body.begin;
  const std::string base_name(get_Ax());
  const typet type(invariant_meta_type());
  program.Ax=declare_invariant_variable(st, gf, --pos, get_Ax(), type);
  assign_invariant_variable(st, gf, program.Ax, base_name, program.assertion);
}
#endif
}

void add_ranking_and_skolem_variables(danger_programt &program,
    const size_t max_program_length)
{
  danger_programt::loopst &loops=program.loops;
  const create_danger_meta_variables_for_loopt create_meta(program);
  std::for_each(loops.begin(), loops.end(), create_meta);
}
