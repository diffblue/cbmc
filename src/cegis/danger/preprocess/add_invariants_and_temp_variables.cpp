#include <algorithm>

#include <cegis/danger/options/danger_program.h>
#include <cegis/danger/util/danger_program_helper.h>
#include <cegis/danger/meta/meta_variable_names.h>
#include <cegis/danger/instrument/meta_variables.h>

namespace
{
void create_tmp_variables(danger_programt &program,
    const size_t max_program_length)
{
  symbol_tablet &st=program.st;
  goto_functionst &gf=program.gf;
  goto_programt::targett insert_after=program.danger_range.begin;
  --insert_after;
  const typet type(danger_meta_type());
  for (size_t i=0; i < max_program_length - 1; ++i)
  {
    const std::string base_name(get_tmp(i));
    insert_after=declare_danger_variable(st, gf, insert_after, base_name, type);
  }
}

void createDx0(danger_programt &prog)
{
  danger_programt::loopst &loops=prog.loops;
  assert(!loops.empty() && "At least one loop required.");
  const typet type(danger_meta_type());
  const danger_programt::loopt &first=*loops.begin();
  goto_programt::targett &meta=prog.Dx0;
  goto_programt::targett pos=first.body.begin;
  meta=declare_danger_variable(prog.st, prog.gf, --pos, get_Dx0(), type);
}

class create_skolem_meta_variablest
{
  symbol_tablet &st;
  goto_functionst &gf;
  const size_t loop_id;
  const typet type;
  danger_programt::meta_vars_positionst &meta;
  goto_programt::targett pos;
  size_t skid;
public:
  create_skolem_meta_variablest(symbol_tablet &st, goto_functionst &gf,
      const size_t loop_id, danger_programt::meta_vars_positionst &meta,
      const goto_programt::targett &pos) :
      st(st), gf(gf), loop_id(loop_id), type(danger_meta_type()), meta(meta), pos(
          pos), skid(0)
  {
  }

  void operator()(const goto_programt::targett &sklm)
  {
    const std::string meta_name=get_Sx(loop_id, skid++);
    pos=declare_danger_variable(st, gf, pos, meta_name, type);
    const std::string full_meta_name(get_danger_meta_name(meta_name));
    const symbol_exprt meta_var(st.lookup(full_meta_name).symbol_expr());
    const irep_idt &sklm_name=get_affected_variable(*sklm);
    danger_assign_user_variable(st, gf, sklm, sklm_name, meta_var);
    meta.Sx.push_back(pos);
  }
};

class create_meta_variables_for_loopt
{
  symbol_tablet &st;
  goto_functionst &gf;
  size_t loop_id;
public:
  create_meta_variables_for_loopt(danger_programt &prog) :
      st(prog.st), gf(prog.gf), loop_id(0u)
  {
  }

  void operator()(danger_programt::loopt &loop)
  {
    const typet type(danger_meta_type());
    danger_programt::meta_vars_positionst &meta=loop.meta_variables;
    goto_programt::targett pos=loop.body.begin;
    const std::string inv(get_Dx(loop_id));
    meta.Dx=declare_danger_variable(st, gf, --pos, inv, type);
    const std::string guard(get_Gx(loop_id));
    meta.Gx=declare_danger_variable(st, gf, meta.Dx, guard, type);
    pos=assign_danger_variable(st, gf, meta.Gx, guard, loop.guard);
    const size_t ranking_count=1; // XXX: Lexicographical ranking?
    for (size_t i=0; i < ranking_count; ++i)
    {
      pos=declare_danger_variable(st, gf, pos, get_Rx(loop_id, i), type);
      meta.Rx.push_back(pos);
    }
    const goto_programt::targetst &sklm=loop.skolem_choices;
    const create_skolem_meta_variablest create_sklm(st, gf, loop_id, meta, pos);
    std::for_each(sklm.begin(), sklm.end(), create_sklm);
    pos=loop.body.end;
    const std::string x_prime(get_Dx_prime(loop_id));
    meta.Dx_prime=declare_danger_variable(st, gf, --pos, x_prime, type);
    pos=meta.Dx_prime;
    for (size_t i=0; i < ranking_count; ++i)
    {
      pos=declare_danger_variable(st, gf, pos, get_Rx_prime(loop_id, i), type);
      meta.Rx_prime.push_back(pos);
    }
    ++loop_id;
  }
};

void createAx(danger_programt &program)
{
  symbol_tablet &st=program.st;
  goto_functionst &gf=program.gf;
  goto_programt::targett pos=program.loops.back().body.begin;
  const std::string base_name(get_Ax());
  const typet type(danger_meta_type());
  program.Ax=declare_danger_variable(st, gf, --pos, get_Ax(), type);
  assign_danger_variable(st, gf, program.Ax, base_name, program.assertion);
}

void create_meta_variables(danger_programt &program)
{
  createDx0(program);
  danger_programt::loopst &loops=program.loops;
  const create_meta_variables_for_loopt create(program);
  std::for_each(loops.begin(), loops.end(), create);
  createAx(program);
}
}

void add_danger_invariants_and_temp_variables(danger_programt &program,
    const size_t max_program_length)
{
  create_tmp_variables(program, max_program_length);
  create_meta_variables(program);
}
