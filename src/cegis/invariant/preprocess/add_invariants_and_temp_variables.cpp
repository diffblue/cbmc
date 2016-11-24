#include <algorithm>

#include <cegis/invariant/meta/meta_variable_names.h>
#include <cegis/invariant/instrument/meta_variables.h>
#include <cegis/invariant/util/invariant_program_helper.h>
#include <cegis/invariant/options/invariant_program.h>
#include <cegis/invariant/preprocess/add_invariants_and_temp_variables.h>

namespace
{
bool need_temp_variables(const size_t max_program_length)
{
  return max_program_length >= 2u;
}
}

void create_tmp_variables(invariant_programt &program,
    const size_t max_program_length)
{
  if (!need_temp_variables(max_program_length)) return;
  symbol_tablet &st=program.st;
  goto_functionst &gf=program.gf;
  goto_programt &body=get_entry_body(gf);
  goto_programt::targett insert_after=program.invariant_range.begin;
  --insert_after;
  const typet type(invariant_meta_type());
  for (size_t i=0; i < max_program_length - 1; ++i)
  {
    const std::string name(get_tmp(i));
    insert_after=declare_invariant_variable(st, gf, insert_after, name, type);
    if (i == 0) move_labels(body, program.invariant_range.begin, insert_after);
  }
}

namespace
{
class create_meta_variables_for_loopt
{
  symbol_tablet &st;
  goto_functionst &gf;
  const inv_name_factoryt &inv_name;
  const inv_name_factoryt &inv_prime_name;
  size_t loop_id;
public:
  create_meta_variables_for_loopt(invariant_programt &prog,
      const inv_name_factoryt &inv_name,
      const inv_name_factoryt &inv_prime_name) :
      st(prog.st), gf(prog.gf), inv_name(inv_name), inv_prime_name(
          inv_prime_name), loop_id(0u)
  {
  }

  void operator()(invariant_programt::invariant_loopt * const loop)
  {
    const typet type(invariant_meta_type());
    invariant_programt::meta_vars_positionst &im=loop->meta_variables;
    goto_programt::targett pos=loop->body.begin;
    const std::string inv(inv_name(loop_id));
    im.Ix=declare_invariant_variable(st, gf, --pos, inv, type);
    goto_programt &body=get_entry_body(gf);
    move_labels(body, loop->body.begin, im.Ix);
    const std::string guard(get_Gx(loop_id));
    im.Gx=declare_invariant_variable(st, gf, im.Ix, guard, type);
    assign_invariant_variable(st, gf, im.Gx, guard, loop->guard);
    pos=loop->body.end;
    const std::string x_prime(inv_prime_name(loop_id));
    im.Ix_prime=declare_invariant_variable(st, gf, --pos, x_prime, type);
    move_labels(body, loop->body.end, im.Ix_prime);
    ++loop_id;
  }
};

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

void createIx0(invariant_programt &program, const std::string &inv0_name)
{
  const invariant_programt &prog=program;
  invariant_programt::const_invariant_loopst loops(prog.get_loops());
  assert(!loops.empty() && "At least one loop required.");
  const typet type(invariant_meta_type());
  const invariant_programt::invariant_loopt &first=*loops.front();
  goto_programt::targett &meta=program.Ix0;
  goto_programt::targett pos=first.meta_variables.Ix;
  goto_functionst &gf=program.gf;
  meta=declare_invariant_variable(program.st, gf, --pos, inv0_name, type);
  move_labels(get_entry_body(gf), first.body.begin, meta);
}
}

void add_invariant_variables(invariant_programt &prog,
    const std::string &inv0_name, const inv_name_factoryt inv_name,
    const inv_name_factoryt inv_prime_name)
{
  const invariant_programt::invariant_loopst loops(prog.get_loops());
  const create_meta_variables_for_loopt create(prog, inv_name, inv_prime_name);
  std::for_each(loops.begin(), loops.end(), create);
  createIx0(prog, inv0_name);
  createAx(prog);
}
