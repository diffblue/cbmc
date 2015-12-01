#include <algorithm>

#include <cegis/danger/meta/literals.h>
#include <cegis/danger/meta/meta_variable_names.h>
#include <cegis/danger/value/danger_goto_solution.h>
#include <cegis/danger/options/danger_program.h>
#include <cegis/danger/util/copy_instructions.h>
#include <cegis/danger/util/danger_program_helper.h>
#include <cegis/danger/instrument/meta_variables.h>
#include <cegis/danger/symex/verify/insert_candidate.h>

namespace
{
class assign_x0t
{
  const symbol_tablet &st;
  goto_functionst &gf;
  goto_programt::targetst::const_iterator current_choice;
public:
  assign_x0t(danger_programt &prog) :
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
    danger_assign_user_variable(st, gf, pos, var_name, x0_value);
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

typedef std::map<const irep_idt, const irep_idt> replacementst;

class replace_name_visitort: public expr_visitort
{
  const replacementst &repl;
public:
  replace_name_visitort(const replacementst &repl) :
      repl(repl)
  {
  }

  virtual ~replace_name_visitort()
  {
  }

  virtual void operator()(exprt &expr)
  {
    if (ID_symbol != expr.id()) return;
    symbol_exprt &symbol=to_symbol_expr(expr);
    for (replacementst::const_iterator it=repl.begin(); it != repl.end(); ++it)
      if (symbol.get_identifier() == it->first)
        symbol.set_identifier(it->second);
  }
};

class insert_instrt
{
  copy_instructionst &copy_instr;
  goto_programt &body;
  goto_programt::targett &pos;
  replace_name_visitort visitor;
public:
  insert_instrt(copy_instructionst &copy_instr, goto_programt &body,
      goto_programt::targett &pos, const replacementst &replacements) :
      copy_instr(copy_instr), body(body), pos(pos), visitor(replacements)
  {
  }

  void operator()(const goto_programt::const_targett &target)
  {
    copy_instr(pos=body.insert_after(pos), target);
    pos->guard.visit(visitor);
    pos->code.visit(visitor);
  }
};

void insert_program(goto_programt &body, goto_programt::targett pos,
    const goto_programt::instructionst &prog, const replacementst &replacements)
{
  copy_instructionst copy_instr;
  insert_instrt insert_instr(copy_instr, body, pos, replacements);
  goto_programt::const_targett first=prog.begin();
  goto_programt::const_targett last=prog.end();
  if (first == last) return;
  --last;
  for (; first != last; ++first)
    insert_instr(first);
  copy_instr.finalize(++pos, last);
}

void insert_program(goto_programt &body, const goto_programt::targett &pos,
    const goto_programt::instructionst &prog, const irep_idt &org_name,
    const irep_idt &new_name)
{
  replacementst repl;
  repl.insert(std::make_pair(org_name, new_name));
  insert_program(body, pos, prog, repl);
}

void insert_program(goto_programt &body, const goto_programt::targett &pos,
    const goto_programt::instructionst &prog)
{
  const replacementst replacements;
  insert_program(body, pos, prog, replacements);
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
    const danger_programt::meta_vars_positionst &vars=loop.meta_variables;
    insert_program(body, vars.Dx, solution.invariant);
    const irep_idt &Dx=get_affected_variable(*vars.Dx);
    const irep_idt &Dx_prime=get_affected_variable(*vars.Dx_prime);
    insert_program(body, vars.Dx_prime, solution.invariant, Dx, Dx_prime);
    if (!vars.Rx.empty() && !vars.Rx_prime.empty())
    {
      const goto_programt::targett Rx=*vars.Rx.rbegin();
      insert_program(body, *vars.Rx.rbegin(), solution.ranking);
      const irep_idt &Rx_n=get_affected_variable(*Rx);
      const goto_programt::targett Rx_prime=*vars.Rx_prime.rbegin();
      const irep_idt &Rx_pn=get_affected_variable(*Rx_prime);
      insert_program(body, Rx_prime, solution.ranking, Rx_n, Rx_pn); // XXX: Lexicographical ranking?
    }
    if (!vars.Sx.empty())
      insert_program(body, *vars.Sx.rbegin(), solution.skolem);
  }
};

void insert_programs(danger_programt &prog, const candidatet &candidate)
{
  const candidatet::danger_programst &progs=candidate.danger_programs;
  if (progs.empty()) return;
  goto_programt &body=get_danger_body(prog.gf);
  const goto_programt::instructionst &first_inv=progs.begin()->invariant;
  const std::string D0x(get_danger_meta_name(get_Dx(0)));
  const std::string Dx0(get_danger_meta_name(get_Dx0()));
  insert_program(body, prog.Dx0, first_inv, D0x, Dx0);
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
