#include <algorithm>

#include <cegis/danger/util/danger_program_helper.h>
#include <cegis/danger/constraint/danger_constraint_factory.h>
#include <cegis/danger/meta/meta_variable_names.h>
#include <cegis/danger/instrument/meta_variables.h>
#include <cegis/danger/symex/verify/restrict_counterexamples.h>

namespace
{
bool is_assert(const goto_programt::instructiont &instr)
{
  return goto_program_instruction_typet::ASSERT == instr.type;
}

goto_programt::targett find_assertion(goto_functionst &gf)
{
  goto_programt &body=get_danger_body(gf);
  goto_programt::instructionst &i=body.instructions;
  const goto_programt::targett it=std::find_if(i.begin(), i.end(), &is_assert);
  assert(i.end() != it);
  return it;
}

goto_programt::targett add_assume(goto_functionst &gf)
{
  goto_programt &body=get_danger_body(gf);
  goto_programt::targett pos=find_assertion(gf);
  if (goto_program_instruction_typet::ASSUME == (--pos)->type) return pos;
  pos=body.insert_after(pos);
  pos->type=goto_program_instruction_typet::ASSUME;
  pos->source_location=default_danger_source_location();
  return pos;
}

void force_all_guards_violated(exprt::operandst &op, const size_t num_loops)
{
  for (size_t i=0; i < num_loops; ++i)
  {
    const notequal_exprt Gx=danger_component_as_bool(get_Gx(i));
    const equal_exprt not_Gx(Gx.lhs(), Gx.rhs());
    op.push_back(not_Gx);
  }
}

#if 0
void get_all_exits(exprt::operandst &op, const size_t num_loops)
{
  for (size_t i=0; i < num_loops; ++i)
  {
    op.push_back(danger_component_as_bool(get_Gx(i)));
  }
}
#endif
}

void force_assertion_satisfaction(goto_functionst &gf, const size_t num_loops)
{
  exprt::operandst op;
  force_all_guards_violated(op, num_loops);
  op.push_back(danger_component_as_bool(get_Ax()));
  goto_programt::targett pos=add_assume(gf);
  pos->guard=conjunction(op);
}

void force_assertion_violation(goto_functionst &gf, const size_t num_loops)
{
  exprt::operandst op;
  force_all_guards_violated(op, num_loops);
  const notequal_exprt Ax(danger_component_as_bool(get_Ax()));
  const equal_exprt not_Ax(Ax.lhs(), Ax.rhs());
  op.push_back(not_Ax);
  goto_programt::targett pos=add_assume(gf);
  pos->guard=conjunction(op);
}

void force_loop_exit(goto_functionst &gf, const exprt::operandst &loop_guards)
{
  const size_t num_loops=loop_guards.size();
  exprt::operandst exits;
  for (size_t i=0; i < num_loops; ++i)
  {
    const notequal_exprt Gx=danger_component_as_bool(get_Gx(i));
    exprt not_Gx_prime=loop_guards[i];
    if (ID_not == not_Gx_prime.id()) not_Gx_prime=
        to_not_expr(not_Gx_prime).op();
    else not_Gx_prime=not_exprt(not_Gx_prime);
    exits.push_back(and_exprt(Gx, not_Gx_prime));
  }
  goto_programt::targett pos=add_assume(gf);
  pos->guard=disjunction(exits);
}

void force_guard_violation(goto_functionst &gf, const size_t num_loops)
{
  exprt::operandst op;
  force_all_guards_violated(op, num_loops);
  goto_programt::targett pos=add_assume(gf);
  pos->guard=disjunction(op);
}

void force_invariant_and_guard_satisfaction(goto_functionst &gf,
    const size_t num_loops)
{
  exprt::operandst op;
  for (size_t i=0; i < num_loops; ++i)
  {
    const notequal_exprt Dx=danger_component_as_bool(get_Dx(i));
    const notequal_exprt Gx=danger_component_as_bool(get_Gx(i));
    op.push_back(and_exprt(Dx, Gx));
  }
  goto_programt::targett pos=add_assume(gf);
  pos->guard=disjunction(op);
}
