/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <algorithm>

#include <cegis/cegis-util/program_helper.h>
#include <cegis/instrument/meta_variables.h>
#include <cegis/instrument/instrument_var_ops.h>
#include <cegis/invariant/util/invariant_program_helper.h>
#include <cegis/invariant/meta/meta_variable_names.h>
#include <cegis/danger/meta/meta_variable_names.h>
#include <cegis/danger/constraint/danger_constraint_factory.h>
#include <cegis/danger/symex/verify/restrict_counterexamples.h>

namespace
{
bool is_assert(const goto_programt::instructiont &instr)
{
  return goto_program_instruction_typet::ASSERT == instr.type;
}

goto_programt::targett find_assertion(goto_functionst &gf)
{
  goto_programt &body=get_entry_body(gf);
  goto_programt::instructionst &i=body.instructions;
  const goto_programt::targett it=std::find_if(i.begin(), i.end(), &is_assert);
  assert(i.end() != it);
  return it;
}

goto_programt::targett add_assume(goto_functionst &gf)
{
  goto_programt &body=get_entry_body(gf);
  goto_programt::targett pos=find_assertion(gf);
  if(goto_program_instruction_typet::ASSUME == (--pos)->type) return pos;
  pos=body.insert_after(pos);
  pos->type=goto_program_instruction_typet::ASSUME;
  pos->source_location=default_cegis_source_location();
  return pos;
}

void force_all_guards_violated(exprt::operandst &op, const size_t num_loops)
{
  for(size_t i=0; i < num_loops; ++i)
  {
    const notequal_exprt Gx=danger_component_as_bool(get_Gx(i));
    const equal_exprt not_Gx(Gx.lhs(), Gx.rhs());
    op.push_back(not_Gx);
  }
}
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

void force_ranking_error(goto_functionst &gf, const size_t num_loops)
{
  exprt::operandst op;
  for(size_t i=0; i < num_loops; ++i)
  {
  const exprt::operandst conj={ danger_component_as_bool(get_Dx(i)),
      danger_component_as_bool(get_Dx(i)), danger_component_as_bool(get_Gx(i)),
      danger_component_as_bool(get_Dx_prime(i)) };
    op.push_back(conjunction(conj));
  }
  goto_programt::targett pos=add_assume(gf);
  pos->guard=disjunction(op);
}
