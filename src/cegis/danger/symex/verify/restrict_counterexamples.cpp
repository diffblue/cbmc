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

goto_programt::targett find_assertion(goto_programt &body)
{
  goto_programt::instructionst &i=body.instructions;
  const goto_programt::targett it=std::find_if(i.begin(), i.end(), &is_assert);
  assert(i.end() != it);
  return it;
}
}

void force_assertion_satisfaction(goto_functionst &gf, const size_t num_loops)
{
  goto_programt &body=get_danger_body(gf);
  goto_programt::targett pos=find_assertion(body);
  pos=body.insert_before(pos);
  pos->type=goto_program_instruction_typet::ASSUME;
  pos->source_location=default_danger_source_location();
  exprt::operandst op;
  for (size_t i=0; i < num_loops; ++i)
  {
    const notequal_exprt Dx=danger_component_as_bool(get_Dx(i));
    const notequal_exprt Gx=danger_component_as_bool(get_Gx(i));
    const equal_exprt not_Gx(Gx.lhs(), Gx.rhs());
    op.push_back(Dx);
    op.push_back(not_Gx);
  }
  pos->guard=conjunction(op);
}

void force_invariant_and_guard_satisfaction(goto_functionst &gf,
    const size_t num_loops)
{

}
