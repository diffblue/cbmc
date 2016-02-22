#include <algorithm>

#include <cegis/invariant/options/target_copy_helper.h>

target_copy_helpert::target_copy_helpert(const goto_programt &old_body,
    goto_programt &new_body) :
    old_instrs(old_body.instructions), new_instrs(new_body.instructions)
{
}

target_copy_helpert::~target_copy_helpert()
{
}

goto_programt::targett target_copy_helpert::operator()(
    const goto_programt::targett &target) const
{
  const goto_programt::targett empty;
  if (empty == target) return empty;
  const goto_programt::const_targett old_target=target;
  const size_t old_distance=std::distance(old_instrs.begin(), old_target);
  goto_programt::targett new_target=new_instrs.begin();
  std::advance(new_target, old_distance);
  return new_target;
}

invariant_programt::program_ranget target_copy_helpert::operator()(
    const invariant_programt::program_ranget &range) const
{
  invariant_programt::program_ranget result;
  result.begin=operator()(range.begin);
  result.end=operator()(range.end);
  return result;
}

invariant_programt::meta_vars_positionst target_copy_helpert::operator()(
    const invariant_programt::meta_vars_positionst &vars) const
{
  invariant_programt::meta_vars_positionst result;
  result.Gx=operator()(vars.Gx);
  result.Ix=operator()(vars.Ix);
  result.Ix_prime=operator()(vars.Ix_prime);
  return result;
}

void target_copy_helpert::operator()(
    invariant_programt::invariant_loopt &result,
    const invariant_programt::invariant_loopt &loop) const
{
  result.guard=loop.guard;
  result.body=operator()(loop.body);
  result.meta_variables=operator()(loop.meta_variables);
  goto_programt::targetst &new_s=result.skolem_choices;
  const goto_programt::targetst &old_s=loop.skolem_choices;
  const auto &fix=std::ref(*this);
  std::transform(old_s.begin(), old_s.end(), std::back_inserter(new_s), fix);
}
