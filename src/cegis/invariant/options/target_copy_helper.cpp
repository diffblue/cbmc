/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <algorithm>
#include <iterator>
#include <functional>

#include <cegis/cegis-util/iterator_helper.h>
#include <cegis/invariant/options/target_copy_helper.h>

target_copy_helpert::target_copy_helpert(const goto_programt &old_body,
    goto_programt &new_body) :
    old_instrs(old_body.instructions), new_instrs(new_body.instructions)
{
}

goto_programt::targett target_copy_helpert::operator()(
    const goto_programt::targett &target) const
{
  return copy_iterator(old_instrs, new_instrs, target);
}

void target_copy_helpert::operator()(goto_programt::targetst &tgt,
    const goto_programt::targetst &src) const
{
  tgt.resize(src.size());
  std::transform(src.begin(), src.end(), tgt.begin(), *this);
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
