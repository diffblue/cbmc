/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <algorithm>

#include <cegis/cegis-util/program_helper.h>
#include <cegis/invariant/options/target_copy_helper.h>
#include <cegis/invariant/util/invariant_program_helper.h>
#include <cegis/safety/options/safety_program.h>

safety_programt::safety_programt()
{
}

namespace
{
safety_programt &assign(safety_programt &lhs, const safety_programt &rhs)
{
  const target_copy_helpert copy(get_entry_body(rhs.gf),
      get_entry_body(lhs.gf));
  const safety_programt::safety_loopst &old_loops=rhs.safety_loops;
  safety_programt::safety_loopst &new_loops=lhs.safety_loops;
  new_loops.resize(old_loops.size());
  std::transform(old_loops.begin(), old_loops.end(), new_loops.begin(),
      [&copy](const invariant_programt::invariant_loopt &old_loop)
      { invariant_programt::invariant_loopt new_loop;
        copy(new_loop, old_loop);
        return new_loop;});
  return lhs;
}
}

safety_programt::safety_programt(const safety_programt &other) :
    invariant_programt(other)
{
  assign(*this, other);
}

safety_programt::safety_programt(const symbol_tablet &st,
    const class goto_functionst &gf) :
    invariant_programt(st, gf)
{
}

safety_programt::~safety_programt()
{
}

safety_programt &safety_programt::operator=(const safety_programt &other)
{
  invariant_programt::operator =(other);
  return assign(*this, other);
}

invariant_programt::const_invariant_loopst safety_programt::get_loops() const
{
  const_invariant_loopst result(safety_loops.size());
  std::transform(safety_loops.begin(), safety_loops.end(), result.begin(),
      [](const invariant_loopt &loop)
      { return &loop;});
  return result;
}

invariant_programt::invariant_loopst safety_programt::get_loops()
{
  invariant_loopst result(safety_loops.size());
  std::transform(safety_loops.begin(), safety_loops.end(), result.begin(),
      [](invariant_loopt &loop)
      { return &loop;});
  return result;
}

invariant_programt::invariant_loopt &safety_programt::add_loop()
{
  safety_loops.push_back(invariant_loopt());
  return safety_loops.back();
}
