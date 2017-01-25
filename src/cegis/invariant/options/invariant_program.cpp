/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <algorithm>

#include <cegis/cegis-util/program_helper.h>
#include <cegis/invariant/util/invariant_program_helper.h>
#include <cegis/invariant/options/target_copy_helper.h>
#include <cegis/invariant/options/invariant_program.h>

invariant_programt::invariant_programt()
{
}

invariant_programt::invariant_programt(const symbol_tablet &st,
    const goto_functionst &gf) :
    st(st)
{
  this->gf.copy_from(gf);
}

namespace
{
invariant_programt &assign(invariant_programt &lhs,
    const invariant_programt &rhs)
{
  const target_copy_helpert fix(get_entry_body(rhs.gf), get_entry_body(lhs.gf));
  lhs.invariant_range=fix(rhs.invariant_range);
  lhs.assertion=rhs.assertion;
  lhs.Ix0=fix(rhs.Ix0);
  lhs.Ax=fix(rhs.Ax);
  const goto_programt::targetst &old_x0=rhs.x0_choices;
  lhs.x0_choices.resize(old_x0.size());
  std::transform(old_x0.begin(), old_x0.end(), lhs.x0_choices.begin(), fix);
  return lhs;
}
}

invariant_programt::invariant_programt(const invariant_programt &other) :
    st(other.st)
{
  gf.copy_from(other.gf);
  assign(*this, other);
}

invariant_programt &invariant_programt::operator =(
    const invariant_programt &other)
{
  st=other.st;
  gf.clear();
  gf.copy_from(other.gf);
  return assign(*this, other);
}

invariant_programt::~invariant_programt()
{
}
