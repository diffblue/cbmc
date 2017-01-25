/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <cegis/cegis-util/program_helper.h>
#include <cegis/invariant/options/target_copy_helper.h>
#include <cegis/control/options/control_program.h>

control_programt::control_programt(const symbol_tablet &st,
    const goto_functionst &gf) :
    st(st)
{
  this->gf.copy_from(gf);
}

namespace
{
control_programt &copy(control_programt &lhs, const control_programt &rhs)
{
  lhs.gf.copy_from(rhs.gf);
  goto_programt &lhs_body=get_entry_body(lhs.gf);
  const goto_programt &rhs_body=get_entry_body(rhs.gf);
  const target_copy_helpert copy(rhs_body, lhs_body);
  copy(lhs.counterexample_locations, rhs.counterexample_locations);
  return lhs;
}
}

control_programt::control_programt(const control_programt &other) :
    st(other.st)
{
  copy(*this, other);
}

control_programt::control_programt()
{
}

control_programt &control_programt::operator =(const control_programt &other)
{
  st.clear();
  st=other.st;
  gf.clear();
  return copy(*this, other);
}
