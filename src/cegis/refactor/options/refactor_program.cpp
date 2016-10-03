#include <cegis/cegis-util/program_helper.h>
#include <cegis/invariant/options/target_copy_helper.h>
#include <cegis/refactor/options/refactor_program.h>

refactor_programt::refactor_programt(const symbol_tablet &st,
    const goto_functionst &gf) :
    st(st)
{
  this->gf.copy_from(gf);
}

namespace
{
refactor_programt &copy(refactor_programt &lhs, const refactor_programt &rhs)
{
  lhs.gf.copy_from(rhs.gf);
  goto_programt &lhs_body=get_entry_body(lhs.gf);
  const goto_programt &rhs_body=get_entry_body(rhs.gf);
  const target_copy_helpert copy(rhs_body, lhs_body);
  copy(lhs.counterexample_locations, rhs.counterexample_locations);
  return lhs;
}
}

refactor_programt::refactor_programt(const refactor_programt &other) :
    st(other.st)
{
  copy(*this, other);
}

refactor_programt::refactor_programt()
{
}

refactor_programt &refactor_programt::operator =(const refactor_programt &other)
{
  st.clear();
  st=other.st;
  gf.clear();
  return copy(*this, other);
}
