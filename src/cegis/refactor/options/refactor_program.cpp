/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <cegis/cegis-util/iterator_helper.h>
#include <cegis/cegis-util/program_helper.h>
#include <cegis/refactor/options/refactor_program.h>

refactor_programt::refactor_programt(const symbol_tablet &st,
    const goto_functionst &gf) :
    st(st)
{
  this->gf.copy_from(gf);
}

namespace
{
class copy_targett
{
  goto_functionst &lhs_func;
  const goto_functionst &rhs_func;
public:
  copy_targett(goto_functionst &lhs_func, const goto_functionst &rhs_func) :
      lhs_func(lhs_func), rhs_func(rhs_func)
  {
  }

  goto_programt::targett operator()(const goto_programt::targett rhs) const
  {
    const goto_programt::targett empty;
    if (empty == rhs) return empty;
    const std::string &function=id2string(rhs->function);
    goto_programt &lhs_body=get_body(lhs_func, function);
    const goto_programt &rhs_body=get_body(rhs_func, function);
    return copy_iterator(rhs_body.instructions, lhs_body.instructions, rhs);
  }

  void operator()(goto_programt::targetst &lhs,
      const goto_programt::targetst &rhs) const
  {
    lhs.resize(rhs.size());
    std::transform(rhs.begin(), rhs.end(), lhs.begin(), *this);
  }
};

void copy(const copy_targett &copy, goto_ranget &lhs, const goto_ranget &rhs)
{
  lhs.first=copy(rhs.first);
  lhs.second=copy(rhs.second);
}

void copy(const copy_targett &copy, refactor_programt::sketcht &lhs,
    const refactor_programt::sketcht &rhs)
{
  lhs.init=copy(rhs.init);
  ::copy(copy, lhs.input_range, rhs.input_range);
  ::copy(copy, lhs.spec_range, rhs.spec_range);
  lhs.state_vars=rhs.state_vars;
  lhs.types=rhs.types;
}

refactor_programt &copy(refactor_programt &lhs, const refactor_programt &rhs)
{
  lhs.gf.copy_from(rhs.gf);
  const copy_targett copy(lhs.gf, rhs.gf);
  lhs.counterexample_locations.clear();
  for (const refactor_programt::counterexample_locationst::value_type &entry : rhs.counterexample_locations)
    copy(lhs.counterexample_locations[entry.first], entry.second);
  lhs.sketches.resize(rhs.sketches.size());
  for (size_t i=0; i < lhs.sketches.size(); ++i)
    ::copy(copy, lhs.sketches[i], rhs.sketches[i]);
  lhs.programs=rhs.programs;
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
