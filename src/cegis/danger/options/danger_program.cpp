#include <algorithm>
#include <iterator>

#include <cegis/danger/util/danger_program_helper.h>
#include <cegis/danger/options/danger_program.h>

danger_programt::danger_programt()
{
}

danger_programt::danger_programt(const symbol_tablet &st,
    const goto_functionst &gf) :
    st(st)
{
  this->gf.copy_from(gf);
}

danger_programt::~danger_programt()
{
}

void danger_programt::set_goto_program(const symbol_tablet &st,
    const goto_functionst &gf)
{
  this->st=st;
  this->gf.clear();
  this->gf.copy_from(gf);
}

namespace
{
class copy_targett
{
  const copy_targett &fix;
  const goto_programt::instructionst &old_instrs;
  goto_programt::instructionst &new_instrs;
public:
  copy_targett(const goto_functionst &old_gf, goto_functionst &new_gf) :
      fix(*this), old_instrs(get_danger_body(old_gf).instructions), new_instrs(
          get_danger_body(new_gf).instructions)
  {
  }
  goto_programt::targett operator()(const goto_programt::targett &target) const
  {
    const goto_programt::targett empty;
    if (empty == target) return empty;
    const goto_programt::const_targett old_target=target;
    const size_t old_distance=std::distance(old_instrs.begin(), old_target);
    goto_programt::targett new_target=new_instrs.begin();
    std::advance(new_target, old_distance);
    return new_target;
  }
  danger_programt::meta_vars_positionst operator()(
      const danger_programt::meta_vars_positionst &vars) const
  {
    danger_programt::meta_vars_positionst result;
    result.Gx=fix(vars.Gx);
    result.Dx=fix(vars.Dx);
    const goto_programt::targetst &old_r=vars.Rx;
    goto_programt::targetst &new_r=result.Rx;
    new_r.resize(old_r.size());
    std::transform(old_r.begin(), old_r.end(), new_r.begin(), fix);
    const goto_programt::targetst &old_s=vars.Sx;
    goto_programt::targetst &new_s=result.Sx;
    new_s.resize(old_s.size());
    std::transform(old_s.begin(), old_s.end(), new_s.begin(), fix);
    result.Dx_prime=fix(vars.Dx_prime);
    const goto_programt::targetst &old_rp=vars.Rx_prime;
    goto_programt::targetst &new_rp=result.Rx_prime;
    new_rp.resize(old_rp.size());
    std::transform(old_rp.begin(), old_rp.end(), new_rp.begin(), fix);
    return result;
  }
  danger_programt::program_ranget operator()(
      const danger_programt::program_ranget &range) const
  {
    danger_programt::program_ranget result;
    result.begin=fix(range.begin);
    result.end=fix(range.end);
    return result;
  }
  danger_programt::loopt operator()(const danger_programt::loopt &loop) const
  {
    danger_programt::loopt result;
    result.body=fix(loop.body);
    result.guard=loop.guard;
    goto_programt::targetst &new_s=result.skolem_choices;
    const goto_programt::targetst &old_s=loop.skolem_choices;
    std::transform(old_s.begin(), old_s.end(), std::back_inserter(new_s), fix);
    result.meta_variables=fix(loop.meta_variables);
    return result;
  }
};

danger_programt &assign(danger_programt &lhs, const danger_programt &rhs)
{
  const copy_targett fix(rhs.gf, lhs.gf);
  const danger_programt::loopst &old_loops=rhs.loops;
  lhs.loops.resize(old_loops.size());
  std::transform(old_loops.begin(), old_loops.end(), lhs.loops.begin(), fix);
  const goto_programt::targetst &old_x0=rhs.x0_choices;
  lhs.x0_choices.resize(old_x0.size());
  std::transform(old_x0.begin(), old_x0.end(), lhs.x0_choices.begin(), fix);
  lhs.danger_range=fix(rhs.danger_range);
  lhs.assertion=rhs.assertion;
  lhs.Dx0=fix(rhs.Dx0);
  lhs.Ax=fix(rhs.Ax);
  return lhs;
}
}

danger_programt::danger_programt(const danger_programt &other) :
    st(other.st)
{
  gf.copy_from(other.gf);
  assign(*this, other);
}

danger_programt &danger_programt::operator =(const danger_programt &other)
{
  set_goto_program(other.st, other.gf);
  return assign(*this, other);
}
