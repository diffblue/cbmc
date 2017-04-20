/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <cegis/cegis-util/instruction_iterator.h>

namespace
{
bool has_body(const goto_functionst::function_mapt::iterator &it,
    const goto_functionst::function_mapt::const_iterator &end)
{
  if(end == it) return false;
  return it->second.body_available();
}
}

instr_iteratort::instr_iteratort()
{
}

instr_iteratort::instr_iteratort(goto_functionst &gf) :
    func_it(gf.function_map.begin()), func_end(gf.function_map.end())
{
  while(!has_body(func_it, func_end) && func_end != func_it)
    ++func_it;
  if(has_body(func_it, func_end))
    prog_it=func_it->second.body.instructions.begin();
}

instr_iteratort &instr_iteratort::operator++()
{
  if(func_it->second.body.instructions.end() == prog_it) do
  {
    ++func_it;
    if(func_end == func_it)
    {
      func_it=goto_functionst::function_mapt::iterator();
      prog_it=goto_programt::targett();
      break;
    } else prog_it=func_it->second.body.instructions.begin();
  } while(func_it->second.body.instructions.end() == prog_it);
  else ++prog_it;
  return *this;
}

instr_iteratort instr_iteratort::operator++(int)
{
  const instr_iteratort retval=*this;
  operator ++();
  return retval;
}

bool instr_iteratort::operator==(const instr_iteratort &other) const
{
  return func_it == other.func_it && prog_it == other.prog_it;
}

bool instr_iteratort::operator!=(const instr_iteratort &other) const
{
  return func_it != other.func_it && prog_it != other.prog_it;
}

instr_iteratort::reference instr_iteratort::operator*()
{
  return *prog_it;
}

instr_iteratort::pointer instr_iteratort::operator->()
{
  return &*prog_it;
}

instr_iteratort::operator goto_programt::targett() const
{
  return prog_it;
}

const instr_iteratort instr_iteratort::end;
