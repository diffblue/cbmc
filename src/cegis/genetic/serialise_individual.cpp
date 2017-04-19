/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <util/bv_arithmetic.h>

#include <cegis/value/program_individual.h>
#include <cegis/genetic/serialise_individual.h>

void serialise(std::deque<unsigned int> &stream,
    const class program_individualt &ind,
    const std::function<size_t(size_t)> max_prog_sz)
{
  const program_individualt::programst &progs=ind.programs;
  const size_t num_progs=progs.size();
  for(size_t i=0; i < num_progs; ++i)
  {
    if(max_prog_sz(i) == 0u) continue;
    const program_individualt::programt &prog=progs[i];
    assert(!prog.empty());
    stream.push_back(static_cast<unsigned int>(prog.size()));
    for(const program_individualt::instructiont &instr : prog)
    {
      stream.push_back(static_cast<unsigned int>(instr.opcode));
      size_t op_count=0;
      for(const program_individualt::instructiont::opt &op : instr.ops)
      {
        stream.push_back(static_cast<unsigned int>(op));
        ++op_count;
      }
      for(; op_count < 3u; ++op_count)
        stream.push_back(0u);
    }
  }
  for(const program_individualt::x0t::value_type &x0 : ind.x0)
    stream.push_back(static_cast<unsigned int>(x0));
}

void serialise(std::deque<unsigned int> &stream,
    const std::map<const irep_idt, exprt> assignments)
{
  for(const std::pair<const irep_idt, exprt> &assignment : assignments)
  {
    const bv_arithmetict arith(assignment.second);
    const mp_integer::llong_t v=arith.to_integer().to_long();
    stream.push_back(static_cast<unsigned int>(v));
  }
}
