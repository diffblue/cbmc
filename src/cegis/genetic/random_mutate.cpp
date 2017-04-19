/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <algorithm>

#include <cegis/genetic/random_individual.h>
#include <cegis/genetic/random_mutate.h>

random_mutatet::random_mutatet(random_individualt &random,
    const std::function<size_t(void)> &num_consts) :
    random(random), num_consts(num_consts)
{
}

random_mutatet::~random_mutatet()
{
}

namespace
{
void mutate_opcode(random_mutatet::individualt::instructiont &instr,
    random_individualt &rand, const size_t index)
{
  const random_mutatet::individualt::instructiont::opst old_ops=instr.ops;
  rand.havoc(instr, index);
  random_mutatet::individualt::instructiont::opst &new_ops=instr.ops;
  const size_t size=std::min(old_ops.size(), new_ops.size());
  for(size_t i=0; i < size; ++i)
    new_ops[i]=old_ops[i];
}
}

void random_mutatet::operator()(individualt &lhs, const individualt &rhs) const
{
  lhs=rhs;
  const size_t num_x0=lhs.x0.size();
  size_t num_mutation_candidates=num_x0;
  for(const individualt::programt &prog : lhs.programs)
  {
    for(const individualt::instructiont &instr : prog)
      num_mutation_candidates+=instr.ops.size() + 1;
  }

  size_t mutation_target=random.rand() % (num_mutation_candidates + 1);
  if(mutation_target < num_consts())
  {
    lhs.x0[mutation_target]=random.constant();
    return;
  }
  if(mutation_target < num_x0)
  {
    lhs.x0[mutation_target]=random.x0();
    return;
  }
  mutation_target-=num_x0;
  for(individualt::programt &prog : lhs.programs)
  {
    for(size_t i=0; i < prog.size(); ++i)
    {
      individualt::instructiont &instr=prog[i];
      if(!mutation_target) return mutate_opcode(instr, random, i);
      --mutation_target;
      const size_t length=instr.ops.size();
      if(mutation_target < length)
      {
        instr.ops[mutation_target]=random.op(i);
        return;
      }
      mutation_target-=length;
    }
  }
}

void random_mutatet::havoc(individualt &ind) const
{
  random.havoc(ind);
}

void random_mutatet::post_process(program_individualt &ind) const
{
  random.post_process(ind);
}
