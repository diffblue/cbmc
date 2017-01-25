/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <cegis/jsa/genetic/jsa_random.h>
#include <cegis/jsa/genetic/solution_helper.h>
#include <cegis/jsa/genetic/random_jsa_mutate.h>

random_jsa_mutatet::random_jsa_mutatet(const jsa_randomt &random) :
    random(random)
{
}

void random_jsa_mutatet::operator()(individualt &lhs,
    const individualt &rhs) const
{
  lhs=rhs;
  size_t mutation_index=random.rand() % get_num_genetic_targets(lhs);
  const size_t num_inv_instrs=lhs.invariant.size();
  if (mutation_index < num_inv_instrs)
    return random.havoc(lhs.invariant[mutation_index]);
  mutation_index-=num_inv_instrs;
  for (individualt::predicatet &pred : lhs.predicates)
  {
    const size_t num_instrs=pred.size() * OPERANDS_PER_JSA_PREDICATE_INSTRUCTION;
    if (mutation_index >= num_instrs) { mutation_index-=num_instrs; continue; }

    individualt::predicatet::value_type &instr=pred[mutation_index / OPERANDS_PER_JSA_PREDICATE_INSTRUCTION];
    individualt::predicatet::value_type tmp(instr);
    random.havoc(tmp);
    switch (mutation_index % OPERANDS_PER_JSA_PREDICATE_INSTRUCTION)
    {
    case 0: instr.op0=tmp.op0; return;
    case 1: instr.op1=tmp.op1; return;
    case 2: instr.opcode=tmp.opcode; return;
    case 3: instr.result_op=tmp.result_op; return;
    default: assert(!"Invalid predicate mutation index");
    }
  }
  individualt::queryt &query=lhs.query;
  assert(mutation_index < query.size() * OPERANDS_PER_JSA_QUERY_INSTRUCTION);
  const size_t query_index=mutation_index / OPERANDS_PER_JSA_QUERY_INSTRUCTION;
  individualt::queryt::value_type &instr=query[query_index];
  individualt::queryt::value_type tmp(instr);
  random.havoc(tmp, query_index);
  switch(mutation_index % OPERANDS_PER_JSA_QUERY_INSTRUCTION)
  {
  case 0: instr.op0=tmp.op0; break;
  case 1: instr.op1=tmp.op1; break;
  case 2: instr.opcode=tmp.opcode; break;
  default: assert(!"Invalid query mutation index");
  }
}

void random_jsa_mutatet::havoc(individualt &ind) const
{
  random.havoc(ind);
}

void random_jsa_mutatet::post_process(individualt &ind) const
{
  // TODO: Implement!
}
