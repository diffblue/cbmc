/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <algorithm>

#include <cegis/jsa/genetic/jsa_random.h>
#include <cegis/jsa/genetic/solution_helper.h>
#include <cegis/jsa/genetic/random_jsa_cross.h>

random_jsa_crosst::random_jsa_crosst(const jsa_randomt &random) :
    random(random)
{
}

namespace
{
typedef random_jsa_crosst::individualt individualt;
typedef individualt::invariantt invariantt;
typedef individualt::predicatet predicatet;
typedef individualt::queryt queryt;

void splice(invariantt::value_type &result, const invariantt::value_type &lhs,
    const invariantt::value_type &rhs, const size_t offset)
{
  result=lhs;
}

void splice(predicatet::value_type &result, const predicatet::value_type &lhs,
    const predicatet::value_type &rhs, const size_t offset)
{
  result=rhs;
  switch(offset) {
  case 3: result.opcode=lhs.opcode;
  case 2: result.op1=lhs.op1;
  case 1: result.op0=lhs.op0;
  case 0: break;
  default: assert(!"Invalid predicate instruction index.");
  }
}

void splice(queryt::value_type &result, const queryt::value_type &lhs,
    const queryt::value_type &rhs, const size_t offset)
{
  result=rhs;
  switch(offset) {
  case 2: result.op1=lhs.op1;
  case 1: result.op0=lhs.op0;
  case 0: break;
  default: assert(!"Invalid query instruction index.");
  }
}

template<class containert>
void splice(containert &result, const containert &lhs, const containert &rhs,
    const size_t offset, const size_t element_size)
{
  const size_t rhs_size=rhs.size();
  const size_t offset_index=offset / element_size;
  assert(rhs_size > 0);
  const size_t rhs_offset_index=std::min(offset_index, rhs_size - 1);
  const size_t result_size=offset_index + rhs_size - rhs_offset_index;
  result.resize(result_size);
  const typename containert::const_iterator lhs_first=lhs.begin();
  const typename containert::iterator result_first=result.begin();
  std::copy(lhs_first, std::next(lhs_first, offset_index), result_first);
  const typename containert::const_iterator rhs_first=rhs.begin();
  const typename containert::iterator result_mid=std::next(result_first, offset_index);
  std::copy(std::next(rhs_first, rhs_offset_index), rhs.end(), result_mid);
  splice(result[offset_index], lhs[offset_index], rhs[rhs_offset_index], offset % element_size);
}

void check_consistency(const individualt &individual)
{
  assert(individual.invariant.size() == 1);
  assert(individual.predicates.size() >= 1);
  for (const individualt::predicatet &predicate : individual.predicates)
    assert(predicate.size() >= 1);
  assert(individual.query.size() >= 1);
}

void cross(individualt &offspring, const individualt &father,
    const individualt &mother, size_t offset)
{
  offspring.predicates=mother.predicates;
  offspring.query=mother.query;
  const individualt::invariantt &f_inv=father.invariant;
  const size_t f_inv_size=f_inv.size();
  if (offset < f_inv_size)
  {
    const individualt::invariantt &m_inv=mother.invariant;
    return splice(offspring.invariant, f_inv, m_inv, offset, OPERANDS_PER_JSA_INVARIANT_INSTRUCTION);
  }
  offset-=f_inv_size;
  offspring.invariant=father.invariant;
  for (size_t pred_index=0; pred_index < father.predicates.size(); ++pred_index)
  {
    const individualt::predicatet &f_pred=father.predicates[pred_index];
    const size_t f_pred_size=f_pred.size() * OPERANDS_PER_JSA_PREDICATE_INSTRUCTION;
    individualt::predicatet &offspring_pred=offspring.predicates[pred_index];
    if (offset >= f_pred_size)
    {
      offspring_pred=f_pred;
      offset-=f_pred_size;
      continue;
    }
    const individualt::predicatet &m_pred=mother.predicates[pred_index];
    return splice(offspring_pred, f_pred, m_pred, offset, OPERANDS_PER_JSA_PREDICATE_INSTRUCTION);
  }
  offspring.predicates=father.predicates;
  const queryt &f_query=father.query;
  assert(offset < f_query.size() * OPERANDS_PER_JSA_QUERY_INSTRUCTION);
  splice(offspring.query, f_query, mother.query, offset, OPERANDS_PER_JSA_QUERY_INSTRUCTION);
  check_consistency(offspring);
}
}

void random_jsa_crosst::operator()(const individualst &parents,
    const individualst &children) const
{
  assert(parents.size() >= 2 && children.size() >= 2);
  const individualt &father=*parents.front();
  const individualt &mother=*parents[1];
  individualt &son=*children.front();
  individualt &daughter=*children[1];

  const size_t father_sz=get_num_genetic_targets(father);
  const size_t mother_sz=get_num_genetic_targets(mother);
  const size_t son_offset=random.rand() % father_sz;
  const size_t daughter_offset=random.rand() % mother_sz;
  cross(son, father, mother, son_offset);
  cross(daughter, mother, father, daughter_offset);
}
