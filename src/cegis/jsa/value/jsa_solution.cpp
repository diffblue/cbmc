/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <cegis/invariant/util/copy_instructions.h>
#include <cegis/jsa/value/jsa_solution.h>

jsa_solutiont::jsa_solutiont() :
    max_size(1)
{
}

namespace
{
jsa_solutiont &copy_instrs(jsa_solutiont &lhs, const jsa_solutiont &rhs)
{
  lhs.predicates.clear();
  lhs.predicates.resize(rhs.predicates.size());
  for (size_t i=0; i < lhs.predicates.size(); ++i)
    copy_instructions(lhs.predicates[i], rhs.predicates[i]);
  lhs.query.clear();
  copy_instructions(lhs.query, rhs.query);
  lhs.invariant.clear();
  copy_instructions(lhs.invariant, rhs.invariant);
  return lhs;
}
}

jsa_solutiont::jsa_solutiont(const jsa_solutiont &other) :
    max_size(other.max_size)
{
  copy_instrs(*this, other);
}

jsa_solutiont &jsa_solutiont::operator =(const jsa_solutiont &other)
{
  max_size=other.max_size;
  return copy_instrs(*this, other);
}

void jsa_solutiont::clear() {
  max_size=0;
  predicates.clear();
  query.clear();
  invariant.clear();
}
