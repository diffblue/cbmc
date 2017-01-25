/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <cegis/invariant/options/target_copy_helper.h>
#include <cegis/cegis-util/program_helper.h>
#include <cegis/jsa/options/jsa_program.h>

jsa_programt::jsa_programt()
{
}

namespace
{
jsa_programt &assign(jsa_programt &lhs, const jsa_programt &rhs)
{
  lhs.gf.clear();
  lhs.gf.copy_from(rhs.gf);
  goto_programt &new_body=get_entry_body(lhs.gf);
  const goto_programt &old_body=get_entry_body(rhs.gf);
  const target_copy_helpert copy(old_body, new_body);
  copy(lhs.inductive_step_renondets, rhs.inductive_step_renondets);
  copy(lhs.counterexample_locations, rhs.counterexample_locations);
  lhs.synthetic_variables=copy(rhs.synthetic_variables);
  lhs.base_case=copy(rhs.base_case);
  lhs.inductive_assumption=copy(rhs.inductive_assumption);
  lhs.inductive_step=copy(rhs.inductive_step);
  lhs.property_entailment=copy(rhs.property_entailment);
  lhs.body.first=copy(rhs.body.first);
  lhs.body.second=copy(rhs.body.second);
  lhs.guard=rhs.guard;
  return lhs;
}
}

jsa_programt::jsa_programt(const jsa_programt &other) :
    st(other.st)
{
  assign(*this, other);
}

jsa_programt::jsa_programt(const symbol_tablet &st, const goto_functionst &gf) :
    st(st)
{
  this->gf.copy_from(gf);
}

jsa_programt::~jsa_programt()
{
}

jsa_programt &jsa_programt::operator =(const jsa_programt &other)
{
  st=other.st;
  return assign(*this, other);
}
