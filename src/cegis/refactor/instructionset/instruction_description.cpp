/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <cegis/refactor/instructionset/instruction_description.h>

instruction_descriptiont::instruction_descriptiont(const typest &signature,
    const instruction_factoryt &factory) :
    signature(signature), factory(factory)
{
  assert(!signature.empty());
}

bool instruction_descriptiont::has_result() const
{
  return ID_empty != result_type().id();
}

const typet &instruction_descriptiont::result_type() const
{
  return signature.front();
}

instruction_descriptiont::typest instruction_descriptiont::operand_types() const
{
  return typest(std::next(signature.begin()), signature.end());
}

goto_programt::targett instruction_descriptiont::operator()(
    const symbol_tablet &st, const std::string &func_name, goto_programt &body,
    goto_programt::targett pos) const
{
  return factory(st, func_name, body, pos);
}
