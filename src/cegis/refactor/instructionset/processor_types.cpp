/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <ansi-c/c_types.h>

#include <cegis/refactor/instructionset/processor_types.h>

typet cegis_opcode_type()
{
  return unsigned_char_type();
}

typet cegis_operand_type()
{
  return cegis_opcode_type();
}

typet cegis_size_type()
{
  return cegis_opcode_type();
}

bool is_cegis_primitive(const typet &type)
{
  const irep_idt &id=type.id();
  return ID_c_bool == id || ID_floatbv == id || ID_unsignedbv == id
      || ID_signedbv == id;
}
