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
