/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "java2goto.h"

goto_programt convert_cfg(const java_bytecode_parse_treet::methodt &);
void convert_instructions(goto_programt &);

goto_programt java2goto(const java_bytecode_parse_treet::methodt &method)
{
  goto_programt dest = convert_cfg(method);

  convert_instructions(dest);

  return dest;
}
