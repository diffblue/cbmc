/*******************************************************************\

Module: Group Basic Blocks in Goto Program

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAM_BASIC_BLOCKS_H
#define CPROVER_GOTO_PROGRAM_BASIC_BLOCKS_H

#include "goto_program.h"

void basic_blocks(goto_programt &goto_program,
                  unsigned max_block_size=0);

#endif
