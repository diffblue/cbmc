/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_JAVA_BYTECODE_JAVA2GOTO_H
#define CPROVER_JAVA_BYTECODE_JAVA2GOTO_H

#include <goto-programs/goto_model.h>

#include "java_bytecode_parse_tree.h"

/// Turns a method into a goto program
goto_programt java2goto(const java_bytecode_parse_treet::methodt &);

#endif // CPROVER_JAVA_BYTECODE_JAVA2GOTO_H
