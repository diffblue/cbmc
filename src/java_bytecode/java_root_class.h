/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_JAVA_BYTECODE_JAVA_ROOT_CLASS_H
#define CPROVER_JAVA_BYTECODE_JAVA_ROOT_CLASS_H

#include <util/std_expr.h>

// adds expected members for a root class,
// which is usually java.lang.Object

void java_root_class(
  class symbolt &class_symbol);

#endif // CPROVER_JAVA_BYTECODE_JAVA_ROOT_CLASS_H
