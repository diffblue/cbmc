/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_JAVA_CLASS_IDENTIFIER_H
#define CPROVER_JAVA_CLASS_IDENTIFIER_H

#include <util/std_expr.h>

void create_class_identifier(
  class symbolt &class_symbol);

exprt make_virtual_function(
  const symbol_exprt &function,
  const exprt &this_obj);

#endif /* CPROVER_JAVA_CLASS_IDENTIFIER_H */
