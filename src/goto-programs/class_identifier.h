/*******************************************************************\

Module: Extract class identifier

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_CLASS_IDENTIFIER_H
#define CPROVER_GOTO_PROGRAMS_CLASS_IDENTIFIER_H

class exprt;
class namespacet;
class symbol_typet;

exprt get_class_identifier_field(
  const exprt &this_expr,
  const symbol_typet &suggested_type,
  const namespacet &ns);

#endif
