/*******************************************************************\

Module: Extract class identifier

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

/// \file
/// Extract class identifier

#ifndef CPROVER_GOTO_PROGRAMS_CLASS_IDENTIFIER_H
#define CPROVER_GOTO_PROGRAMS_CLASS_IDENTIFIER_H

class exprt;
class namespacet;
class struct_tag_typet;
class struct_exprt;

exprt get_class_identifier_field(
  const exprt &this_expr,
  const struct_tag_typet &suggested_type,
  const namespacet &ns);

void set_class_identifier(
  struct_exprt &expr,
  const namespacet &ns,
  const struct_tag_typet &class_type);

#endif
