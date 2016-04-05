/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/symbol.h>

#include "java_class_identifier.h"
#include "java_types.h"

/*******************************************************************

 Function: class_identifier_type

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet class_identifier_type()
{
  return java_int_type();
}

/*******************************************************************

 Function: create_class_identifier

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void create_class_identifier(symbolt &class_symbol)
{
  struct_typet::componentt component;
  component.set_name("@class_identifier");
  component.type()=class_identifier_type();
  
  // add at the beginning
  struct_typet &struct_type=to_struct_type(class_symbol.type);
  struct_typet::componentst &components=struct_type.components();
  components.insert(components.begin(), component);
}

/*******************************************************************

 Function: make_virtual_function

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt make_virtual_function(
  const symbol_exprt &func,
  const exprt &this_obj)
{
  exprt virtual_function("virtual_function");
  virtual_function.copy_to_operands(func, this_obj);

  return virtual_function;
}
