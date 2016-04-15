/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/symbol.h>
#include <util/std_types.h>

#include "java_class_identifier.h"

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
  component.set_pretty_name("@class_identifier");
  component.type()=string_typet();
  
  // add at the beginning
  struct_typet &struct_type=to_struct_type(class_symbol.type);
  struct_typet::componentst &components=struct_type.components();
  components.insert(components.begin(), component);
}

