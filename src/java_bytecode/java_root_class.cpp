/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "java_root_class.h"

#include <util/symbol.h>
#include <util/std_types.h>

#include "java_types.h"

/*******************************************************************

 Function: java_root_class

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void java_root_class(symbolt &class_symbol)
{
  struct_typet &struct_type=to_struct_type(class_symbol.type);
  struct_typet::componentst &components=struct_type.components();

  {
    // for monitorenter/monitorexit
    struct_typet::componentt component;
    component.set_name("@lock");
    component.set_pretty_name("@lock");
    component.type()=java_boolean_type();

    // add at the beginning
    components.insert(components.begin(), component);
  }

  {
    // the class identifier is used for stuff such as 'instanceof'
    struct_typet::componentt component;
    component.set_name("@class_identifier");
    component.set_pretty_name("@class_identifier");
    component.type()=string_typet();

    // add at the beginning
    components.insert(components.begin(), component);
  }
}
