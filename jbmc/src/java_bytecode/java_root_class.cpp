/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "java_root_class.h"

#include <util/arith_tools.h>
#include <util/symbol.h>

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

/// Adds members for an object of the root class (usually java.lang.Object).
/// \param jlo [out] : object to initialize
/// \param root_type: type of the root class
/// \param lock: lock field
/// \param class_identifier: class identifier field, generally begins with
///        "java::" prefix.
void java_root_class_init(
  struct_exprt &jlo,
  const struct_typet &root_type,
  const bool lock,
  const irep_idt &class_identifier)
{
  jlo.operands().resize(root_type.components().size());

  const std::size_t clsid_nb=root_type.component_number("@class_identifier");
  const typet &clsid_type=root_type.components()[clsid_nb].type();
  constant_exprt clsid(class_identifier, clsid_type);
  jlo.operands()[clsid_nb]=clsid;

  const std::size_t lock_nb=root_type.component_number("@lock");
  const typet &lock_type=root_type.components()[lock_nb].type();
  jlo.operands()[lock_nb]=from_integer(lock, lock_type);
}
