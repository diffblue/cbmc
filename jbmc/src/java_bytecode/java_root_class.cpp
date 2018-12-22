/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "java_root_class.h"

#include <util/arith_tools.h>
#include <util/symbol.h>

#include "java_types.h"

/// Create components to an object of the root class (usually java.lang.Object)
/// Specifically, we add a new component, '\@class_identifier'. This used
/// primary to replace an expression like 'e instanceof A' with
/// 'e.\@class_identifier == "A"'
/// \param class_symbol: class symbol
void java_root_class(symbolt &class_symbol)
{
  struct_typet &struct_type=to_struct_type(class_symbol.type);
  struct_typet::componentst &components=struct_type.components();

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
/// \param [out] jlo: object to initialize
/// \param root_type: type of the root class
/// \param class_identifier: class identifier field, generally begins with
///        "java::" prefix.
void java_root_class_init(
  struct_exprt &jlo,
  const struct_typet &root_type,
  const irep_idt &class_identifier)
{
  jlo.operands().resize(root_type.components().size());

  const std::size_t clsid_nb=root_type.component_number("@class_identifier");
  const typet &clsid_type=root_type.components()[clsid_nb].type();
  constant_exprt clsid(class_identifier, clsid_type);
  jlo.operands()[clsid_nb]=clsid;

  // Check if the 'cproverMonitorCount' component exists and initialize it.
  // This field is only present when the java core models are embedded. It is
  // used to implement a critical section, which is necessary to support
  // concurrency.
  if(root_type.has_component("cproverMonitorCount"))
  {
    const std::size_t count_nb =
      root_type.component_number("cproverMonitorCount");
    const typet &count_type = root_type.components()[count_nb].type();
    jlo.operands()[count_nb] = from_integer(0, count_type);
  }
}
