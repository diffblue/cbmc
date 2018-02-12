/*******************************************************************\

 Module: GOTO Program Utilities

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

#include <algorithm>

#include "resolve_inherited_component.h"

/// See the operator() method comment.
/// \param symbol_table: The symbol table to resolve the component against
resolve_inherited_componentt::resolve_inherited_componentt(
  const symbol_tablet &symbol_table):
    symbol_table(symbol_table)
{
  class_hierarchy(symbol_table);
}

/// See the operator() method comment
/// \param symbol_table: The symbol table to resolve the component against
/// \param class_hierarchy: A prebuilt class_hierachy based on the symbol_table
///
resolve_inherited_componentt::resolve_inherited_componentt(
  const symbol_tablet &symbol_table, const class_hierarchyt &class_hierarchy):
    class_hierarchy(class_hierarchy),
    symbol_table(symbol_table)
{
  // We require the class_hierarchy to be already populated if we are being
  // supplied it.
  PRECONDITION(!class_hierarchy.class_map.empty());
}

/// Given a class and a component, identify the concrete field or method it is
/// resolved to. For example, a reference Child.abc refers to Child's method or
/// field if it exists, or else Parent.abc, and so on regarding Parent's
/// ancestors. If none are found, an empty string will be returned.
/// \param class_id: The name of the class the function is being called on
/// \param component_name: The base name of the component (i.e. without the
///   class specifier)
/// \return The concrete component that has been resolved
resolve_inherited_componentt::inherited_componentt
  resolve_inherited_componentt::operator()(
    const irep_idt &class_id, const irep_idt &component_name)
{
  PRECONDITION(!class_id.empty());
  PRECONDITION(!component_name.empty());

  irep_idt current_class=class_id;
  while(!current_class.empty())
  {
    const irep_idt &full_component_identifier=
      build_full_component_identifier(current_class, component_name);

    if(symbol_table.has_symbol(full_component_identifier))
    {
      return inherited_componentt(current_class, component_name);
    }

    const class_hierarchyt::idst &parents=
      class_hierarchy.class_map[current_class].parents;

    if(parents.empty())
      break;
    current_class=parents.front();
  }

  return inherited_componentt();
}

/// Build a component name as found in a GOTO symbol table equivalent to the
/// name of a concrete component component_name on class class_name
/// \param component_name: The name of the component
/// \param class_name: The class the implementation would be found on.
/// \return A name for looking up in the symbol table for classes `class_name`'s
///   component `component_name`
irep_idt resolve_inherited_componentt::build_full_component_identifier(
  const irep_idt &class_name, const irep_idt &component_name)
{
  // Verify the parameters are called in the correct order.
  PRECONDITION(id2string(class_name).find("::")!=std::string::npos);
  PRECONDITION(id2string(component_name).find("::")==std::string::npos);
  return id2string(class_name)+'.'+id2string(component_name);
}

/// Get the full name of this function
/// \return The symbol name for this function call
irep_idt resolve_inherited_componentt::inherited_componentt::
  get_full_component_identifier() const
{
  return resolve_inherited_componentt::build_full_component_identifier(
    class_identifier, component_identifier);
}

/// Use to check if this inherited_componentt has been fully constructed.
/// \return True if this represents a real concrete component
bool resolve_inherited_componentt::inherited_componentt::is_valid() const
{
  return !class_identifier.empty();
}
