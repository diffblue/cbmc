/*******************************************************************\

Module: GOTO Program Utilities

Author: Diffblue Ltd.

\*******************************************************************/

#include "resolve_inherited_component.h"

#include <util/range.h>
#include <util/std_types.h>
#include <util/symbol_table.h>

#include <algorithm>

/// See the operator() method comment
/// \param symbol_table: The symbol table to resolve the component against
resolve_inherited_componentt::resolve_inherited_componentt(
  const symbol_tablet &symbol_table)
  : symbol_table(symbol_table)
{
}

/// Given a class and a component, identify the concrete field or method it is
/// resolved to. For example, a reference Child.abc refers to Child's method or
/// field if it exists, or else Parent.abc, and so on regarding Parent's
/// ancestors. If none are found, an empty string will be returned.
/// \param class_id: The name of the class the function is being called on
/// \param component_name: The base name of the component (i.e. without the
///   class specifier)
/// \param include_interfaces: If true, consider inheritance from interfaces
///   (parent types other than the first listed)
/// \param user_filter: Predicate that should return true for symbols that can
///   be returned. Those for which it returns false will be ignored.
/// \return The concrete component that has been resolved
optionalt<resolve_inherited_componentt::inherited_componentt>
resolve_inherited_componentt::operator()(
  const irep_idt &class_id,
  const irep_idt &component_name,
  bool include_interfaces,
  const std::function<bool(const symbolt &)> user_filter)
{
  PRECONDITION(!class_id.empty());
  PRECONDITION(!component_name.empty());

  std::vector<irep_idt> classes_to_visit;
  classes_to_visit.push_back(class_id);
  while(!classes_to_visit.empty())
  {
    irep_idt current_class = classes_to_visit.back();
    classes_to_visit.pop_back();

    const irep_idt &full_component_identifier=
      build_full_component_identifier(current_class, component_name);

    const symbolt *symbol = symbol_table.lookup(full_component_identifier);
    if(symbol && user_filter(*symbol))
    {
      return inherited_componentt(current_class, component_name);
    }

    const auto current_class_symbol_it =
      symbol_table.symbols.find(current_class);

    if(current_class_symbol_it != symbol_table.symbols.end())
    {
      const auto parents =
        make_range(to_struct_type(current_class_symbol_it->second.type).bases())
          .map([](const struct_typet::baset &base) {
            return base.type().get_identifier();
          });

      if(include_interfaces)
      {
        classes_to_visit.insert(
          classes_to_visit.end(), parents.begin(), parents.end());
      }
      else
      {
        if(!parents.empty())
          classes_to_visit.push_back(*parents.begin());
      }
    }
  }

  return {};
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

/// Given a class and a component, identify the concrete method it is
/// resolved to. For example, a reference Child.abc refers to Child's method or
/// field if it exists, or else Parent.abc, and so on regarding Parent's
/// ancestors. If none are found, an empty string will be returned.
/// This looks first for non-abstract methods inherited from the first base
/// (i.e., for Java the superclass), then for non-abstract methods inherited
/// otherwise (for Java, interface default methods), then for any abstract
/// declaration.
/// \param classname: The name of the class the function is being called on
/// \param call_basename: The base name of the component (i.e. without the
///   class specifier)
/// \param symbol_table: Global symbol table
/// \return The concrete component that has been resolved
optionalt<resolve_inherited_componentt::inherited_componentt>
get_inherited_method_implementation(
  const irep_idt &call_basename,
  const irep_idt &classname,
  const symbol_tablet &symbol_table)
{
  resolve_inherited_componentt call_resolver{symbol_table};
  auto exclude_abstract_methods = [&](const symbolt &symbol) {
    return !symbol.type.get_bool(ID_C_abstract);
  };

  auto resolved_call =
    call_resolver(classname, call_basename, false, exclude_abstract_methods);
  if(!resolved_call)
  {
    // Check for a default implementation:
    resolved_call =
      call_resolver(classname, call_basename, true, exclude_abstract_methods);
  }
  if(!resolved_call)
  {
    // Finally accept any abstract definition, which will likely get stubbed:
    resolved_call = call_resolver(classname, call_basename, true);
  }
  return resolved_call;
}
