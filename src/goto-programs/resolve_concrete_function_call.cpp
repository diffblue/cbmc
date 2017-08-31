/*******************************************************************\

 Module: GOTO Program Utilities

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

#include <algorithm>

#include "resolve_concrete_function_call.h"

/// See the operator() method comment.
/// \param symbol_table: The symbol table to resolve the function call in
resolve_concrete_function_callt::resolve_concrete_function_callt(
  const symbol_tablet &symbol_table):
    symbol_table(symbol_table)
{
  class_hierarchy(symbol_table);
}

/// See the operator() method comment
/// \param symbol_table: The symbol table to resolve the function call in
/// \param class_hierarchy: A prebuilt class_hierachy based on the symbol_table
///
resolve_concrete_function_callt::resolve_concrete_function_callt(
  const symbol_tablet &symbol_table, const class_hierarchyt &class_hierarchy):
    class_hierarchy(class_hierarchy),
    symbol_table(symbol_table)
{
  // We require the class_hierarchy to be already populated if we are being
  // supplied it.
  PRECONDITION(!class_hierarchy.class_map.empty());
}

/// Given a virtual function call, identify what concrete call this would be
/// resolved to. For example, calling a method on a class will call its
/// implementions if it exists, else will call the first parent that provides an
/// implementation. If none are found, an empty string will be returned.
/// \param class_id: The name of the class the function is being called on
/// \param component_name: The base name of the function (e.g. without the
///   class specifier
/// \return The concrete call that has been resolved
resolve_concrete_function_callt::concrete_function_callt
  resolve_concrete_function_callt::operator()(
    const irep_idt &class_id, const irep_idt &component_name)
{
  PRECONDITION(!class_id.empty());
  PRECONDITION(!component_name.empty());

  irep_idt current_class=class_id;
  while(!current_class.empty())
  {
    const irep_idt &virtual_method_name=
      build_virtual_method_name(current_class, component_name);

    if(symbol_table.has_symbol(virtual_method_name))
    {
      return concrete_function_callt(current_class, component_name);
    }

    const class_hierarchyt::idst &parents=
      class_hierarchy.class_map[current_class].parents;

    if(parents.empty())
      break;
    current_class=parents.front();
  }

  return concrete_function_callt();
}

/// Build a method name as found in a GOTO symbol table equivalent to the name
/// of a concrete call of method component_method_name on class class_name
/// \param component_method_name: The name of the function
/// \param class_name: The class the implementation would be found on.
/// \return A name for looking up in the symbol table for classes `class_name`'s
///   implementation of `component_name`
irep_idt resolve_concrete_function_callt::build_virtual_method_name(
  const irep_idt &class_name, const irep_idt &component_method_name)
{
  // Verify the parameters are called in the correct order.
  PRECONDITION(id2string(class_name).find("::")!=std::string::npos);
  PRECONDITION(id2string(component_method_name).find("(")!=std::string::npos);
  return id2string(class_name)+'.'+id2string(component_method_name);
}

/// Get the full name of this function
/// \return The symbol name for this function call
irep_idt resolve_concrete_function_callt::concrete_function_callt::
  get_virtual_method_name() const
{
  return resolve_concrete_function_callt::build_virtual_method_name(
    class_identifier, function_identifier);
}

/// Use to check if this concrete_function_callt has been fully constructed.
/// \return True if this represents a real concrete function call
bool resolve_concrete_function_callt::concrete_function_callt::is_valid() const
{
  return !class_identifier.empty();
}
