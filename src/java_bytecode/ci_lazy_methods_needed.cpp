/*******************************************************************\

Module: Context-insensitive lazy methods container

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

/// \file
/// Context-insensitive lazy methods container

#include "ci_lazy_methods.h"

#include <string>

/// Notes `method_symbol_name` is referenced from some reachable function, and
/// should therefore be elaborated.
/// \par parameters: `method_symbol_name`: method name; must exist in symbol
///   table.
void ci_lazy_methods_neededt::add_needed_method(
  const irep_idt &method_symbol_name)
{
  needed_methods.push_back(method_symbol_name);
}

/// Notes class `class_symbol_name` will be instantiated, or a static field
/// belonging to it will be accessed. Also notes that its static initializer is
/// therefore reachable.
/// \par parameters: `class_symbol_name`: class name; must exist in symbol
///   table.
/// \return Returns true if `class_symbol_name` is new (not seen before).
bool ci_lazy_methods_neededt::add_needed_class(
  const irep_idt &class_symbol_name)
{
  if(!needed_classes.insert(class_symbol_name).second)
    return false;

  const std::string &class_name_string = id2string(class_symbol_name);
  const irep_idt cprover_validate(
    class_name_string + ".cproverNondetInitialize:()V");
  if(symbol_table.symbols.count(cprover_validate))
    add_needed_method(cprover_validate);

  return true;
}
