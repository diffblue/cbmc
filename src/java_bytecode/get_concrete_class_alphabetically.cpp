/*******************************************************************\

Module: Java Bytecode Language Conversion

Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

/// \file
/// Select a subclass of the provided type, picking the alphabetically first

#include "get_concrete_class_alphabetically.h"

#include <algorithm>

#include <util/invariant.h>
#include <util/namespace.h>
#include <util/std_types.h>
#include <util/symbol_table.h>

#include <goto-programs/class_hierarchy.h>

/// Get type the pointer is pointing to, replacing it with a concrete
/// implementation when it is abstract.
/// \param `pointer_type`: The type of the pointer
/// \return The subtype of the pointer. If this is an abstract class then we
///   will randomly select a concrete child class.
pointer_typet get_concrete_class_alphabeticallyt::operator()(
  const pointer_typet &pointer_type)
{
  const typet &subtype=ns.follow(pointer_type.subtype());
  INVARIANT(subtype.id()==ID_struct,
    "Can only find derived classes of class types");

  const class_typet &class_type=to_class_type(subtype);
  INVARIANT(class_type.is_class(),
    "Can only find derived classes of class types");

  const class_typet &selected_subtype=select_concrete_type(class_type);

  // If we've not selected a subtype (i.e. there aren't any) we should
  // return the original unmodified type
  if(selected_subtype==class_type)
  {
    return pointer_type;
  }

  // Recreate the pointer_type as it was before
  if(pointer_type.subtype().id()==ID_symbol)
  {
    INVARIANT(
      ns.get_symbol_table().has_symbol(selected_subtype.get(ID_name)),
      "Selected a type that wasn't in the symbol table");

    symbol_typet symbol_subtype(selected_subtype.get(ID_name));

    return pointer_typet(symbol_subtype);
  }
  else
  {
    return pointer_typet(selected_subtype);
  }
}

/// Select the alphabetically first concrete sub-class of an abstract class or
/// interface This can be then used when analyzing the function.
/// \param `abstract_type`: an class type that is abstract (i.e. either an
///   interface or a abstract class).
/// \return A class_typet that the GOTO code should instantiate to fill this
///   type. This will be a concrete type unless no concrete types are found that
///   inherit from the abstract_type. `
class_typet get_concrete_class_alphabeticallyt::select_concrete_type(
  const class_typet &abstract_type)
{
  const symbol_tablet &symbol_table=ns.get_symbol_table();
  // abstract class - we should find a derived class ideally to test with
  class_hierarchyt class_hierachy;
  class_hierachy(symbol_table);
  class_hierarchyt::idst child_ids=
    class_hierachy.get_children_trans(abstract_type.get_string(ID_name));

  // filter out abstract classes
  class_hierarchyt::idst concrete_childen;
  std::copy_if(
    child_ids.begin(),
    child_ids.end(),
    std::back_inserter(concrete_childen),
    [&] (const irep_idt &child_class_id)
    {
      const symbolt &type_symbol=symbol_table.lookup(child_class_id);
      const class_typet &child_type=to_class_type(type_symbol.type);
      return child_type.is_class() && !child_type.is_abstract();
    });


  if(!concrete_childen.empty())
  {
    // Alphabetize the list
    std::sort(
      concrete_childen.begin(),
      concrete_childen.end(),
      [](const irep_idt &a, const irep_idt &b)
      {
        return a.compare(b)<0;
      });

    const symbolt &type_symbol=
      symbol_table.lookup(concrete_childen.front());
    INVARIANT(
      type_symbol.type.id()==ID_struct,
      "Should always substitute a class type");

    const class_typet &child_type=to_class_type(type_symbol.type);
    INVARIANT(child_type.is_class(), "Should always substitute a class type");
    return child_type;
  }
  else
  {
    // else no children in the symbol table - here the best we can do is
    // mock the interface/abstract object
    return abstract_type;
  }
}
