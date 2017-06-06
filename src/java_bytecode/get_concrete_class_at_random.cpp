// Copyright 2016-2017 DiffBlue Limited. All Rights Reserved.

/// \file
/// Java Bytecode Language Conversion

#include "get_concrete_class_at_random.h"

#include <algorithm>
#include <random>

#include <util/namespace.h>
#include <util/std_types.h>
#include <util/symbol_table.h>

#include <goto-programs/class_hierarchy.h>

/// Get type the pointer is pointing to, replacing it with a concrete
/// implementation when it is abstract.
/// \param `pointer_type`: The type of the pointer
/// \return The subtype of the pointer. If this is an abstract class then we
///   will randomly select a concrete child class.
typet get_concrete_class_at_randomt::operator()(
  const pointer_typet &pointer_type)
{
  const typet &subtype=ns.follow(pointer_type.subtype());
  if(subtype.id()==ID_struct)
  {
    const class_typet &class_type=to_class_type(subtype);

    if(class_type.is_class() && class_type.is_abstract())
    {
      return select_concrete_type(class_type);
    }
  }

  // Here we must return the original subtype as if it is a pointer to a java
  // array java_object_factoryt::gen_nondet_array_init relies on the subtype
  // being a ID_symbol, here we have followed the symbol to its resolution.
  // Perhaps java_object_factoryt::gen_nondet_array_init should support this
  // Perhaps select_concrete_type when it fails should also ensure it doesn't
  // modify the subtype (currently if no concrete implementations we'd do the same
  // - swap a symbol to a struct
  return pointer_type.subtype();
}

/// Randomly select a concrete sub-class of an abstract class or interface This
/// can be then used when analyzing the function.
/// \param `abstract_type`: an class type that is abstract (i.e. either an
/// interface or a abstract class).
/// \return A class_typet that the GOTO code should instantiate to fill this
///   type. This will be a concrete type unless no concrete types are found that
///   inherit from the abstract_type. `
class_typet get_concrete_class_at_randomt::select_concrete_type(
  const class_typet &abstract_type)
{
  if(!abstract_type.is_abstract())
    throw std::invalid_argument("abstract_type");

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


  if(concrete_childen.size()>0)
  {
    //Will be used to obtain a seed for the random number engine
    std::random_device rd;
    //Standard mersenne_twister_engine seeded with rd()
    std::mt19937 gen(rd());
    std::uniform_int_distribution<unsigned long> class_selector(
      0, concrete_childen.size()-1);
    unsigned long selected_class_index=class_selector(gen);
    const symbolt &type_symbol=
      symbol_table.lookup(concrete_childen[selected_class_index]);
    const class_typet &child_type=to_class_type(type_symbol.type);
    return child_type;
  }
  else
  {
    // else no children in the symbol table - here the best we can do is
    // mock the interface/abstract object
    return abstract_type;
  }
}
