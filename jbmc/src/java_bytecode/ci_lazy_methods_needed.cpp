/*******************************************************************\

Module: Context-insensitive lazy methods container

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

/// \file
/// Context-insensitive lazy methods container

#include "ci_lazy_methods.h"
#include "java_static_initializers.h"

#include <java_bytecode/select_pointer_type.h>
#include <string>
#include <util/namespace.h>
#include <util/std_types.h>

/// Notes `method_symbol_name` is referenced from some reachable function, and
/// should therefore be elaborated.
/// \param method_symbol_name: method name; must exist in symbol table.
void ci_lazy_methods_neededt::add_needed_method(
  const irep_idt &method_symbol_name)
{
  callable_methods.insert(method_symbol_name);
}

/// For a given class id, note that its static initializer is needed.
/// This applies the same logic to the given class that
/// `java_bytecode_convert_methodt::get_clinit_call` applies e.g. to classes
/// whose constructor we call in a method body. This duplication is unavoidable
/// because ci_lazy_methods essentially has to go through the same logic as
/// __CPROVER_start in its initial setup, and because return values of opaque
/// methods need to be considered in ci_lazy_methods too.
/// \param class_id: The given class id
/// \param symbol_table: Used to look up occurrences of static initializers
void ci_lazy_methods_neededt::add_clinit_call(
  const irep_idt &class_id,
  const symbol_tablet &symbol_table)
{
  const irep_idt &clinit_wrapper = clinit_wrapper_name(class_id);
  if(symbol_table.symbols.count(clinit_wrapper))
    add_needed_method(clinit_wrapper);
}

/// Notes class `class_symbol_name` will be instantiated, or a static field
/// belonging to it will be accessed. Also notes that its static initializer is
/// therefore reachable.
/// \param class_symbol_name: class name; must exist in symbol table.
/// \return Returns true if `class_symbol_name` is new (not seen before).
bool ci_lazy_methods_neededt::add_needed_class(
  const irep_idt &class_symbol_name)
{
  if(!instantiated_classes.insert(class_symbol_name).second)
    return false;

  const std::string &class_name_string = id2string(class_symbol_name);
  const irep_idt cprover_validate(
    class_name_string + ".cproverNondetInitialize:()V");
  if(symbol_table.symbols.count(cprover_validate))
    add_needed_method(cprover_validate);

  // Special case for enums. We may want to generalise this, the comment in
  // \ref java_object_factoryt::gen_nondet_pointer_init (TG-4689).
  namespacet ns(symbol_table);
  const auto &class_type =
    to_java_class_type(ns.lookup(class_symbol_name).type);
  if(class_type.get_base("java::java.lang.Enum"))
    add_clinit_call(class_symbol_name, symbol_table);

  return true;
}

/// Add to the needed classes all classes specified, the replacement type if it
/// will be replaced, and all fields it contains.
/// \param pointer_type: The type to add
void ci_lazy_methods_neededt::add_all_needed_classes(
  const pointer_typet &pointer_type)
{
  namespacet ns{symbol_table};

  initialize_instantiated_classes_from_pointer(pointer_type, ns);

  // TODO we should be passing here a map that maps generic parameters
  // to concrete types in the current context TG-2664
  const pointer_typet &subbed_pointer_type =
    pointer_type_selector.convert_pointer_type(pointer_type, {}, ns);

  if(subbed_pointer_type != pointer_type)
  {
    initialize_instantiated_classes_from_pointer(subbed_pointer_type, ns);
  }
}

/// Build up list of methods for types for a specific pointer type. See
/// `add_all_needed_classes` for more details.
/// \param pointer_type: The type to gather methods for.
/// \param ns: global namespace
void ci_lazy_methods_neededt::initialize_instantiated_classes_from_pointer(
  const pointer_typet &pointer_type,
  const namespacet &ns)
{
  const symbol_typet &class_type = to_symbol_type(pointer_type.subtype());
  const auto &param_classid = class_type.get_identifier();

  // Note here: different arrays may have different element types, so we should
  // explore again even if we've seen this classid before in the array case.
  if(add_needed_class(param_classid) || is_java_array_tag(param_classid))
  {
    gather_field_types(pointer_type.subtype(), ns);
  }

  if(is_java_generic_type(pointer_type))
  {
    // Assume if this is a generic like X<A, B, C>, then any concrete parameters
    // will at some point be instantiated.
    const auto &generic_args =
      to_java_generic_type(pointer_type).generic_type_arguments();
    for(const auto &generic_arg : generic_args)
    {
      if(!is_java_generic_parameter(generic_arg))
      {
        initialize_instantiated_classes_from_pointer(generic_arg, ns);
      }
    }
  }
}

/// For a given type, gather all fields referenced by that type
/// \param class_type: root of class tree to search
/// \param ns: global namespaces.
void ci_lazy_methods_neededt::gather_field_types(
  const typet &class_type,
  const namespacet &ns)
{
  const auto &underlying_type = to_struct_type(ns.follow(class_type));
  if(is_java_array_tag(underlying_type.get_tag()))
  {
    // If class_type is not a symbol this may be a reference array,
    // but we can't tell what type.
    if(class_type.id() == ID_symbol_type)
    {
      const typet &element_type =
        java_array_element_type(to_symbol_type(class_type));
      if(element_type.id() == ID_pointer)
      {
        // This is a reference array -- mark its element type available.
        add_all_needed_classes(to_pointer_type(element_type));
      }
    }
  }
  else
  {
    for(const auto &field : underlying_type.components())
    {
      if(field.type().id() == ID_struct || field.type().id() == ID_symbol_type)
        gather_field_types(field.type(), ns);
      else if(field.type().id() == ID_pointer)
      {
        if(field.type().subtype().id() == ID_symbol_type)
        {
          add_all_needed_classes(to_pointer_type(field.type()));
        }
        else
        {
          // If raw structs were possible this would lead to missed
          // dependencies, as both array element and specialised generic type
          // information cannot be obtained in this case.
          // We should therefore only be skipping pointers such as the uint16t*
          // in our internal String representation.
          INVARIANT(
            field.type().subtype().id() != ID_struct,
            "struct types should be referred to by symbol at this stage");
        }
      }
    }
  }
}
