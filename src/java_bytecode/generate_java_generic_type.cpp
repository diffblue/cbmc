/*******************************************************************\

 Module: MODULE NAME

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/
#include "generate_java_generic_type.h"
#include <util/namespace.h>
#include <java_bytecode/java_types.h>
#include <java_bytecode/java_utils.h>

#include <iostream>
#include <sstream>

generate_java_generic_typet::generate_java_generic_typet(
  symbol_tablet &symbol_table,
  message_handlert &message_handler):
    symbol_table(symbol_table),
    message_handler(message_handler)
{}

symbolt generate_java_generic_typet::operator()(
  const java_type_with_generic_typet &existing_generic_type)
{
  namespacet ns(symbol_table);

  const typet &pointer_subtype=ns.follow(existing_generic_type.subtype());

  INVARIANT(
    pointer_subtype.id()==ID_struct, "Only pointers to classes in java");

  const java_class_typet &java_class=to_java_class_type(pointer_subtype);

  java_class_typet replacement_type=java_class;
  replacement_type.components().clear();

  const irep_idt new_tag=build_generic_tag(existing_generic_type, java_class);
  replacement_type.set_tag(new_tag);

  for(const struct_union_typet::componentt &component_type :
    java_class.components())
  {
    if(!is_java_generic_type(component_type.type()))
    {
      replacement_type.components().push_back(component_type);
      continue;
    }

    INVARIANT(
      existing_generic_type.type_parameters.size()==1,
      "Must have a type parameter");

    struct_union_typet::componentt replacement_comp=component_type;
    replacement_comp.type()=existing_generic_type.type_parameters[0];

    replacement_type.components().push_back(replacement_comp);

  }
  INVARIANT(
    replacement_type.components().size()==java_class.components().size(),
    "All components in the original class should be in the new class");

  generate_class_stub(new_tag, symbol_table, message_handler);
  INVARIANT(symbol_table.has_symbol("java::"+id2string(new_tag)), "New class not created");
  return symbol_table.lookup("java::"+id2string(new_tag));
}

irep_idt generate_java_generic_typet::build_generic_tag(
  const java_type_with_generic_typet &existing_generic_type,
  const java_class_typet &original_class)
{
  std::ostringstream new_tag_buffer;
  new_tag_buffer << original_class.get_tag();
  new_tag_buffer << "<";
  bool first=true;
  for(const typet &param : existing_generic_type.type_parameters)
  {
    if(!first)
      new_tag_buffer << ", ";
    first=false;

    INVARIANT(
      is_java_inst_generic_type(param),
      "Only create full concretized generic types");
    new_tag_buffer << param.subtype().get(ID_identifier);
  }

  new_tag_buffer << ">";

  return new_tag_buffer.str();
}
