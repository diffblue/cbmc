/*******************************************************************\

 Module: Generate Java Generic Type - Instantiate a generic class with
         concrete type information.

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/
#include "generate_java_generic_type.h"
#include <util/namespace.h>
#include <java_bytecode/java_types.h>
#include <java_bytecode/java_utils.h>


generate_java_generic_typet::generate_java_generic_typet(
  message_handlert &message_handler):
    message_handler(message_handler)
{}

/// Generate a concrete instantiation of a generic type.
/// \param existing_generic_type The type to be concretised
/// \param symbol_table The symbol table that the concrete type will be
/// inserted into.
/// \return The symbol as it was retrieved from the symbol table after
/// it has been inserted into.
symbolt generate_java_generic_typet::operator()(
  const java_generic_typet &existing_generic_type,
  symbol_tablet &symbol_table) const
{
  namespacet ns(symbol_table);

  const typet &pointer_subtype=ns.follow(existing_generic_type.subtype());

  INVARIANT(
    pointer_subtype.id()==ID_struct, "Only pointers to classes in java");

  const java_class_typet &replacement_type=
    to_java_class_type(pointer_subtype);
  const irep_idt new_tag=build_generic_tag(
    existing_generic_type, replacement_type);
  struct_union_typet::componentst replacement_components=
    replacement_type.components();

  // Small auxiliary function, to perform the inplace
  // modification of the generic fields.
  auto replace_type_for_generic_field=
    [&](struct_union_typet::componentt &component)
    {
      if(is_java_generic_parameter(component.type()))
      {
        auto replacement_type_param=
          to_java_generics_class_type(replacement_type);

        auto component_identifier=
          to_java_generic_parameter(component.type()).type_variable()
            .get_identifier();

        optionalt<size_t> results=java_generics_get_index_for_subtype(
          replacement_type_param, component_identifier);

        INVARIANT(
          results.has_value(),
          "generic component type not found");

        if(results)
        {
          component.type()=
            existing_generic_type.generic_type_variables()[*results];
        }
      }
      return component;
    };

  std::size_t pre_modification_size=to_java_class_type(
    ns.follow(existing_generic_type.subtype())).components().size();

  std::for_each(
    replacement_components.begin(),
    replacement_components.end(),
    replace_type_for_generic_field);

  std::size_t after_modification_size=
    replacement_type.components().size();

  INVARIANT(
    pre_modification_size==after_modification_size,
    "All components in the original class should be in the new class");

  const auto expected_symbol="java::"+id2string(new_tag);

  generate_class_stub(
    new_tag,
    symbol_table,
    message_handler,
    replacement_components);
  auto symbol=symbol_table.lookup(expected_symbol);
  INVARIANT(symbol, "New class not created");
  return *symbol;
}

/// Build a unique tag for the generic to be instantiated.
/// \param existing_generic_type The type we want to concretise
/// \param original_class
/// \return A tag for the new generic we want a unique tag for.
irep_idt generate_java_generic_typet::build_generic_tag(
  const java_generic_typet &existing_generic_type,
  const java_class_typet &original_class) const
{
  std::ostringstream new_tag_buffer;
  new_tag_buffer << original_class.get_tag();
  new_tag_buffer << "<";
  bool first=true;
  for(const typet &param : existing_generic_type.generic_type_variables())
  {
    if(!first)
      new_tag_buffer << ",";
    first=false;

    INVARIANT(
      is_java_generic_inst_parameter(param),
      "Only create full concretized generic types");
    new_tag_buffer << param.subtype().get(ID_identifier);
  }

  new_tag_buffer << ">";

  return new_tag_buffer.str();
}


/// Activate the generic instantiation code.
/// \param message_handler
/// \param symbol_table The symbol table so far.
void
instantiate_generics(
  message_handlert &message_handler,
  symbol_tablet &symbol_table)
{
  generate_java_generic_typet instantiate_generic_type(message_handler);
  // check out the symbols in the symbol table at this point to see if we
  // have a a generic type in.
  for(const auto &symbol : symbol_table.symbols)
  {
    if(symbol.second.type.id()==ID_struct)
    {
      auto symbol_struct=to_struct_type(symbol.second.type);
      auto &components=symbol_struct.components();

      for(const auto &component : components)
      {
        if(is_java_generic_type(component.type()))
        {
          const auto &type_vars=to_java_generic_type(component.type()).
            generic_type_variables();

          // Before we can instantiate a generic component, we need
          // its type variables to be instantiated parameters
          if(all_of(type_vars.cbegin(), type_vars.cend(),
                    [](const typet &type)
                    {
                      return is_java_generic_inst_parameter(type);
                    }))
          {
            instantiate_generic_type(
              to_java_generic_type(component.type()), symbol_table);
          }
        }
      }
    }
  }
}
