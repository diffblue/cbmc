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
  INVARIANT(
    is_java_generic_class_type(pointer_subtype),
    "Generic references type must be a generic class");

  const java_generic_class_typet &generic_class_definition =
    to_java_generic_class_type(to_java_class_type(pointer_subtype));

  const irep_idt new_tag =
    build_generic_tag(existing_generic_type, generic_class_definition);
  struct_union_typet::componentst replacement_components =
    generic_class_definition.components();

  // Small auxiliary function, to perform the inplace
  // modification of the generic fields.
  auto replace_type_for_generic_field =
    [&](struct_union_typet::componentt &component) {

      component.type() = substitute_type(
        component.type(), generic_class_definition, existing_generic_type);

      return component;
    };

  std::size_t pre_modification_size=to_java_class_type(
    ns.follow(existing_generic_type.subtype())).components().size();

  std::for_each(
    replacement_components.begin(),
    replacement_components.end(),
    replace_type_for_generic_field);

  std::size_t after_modification_size =
    generic_class_definition.components().size();

  INVARIANT(
    pre_modification_size==after_modification_size,
    "All components in the original class should be in the new class");

  const java_class_typet &new_java_class = construct_specialised_generic_type(
    generic_class_definition, new_tag, replacement_components);
  const type_symbolt &class_symbol =
    build_symbol_from_specialised_class(new_java_class);

  std::pair<symbolt &, bool> res = symbol_table.insert(std::move(class_symbol));
  if(!res.second)
  {
    messaget message(message_handler);
    message.warning() << "stub class symbol " << class_symbol.name
                      << " already exists" << messaget::eom;
  }

  const auto expected_symbol="java::"+id2string(new_tag);
  auto symbol=symbol_table.lookup(expected_symbol);
  INVARIANT(symbol, "New class not created");
  return *symbol;
}

/// For a given type, if the type contains a Java generic parameter, we look
/// that parameter up and return the relevant type. This works recursively on
/// arrays so that T [] is converted to RelevantType [].
/// \param parameter_type: The type under consideration
/// \param generic_class: The generic class that the \p parameter_type
/// belongs to (e.g. the type of a component of the class). This is used to
/// look up the mapping from name of generic parameter to its index.
/// \param generic_reference: The instantiated version of the generic class
/// used to look up the instantiated type. This is expected to be fully
/// instantiated.
/// \return A newly constructed type with generic parameters replaced, or if
/// there are none to replace, the original type.
typet generate_java_generic_typet::substitute_type(
  const typet &parameter_type,
  const java_generic_class_typet &generic_class,
  const java_generic_typet &generic_reference) const
{
  if(is_java_generic_parameter(parameter_type))
  {
    auto component_identifier = to_java_generic_parameter(parameter_type)
                                  .type_variable()
                                  .get_identifier();

    optionalt<size_t> results =
      java_generics_get_index_for_subtype(generic_class, component_identifier);

    INVARIANT(results.has_value(), "generic component type not found");
    return generic_reference.generic_type_variables()[*results];
  }
  else if(parameter_type.id() == ID_pointer)
  {
    if(is_java_generic_type(parameter_type))
    {
      const java_generic_typet &generic_type =
        to_java_generic_type(parameter_type);

      java_generic_typet::generic_type_variablest replaced_type_variables;

      // Swap each parameter
      std::transform(
        generic_type.generic_type_variables().begin(),
        generic_type.generic_type_variables().end(),
        std::back_inserter(replaced_type_variables),
        [&](const java_generic_parametert &generic_param)
          -> java_generic_parametert {
            const typet &replacement_type =
              substitute_type(generic_param, generic_class, generic_reference);

            // This code will be simplified when references aren't considered to
            // be generic parameters
            if(is_java_generic_parameter(replacement_type))
            {
              return to_java_generic_parameter(replacement_type);
            }
            else
            {
              INVARIANT(
                is_reference(replacement_type),
                "All generic parameters should be references");
              return java_generic_inst_parametert(
                to_symbol_type(replacement_type.subtype()));
            }
          });

      java_generic_typet new_type = generic_type;
      new_type.generic_type_variables() = replaced_type_variables;
      return new_type;
    }
    else if(parameter_type.subtype().id() == ID_symbol)
    {
      const symbol_typet &array_subtype =
        to_symbol_type(parameter_type.subtype());
      if(is_java_array_tag(array_subtype.get_identifier()))
      {
        const typet &array_element_type =
          java_array_element_type(array_subtype);

        const typet &new_array_type =
          substitute_type(array_element_type, generic_class, generic_reference);

        typet replacement_array_type = java_array_type('a');
        replacement_array_type.subtype().set(ID_C_element_type, new_array_type);
        return replacement_array_type;
      }
    }
  }
  return parameter_type;
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
    const irep_idt &id(id2string(param.subtype().get(ID_identifier)));
    new_tag_buffer << id2string(id);
    if(is_java_array_tag(id))
    {
      const typet &element_type =
        java_array_element_type(to_symbol_type(param.subtype()));

      // If this is an array of references then we will specialize its
      // identifier using the type of the objects in the array. Else, there can
      // be a problem with the same symbols for different instantiations using
      // arrays with different types.
      if(element_type.id() == ID_pointer)
      {
        const symbol_typet element_symbol =
          to_symbol_type(element_type.subtype());
        new_tag_buffer << "of_" << id2string(element_symbol.get_identifier());
      }
    }
  }

  new_tag_buffer << ">";

  return new_tag_buffer.str();
}

/// Build the specalised version of the specific class, with the specified
/// parameters and name.
/// \param generic_class_definition: The generic class we are specialising
/// \param new_tag: The new name for the class (like Generic<java::Float>)
/// \param new_components: The specialised components
/// \return The newly constructed class.
java_class_typet
generate_java_generic_typet::construct_specialised_generic_type(
  const java_generic_class_typet &generic_class_definition,
  const irep_idt &new_tag,
  const struct_typet::componentst &new_components) const
{
  java_class_typet specialised_class = generic_class_definition;
  // We are specialising the logic - so we don't want to be marked as generic
  specialised_class.set(ID_C_java_generics_class_type, false);
  specialised_class.set(ID_name, "java::" + id2string(new_tag));
  specialised_class.set(ID_base_name, new_tag);
  specialised_class.components() = new_components;
  return specialised_class;
}

/// Construct the symbol to be moved into the symbol table
/// \param specialised_class: The newly constructed specialised class
/// \return The symbol to add to the symbol table
type_symbolt generate_java_generic_typet::build_symbol_from_specialised_class(
  const java_class_typet &specialised_class) const
{
  type_symbolt new_symbol(specialised_class);
  new_symbol.base_name = specialised_class.get(ID_base_name);
  new_symbol.pretty_name = specialised_class.get(ID_base_name);
  new_symbol.name = specialised_class.get(ID_name);
  new_symbol.mode = ID_java;
  return new_symbol;
}
