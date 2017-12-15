/*******************************************************************\

 Module: Generate Java Generic Type - Instantiate a generic class with
         concrete type information.

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

#include <iterator>

#include "generate_java_generic_type.h"
#include "generic_arguments_name_builder.h"
#include <util/namespace.h>
#include <java_bytecode/java_types.h>
#include <java_bytecode/java_utils.h>

generate_java_generic_typet::generate_java_generic_typet(
  message_handlert &message_handler):
    message_handler(message_handler)
{}

/// Small auxiliary function, to print a single generic argument name.
/// \param argument argument type
/// \return printed name of the argument
static std::string argument_name_printer(const reference_typet &argument)
{
  const irep_idt &id(id2string(argument.subtype().get(ID_identifier)));
  if(is_java_array_tag(id))
  {
    std::string name = pretty_print_java_type(id2string(id));
    const typet &element_type =
      java_array_element_type(to_symbol_type(argument.subtype()));

    // If this is an array of references then we will specialize its
    // identifier using the type of the objects in the array. Else, there
    // can be a problem with the same symbols for different instantiations
    // using arrays with different types.
    if(element_type.id() == ID_pointer)
    {
      const symbol_typet element_symbol =
        to_symbol_type(element_type.subtype());
      name.append("of_" + id2string(element_symbol.get_identifier()));
    }
    return name;
  }
  else
  {
    return id2string(id);
  }
}

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
    is_java_generic_class_type(pointer_subtype) ||
      is_java_implicitly_generic_class_type(pointer_subtype),
    "Generic references type must be a generic class");

  const java_class_typet &class_definition =
    to_java_class_type(pointer_subtype);

  const std::string generic_name = build_generic_name(
    existing_generic_type, class_definition, argument_name_printer);
  struct_union_typet::componentst replacement_components =
    class_definition.components();

  // Small auxiliary function, to perform the inplace
  // modification of the generic fields.
  auto replace_type_for_generic_field =
    [&](struct_union_typet::componentt &component) {

      component.type() = substitute_type(
        component.type(), class_definition, existing_generic_type);

      return component;
    };

  std::size_t pre_modification_size=to_java_class_type(
    ns.follow(existing_generic_type.subtype())).components().size();

  std::for_each(
    replacement_components.begin(),
    replacement_components.end(),
    replace_type_for_generic_field);

  std::size_t after_modification_size = class_definition.components().size();

  INVARIANT(
    pre_modification_size==after_modification_size,
    "All components in the original class should be in the new class");

  const java_specialized_generic_class_typet new_java_class{
    generic_name,
    class_definition,
    replacement_components,
    existing_generic_type.generic_type_arguments()};

  const type_symbolt &class_symbol =
    build_symbol_from_specialised_class(new_java_class);

  std::pair<symbolt &, bool> res = symbol_table.insert(std::move(class_symbol));
  if(!res.second)
  {
    messaget message(message_handler);
    message.warning() << "stub class symbol " << class_symbol.name
                      << " already exists" << messaget::eom;
  }

  const auto expected_symbol="java::"+id2string(generic_name);
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
  const java_class_typet &class_definition,
  const java_generic_typet &generic_reference) const
{
  if(is_java_generic_parameter(parameter_type))
  {
    auto component_identifier = to_java_generic_parameter(parameter_type)
                                  .type_variable()
                                  .get_identifier();

    // see if it is a generic parameter introduced by this class
    optionalt<size_t> results;
    if(is_java_generic_class_type(class_definition))
    {
      const java_generic_class_typet &generic_class =
        to_java_generic_class_type(class_definition);

      results = java_generics_get_index_for_subtype(
        generic_class.generic_types(), component_identifier);
    }
    // see if it is an implicit generic parameter introduced by an outer class
    if(!results.has_value())
    {
      INVARIANT(
        is_java_implicitly_generic_class_type(class_definition),
        "The parameter must either be a generic type or implicit generic type");
      const java_implicitly_generic_class_typet &implicitly_generic_class =
        to_java_implicitly_generic_class_type(class_definition);
      results = java_generics_get_index_for_subtype(
        implicitly_generic_class.implicit_generic_types(),
        component_identifier);
    }

    INVARIANT(results.has_value(), "generic component type not found");
    return generic_reference.generic_type_arguments()[*results];
  }
  else if(parameter_type.id() == ID_pointer)
  {
    if(is_java_generic_type(parameter_type))
    {
      const java_generic_typet &generic_type =
        to_java_generic_type(parameter_type);

      java_generic_typet::generic_type_argumentst replaced_type_variables;

      // Swap each parameter
      std::transform(
        generic_type.generic_type_arguments().begin(),
        generic_type.generic_type_arguments().end(),
        std::back_inserter(replaced_type_variables),
        [&](const reference_typet &generic_param) -> reference_typet
        {
          const typet &replacement_type =
            substitute_type(generic_param, class_definition, generic_reference);

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
            return to_reference_type(replacement_type);
          }
        });

      java_generic_typet new_type = generic_type;
      new_type.generic_type_arguments() = replaced_type_variables;
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

        const typet &new_array_type = substitute_type(
          array_element_type, class_definition, generic_reference);

        typet replacement_array_type = java_array_type('a');
        replacement_array_type.subtype().set(ID_C_element_type, new_array_type);
        return replacement_array_type;
      }
    }
  }
  return parameter_type;
}

/// Build a unique name for the generic to be instantiated.
/// Example: if \p existing_generic_type is a pointer to `Outer<T>.Inner`
/// (\p original_class) with parameter `T` being specialized with argument
/// `Integer`, then the function returns a string `Outer<\p
/// argument_name_printer(Integer)>$Inner`.
/// \param existing_generic_type The type we want to concretise
/// \param original_class The original class type for \p existing_generic_type
/// \param argument_name_printer A custom function to print names of individual
/// arguments (such as `Integer`, `Integer[]` for concise names or `java::java
/// .lang.Integer`, `array[reference]of_java::java.lang.Integer`)
/// \return A name for the new specialized generic class we want a unique name
/// for.
std::string generate_java_generic_typet::build_generic_name(
  const java_generic_typet &existing_generic_type,
  const java_class_typet &original_class,
  const generic_arguments_name_buildert::name_printert &argument_name_printer)
  const
{
  std::ostringstream generic_name_buffer;
  const std::string &original_class_name = original_class.get_tag().c_str();

  // gather together all implicit generic types and generic types
  std::vector<java_generic_parametert> generic_types;
  if(is_java_implicitly_generic_class_type(original_class))
  {
    const java_implicitly_generic_class_typet
      &implicitly_generic_original_class =
        to_java_implicitly_generic_class_type(original_class);
    generic_types.insert(
      generic_types.end(),
      implicitly_generic_original_class.implicit_generic_types().begin(),
      implicitly_generic_original_class.implicit_generic_types().end());
  }
  if(is_java_generic_class_type(original_class))
  {
    const java_generic_class_typet &generic_original_class =
      to_java_generic_class_type(original_class);
    generic_types.insert(
      generic_types.end(),
      generic_original_class.generic_types().begin(),
      generic_original_class.generic_types().end());
  }

  INVARIANT(
    generic_types.size() ==
      existing_generic_type.generic_type_arguments().size(),
    "All generic types must be concretized");

  auto generic_type_p = generic_types.begin();
  std::string previous_class_name;
  std::string current_class_name;
  generic_arguments_name_buildert build_generic_arguments(
    argument_name_printer);

  // add generic arguments to each generic (outer) class
  for(const auto &generic_argument :
      existing_generic_type.generic_type_arguments())
  {
    previous_class_name = current_class_name;
    current_class_name = generic_type_p->get_parameter_class_name();

    // if the class names do not match, it means that the next generic
    // (outer) class is being handled
    if(current_class_name != previous_class_name)
    {
      // add the arguments of the previous generic class to the buffer
      // and reset the builder
      generic_name_buffer << build_generic_arguments.finalize();

      INVARIANT(
        has_prefix(current_class_name, previous_class_name),
        "Generic types are ordered from the outermost outer class inwards");

      // add the remaining part of the current generic class name to the buffer
      // example: if current_outer_class = A$B$C, previous_outer_class = A,
      // then substr of current, starting at the length of previous is $B$C
      generic_name_buffer << current_class_name.substr(
        previous_class_name.length());
    }

    // add an argument to the current generic class
    build_generic_arguments.add_argument(generic_argument);
    ++generic_type_p;
  }
  generic_name_buffer << build_generic_arguments.finalize();

  // add the remaining part of the original class name to the buffer
  generic_name_buffer << original_class_name.substr(
    current_class_name.length());

  return generic_name_buffer.str();
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
