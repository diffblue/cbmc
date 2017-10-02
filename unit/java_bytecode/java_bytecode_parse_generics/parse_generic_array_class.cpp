/*******************************************************************\

 Module: Unit tests for parsing generic classes

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

#include <catch.hpp>

#include <util/config.h>
#include <util/cmdline.h>
#include <util/language.h>
#include <util/prefix.h>

#include <java_bytecode/java_bytecode_language.h>
#include <src/java_bytecode/load_java_class.h>

#include <iostream>
#include <util/namespace.h>

SCENARIO(
  "java_bytecode_parse_generic_array_class",
  "[core][java_bytecode][java_bytecode_parse_generics]")
{
  const symbol_tablet &new_symbol_table=
    load_java_class("GenericArray", ""
      "./java_bytecode/java_bytecode_parse_generics");

  std::string class_prefix="java::GenericArray";

  REQUIRE(new_symbol_table.has_symbol(class_prefix));

  const struct_typet &type=to_struct_type(
    new_symbol_table.lookup(class_prefix)
      .type);

  THEN("There should be a component with name t")
  {
    REQUIRE(type.has_component("t"));
  }

  const pointer_typet &t_component=to_pointer_type(
    type.get_component("t")
      .type());
  const symbol_typet &subtype=to_symbol_type(t_component.subtype());

  THEN("The t component is a valid java array")
  {
    const struct_typet &subtype_type=to_struct_type(
      new_symbol_table.lookup(subtype.get_identifier())
        .type);
    REQUIRE(is_valid_java_array(subtype_type));
  }

  THEN("The elements of the t component have the parametric type T")
  {
    const typet &element=static_cast<const typet &>(subtype.find(
      ID_C_element_type));
    REQUIRE(is_java_generic_parameter(element));

    REQUIRE(
      to_java_generic_parameter(element).type_variable().get_identifier()==
      "java::GenericArray::T");
  }
}
