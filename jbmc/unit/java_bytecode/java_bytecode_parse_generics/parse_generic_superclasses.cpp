/*******************************************************************\

 Module: Unit tests for parsing classes with generic superclasses or interfaces
         with unsupported signatures, falling back to using the raw type
         descriptors

 Author: Diffblue Ltd.

\*******************************************************************/

#include <testing-utils/catch.hpp>
#include <java-testing-utils/load_java_class.h>
#include <java-testing-utils/require_type.h>

SCENARIO(
  "parse generic superclass signature",
  "[core][java_byte code[java_bytecode_parse_generics]]")
{
  const symbol_tablet &new_symbol_table = load_java_class(
    "GenericBounds", "./java_bytecode/java_bytecode_parse_generics");

  const std::string base_generic = "java::Generic";
  const irep_idt base_generic_interface = "java::InterfaceGeneric";

  const std::string load_class("java::GenericBounds");
  THEN(
    "these fields have a non-generic base class / interface  as their real "
    "generic signature is unsupported at the moment")
  {
    // once bounds in generic signatures are supported, this test must be
    // changed to check for the correct generic types, TODO(mgudemann),
    // cf. TG-1286, TG-675
    {
      const symbolt &upper_symbol =
        new_symbol_table.lookup_ref("java::GenericBoundsUpper");
      const java_class_typet &upper_type =
        to_java_class_type(upper_symbol.type);
      REQUIRE(upper_type.bases().size() == 1);
      const struct_tag_typet base_type = require_type::require_struct_tag(
        upper_type.bases().at(0).type(), base_generic);
      REQUIRE_FALSE(is_java_generic_struct_tag_type(base_type));
    }
    {
      const symbolt &lower_symbol =
        new_symbol_table.lookup_ref("java::GenericBoundsLower");
      const java_class_typet &lower_type =
        to_java_class_type(lower_symbol.type);
      REQUIRE(lower_type.bases().size() == 1);
      const struct_tag_typet base_type = require_type::require_struct_tag(
        lower_type.bases().at(0).type(), base_generic);
      REQUIRE_FALSE(is_java_generic_struct_tag_type(base_type));
    }
    {
      const symbolt &interface_symbol =
        new_symbol_table.lookup_ref("java::GenericInterface");
      const java_class_typet &interface_type =
        to_java_class_type(interface_symbol.type);
      REQUIRE(interface_type.bases().size() == 2);
      const struct_tag_typet base_type = require_type::require_struct_tag(
        interface_type.bases().at(1).type(), base_generic_interface);
      REQUIRE_FALSE(is_java_generic_struct_tag_type(base_type));
    }
  }
}
