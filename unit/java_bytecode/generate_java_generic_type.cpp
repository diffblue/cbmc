/*******************************************************************\

 Module: Unit tests for generating new type with generic parameters
         substitued for concrete types

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

#include <catch.hpp>

#include <util/symbol_table.h>

#include <java_bytecode/generate_java_generic_type.h>
#include <java_bytecode/java_types.h>

SCENARIO(
  "generate_java_generic_type",
  "[CORE][java_bytecode][generate_java_generic_type")
{
  GIVEN("A generic java type and a concrete substitution")
  {
    symbol_tablet symbol_table;


    null_message_handlert message_handler;
    generate_java_generic_typet type_generator(symbol_table, message_handler);


    const reference_typet &boxed_integer_type=to_reference_type(java_type_from_string("Ljava/lang/Integer;"));

    java_type_with_generic_typet generic_type;
    generic_type.type_parameters.push_back(java_inst_generic_typet(boxed_integer_type));

    struct_typet base_class;
    base_class.components().push_back(struct_union_typet::componentt("a", java_generic_typet("T")));
    base_class.set_tag("UserClass");

    generic_type.subtype()=base_class;

    const symbolt &new_symbol=type_generator(generic_type);
    REQUIRE(new_symbol.is_type);



    REQUIRE(new_symbol.base_name=="UserClass<Integer>");
    REQUIRE(new_symbol.type.id()==ID_pointer);

  }
}
