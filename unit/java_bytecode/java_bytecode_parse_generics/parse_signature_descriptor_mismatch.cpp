/*******************************************************************\

 Module: Unit tests for parsing generic classes

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

#include <testing-utils/catch.hpp>

#include <memory>

#include <util/config.h>
#include <util/language.h>
#include <java_bytecode/java_bytecode_language.h>
#include <iostream>
#include <testing-utils/load_java_class.h>
#include <testing-utils/require_symbol.h>

SCENARIO(
  "java_bytecode_parse_signature_descriptor_mismatch",
  "[core][java_bytecode][java_bytecode_parse_generics]")
{
  const symbol_tablet &new_symbol_table=
    load_java_class(
      "Outer",
      "./java_bytecode/java_bytecode_parse_generics");

  const std::string class_prefix="java::Outer";
  REQUIRE(new_symbol_table.has_symbol(class_prefix));

  const std::string inner_prefix=class_prefix+"$Inner";
  THEN("There is a (complete) symbol for the inner class Inner")
  {
    REQUIRE(new_symbol_table.has_symbol(inner_prefix));

    const symbolt &inner_symbol=new_symbol_table.lookup_ref(inner_prefix);
    const class_typet &inner_class_type=
      require_symbol::require_complete_class(inner_symbol);
  }

  THEN("There is a symbol for the constructor of the inner class with correct"
         " descriptor")
  {
    const std::string func_name=".<init>";
    const std::string func_descriptor=":(LOuter;LAbstractGenericClass;)V";
    const std::string process_func_name=
      inner_prefix+func_name+func_descriptor;
    REQUIRE(new_symbol_table.has_symbol(process_func_name));

    const code_typet func_code=
      to_code_type(new_symbol_table.lookup_ref(process_func_name).type);
    REQUIRE(func_code.parameters().size()==3);
  }

  const std::string inner_enum_prefix=class_prefix+"$InnerEnum";
  THEN("There is a (complete) symbol for the inner enum InnerEnum")
  {
    REQUIRE(new_symbol_table.has_symbol(inner_enum_prefix));

    const symbolt &inner_enum_symbol=
      new_symbol_table.lookup_ref(inner_enum_prefix);
    const class_typet &inner_enum_class_type=
      require_symbol::require_complete_class(inner_enum_symbol);
  }

  THEN("There is a symbol for the constructor of the inner enum with correct"
         " number of parameters")
  {
    const std::string func_name=".<init>";
    const std::string func_descriptor=":(Ljava/lang/String;I)V";
    const std::string process_func_name=
      inner_enum_prefix+func_name+func_descriptor;
    REQUIRE(new_symbol_table.has_symbol(process_func_name));

    const code_typet func_code=
      to_code_type(new_symbol_table.lookup_ref(process_func_name).type);
    REQUIRE(func_code.parameters().size()==3);
  }
}
