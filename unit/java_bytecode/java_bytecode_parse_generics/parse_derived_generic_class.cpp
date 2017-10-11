/*******************************************************************\

 Module: Unit tests for parsing generic classes

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

#include <testing-utils/catch.hpp>

#include <istream>
#include <memory>

#include <util/config.h>
#include <util/language.h>
#include <util/message.h>
#include <java_bytecode/java_bytecode_language.h>
#include <iostream>
#include <testing-utils/load_java_class.h>

SCENARIO(
  "java_bytecode_parse_derived_generic_class",
  "[core][java_bytecode][java_bytecode_parse_generics]")
{
  const symbol_tablet &new_symbol_table=
    load_java_class(
      "DerivedGeneric",
      "./java_bytecode/java_bytecode_parse_generics");

  THEN("There should be a symbol for the DerivedGenreic class")
  {
    std::string class_prefix="java::DerivedGeneric";
    REQUIRE(new_symbol_table.has_symbol(class_prefix));

    const symbolt &derived_symbol=new_symbol_table.lookup_ref(class_prefix);
    REQUIRE(derived_symbol.is_type);
    const typet &derived_type=derived_symbol.type;
    REQUIRE(derived_type.id()==ID_struct);
    const class_typet &class_type=to_class_type(derived_type);
    REQUIRE(class_type.is_class());
    REQUIRE_FALSE(class_type.get_bool(ID_incomplete_class));

    // TODO(tkiley): Currently we do not support extracting information
    // about the base classes generic information.
  }
}
