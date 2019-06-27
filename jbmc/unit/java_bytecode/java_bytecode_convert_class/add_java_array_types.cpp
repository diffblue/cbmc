// Copyright 2016-2019 Diffblue Limited. All Rights Reserved.

#include <java_bytecode/java_bytecode_convert_class.h>
#include <testing-utils/require_symbol.h>
#include <testing-utils/use_catch.h>
#include <util/symbol_table.h>

TEST_CASE("Add array types", "[core]")
{
  symbol_tablet symbol_table;
  add_java_array_types(symbol_table);

  const std::vector<std::string> array_types = {"byte",
                                                "short",
                                                "int",
                                                "long",
                                                "char",
                                                "float",
                                                "double",
                                                "boolean",
                                                "reference"};

  // type, clone method, local variables in clone method
  size_t symbols_per_array = 1 + 1 + 3;
  REQUIRE(
    symbol_table.symbols.size() == array_types.size() * symbols_per_array);

  SECTION("Array class symbol exists")
  {
    for(const std::string array_type : array_types)
    {
      const auto array_type_symbol = require_symbol::require_symbol_exists(
        symbol_table, "java::array[" + array_type + "]");
      REQUIRE(array_type_symbol.is_type);
      REQUIRE(can_cast_type<struct_typet>(array_type_symbol.type));
      REQUIRE(is_valid_java_array(to_struct_type(array_type_symbol.type)));
    }
  }
  SECTION("Array clone method exists")
  {
    for(const std::string array_type : array_types)
    {
      const auto array_type_symbol = require_symbol::require_symbol_exists(
        symbol_table,
        "java::array[" + array_type + "].clone:()Ljava/lang/Object;");
      REQUIRE(array_type_symbol.is_function());
    }
  }
}
