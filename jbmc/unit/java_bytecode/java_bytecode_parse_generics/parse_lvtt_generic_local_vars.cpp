/*******************************************************************\

Module: Unit tests for parsing generic local variables from the LVTT

Author: Diffblue Ltd.

\*******************************************************************/

#include <java-testing-utils/load_java_class.h>
#include <java-testing-utils/require_type.h>
#include <testing-utils/use_catch.h>

SCENARIO(
  "parse_lvtt_generic_local_vars",
  "[core][java_bytecode][java_bytecode_parse_generics]")
{
  const symbol_tablet &new_symbol_table = load_java_class(
    "GenericLocalVar", "./java_bytecode/java_bytecode_parse_generics");

  const std::string var_name("java::GenericLocalVar.f:()V::1::l");
  REQUIRE(new_symbol_table.has_symbol(var_name));

  WHEN("Local variable has an entry in the LVTT")
  {
    THEN("The type should be generic and instantiated with Double")
    {
      const symbolt &var_symbol = new_symbol_table.lookup_ref(var_name);
      java_generic_typet local_var_type =
        require_type::require_java_generic_type(
          var_symbol.type,
          {{require_type::type_argument_kindt::Inst,
            "java::java.lang.Double"}});
    }
  }
}
