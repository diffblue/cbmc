/*******************************************************************\

Module: Unit tests for parsing generic classes

Author: Diffblue Ltd.

\*******************************************************************/

#include <testing-utils/catch.hpp>
#include <java-testing-utils/load_java_class.h>
#include <java-testing-utils/require_type.h>

SCENARIO(
  "parse_signature_descriptor_mismatch",
  "[core][java_bytecode][java_bytecode_parse_generics]")
{
  const symbol_tablet &new_symbol_table = load_java_class(
    "SignatureDescriptorMismatch",
    "./java_bytecode/java_bytecode_parse_generics");

  const std::string class_prefix = "java::SignatureDescriptorMismatch";
  REQUIRE(new_symbol_table.has_symbol(class_prefix));

  const std::string inner_prefix = class_prefix + "$Inner";
  THEN("There is a (complete) symbol for the inner class Inner")
  {
    REQUIRE(new_symbol_table.has_symbol(inner_prefix));

    const symbolt &inner_symbol = new_symbol_table.lookup_ref(inner_prefix);
    const class_typet &inner_class_type =
      require_type::require_complete_java_implicitly_generic_class(
        inner_symbol.type);
  }

  THEN(
    "There is a symbol for the constructor of the class Inner with "
    "the correct number of parameters")
  {
    const std::string func_name = ".<init>";
    const std::string func_descriptor =
      ":(LSignatureDescriptorMismatch;LAbstractGeneric;)V";
    const std::string process_func_name =
      inner_prefix + func_name + func_descriptor;
    REQUIRE(new_symbol_table.has_symbol(process_func_name));

    const java_method_typet func_code =
      to_java_method_type(new_symbol_table.lookup_ref(process_func_name).type);
    REQUIRE(func_code.parameters().size() == 3);

    // TODO: for now, the parameters are not generic because we fall back to
    // descriptor due to mismatch; enable tests when fixed - issue TG-1309
    // java_method_typet::parametert param_parent=
    //  require_type::require_parameter(func_code,"arg1a");
    // REQUIRE(is_java_generic_type(param_parent.type()));
    // java_method_typet::parametert param_t=
    //  require_type::require_parameter(func_code,"t");
    // REQUIRE(is_java_generic_type(param_t.type()));
  }

  const std::string inner_enum_prefix = class_prefix + "$InnerEnum";
  THEN("There is a (complete) symbol for the inner enum InnerEnum")
  {
    REQUIRE(new_symbol_table.has_symbol(inner_enum_prefix));

    const symbolt &inner_enum_symbol =
      new_symbol_table.lookup_ref(inner_enum_prefix);
    require_type::require_complete_java_non_generic_class(
      inner_enum_symbol.type);
  }

  THEN(
    "There is a symbol for the constructor of the inner enum with the "
    "correct number of parameters")
  {
    const std::string func_name = ".<init>";
    const std::string func_descriptor = ":(Ljava/lang/String;I)V";
    const std::string process_func_name =
      inner_enum_prefix + func_name + func_descriptor;
    REQUIRE(new_symbol_table.has_symbol(process_func_name));

    const java_method_typet func_code =
      to_java_method_type(new_symbol_table.lookup_ref(process_func_name).type);
    REQUIRE(func_code.parameters().size() == 3);

    // TODO: for now, the parameters are not generic because we fall back to
    // descriptor due to mismatch; enable tests when fixed - issue TG-1309
    // java_method_typet::parametert param_parent=
    //  require_type::require_parameter(func_code,"arg1a");
    // REQUIRE(is_java_generic_type(param_parent.type()));
    // java_method_typet::parametert param_t=
    //  require_type::require_parameter(func_code,"arg2i");
    // REQUIRE(is_java_generic_type(param_t.type()));
  }
}
