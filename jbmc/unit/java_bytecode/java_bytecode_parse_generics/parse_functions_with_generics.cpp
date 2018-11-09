/*******************************************************************\

Module: Unit tests for parsing generic classes

Author: Diffblue Ltd.

\*******************************************************************/

#include <java-testing-utils/load_java_class.h>
#include <java-testing-utils/require_type.h>
#include <testing-utils/use_catch.h>

SCENARIO(
  "parse_functions_with_generics",
  "[core][java_bytecode][java_bytecode_parse_generics]")
{
  const symbol_tablet &new_symbol_table = load_java_class(
    "FunctionsWithGenerics", "./java_bytecode/java_bytecode_parse_generics");

  std::string class_prefix = "java::FunctionsWithGenerics";

  WHEN("Parsing processReturnSame")
  {
    THEN("There should be a symbol for the function")
    {
      const std::string func_name = ".processReturnSame";
      const std::string func_descriptor = ":(LGeneric;)LGeneric;";
      const std::string process_func_name =
        class_prefix + func_name + func_descriptor;

      REQUIRE(new_symbol_table.has_symbol(process_func_name));

      const symbolt func_symbol =
        new_symbol_table.lookup_ref(process_func_name);
      const java_method_typet &func_code =
        require_type::require_java_method(func_symbol.type);

      THEN("It has parameter x pointing to Generic")
      {
        const java_method_typet::parametert &param_x =
          require_type::require_parameter(func_code, "x");
        require_type::require_pointer(
          param_x.type(), struct_tag_typet("java::Generic"));

        THEN("x is generic with parameter pointing to java.lang.Integer")
        {
          require_type::require_java_generic_type(
            param_x.type(),
            {{require_type::type_argument_kindt::Inst,
              "java::java.lang.Integer"}});
        }
      }

      THEN("It has return type pointing to Generic")
      {
        const typet return_type = func_code.return_type();
        require_type::require_pointer(
          return_type, struct_tag_typet("java::Generic"));

        THEN("It is generic with parameter pointing to java.lang.Integer")
        {
          require_type::require_java_generic_type(
            return_type,
            {{require_type::type_argument_kindt::Inst,
              "java::java.lang.Integer"}});
        }
      }
    }
  }

  WHEN("Parsing processReturnDifferent")
  {
    THEN("There should be a symbol for the function")
    {
      const std::string func_name = ".processReturnDifferent";
      const std::string func_descriptor = ":(LGeneric;)LGeneric;";
      const std::string process_func_name =
        class_prefix + func_name + func_descriptor;

      REQUIRE(new_symbol_table.has_symbol(process_func_name));

      const symbolt func_symbol =
        new_symbol_table.lookup_ref(process_func_name);
      const java_method_typet func_code =
        require_type::require_java_method(func_symbol.type);

      THEN("It has parameter s pointing to Generic")
      {
        const java_method_typet::parametert &param_s =
          require_type::require_parameter(func_code, "s");
        require_type::require_pointer(
          param_s.type(), struct_tag_typet("java::Generic"));

        THEN("s is generic with parameter pointing to java.lang.String")
        {
          require_type::require_java_generic_type(
            param_s.type(),
            {{require_type::type_argument_kindt::Inst,
              "java::java.lang.String"}});
        }
      }

      THEN("It has return type pointing to Generic")
      {
        const typet return_type = func_code.return_type();
        require_type::require_pointer(
          return_type, struct_tag_typet("java::Generic"));

        THEN("It is generic with parameter pointing to java.lang.Integer")
        {
          require_type::require_java_generic_type(
            return_type,
            {{require_type::type_argument_kindt::Inst,
              "java::java.lang.Integer"}});
        }
      }
    }
  }

  WHEN("Parsing processReturnMultipleSame")
  {
    THEN("There should be a symbol for the function")
    {
      const std::string func_name = ".processReturnMultipleSame";
      const std::string func_descriptor = ":(LGeneric;LGeneric;)LGeneric;";
      const std::string process_func_name =
        class_prefix + func_name + func_descriptor;

      REQUIRE(new_symbol_table.has_symbol(process_func_name));

      const symbolt func_symbol =
        new_symbol_table.lookup_ref(process_func_name);
      const java_method_typet func_code =
        require_type::require_java_method(func_symbol.type);

      THEN("It has parameter x pointing to Generic")
      {
        const java_method_typet::parametert &param_x =
          require_type::require_parameter(func_code, "x");
        require_type::require_pointer(
          param_x.type(), struct_tag_typet("java::Generic"));

        THEN("x is generic with parameter pointing to java.lang.Integer")
        {
          require_type::require_java_generic_type(
            param_x.type(),
            {{require_type::type_argument_kindt::Inst,
              "java::java.lang.Integer"}});
        }
      }

      THEN("It has parameter y pointing to Generic")
      {
        const java_method_typet::parametert &param_y =
          require_type::require_parameter(func_code, "y");
        require_type::require_pointer(
          param_y.type(), struct_tag_typet("java::Generic"));

        THEN("y is generic with parameter pointing to java.lang.Integer")
        {
          require_type::require_java_generic_type(
            param_y.type(),
            {{require_type::type_argument_kindt::Inst,
              "java::java.lang.Integer"}});
        }
      }

      THEN("It has return type pointing to Generic")
      {
        const typet return_type = func_code.return_type();
        require_type::require_pointer(
          return_type, struct_tag_typet("java::Generic"));

        THEN("It is generic with parameter pointing to java.lang.Integer")
        {
          require_type::require_java_generic_type(
            return_type,
            {{require_type::type_argument_kindt::Inst,
              "java::java.lang.Integer"}});
        }
      }
    }
  }

  WHEN("Parsing processReturnMultipleDifferent")
  {
    THEN("There should be a symbol for the function")
    {
      const std::string func_name = ".processReturnMultipleDifferent";
      const std::string func_descriptor = ":(LGeneric;LGeneric;)LGeneric;";
      const std::string process_func_name =
        class_prefix + func_name + func_descriptor;

      REQUIRE(new_symbol_table.has_symbol(process_func_name));

      const symbolt func_symbol =
        new_symbol_table.lookup_ref(process_func_name);
      const java_method_typet func_code =
        require_type::require_java_method(func_symbol.type);

      THEN("It has parameter s pointing to Generic")
      {
        const java_method_typet::parametert &param_s =
          require_type::require_parameter(func_code, "s");
        require_type::require_pointer(
          param_s.type(), struct_tag_typet("java::Generic"));

        THEN("s is generic with parameter pointing to java.lang.String")
        {
          require_type::require_java_generic_type(
            param_s.type(),
            {{require_type::type_argument_kindt::Inst,
              "java::java.lang.String"}});
        }
      }

      THEN("It has parameter b pointing to Generic")
      {
        const java_method_typet::parametert &param_b =
          require_type::require_parameter(func_code, "b");
        require_type::require_pointer(
          param_b.type(), struct_tag_typet("java::Generic"));

        THEN("b is generic with parameter pointing to java.lang.Boolean")
        {
          require_type::require_java_generic_type(
            param_b.type(),
            {{require_type::type_argument_kindt::Inst,
              "java::java.lang.Boolean"}});
        }
      }

      THEN("It has return type pointing to Generic")
      {
        const typet return_type = func_code.return_type();
        require_type::require_pointer(
          return_type, struct_tag_typet("java::Generic"));

        THEN("It is generic with parameter pointing to java.lang.Integer")
        {
          require_type::require_java_generic_type(
            return_type,
            {{require_type::type_argument_kindt::Inst,
              "java::java.lang.Integer"}});
        }
      }
    }
  }

  WHEN("Parsing returnInnerField")
  {
    THEN("There should be a symbol for the function")
    {
      const std::string func_name = ".returnInnerField";
      const std::string func_descriptor =
        ":(LFunctionsWithGenerics$Inner;)LGeneric;";
      const std::string process_func_name =
        class_prefix + func_name + func_descriptor;

      REQUIRE(new_symbol_table.has_symbol(process_func_name));

      const symbolt func_symbol =
        new_symbol_table.lookup_ref(process_func_name);
      const java_method_typet func_code =
        require_type::require_java_method(func_symbol.type);

      THEN("It has parameter inner pointing to Inner")
      {
        const java_method_typet::parametert &param_inner =
          require_type::require_parameter(func_code, "inner");
        require_type::require_pointer(
          param_inner.type(), struct_tag_typet(class_prefix + "$Inner"));
      }

      THEN("It has return type pointing to Generic")
      {
        const typet return_type = func_code.return_type();
        require_type::require_pointer(
          return_type, struct_tag_typet("java::Generic"));

        THEN("It is generic with parameter pointing to java.lang.Integer")
        {
          require_type::require_java_generic_type(
            return_type,
            {{require_type::type_argument_kindt::Inst,
              "java::java.lang.Integer"}});
        }
      }
    }
  }
}
