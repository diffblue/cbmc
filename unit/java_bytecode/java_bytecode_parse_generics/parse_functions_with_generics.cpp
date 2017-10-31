/*******************************************************************\

 Module: Unit tests for parsing generic classes

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

#include <testing-utils/catch.hpp>
#include <testing-utils/load_java_class.h>
#include <testing-utils/require_type.h>

#include <util/config.h>
#include <util/language.h>

#include <java_bytecode/java_bytecode_language.h>

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
      const code_typet func_code = to_code_type(func_symbol.type);

      THEN("It has parameter x pointing to Generic")
      {
        code_typet::parametert param_x =
          require_type::require_parameter(func_code, "x");
        require_type::require_pointer(
          param_x.type(), symbol_typet("java::Generic"));

        THEN("x is generic with parameter pointing to java.lang.Integer")
        {
          REQUIRE(is_java_generic_type(param_x.type()));

          const java_generic_typet generic_x =
            to_java_generic_type(param_x.type());
          const java_generic_parametert generic_param_x =
            generic_x.generic_type_variables().front();
          require_type::require_pointer(
            generic_param_x, symbol_typet("java::java.lang.Integer"));
        }
      }

      THEN("It has return type pointing to Generic")
      {
        const typet return_type = func_code.return_type();
        require_type::require_pointer(
          return_type, symbol_typet("java::Generic"));

        THEN("It is generic with parameter pointing to java.lang.Integer")
        {
          REQUIRE(is_java_generic_type(return_type));

          const java_generic_typet generic_return_type =
            to_java_generic_type(return_type);
          const java_generic_parametert generic_return_param =
            generic_return_type.generic_type_variables().front();
          require_type::require_pointer(
            generic_return_param, symbol_typet("java::java.lang.Integer"));
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
      const code_typet func_code = to_code_type(func_symbol.type);

      THEN("It has parameter s pointing to Generic")
      {
        code_typet::parametert param_s =
          require_type::require_parameter(func_code, "s");
        require_type::require_pointer(
          param_s.type(), symbol_typet("java::Generic"));

        THEN("s is generic with parameter pointing to java.lang.String")
        {
          REQUIRE(is_java_generic_type(param_s.type()));

          const java_generic_typet generic_s =
            to_java_generic_type(param_s.type());
          const java_generic_parametert generic_param_s =
            generic_s.generic_type_variables().front();
          require_type::require_pointer(
            generic_param_s, symbol_typet("java::java.lang.String"));
        }
      }

      THEN("It has return type pointing to Generic")
      {
        const typet return_type = func_code.return_type();
        require_type::require_pointer(
          return_type, symbol_typet("java::Generic"));

        THEN("It is generic with parameter pointing to java.lang.Integer")
        {
          REQUIRE(is_java_generic_type(return_type));

          const java_generic_typet generic_return_type =
            to_java_generic_type(return_type);
          const java_generic_parametert generic_return_param =
            generic_return_type.generic_type_variables().front();
          require_type::require_pointer(
            generic_return_param, symbol_typet("java::java.lang.Integer"));
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
      const code_typet func_code = to_code_type(func_symbol.type);

      THEN("It has parameter x pointing to Generic")
      {
        code_typet::parametert param_x =
          require_type::require_parameter(func_code, "x");
        require_type::require_pointer(
          param_x.type(), symbol_typet("java::Generic"));

        THEN("x is generic with parameter pointing to java.lang.Integer")
        {
          REQUIRE(is_java_generic_type(param_x.type()));

          const java_generic_typet generic_x =
            to_java_generic_type(param_x.type());
          const java_generic_parametert generic_param_x =
            generic_x.generic_type_variables().front();
          require_type::require_pointer(
            generic_param_x, symbol_typet("java::java.lang.Integer"));
        }
      }

      THEN("It has parameter y pointing to Generic")
      {
        code_typet::parametert param_y =
          require_type::require_parameter(func_code, "y");
        require_type::require_pointer(
          param_y.type(), symbol_typet("java::Generic"));

        THEN("y is generic with parameter pointing to java.lang.Integer")
        {
          REQUIRE(is_java_generic_type(param_y.type()));

          const java_generic_typet generic_y =
            to_java_generic_type(param_y.type());
          const java_generic_parametert generic_param_y =
            generic_y.generic_type_variables().front();
          require_type::require_pointer(
            generic_param_y, symbol_typet("java::java.lang.Integer"));
        }
      }

      THEN("It has return type pointing to Generic")
      {
        const typet return_type = func_code.return_type();
        require_type::require_pointer(
          return_type, symbol_typet("java::Generic"));

        THEN("It is generic with parameter pointing to java.lang.Integer")
        {
          REQUIRE(is_java_generic_type(return_type));

          const java_generic_typet generic_return_type =
            to_java_generic_type(return_type);
          const java_generic_parametert generic_return_param =
            generic_return_type.generic_type_variables().front();
          require_type::require_pointer(
            generic_return_param, symbol_typet("java::java.lang.Integer"));
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
      const code_typet func_code = to_code_type(func_symbol.type);

      THEN("It has parameter s pointing to Generic")
      {
        code_typet::parametert param_s =
          require_type::require_parameter(func_code, "s");
        require_type::require_pointer(
          param_s.type(), symbol_typet("java::Generic"));

        THEN("s is generic with parameter pointing to java.lang.String")
        {
          REQUIRE(is_java_generic_type(param_s.type()));

          const java_generic_typet generic_s =
            to_java_generic_type(param_s.type());
          const java_generic_parametert generic_param_s =
            generic_s.generic_type_variables().front();
          require_type::require_pointer(
            generic_param_s, symbol_typet("java::java.lang.String"));
        }
      }

      THEN("It has parameter b pointing to Generic")
      {
        code_typet::parametert param_b =
          require_type::require_parameter(func_code, "b");
        require_type::require_pointer(
          param_b.type(), symbol_typet("java::Generic"));

        THEN("b is generic with parameter pointing to java.lang.Boolean")
        {
          REQUIRE(is_java_generic_type(param_b.type()));

          const java_generic_typet generic_b =
            to_java_generic_type(param_b.type());
          const java_generic_parametert generic_param_b =
            generic_b.generic_type_variables().front();
          require_type::require_pointer(
            generic_param_b, symbol_typet("java::java.lang.Boolean"));
        }
      }

      THEN("It has return type pointing to Generic")
      {
        const typet return_type = func_code.return_type();
        require_type::require_pointer(
          return_type, symbol_typet("java::Generic"));

        THEN("It is generic with parameter pointing to java.lang.Integer")
        {
          REQUIRE(is_java_generic_type(return_type));

          const java_generic_typet generic_return_type =
            to_java_generic_type(return_type);
          const java_generic_parametert generic_return_param =
            generic_return_type.generic_type_variables().front();
          require_type::require_pointer(
            generic_return_param, symbol_typet("java::java.lang.Integer"));
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
      const code_typet func_code = to_code_type(func_symbol.type);

      THEN("It has parameter inner pointing to Inner")
      {
        code_typet::parametert param_inner =
          require_type::require_parameter(func_code, "inner");
        require_type::require_pointer(
          param_inner.type(), symbol_typet(class_prefix + "$Inner"));
      }

      THEN("It has return type pointing to Generic")
      {
        const typet return_type = func_code.return_type();
        require_type::require_pointer(
          return_type, symbol_typet("java::Generic"));

        THEN("It is generic with parameter pointing to java.lang.Integer")
        {
          REQUIRE(is_java_generic_type(return_type));

          const java_generic_typet generic_return_type =
            to_java_generic_type(return_type);
          const java_generic_parametert generic_return_param =
            generic_return_type.generic_type_variables().front();
          require_type::require_pointer(
            generic_return_param, symbol_typet("java::java.lang.Integer"));
        }
      }
    }
  }
}
