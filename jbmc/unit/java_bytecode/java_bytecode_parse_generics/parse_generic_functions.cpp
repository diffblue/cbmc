/*******************************************************************\

Module: Unit tests for parsing generic classes

Author: Diffblue Ltd.

\*******************************************************************/

#include <testing-utils/catch.hpp>
#include <java-testing-utils/load_java_class.h>
#include <java-testing-utils/require_type.h>

SCENARIO(
  "parse_generic_functions",
  "[core][java_bytecode][java_bytecode_parse_generics]")
{
  const symbol_tablet &new_symbol_table = load_java_class(
    "GenericFunctions", "./java_bytecode/java_bytecode_parse_generics");

  std::string class_prefix = "java::GenericFunctions";

  WHEN("Parsing processSimple")
  {
    THEN("There should be a symbol for the function")
    {
      const std::string func_name = ".processSimple";
      const std::string func_descriptor = ":(LGeneric;)V";
      const std::string process_func_name =
        class_prefix + func_name + func_descriptor;

      REQUIRE(new_symbol_table.has_symbol(process_func_name));

      const symbolt func_symbol =
        new_symbol_table.lookup_ref(process_func_name);
      const java_method_typet func_code =
        require_type::require_java_method(func_symbol.type, 1);
      THEN("It contains parameter x pointing to Generic")
      {
        const java_method_typet::parametert &param_x =
          require_type::require_parameter(func_code, "x");
        require_type::require_pointer(
          param_x.type(), struct_tag_typet("java::Generic"));

        // TODO: the bounds are not parsed yet; extend tests when fixed -
        // issue TG-1286
      }
    }
  }

  WHEN("Parsing processUpperBoundInterface")
  {
    THEN("There should be a symbol for the function")
    {
      const std::string func_name = ".processUpperBoundInterface";
      const std::string func_descriptor = ":(LGeneric;)V";
      const std::string process_func_name =
        class_prefix + func_name + func_descriptor;

      REQUIRE(new_symbol_table.has_symbol(process_func_name));
      const symbolt func_symbol =
        new_symbol_table.lookup_ref(process_func_name);
      const java_method_typet func_code =
        require_type::require_java_method(func_symbol.type, 1);
      THEN("It contains parameter x pointing to Generic")
      {
        const java_method_typet::parametert &param_x =
          require_type::require_parameter(func_code, "x");
        require_type::require_pointer(
          param_x.type(), struct_tag_typet("java::Generic"));

        // TODO: the bounds are not parsed yet; extend tests when fixed -
        // issue TG-1286
      }
    }
  }

  WHEN("Parsing processUpperBoundClass")
  {
    THEN("There should be a symbol for the function")
    {
      const std::string func_name = ".processUpperBoundClass";
      const std::string func_descriptor = ":(LGeneric;)V";
      const std::string process_func_name =
        class_prefix + func_name + func_descriptor;

      REQUIRE(new_symbol_table.has_symbol(process_func_name));
      const symbolt func_symbol =
        new_symbol_table.lookup_ref(process_func_name);
      const java_method_typet func_code =
        require_type::require_java_method(func_symbol.type, 1);
      THEN("It contains parameter x pointing to Generic")
      {
        const java_method_typet::parametert &param_x =
          require_type::require_parameter(func_code, "x");
        require_type::require_pointer(
          param_x.type(), struct_tag_typet("java::Generic"));

        // TODO: the bounds are not parsed yet; extend tests when fixed -
        // issue TG-1286
      }
    }
  }

  WHEN("Parsing processUpperBoundClass2")
  {
    THEN("There should be a symbol for the function")
    {
      const std::string func_name = ".processUpperBoundClass2";
      const std::string func_descriptor = ":(Ljava/lang/Number;)V";
      const std::string process_func_name =
        class_prefix + func_name + func_descriptor;

      REQUIRE(new_symbol_table.has_symbol(process_func_name));
      const symbolt func_symbol =
        new_symbol_table.lookup_ref(process_func_name);
      const java_method_typet func_code =
        require_type::require_java_method(func_symbol.type, 1);
      THEN("It contains parameter x pointing to java.lang.Number")
      {
        const java_method_typet::parametert &param_x =
          require_type::require_parameter(func_code, "x");
        require_type::require_pointer(
          param_x.type(), struct_tag_typet("java::java.lang.Number"));

        // TODO: the bounds are not parsed yet; extend tests when fixed -
        // issue TG-1286
      }
    }
  }

  WHEN("Parsing processDoubleUpperBoundClass")
  {
    THEN("There should be a symbol for the function")
    {
      const std::string func_name = ".processDoubleUpperBoundClass";
      const std::string func_descriptor = ":(LGeneric;)V";
      const std::string process_func_name =
        class_prefix + func_name + func_descriptor;

      REQUIRE(new_symbol_table.has_symbol(process_func_name));
      const symbolt func_symbol =
        new_symbol_table.lookup_ref(process_func_name);
      const java_method_typet func_code =
        require_type::require_java_method(func_symbol.type, 1);
      THEN("It contains parameter x pointing to Generic")
      {
        const java_method_typet::parametert &param_x =
          require_type::require_parameter(func_code, "x");
        require_type::require_pointer(
          param_x.type(), struct_tag_typet("java::Generic"));

        // TODO: the bounds are not parsed yet; extend tests when fixed -
        // issue TG-1286
      }
    }
  }

  WHEN("Parsing processDoubleUpperBoundInterface")
  {
    THEN("There should be a symbol for the function")
    {
      const std::string func_name = ".processDoubleUpperBoundInterface";
      const std::string func_descriptor = ":(LGeneric;)V";
      const std::string process_func_name =
        class_prefix + func_name + func_descriptor;

      REQUIRE(new_symbol_table.has_symbol(process_func_name));
      const symbolt func_symbol =
        new_symbol_table.lookup_ref(process_func_name);
      const java_method_typet func_code =
        require_type::require_java_method(func_symbol.type, 1);
      THEN("It contains parameter x pointing to Generic")
      {
        const java_method_typet::parametert &param_x =
          require_type::require_parameter(func_code, "x");
        require_type::require_pointer(
          param_x.type(), struct_tag_typet("java::Generic"));

        // TODO: the bounds are not parsed yet; extend tests when fixed -
        // issue TG-1286
      }
    }
  }

  WHEN("Parsing processMultipleSimple")
  {
    THEN("There should be a symbol for the function")
    {
      const std::string func_name = ".processMultipleSimple";
      const std::string func_descriptor = ":(LGeneric;LGeneric;)V";
      const std::string process_func_name =
        class_prefix + func_name + func_descriptor;

      REQUIRE(new_symbol_table.has_symbol(process_func_name));
      const symbolt func_symbol =
        new_symbol_table.lookup_ref(process_func_name);
      const java_method_typet func_code =
        require_type::require_java_method(func_symbol.type, 2);

      THEN("It contains parameter t pointing to Generic")
      {
        const java_method_typet::parametert &param_t =
          require_type::require_parameter(func_code, "t");
        require_type::require_pointer(
          param_t.type(), struct_tag_typet("java::Generic"));

        // TODO: the bounds are not parsed yet; extend tests when fixed -
        // issue TG-1286
      }
      THEN("It contains parameter u pointing to Generic")
      {
        const java_method_typet::parametert &param_u =
          require_type::require_parameter(func_code, "u");
        require_type::require_pointer(
          param_u.type(), struct_tag_typet("java::Generic"));

        // TODO: the bounds are not parsed yet; extend tests when fixed -
        // issue TG-1286
      }
    }
  }

  WHEN("Parsing processMultipleUpperBound")
  {
    THEN("There should be a symbol for the function")
    {
      const std::string func_name = ".processMultipleUpperBound";
      const std::string func_descriptor = ":(LGeneric;LGeneric;)V";
      const std::string process_func_name =
        class_prefix + func_name + func_descriptor;

      REQUIRE(new_symbol_table.has_symbol(process_func_name));
      const symbolt func_symbol =
        new_symbol_table.lookup_ref(process_func_name);
      const java_method_typet func_code =
        require_type::require_java_method(func_symbol.type, 2);

      THEN("It contains parameter t pointing to Generic")
      {
        const java_method_typet::parametert &param_t =
          require_type::require_parameter(func_code, "t");
        require_type::require_pointer(
          param_t.type(), struct_tag_typet("java::Generic"));

        // TODO: the bounds are not parsed yet; extend tests when fixed -
        // issue TG-1286
      }
      THEN("It contains parameter u pointing to Generic")
      {
        const java_method_typet::parametert &param_u =
          require_type::require_parameter(func_code, "u");
        require_type::require_pointer(
          param_u.type(), struct_tag_typet("java::Generic"));

        // TODO: the bounds are not parsed yet; extend tests when fixed -
        // issue TG-1286
      }
    }
  }

  WHEN("Parsing returnSimple")
  {
    THEN("There should be a symbol for the function")
    {
      const std::string func_name = ".returnSimple";
      const std::string func_descriptor = ":()LGeneric;";
      const std::string process_func_name =
        class_prefix + func_name + func_descriptor;

      REQUIRE(new_symbol_table.has_symbol(process_func_name));

      const symbolt func_symbol =
        new_symbol_table.lookup_ref(process_func_name);
      const java_method_typet func_code =
        require_type::require_java_method(func_symbol.type, 0);
      THEN("It has return type pointing to Generic")
      {
        require_type::require_pointer(
          func_code.return_type(), struct_tag_typet("java::Generic"));

        // TODO: the bounds are not parsed yet; extend tests when fixed -
        // issue TG-1286
      }
    }
  }

  WHEN("Parsing returnSimpleField")
  {
    THEN("There should be a symbol for the function")
    {
      const std::string func_name = ".returnSimpleField";
      const std::string func_descriptor = ":()Ljava/lang/Object;";
      const std::string process_func_name =
        class_prefix + func_name + func_descriptor;

      REQUIRE(new_symbol_table.has_symbol(process_func_name));

      const symbolt func_symbol =
        new_symbol_table.lookup_ref(process_func_name);
      const java_method_typet func_code =
        require_type::require_java_method(func_symbol.type, 0);
      THEN("It has return type pointing to java.lang.Object")
      {
        require_type::require_pointer(
          func_code.return_type(), struct_tag_typet("java::java.lang.Object"));

        // TODO: the bounds are not parsed yet; extend tests when fixed -
        // issue TG-1286
      }
    }
  }

  WHEN("Parsing returnUpperBoundInterface")
  {
    THEN("There should be a symbol for the function")
    {
      const std::string func_name = ".returnUpperBoundInterface";
      const std::string func_descriptor = ":()LGeneric;";
      const std::string process_func_name =
        class_prefix + func_name + func_descriptor;

      REQUIRE(new_symbol_table.has_symbol(process_func_name));
      const symbolt func_symbol =
        new_symbol_table.lookup_ref(process_func_name);
      const java_method_typet func_code = to_java_method_type(func_symbol.type);
      THEN("It has return type pointing to Generic")
      {
        require_type::require_pointer(
          func_code.return_type(), struct_tag_typet("java::Generic"));

        // TODO: the bounds are not parsed yet; extend tests when fixed -
        // issue TG-1286
      }
    }
  }

  WHEN("Parsing returnUpperBoundClass")
  {
    THEN("There should be a symbol for the function")
    {
      const std::string func_name = ".returnUpperBoundClass";
      const std::string func_descriptor = ":()LGeneric;";
      const std::string process_func_name =
        class_prefix + func_name + func_descriptor;

      REQUIRE(new_symbol_table.has_symbol(process_func_name));
      const symbolt func_symbol =
        new_symbol_table.lookup_ref(process_func_name);
      const java_method_typet func_code =
        require_type::require_java_method(func_symbol.type, 0);
      THEN("It has return type pointing to Generic")
      {
        require_type::require_pointer(
          func_code.return_type(), struct_tag_typet("java::Generic"));

        // TODO: the bounds are not parsed yet; extend tests when fixed -
        // issue TG-1286
      }
    }
  }

  WHEN("Parsing returnDoubleUpperBoundClass")
  {
    THEN("There should be a symbol for the function")
    {
      const std::string func_name = ".returnDoubleUpperBoundClass";
      const std::string func_descriptor = ":()LGeneric;";
      const std::string process_func_name =
        class_prefix + func_name + func_descriptor;

      REQUIRE(new_symbol_table.has_symbol(process_func_name));
      const symbolt func_symbol =
        new_symbol_table.lookup_ref(process_func_name);
      const java_method_typet func_code =
        require_type::require_java_method(func_symbol.type, 0);
      THEN("It has return type pointing to Generic")
      {
        require_type::require_pointer(
          func_code.return_type(), struct_tag_typet("java::Generic"));

        // TODO: the bounds are not parsed yet; extend tests when fixed -
        // issue TG-1286
      }
    }
  }

  WHEN("Parsing returnDoubleUpperBoundInterface")
  {
    THEN("There should be a symbol for the function")
    {
      const std::string func_name = ".returnDoubleUpperBoundInterface";
      const std::string func_descriptor = ":()LGeneric;";
      const std::string process_func_name =
        class_prefix + func_name + func_descriptor;

      REQUIRE(new_symbol_table.has_symbol(process_func_name));
      const symbolt func_symbol =
        new_symbol_table.lookup_ref(process_func_name);
      const java_method_typet func_code =
        require_type::require_java_method(func_symbol.type, 0);
      THEN("It has return type pointing to Generic")
      {
        require_type::require_pointer(
          func_code.return_type(), struct_tag_typet("java::Generic"));

        // TODO: the bounds are not parsed yet; extend tests when fixed -
        // issue TG-1286
      }
    }
  }

  WHEN("Parsing processReturnSimpleSame")
  {
    THEN("There should be a symbol for the function")
    {
      const std::string func_name = ".processReturnSimpleSame";
      const std::string func_descriptor = ":(LGeneric;)LGeneric;";
      const std::string process_func_name =
        class_prefix + func_name + func_descriptor;

      REQUIRE(new_symbol_table.has_symbol(process_func_name));

      const symbolt func_symbol =
        new_symbol_table.lookup_ref(process_func_name);
      const java_method_typet func_code =
        require_type::require_java_method(func_symbol.type, 1);

      THEN("It contains parameter x pointing to Generic")
      {
        const java_method_typet::parametert &param_x =
          require_type::require_parameter(func_code, "x");
        require_type::require_pointer(
          param_x.type(), struct_tag_typet("java::Generic"));

        // TODO: the bounds are not parsed yet; extend tests when fixed -
        // issue TG-1286
      }

      THEN("It has return type pointing to Generic")
      {
        require_type::require_pointer(
          func_code.return_type(), struct_tag_typet("java::Generic"));

        // TODO: the bounds are not parsed yet; extend tests when fixed -
        // issue TG-1286
      }
    }
  }

  WHEN("Parsing processReturnUpperBoundInterfaceSame")
  {
    THEN("There should be a symbol for the function")
    {
      const std::string func_name = ".processReturnUpperBoundInterfaceSame";
      const std::string func_descriptor = ":(LGeneric;)LGeneric;";
      const std::string process_func_name =
        class_prefix + func_name + func_descriptor;

      REQUIRE(new_symbol_table.has_symbol(process_func_name));
      const symbolt func_symbol =
        new_symbol_table.lookup_ref(process_func_name);
      const java_method_typet func_code =
        require_type::require_java_method(func_symbol.type, 1);

      THEN("It contains parameter x pointing to Generic")
      {
        const java_method_typet::parametert &param_x =
          require_type::require_parameter(func_code, "x");
        require_type::require_pointer(
          param_x.type(), struct_tag_typet("java::Generic"));

        // TODO: the bounds are not parsed yet; extend tests when fixed -
        // issue TG-1286
      }

      THEN("It has return type pointing to Generic")
      {
        require_type::require_pointer(
          func_code.return_type(), struct_tag_typet("java::Generic"));

        // TODO: the bounds are not parsed yet; extend tests when fixed -
        // issue TG-1286
      }
    }
  }

  WHEN("Parsing processReturnUpperBoundClassSame")
  {
    THEN("There should be a symbol for the function")
    {
      const std::string func_name = ".processReturnUpperBoundClassSame";
      const std::string func_descriptor = ":(LGeneric;)LGeneric;";
      const std::string process_func_name =
        class_prefix + func_name + func_descriptor;

      REQUIRE(new_symbol_table.has_symbol(process_func_name));
      const symbolt func_symbol =
        new_symbol_table.lookup_ref(process_func_name);
      const java_method_typet func_code =
        require_type::require_java_method(func_symbol.type, 1);

      THEN("It contains parameter x pointing to Generic")
      {
        const java_method_typet::parametert &param_x =
          require_type::require_parameter(func_code, "x");
        require_type::require_pointer(
          param_x.type(), struct_tag_typet("java::Generic"));

        // TODO: the bounds are not parsed yet; extend tests when fixed -
        // issue TG-1286
      }

      THEN("It has return type pointing to Generic")
      {
        require_type::require_pointer(
          func_code.return_type(), struct_tag_typet("java::Generic"));

        // TODO: the bounds are not parsed yet; extend tests when fixed -
        // issue TG-1286
      }
    }
  }

  WHEN("Parsing processReturnDoubleUpperBoundClassSame")
  {
    THEN("There should be a symbol for the function")
    {
      const std::string func_name = ".processReturnDoubleUpperBoundClassSame";
      const std::string func_descriptor = ":(LGeneric;)LGeneric;";
      const std::string process_func_name =
        class_prefix + func_name + func_descriptor;

      REQUIRE(new_symbol_table.has_symbol(process_func_name));
      const symbolt func_symbol =
        new_symbol_table.lookup_ref(process_func_name);
      const java_method_typet func_code =
        require_type::require_java_method(func_symbol.type, 1);

      THEN("It contains parameter x pointing to Generic")
      {
        const java_method_typet::parametert &param_x =
          require_type::require_parameter(func_code, "x");
        require_type::require_pointer(
          param_x.type(), struct_tag_typet("java::Generic"));

        // TODO: the bounds are not parsed yet; extend tests when fixed -
        // issue TG-1286
      }

      THEN("It has return type pointing to Generic")
      {
        require_type::require_pointer(
          func_code.return_type(), struct_tag_typet("java::Generic"));

        // TODO: the bounds are not parsed yet; extend tests when fixed -
        // issue TG-1286
      }
    }
  }

  WHEN("Parsing processReturnDoubleUpperBoundInterfaceSame")
  {
    THEN("There should be a symbol for the function")
    {
      const std::string func_name =
        ".processReturnDoubleUpperBoundInterfaceSame";
      const std::string func_descriptor = ":(LGeneric;)LGeneric;";
      const std::string process_func_name =
        class_prefix + func_name + func_descriptor;

      REQUIRE(new_symbol_table.has_symbol(process_func_name));
      const symbolt func_symbol =
        new_symbol_table.lookup_ref(process_func_name);
      const java_method_typet func_code =
        require_type::require_java_method(func_symbol.type, 1);

      THEN("It contains parameter x pointing to Generic")
      {
        const java_method_typet::parametert &param_x =
          require_type::require_parameter(func_code, "x");
        require_type::require_pointer(
          param_x.type(), struct_tag_typet("java::Generic"));

        // TODO: the bounds are not parsed yet; extend tests when fixed -
        // issue TG-1286
      }

      THEN("It has return type pointing to Generic")
      {
        require_type::require_pointer(
          func_code.return_type(), struct_tag_typet("java::Generic"));

        // TODO: the bounds are not parsed yet; extend tests when fixed -
        // issue TG-1286
      }
    }
  }

  WHEN("Parsing processReturnSimpleDifferent")
  {
    THEN("There should be a symbol for the function")
    {
      const std::string func_name = ".processReturnSimpleDifferent";
      const std::string func_descriptor = ":(LGeneric;)LGeneric;";
      const std::string process_func_name =
        class_prefix + func_name + func_descriptor;

      REQUIRE(new_symbol_table.has_symbol(process_func_name));
      const symbolt func_symbol =
        new_symbol_table.lookup_ref(process_func_name);
      const java_method_typet func_code =
        require_type::require_java_method(func_symbol.type, 1);

      THEN("It contains parameter u pointing to Generic")
      {
        const java_method_typet::parametert &param_u =
          require_type::require_parameter(func_code, "u");
        require_type::require_pointer(
          param_u.type(), struct_tag_typet("java::Generic"));

        // TODO: the bounds are not parsed yet; extend tests when fixed -
        // issue TG-1286
      }

      THEN("It has return type pointing to Generic")
      {
        require_type::require_pointer(
          func_code.return_type(), struct_tag_typet("java::Generic"));

        // TODO: the bounds are not parsed yet; extend tests when fixed -
        // issue TG-1286
      }
    }
  }

  WHEN("Parsing processReturnUpperBoundDifferent")
  {
    THEN("There should be a symbol for the function")
    {
      const std::string func_name = ".processReturnUpperBoundDifferent";
      const std::string func_descriptor = ":(LGeneric;)LGeneric;";
      const std::string process_func_name =
        class_prefix + func_name + func_descriptor;

      REQUIRE(new_symbol_table.has_symbol(process_func_name));
      const symbolt func_symbol =
        new_symbol_table.lookup_ref(process_func_name);
      const java_method_typet func_code =
        require_type::require_java_method(func_symbol.type, 1);

      THEN("It contains parameter u pointing to Generic")
      {
        const java_method_typet::parametert &param_u =
          require_type::require_parameter(func_code, "u");
        require_type::require_pointer(
          param_u.type(), struct_tag_typet("java::Generic"));

        // TODO: the bounds are not parsed yet; extend tests when fixed -
        // issue TG-1286
      }

      THEN("It has return type pointing to Generic")
      {
        require_type::require_pointer(
          func_code.return_type(), struct_tag_typet("java::Generic"));

        // TODO: the bounds are not parsed yet; extend tests when fixed -
        // issue TG-1286
      }
    }
  }

  WHEN("Parsing processReturnMultipleSimpleDifferent")
  {
    THEN("There should be a symbol for the function")
    {
      const std::string func_name = ".processReturnMultipleSimpleDifferent";
      const std::string func_descriptor = ":(LGeneric;LGeneric;)LGeneric;";
      const std::string process_func_name =
        class_prefix + func_name + func_descriptor;

      REQUIRE(new_symbol_table.has_symbol(process_func_name));
      const symbolt func_symbol =
        new_symbol_table.lookup_ref(process_func_name);
      const java_method_typet func_code =
        require_type::require_java_method(func_symbol.type, 2);

      THEN("It contains parameter u pointing to Generic")
      {
        const java_method_typet::parametert &param_u =
          require_type::require_parameter(func_code, "u");
        require_type::require_pointer(
          param_u.type(), struct_tag_typet("java::Generic"));

        // TODO: the bounds are not parsed yet; extend tests when fixed -
        // issue TG-1286
      }

      THEN("It contains parameter v pointing to Generic")
      {
        const java_method_typet::parametert &param_v =
          require_type::require_parameter(func_code, "v");
        require_type::require_pointer(
          param_v.type(), struct_tag_typet("java::Generic"));

        // TODO: the bounds are not parsed yet; extend tests when fixed -
        // issue TG-1286
      }

      THEN("It has return type pointing to Generic")
      {
        require_type::require_pointer(
          func_code.return_type(), struct_tag_typet("java::Generic"));

        // TODO: the bounds are not parsed yet; extend tests when fixed -
        // issue TG-1286
      }
    }
  }

  WHEN("Parsing processReturnMultipleUpperBoundDifferent")
  {
    THEN("There should be a symbol for the function")
    {
      const std::string func_name = ".processReturnMultipleUpperBoundDifferent";
      const std::string func_descriptor = ":(LGeneric;LGeneric;)LGeneric;";
      const std::string process_func_name =
        class_prefix + func_name + func_descriptor;

      REQUIRE(new_symbol_table.has_symbol(process_func_name));
      const symbolt func_symbol =
        new_symbol_table.lookup_ref(process_func_name);
      const java_method_typet func_code =
        require_type::require_java_method(func_symbol.type, 2);

      THEN("It contains parameter u pointing to Generic")
      {
        const java_method_typet::parametert &param_u =
          require_type::require_parameter(func_code, "u");
        require_type::require_pointer(
          param_u.type(), struct_tag_typet("java::Generic"));

        // TODO: the bounds are not parsed yet; extend tests when fixed -
        // issue TG-1286
      }

      THEN("It contains parameter v pointing to Generic")
      {
        const java_method_typet::parametert &param_v =
          require_type::require_parameter(func_code, "v");
        require_type::require_pointer(
          param_v.type(), struct_tag_typet("java::Generic"));

        // TODO: the bounds are not parsed yet; extend tests when fixed -
        // issue TG-1286
      }

      THEN("It has return type pointing to Generic")
      {
        require_type::require_pointer(
          func_code.return_type(), struct_tag_typet("java::Generic"));

        // TODO: the bounds are not parsed yet; extend tests when fixed -
        // issue TG-1286
      }
    }
  }
}
