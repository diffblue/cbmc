/*******************************************************************\

 Module: Unit tests for parsing generic classes

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

#include <testing-utils/catch.hpp>
#include <testing-utils/load_java_class.h>
#include <testing-utils/require_type.h>

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
      const code_typet func_code =
        require_type::require_code(func_symbol.type, 1);
      THEN("It contains parameter x pointing to Generic")
      {
        const code_typet::parametert &param_x =
          require_type::require_parameter(func_code, "x");
        require_type::require_pointer(
          param_x.type(), symbol_typet("java::Generic"));

        THEN("x is generic with type variable T")
        {
          require_type::require_java_generic_type(
            param_x.type(),
            {{require_type::type_argument_kindt::Var, class_prefix + "::T"}});
        }
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
      const code_typet func_code =
        require_type::require_code(func_symbol.type, 1);
      THEN("It contains parameter x pointing to Generic")
      {
        const code_typet::parametert &param_x =
          require_type::require_parameter(func_code, "x");
        require_type::require_pointer(
          param_x.type(), symbol_typet("java::Generic"));

        THEN("x is generic with type variable T")
        {
          require_type::require_java_generic_type(
            param_x.type(),
            {{require_type::type_argument_kindt::Var, class_prefix + "::T"}});

          THEN("The bounds are set correctly")
          {
            // TODO: the bounds are not parsed yet; extend tests when fixed -
            // issue TG-1286
          }
        }
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
      const code_typet func_code =
        require_type::require_code(func_symbol.type, 1);
      THEN("It contains parameter x pointing to Generic")
      {
        const code_typet::parametert &param_x =
          require_type::require_parameter(func_code, "x");
        require_type::require_pointer(
          param_x.type(), symbol_typet("java::Generic"));

        THEN("x is generic with type variable T")
        {
          require_type::require_java_generic_type(
            param_x.type(),
            {{require_type::type_argument_kindt::Var, class_prefix + "::T"}});

          THEN("The bounds are set correctly")
          {
            // TODO: the bounds are not parsed yet; extend tests when fixed -
            // issue TG-1286
          }
        }
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
      const code_typet func_code =
        require_type::require_code(func_symbol.type, 1);
      THEN("It contains parameter x pointing to Generic")
      {
        const code_typet::parametert &param_x =
          require_type::require_parameter(func_code, "x");
        require_type::require_pointer(
          param_x.type(), symbol_typet("java::Generic"));

        THEN("x is generic with type variable T")
        {
          require_type::require_java_generic_type(
            param_x.type(),
            {{require_type::type_argument_kindt::Var, class_prefix + "::T"}});

          THEN("The bounds are set correctly")
          {
            // TODO: the bounds are not parsed yet; extend the tests when
            // fixed - issue TG-1286
          }
        }
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
      const code_typet func_code =
        require_type::require_code(func_symbol.type, 1);
      THEN("It contains parameter x pointing to Generic")
      {
        const code_typet::parametert &param_x =
          require_type::require_parameter(func_code, "x");
        require_type::require_pointer(
          param_x.type(), symbol_typet("java::Generic"));

        THEN("x is generic with type variable T")
        {
          require_type::require_java_generic_type(
            param_x.type(),
            {{require_type::type_argument_kindt::Var, class_prefix + "::T"}});

          THEN("The bounds are set correctly")
          {
            // TODO: the bounds are not parsed yet; extend the tests when
            // fixed - issue TG-1286
          }
        }
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
      const code_typet func_code =
        require_type::require_code(func_symbol.type, 2);

      THEN("It contains parameter t pointing to Generic")
      {
        const code_typet::parametert &param_t =
          require_type::require_parameter(func_code, "t");
        require_type::require_pointer(
          param_t.type(), symbol_typet("java::Generic"));

        THEN("t is generic with type variable T")
        {
          require_type::require_java_generic_type(
            param_t.type(),
            {{require_type::type_argument_kindt::Var, class_prefix + "::T"}});
        }
      }
      THEN("It contains parameter u pointing to Generic")
      {
        const code_typet::parametert &param_u =
          require_type::require_parameter(func_code, "u");
        require_type::require_pointer(
          param_u.type(), symbol_typet("java::Generic"));

        THEN("u is generic with type variable U")
        {
          require_type::require_java_generic_type(
            param_u.type(),
            {{require_type::type_argument_kindt::Var, class_prefix + "::U"}});
        }
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
      const code_typet func_code =
        require_type::require_code(func_symbol.type, 2);

      THEN("It contains parameter t pointing to Generic")
      {
        const code_typet::parametert &param_t =
          require_type::require_parameter(func_code, "t");
        require_type::require_pointer(
          param_t.type(), symbol_typet("java::Generic"));

        THEN("t is generic with type variable T")
        {
          require_type::require_java_generic_type(
            param_t.type(),
            {{require_type::type_argument_kindt::Var, class_prefix + "::T"}});

          THEN("The bounds are set correctly")
          {
            // TODO: the bounds are not parsed yet; extend the tests when
            // fixed - issue TG-1286
          }
        }
      }
      THEN("It contains parameter u pointing to Generic")
      {
        const code_typet::parametert &param_u =
          require_type::require_parameter(func_code, "u");
        require_type::require_pointer(
          param_u.type(), symbol_typet("java::Generic"));

        THEN("u is generic with type variable U")
        {
          require_type::require_java_generic_type(
            param_u.type(),
            {{require_type::type_argument_kindt::Var, class_prefix + "::U"}});

          THEN("The bounds are set correctly")
          {
            // TODO: the bounds are not parsed yet; extend the tests when
            // fixed - issue TG-1286
          }
        }
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
      const code_typet func_code =
        require_type::require_code(func_symbol.type, 0);
      THEN("It has return type pointing to Generic")
      {
        require_type::require_pointer(
          func_code.return_type(), symbol_typet("java::Generic"));

        THEN("It is generic with type variable T")
        {
          require_type::require_java_generic_type(
            func_code.return_type(),
            {{require_type::type_argument_kindt::Var, class_prefix + "::T"}});
        }
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
      const code_typet func_code =
        require_type::require_code(func_symbol.type, 0);
      THEN("It has return type pointing to java.lang.Object")
      {
        require_type::require_pointer(
          func_code.return_type(), symbol_typet("java::java.lang.Object"));

        THEN("It is the generic parameter T")
        {
          require_type::require_java_generic_parameter(
            func_code.return_type(), class_prefix + "::T");
        }
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
      const code_typet func_code = to_code_type(func_symbol.type);
      THEN("It has return type pointing to Generic")
      {
        require_type::require_pointer(
          func_code.return_type(), symbol_typet("java::Generic"));

        THEN("It is generic with type variable T")
        {
          require_type::require_java_generic_type(
            func_code.return_type(),
            {{require_type::type_argument_kindt::Var, class_prefix + "::T"}});

          THEN("The bounds are set correctly")
          {
            // TODO: the bounds are not parsed yet; enable the tests when
            // fixed - issue TG-1286
          }
        }
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
      const code_typet func_code =
        require_type::require_code(func_symbol.type, 0);
      THEN("It has return type pointing to Generic")
      {
        require_type::require_pointer(
          func_code.return_type(), symbol_typet("java::Generic"));

        THEN("It is generic with type variable T")
        {
          require_type::require_java_generic_type(
            func_code.return_type(),
            {{require_type::type_argument_kindt::Var, class_prefix + "::T"}});

          THEN("The bounds are set correctly")
          {
            // TODO: the bounds are not parsed yet; enable the tests when
            // fixed - issue TG-1286
          }
        }
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
      const code_typet func_code =
        require_type::require_code(func_symbol.type, 0);
      THEN("It has return type pointing to Generic")
      {
        require_type::require_pointer(
          func_code.return_type(), symbol_typet("java::Generic"));

        THEN("It is generic with type variable T")
        {
          require_type::require_java_generic_type(
            func_code.return_type(),
            {{require_type::type_argument_kindt::Var, class_prefix + "::T"}});

          THEN("The bounds are set correctly")
          {
            // TODO: the bounds are not parsed yet; enable the tests when
            // fixed - issue TG-1286
          }
        }
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
      const code_typet func_code =
        require_type::require_code(func_symbol.type, 0);
      THEN("It has return type pointing to Generic")
      {
        require_type::require_pointer(
          func_code.return_type(), symbol_typet("java::Generic"));

        THEN("It is generic with type variable T")
        {
          require_type::require_java_generic_type(
            func_code.return_type(),
            {{require_type::type_argument_kindt::Var, class_prefix + "::T"}});

          THEN("The bounds are set correctly")
          {
            // TODO: the bounds are not parsed yet; enable the tests when
            // fixed - issue TG-1286
          }
        }
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
      const code_typet func_code =
        require_type::require_code(func_symbol.type, 1);

      THEN("It contains parameter x pointing to Generic")
      {
        const code_typet::parametert &param_x =
          require_type::require_parameter(func_code, "x");
        require_type::require_pointer(
          param_x.type(), symbol_typet("java::Generic"));

        THEN("x is generic with type variable T")
        {
          require_type::require_java_generic_type(
            param_x.type(),
            {{require_type::type_argument_kindt::Var, class_prefix + "::T"}});
        }
      }

      THEN("It has return type pointing to Generic")
      {
        require_type::require_pointer(
          func_code.return_type(), symbol_typet("java::Generic"));

        THEN("It is generic with type variable T")
        {
          require_type::require_java_generic_type(
            func_code.return_type(),
            {{require_type::type_argument_kindt::Var, class_prefix + "::T"}});
        }
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
      const code_typet func_code =
        require_type::require_code(func_symbol.type, 1);

      THEN("It contains parameter x pointing to Generic")
      {
        const code_typet::parametert &param_x =
          require_type::require_parameter(func_code, "x");
        require_type::require_pointer(
          param_x.type(), symbol_typet("java::Generic"));

        THEN("x is generic with type variable T")
        {
          require_type::require_java_generic_type(
            param_x.type(),
            {{require_type::type_argument_kindt::Var, class_prefix + "::T"}});

          THEN("The bounds are set correctly")
          {
            // TODO: the bounds are not parsed yet; enable the tests when
            // fixed - issue TG-1286
          }
        }
      }

      THEN("It has return type pointing to Generic")
      {
        require_type::require_pointer(
          func_code.return_type(), symbol_typet("java::Generic"));

        THEN("It is generic with type variable T")
        {
          require_type::require_java_generic_type(
            func_code.return_type(),
            {{require_type::type_argument_kindt::Var, class_prefix + "::T"}});

          THEN("The bounds are set correctly")
          {
            // TODO: the bounds are not parsed yet; enable the tests when
            // fixed - issue TG-1286
          }
        }
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
      const code_typet func_code =
        require_type::require_code(func_symbol.type, 1);

      THEN("It contains parameter x pointing to Generic")
      {
        const code_typet::parametert &param_x =
          require_type::require_parameter(func_code, "x");
        require_type::require_pointer(
          param_x.type(), symbol_typet("java::Generic"));

        THEN("x is generic with type variable T")
        {
          require_type::require_java_generic_type(
            param_x.type(),
            {{require_type::type_argument_kindt::Var, class_prefix + "::T"}});

          THEN("The bounds are set correctly")
          {
            // TODO: the bounds are not parsed yet; enable the tests when
            // fixed - issue TG-1286
          }
        }
      }

      THEN("It has return type pointing to Generic")
      {
        require_type::require_pointer(
          func_code.return_type(), symbol_typet("java::Generic"));

        THEN("It is generic with type variable T")
        {
          require_type::require_java_generic_type(
            func_code.return_type(),
            {{require_type::type_argument_kindt::Var, class_prefix + "::T"}});

          THEN("The bounds are set correctly")
          {
            // TODO: the bounds are not parsed yet; enable the tests when
            // fixed - issue TG-1286
          }
        }
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
      const code_typet func_code =
        require_type::require_code(func_symbol.type, 1);

      THEN("It contains parameter x pointing to Generic")
      {
        const code_typet::parametert &param_x =
          require_type::require_parameter(func_code, "x");
        require_type::require_pointer(
          param_x.type(), symbol_typet("java::Generic"));

        THEN("x is generic with type variable T")
        {
          require_type::require_java_generic_type(
            param_x.type(),
            {{require_type::type_argument_kindt::Var, class_prefix + "::T"}});

          THEN("The bounds are set correctly")
          {
            // TODO: the bounds are not parsed yet; extend the tests when
            // fixed - issue TG-1286
          }
        }
      }

      THEN("It has return type pointing to Generic")
      {
        require_type::require_pointer(
          func_code.return_type(), symbol_typet("java::Generic"));

        THEN("It is generic with type variable T")
        {
          require_type::require_java_generic_type(
            func_code.return_type(),
            {{require_type::type_argument_kindt::Var, class_prefix + "::T"}});

          THEN("The bounds are set correctly")
          {
            // TODO: the bounds are not parsed yet; enable the tests when
            // fixed - issue TG-1286
          }
        }
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
      const code_typet func_code =
        require_type::require_code(func_symbol.type, 1);

      THEN("It contains parameter x pointing to Generic")
      {
        const code_typet::parametert &param_x =
          require_type::require_parameter(func_code, "x");
        require_type::require_pointer(
          param_x.type(), symbol_typet("java::Generic"));

        THEN("x is generic with type variable T")
        {
          require_type::require_java_generic_type(
            param_x.type(),
            {{require_type::type_argument_kindt::Var, class_prefix + "::T"}});

          THEN("The bounds are set correctly")
          {
            // TODO: the bounds are not parsed yet; extend the tests when
            // fixed - issue TG-1286
          }
        }
      }

      THEN("It has return type pointing to Generic")
      {
        require_type::require_pointer(
          func_code.return_type(), symbol_typet("java::Generic"));

        THEN("It is generic with type variable T")
        {
          require_type::require_java_generic_type(
            func_code.return_type(),
            {{require_type::type_argument_kindt::Var, class_prefix + "::T"}});

          THEN("The bounds are set correctly")
          {
            // TODO: the bounds are not parsed yet; enable the tests when
            // fixed - issue TG-1286
          }
        }
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
      const code_typet func_code =
        require_type::require_code(func_symbol.type, 1);

      THEN("It contains parameter u pointing to Generic")
      {
        const code_typet::parametert &param_u =
          require_type::require_parameter(func_code, "u");
        require_type::require_pointer(
          param_u.type(), symbol_typet("java::Generic"));

        THEN("u is generic with type variable U")
        {
          require_type::require_java_generic_type(
            param_u.type(),
            {{require_type::type_argument_kindt::Var, class_prefix + "::U"}});
        }
      }

      THEN("It has return type pointing to Generic")
      {
        require_type::require_pointer(
          func_code.return_type(), symbol_typet("java::Generic"));

        THEN("It is generic with type variable T")
        {
          require_type::require_java_generic_type(
            func_code.return_type(),
            {{require_type::type_argument_kindt::Var, class_prefix + "::T"}});
        }
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
      const code_typet func_code =
        require_type::require_code(func_symbol.type, 1);

      THEN("It contains parameter u pointing to Generic")
      {
        const code_typet::parametert &param_u =
          require_type::require_parameter(func_code, "u");
        require_type::require_pointer(
          param_u.type(), symbol_typet("java::Generic"));

        THEN("u is generic with type variable U")
        {
          require_type::require_java_generic_type(
            param_u.type(),
            {{require_type::type_argument_kindt::Var, class_prefix + "::U"}});

          THEN("The bounds are set correctly")
          {
            // TODO: the bounds are not parsed yet; enable the tests when
            // fixed - issue TG-1286
          }
        }
      }

      THEN("It has return type pointing to Generic")
      {
        require_type::require_pointer(
          func_code.return_type(), symbol_typet("java::Generic"));

        THEN("It is generic with type variable T")
        {
          require_type::require_java_generic_type(
            func_code.return_type(),
            {{require_type::type_argument_kindt::Var, class_prefix + "::T"}});

          THEN("The bounds are set correctly")
          {
            // TODO: the bounds are not parsed yet; enable the tests when
            // fixed - issue TG-1286
          }
        }
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
      const code_typet func_code =
        require_type::require_code(func_symbol.type, 2);

      THEN("It contains parameter u pointing to Generic")
      {
        const code_typet::parametert &param_u =
          require_type::require_parameter(func_code, "u");
        require_type::require_pointer(
          param_u.type(), symbol_typet("java::Generic"));

        THEN("u is generic with type variable U")
        {
          require_type::require_java_generic_type(
            param_u.type(),
            {{require_type::type_argument_kindt::Var, class_prefix + "::U"}});
        }
      }

      THEN("It contains parameter v pointing to Generic")
      {
        const code_typet::parametert &param_v =
          require_type::require_parameter(func_code, "v");
        require_type::require_pointer(
          param_v.type(), symbol_typet("java::Generic"));

        THEN("v is generic with type variable V")
        {
          require_type::require_java_generic_type(
            param_v.type(),
            {{require_type::type_argument_kindt::Var, class_prefix + "::V"}});
        }
      }

      THEN("It has return type pointing to Generic")
      {
        require_type::require_pointer(
          func_code.return_type(), symbol_typet("java::Generic"));

        THEN("It is generic with type variable T")
        {
          require_type::require_java_generic_type(
            func_code.return_type(),
            {{require_type::type_argument_kindt::Var, class_prefix + "::T"}});
        }
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
      const code_typet func_code =
        require_type::require_code(func_symbol.type, 2);

      THEN("It contains parameter u pointing to Generic")
      {
        const code_typet::parametert &param_u =
          require_type::require_parameter(func_code, "u");
        require_type::require_pointer(
          param_u.type(), symbol_typet("java::Generic"));

        THEN("u is generic with type variable U")
        {
          require_type::require_java_generic_type(
            param_u.type(),
            {{require_type::type_argument_kindt::Var, class_prefix + "::U"}});

          THEN("The bounds are set correctly")
          {
            // TODO: the bounds are not parsed yet; enable the tests when
            // fixed - issue TG-1286
          }
        }
      }

      THEN("It contains parameter v pointing to Generic")
      {
        const code_typet::parametert &param_v =
          require_type::require_parameter(func_code, "v");
        require_type::require_pointer(
          param_v.type(), symbol_typet("java::Generic"));

        THEN("v is generic with type variable V")
        {
          require_type::require_java_generic_type(
            param_v.type(),
            {{require_type::type_argument_kindt::Var, class_prefix + "::V"}});

          THEN("The bounds are set correctly")
          {
            // TODO: the bounds are not parsed yet; enable the tests when
            // fixed - issue TG-1286
          }
        }
      }

      THEN("It has return type pointing to Generic")
      {
        require_type::require_pointer(
          func_code.return_type(), symbol_typet("java::Generic"));

        THEN("It is generic with type variable T")
        {
          require_type::require_java_generic_type(
            func_code.return_type(),
            {{require_type::type_argument_kindt::Var, class_prefix + "::T"}});

          THEN("The bounds are set correctly")
          {
            // TODO: the bounds are not parsed yet; enable the tests when
            // fixed - issue TG-1286
          }
        }
      }
    }
  }
}
