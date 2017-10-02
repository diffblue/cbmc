/*******************************************************************\

 Module: Unit tests for specializing generic methods

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

#include <testing-utils/catch.hpp>
#include <java_bytecode/java_bytecode_language.h>
#include <java_bytecode/specialize_java_generic_method.h>
#include <util/namespace.h>
#include <testing-utils/load_java_class.h>
#include <testing-utils/require_type.h>
#include <iostream>

SCENARIO(
  "java_bytecode_specialize_generics",
  "[core][java_bytecode][java_bytecode_specialize_generics]")
{
  symbol_tablet new_symbol_table=load_java_class("generics", ""
    "./java_bytecode/java_bytecode_specialize_generics");

  stream_message_handlert message_handler(std::cout);
  specialize_java_generic_methodt
    instantiate_generic_method{message_handler};


  GIVEN("Some class files with Generics")
  {
    WHEN("A method returns a generic type")
    {
      REQUIRE(
        new_symbol_table.has_symbol(
          "java::generics$bound_element.f:()Ljava/lang/Number;"));

      const symbolt &generic_method_symbol=
        new_symbol_table.lookup_ref(
          "java::generics$bound_element.f:()Ljava/lang/Number;");

      THEN("When parsing the method")
      {
        const code_typet &code=
          require_type::require_code_type(generic_method_symbol.type, 1);

        require_type::require_java_generic_parameter_variables(
          code.return_type(),
          {"java::generics$bound_element::NUM"});
      }

      const symbolt &specialized_method_symbol=instantiate_generic_method(
        generic_method_symbol,
        {
          {"java::generics$bound_element::NUM",
            symbol_typet("java::java.lang.Integer")
          }
        },
        new_symbol_table);

      THEN("When specializing the method with a concrete type")
      {
        REQUIRE(
          new_symbol_table.has_symbol(
            "java::generics$bound_element.f:()Ljava/lang/Number;"
              "<java::java.lang.Integer>"));

        const code_typet &new_code=require_type::require_code_type(
          specialized_method_symbol.type, 1);

        require_type::require_java_non_generic_type(
          new_code.return_type(), {"java::java.lang.Integer"});
      }
    }

    WHEN("A method takes a single generic parameter")
    {
      REQUIRE(
        new_symbol_table.has_symbol(
          "java::generics$bound_element.g:(Ljava/lang/Number;)V"));

      const symbolt &generic_method_symbol=
        new_symbol_table.lookup_ref(
          "java::generics$bound_element.g:(Ljava/lang/Number;)V");

      THEN("When parsing the method")
      {
        const code_typet &code=require_type::require_code_type(
          generic_method_symbol.type, 2);

        require_type::require_java_generic_parameter_variables(
          code.parameters()[1].type(),
          {"java::generics$bound_element::NUM"});
      }

      const symbolt &specialized_method_symbol=instantiate_generic_method(
        generic_method_symbol,
        {
          {"java::generics$bound_element::NUM",
            symbol_typet("java::java.lang.Integer")
          }
        },
        new_symbol_table);

      THEN("When specializing the method with a single concrete type")
      {
        REQUIRE(
          new_symbol_table.has_symbol(
            "java::generics$bound_element.g:(Ljava/lang/Number;)V"
              "<java::java.lang.Integer>"));

        const code_typet &new_code=require_type::require_code_type(
          specialized_method_symbol.type, 2);

        require_type::require_java_non_generic_type(
          new_code.parameters()[1].type(), {"java::java.lang.Integer"});
      }
    }

    WHEN("A method takes two generic parameters")
    {
      REQUIRE(
        new_symbol_table.has_symbol(
          "java::generics$double_element.insert:"
            "(Ljava/lang/Object;Ljava/lang/Object;)V"));

      const symbolt &generic_method_symbol=
        new_symbol_table.lookup_ref(
          "java::generics$double_element.insert:"
            "(Ljava/lang/Object;Ljava/lang/Object;)V");

      THEN("When parsing the method")
      {
        const code_typet &code=require_type::require_code_type(
          generic_method_symbol.type, 3);

        require_type::require_java_generic_parameter_variables(
          code.parameters()[1].type(),
          {"java::generics$double_element::A"});

        require_type::require_java_generic_parameter_variables(
          code.parameters()[2].type(),
          {"java::generics$double_element::B"});
      }

      const symbolt &specialized_method=instantiate_generic_method(
        generic_method_symbol,
        {
          {"java::generics$double_element::A",
            symbol_typet("java::java.lang.Integer")
          },
          {"java::generics$double_element::B",
            symbol_typet("java::java.lang.Double")
          }
        },
        new_symbol_table);

      THEN("When specializing the method with two concrete types")
      {
        REQUIRE(
          new_symbol_table.has_symbol(
            "java::generics$double_element.insert:"
              "(Ljava/lang/Object;Ljava/lang/Object;)V"
              "<java::java.lang.Integer,java::java.lang.Double>"));

        const code_typet &new_code=require_type::require_code_type(
          specialized_method.type, 3);

        require_type::require_java_non_generic_type(
          new_code.parameters()[1].type(), {"java::java.lang.Integer"});

        require_type::require_java_non_generic_type(
          new_code.parameters()[2].type(), {"java::java.lang.Double"});
      }


      WHEN(
        "A method takes a single argument which is parameterized"
        "on two type variables")
      {
        REQUIRE(
          new_symbol_table.has_symbol(
            "java::generics$double_element.setMap:(Lgenerics$GMap;)V"));

        const symbolt &generic_method_symbol=
          new_symbol_table.lookup_ref(
            "java::generics$double_element.setMap:(Lgenerics$GMap;)V");

        THEN("When parsing the method")
        {
          const code_typet &code=require_type::require_code_type(
            generic_method_symbol.type, 2);

          require_type::require_java_generic_type_variables(
            code.parameters()[1].type(),
            {"java::generics$double_element::A",
             "java::generics$double_element::B"
            });
        }

        const symbolt &specialized_method=instantiate_generic_method(
          generic_method_symbol,
          {
            {"java::generics$double_element::A",
              symbol_typet("java::java.lang.Integer")
            },
            {"java::generics$double_element::B",
              symbol_typet("java::java.lang.Double")
            }
          },
          new_symbol_table);

        THEN("When specializing the method with two concrete types")
        {
          REQUIRE(
            new_symbol_table.has_symbol(
              "java::generics$double_element.setMap:(Lgenerics$GMap;)V"
                "<java::java.lang.Integer,java::java.lang.Double>"));

          REQUIRE(new_symbol_table.has_symbol(
            "java::generics$GMap"
              "<java::java.lang.Integer,java::java.lang.Double>"));

          const symbolt &new_param_type=new_symbol_table.lookup_ref(
            "java::generics$GMap"
              "<java::java.lang.Integer,java::java.lang.Double>");

          const code_typet &new_code=require_type::require_code_type(
            specialized_method.type, 2);

          REQUIRE(new_code.parameters()[1].type()==new_param_type.type);
        }
      }

      WHEN(
        "A method takes a single argument which is parameterized"
        "on a single type variable")
      {
        REQUIRE(
          new_symbol_table.has_symbol(
            "java::generics$compound_element."
              "setFixedElem:(Lgenerics$GList;)V"));

        const symbolt &generic_method_symbol=
          new_symbol_table.lookup_ref(
            "java::generics$compound_element.setFixedElem:(Lgenerics$GList;)V");

        THEN("When parsing the method")
        {
          const code_typet &code=require_type::require_code_type(
            generic_method_symbol.type, 2);

          require_type::require_java_generic_type_instantiations(
            code.parameters()[1].type(),
            {"java::java.lang.Integer"});
        }

        const symbolt &specialized_method=instantiate_generic_method(
          generic_method_symbol,
          {
            {"java::generics$compound_element::B",
              symbol_typet("java::java.lang.Integer")
            }
          },
          new_symbol_table);

        THEN("When specializing the method with a concrete type")
        {
          REQUIRE(
            new_symbol_table.has_symbol(
              "java::generics$compound_element.setFixedElem:(Lgenerics$GList;)V"
                "<java::java.lang.Integer>"));

          const code_typet &new_code=require_type::require_code_type(
            specialized_method.type, 2);

          REQUIRE(new_symbol_table.has_symbol(
            "java::generics$GList<java::java.lang.Integer>"));

          const symbolt &new_param_type=new_symbol_table.lookup_ref(
            "java::generics$GList<java::java.lang.Integer>");

          REQUIRE(new_code.parameters()[1].type()==new_param_type.type);
        }
      }

      WHEN(
        "A method returns a type which is parameterized on a"
        "single type variable")
      {
        REQUIRE(
          new_symbol_table.has_symbol(
            "java::generics$compound_element.getElem:()Lgenerics$GList;"));

        const symbolt &generic_method_symbol=
          new_symbol_table.lookup_ref(
            "java::generics$compound_element.getElem:()Lgenerics$GList;");

        THEN("When parsing the method")
        {
          const code_typet &code=require_type::require_code_type(
            generic_method_symbol.type, 1);

          require_type::require_java_generic_type_variables(
            code.return_type(),
            {"java::generics$compound_element::B"});
        }

        const symbolt &specialized_method_symbol=instantiate_generic_method(
          generic_method_symbol,
          {
            {"java::generics$compound_element::B",
              symbol_typet("java::java.lang.Integer")
            }
          },
          new_symbol_table);

        THEN("When specializing the method with a concrete type")
        {
          REQUIRE(
            new_symbol_table.has_symbol(
              "java::generics$compound_element.getElem:()"
                "Lgenerics$GList;<java::java.lang.Integer>"));

          const code_typet &new_code=require_type::require_code_type(
            specialized_method_symbol.type, 1);

          REQUIRE(new_symbol_table.has_symbol(
            "java::generics$GList<java::java.lang.Integer>"));

          const symbolt &new_param_type=new_symbol_table.lookup_ref(
            "java::generics$GList<java::java.lang.Integer>");

          REQUIRE(new_code.return_type()==new_param_type.type);
        }
      }
    }
  }
}
