/*******************************************************************\

 Module: Unit tests for parsing generic classes

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

#include <catch.hpp>

#include <istream>
#include <memory>

#include <util/config.h>
#include <util/language.h>
#include <util/message.h>
#include <java_bytecode/java_bytecode_language.h>

SCENARIO(
  "java_bytecode_parse_generics",
  "[core][java_bytecode][java_bytecode_parse_generics]")
{
  std::unique_ptr<languaget>java_lang(new_java_bytecode_language());

  // Configure the path loading
  cmdlinet command_line;
  command_line.set(
    "java-cp-include-files",
    "./java_bytecode/java_bytecode_parse_generics");
  config.java.classpath.push_back(
    "./java_bytecode/java_bytecode_parse_generics");

  std::istringstream java_code_stream("ignored");
  null_message_handlert message_handler;

  // Configure the language, load the class files
  java_lang->get_language_options(command_line);
  java_lang->set_message_handler(message_handler);
  java_lang->parse(java_code_stream, "generics.class");
  symbol_tablet new_symbol_table;
  java_lang->typecheck(new_symbol_table, "");
  java_lang->final(new_symbol_table);

  GIVEN("Some class files with Generics")
  {
    WHEN("Parsing a class with type variable")
    {
      REQUIRE(new_symbol_table.has_symbol("java::generics$element"));
      THEN("The symbol type should be generic")
      {
        const symbolt &class_symbol=
          new_symbol_table.lookup("java::generics$element");
        const typet &symbol_type=class_symbol.type;

        REQUIRE(symbol_type.id()==ID_struct);
        class_typet class_type=to_class_type(symbol_type);
        REQUIRE(class_type.is_class());
        java_class_typet java_class_type=to_java_class_type(class_type);
        REQUIRE(is_java_generics_class_type(java_class_type));
        java_generics_class_typet java_generics_class_type=
          to_java_generics_class_type(java_class_type);

        const struct_union_typet::componentt &elem=
          java_generics_class_type.get_component("elem");
        const typet &elem_type=java_class_type.component_type("elem");

        REQUIRE(is_java_generic_parameter(elem_type));

        REQUIRE(java_generics_class_type.generic_types().size()==1);
        THEN("Type variable is named 'E'")
        {
          typet &type_var=java_generics_class_type.generic_types().front();
          REQUIRE(is_java_generic_parameter(type_var));
          java_generic_parametert generic_type_var=
            to_java_generic_parameter(type_var);
          REQUIRE(
            generic_type_var.type_variable().get_identifier()==
            "java::generics$element::E");
          typet &sub_type=generic_type_var.subtype();
          REQUIRE(sub_type.id()==ID_symbol);
          symbol_typet &bound_type=to_symbol_type(sub_type);
          REQUIRE(bound_type.get_identifier()=="java::java.lang.Object");
        }
      }
    }
  }

  GIVEN("Some class files with generic type variable")
  {
    WHEN("Parsing a class with bounded type variable")
    {
      REQUIRE(new_symbol_table.has_symbol("java::generics$bound_element"));
      THEN("The symbol type should be generic")
      {
        const symbolt &class_symbol=
          new_symbol_table.lookup("java::generics$bound_element");
        const typet &symbol_type=class_symbol.type;

        REQUIRE(symbol_type.id()==ID_struct);
        class_typet class_type=to_class_type(symbol_type);
        REQUIRE(class_type.is_class());
        java_class_typet java_class_type=to_java_class_type(class_type);
        REQUIRE(is_java_generics_class_type(java_class_type));
        java_generics_class_typet java_generics_class_type=
          to_java_generics_class_type(java_class_type);
        REQUIRE(java_generics_class_type.generic_types().size()==1);
        typet &type_var=java_generics_class_type.generic_types().front();
        REQUIRE(is_java_generic_parameter(type_var));
        java_generic_parametert generic_type_var=
          to_java_generic_parameter(type_var);

        REQUIRE(
          generic_type_var.type_variable().get_identifier()==
          "java::generics$bound_element::NUM");
        REQUIRE(
          java_generics_class_type_var(0, java_generics_class_type)==
          "java::generics$bound_element::NUM");
        THEN("Bound must be Number")
        {
          typet &sub_type=generic_type_var.subtype();
          REQUIRE(sub_type.id()==ID_symbol);
          symbol_typet &bound_type=to_symbol_type(sub_type);
          REQUIRE(bound_type.get_identifier()=="java::java.lang.Number");
          REQUIRE(
            to_symbol_type(
              java_generics_class_type_bound(0, java_generics_class_type))
            .get_identifier()=="java::java.lang.Number");
        }

        const struct_union_typet::componentt &elem=
          java_generics_class_type.get_component("elem");
        const typet &elem_type=java_class_type.component_type("elem");

        REQUIRE(is_java_generic_parameter(elem_type));
      }
    }
  }

  GIVEN("Some class files with generic type variable")
  {
    WHEN("Parsing a class with bounded type variable")
    {
      REQUIRE(new_symbol_table.has_symbol("java::generics"));

      THEN("The generic fields should be annotated with concrete types")
      {
        const symbolt &class_symbol=new_symbol_table.lookup("java::generics");
        const typet &symbol_type=class_symbol.type;

        REQUIRE(symbol_type.id()==ID_struct);
        class_typet class_type=to_class_type(symbol_type);
        REQUIRE(class_type.is_class());
        java_class_typet java_class_type=to_java_class_type(class_type);
        REQUIRE(!is_java_generics_class_type(java_class_type));

        const struct_union_typet::componentt &belem=
          java_class_type.get_component("belem");
        const typet &belem_type=java_class_type.component_type("belem");

        REQUIRE(belem_type!=nil_typet());
        REQUIRE(is_java_generic_type(belem_type));
        THEN("Field has instantiated type variable")
        {
          const java_generic_typet &container=
            to_java_generic_type(belem_type);

          const std::vector<java_generic_parametert> &generic_types=
            container.generic_type_variables();
          REQUIRE(generic_types.size()==1);

          const typet& inst_type=java_generic_get_inst_type(0, container);

          REQUIRE(inst_type.id()==ID_pointer);
          const typet &inst_type_symbol=inst_type.subtype();
          REQUIRE(inst_type_symbol.id()==ID_symbol);
          REQUIRE(
            to_symbol_type(inst_type_symbol).get_identifier()==
            "java::java.lang.Integer");
        }
      }
    }
  }

  GIVEN("Some class files with Generics")
  {
    WHEN("Methods with generic signatures")
    {
      REQUIRE(
        new_symbol_table
          .has_symbol("java::generics$bound_element.f:()Ljava/lang/Number;"));

      THEN("The method should have generic return type")
      {
        const symbolt &method_symbol=
          new_symbol_table
            .lookup("java::generics$bound_element.f:()Ljava/lang/Number;");
        const typet &symbol_type=method_symbol.type;

        REQUIRE(symbol_type.id()==ID_code);

        const code_typet &code=to_code_type(symbol_type);
      }

      REQUIRE(
        new_symbol_table
          .has_symbol("java::generics$bound_element.g:(Ljava/lang/Number;)V"));

      THEN("The method should have a generic parameter.")
      {
        const symbolt &method_symbol=
          new_symbol_table
            .lookup("java::generics$bound_element.g:(Ljava/lang/Number;)V");
        const typet &symbol_type=method_symbol.type;

        REQUIRE(symbol_type.id()==ID_code);

        const code_typet &code=to_code_type(symbol_type);

        bool found=false;
        for(const auto &p : code.parameters())
        {
          if(p.get_identifier()==
             "java::generics$bound_element.g:(Ljava/lang/Number;)V::e")
          {
            found=true;
            const typet &t=p.type();
            REQUIRE(is_java_generic_parameter(p.type()));
            const java_generic_parametert &gen_type=
              to_java_generic_parameter(p.type());
            const symbol_typet &type_var=gen_type.type_variable();
            REQUIRE(type_var.get_identifier()==
                    "java::generics$bound_element::NUM");
            break;
          }
        }
        REQUIRE(found);
      }
    }
  }
  GIVEN("A class with multiple bounds")
  {
    THEN("The bounds should be encoded")
    {
      REQUIRE(
        new_symbol_table.has_symbol("java::generics$double_bound_element"));
      THEN("The symbol should have a generic parameter")
      {
        const symbolt &class_symbol=
          new_symbol_table.lookup("java::generics$double_bound_element");
        const typet &symbol_type=class_symbol.type;

        REQUIRE(symbol_type.id()==ID_struct);
        class_typet class_type=to_class_type(symbol_type);
        REQUIRE(class_type.is_class());
        java_class_typet java_class_type=to_java_class_type(class_type);
        REQUIRE_FALSE(is_java_generics_class_type(java_class_type));

        // TODO (tkiley): Extend this unit test when bounds are correctly
        // parsed.
#if 0
        java_generics_class_typet java_generics_class_type=
          to_java_generics_class_type(java_class_type);
        REQUIRE(java_generics_class_type.generic_types().size()==1);
        typet &type_var=java_generics_class_type.generic_types().front();
        REQUIRE(is_java_generic_parameter(type_var));
        java_generic_parametert generic_type_var=
          to_java_generic_parameter(type_var);

        REQUIRE(
          generic_type_var.type_variable().get_identifier()==
          "java::generics$double_bound_element::T");
        REQUIRE(
          java_generics_class_type_var(0, java_generics_class_type)==
          "java::generics$double_bound_element::T");
        THEN("Bound must be Number and dummyInterface")
        {

        }
#endif
      }
    }
  }
  GIVEN("A class with multiple generic parameters")
  {
    THEN("Both generic parameters should be encoded")
    {
      const symbolt &class_symbol=
        new_symbol_table.lookup("java::generics$two_elements");
      const typet &symbol_type=class_symbol.type;

      REQUIRE(symbol_type.id()==ID_struct);
      class_typet class_type=to_class_type(symbol_type);
      REQUIRE(class_type.is_class());
      java_class_typet java_class_type=to_java_class_type(class_type);
      REQUIRE(is_java_generics_class_type(java_class_type));

      java_generics_class_typet java_generics_class_type=
        to_java_generics_class_type(java_class_type);
      REQUIRE(java_generics_class_type.generic_types().size()==2);

      auto generic_param_iterator=
        java_generics_class_type.generic_types().cbegin();

      // The first parameter should be called K
      {
        const typet &first_param=*generic_param_iterator;
        REQUIRE(is_java_generic_parameter(first_param));
        java_generic_parametert generic_type_var=
          to_java_generic_parameter(first_param);

        REQUIRE(
          generic_type_var.type_variable().get_identifier()==
          "java::generics$two_elements::K");
        REQUIRE(
          java_generics_class_type_var(0, java_generics_class_type)==
          "java::generics$two_elements::K");
      }

      ++generic_param_iterator;


      // The second parameter should be called V
      {
        const typet &second_param=*generic_param_iterator;
        REQUIRE(is_java_generic_parameter(second_param));
        java_generic_parametert generic_type_var=
          to_java_generic_parameter(second_param);

        REQUIRE(
          generic_type_var.type_variable().get_identifier()==
          "java::generics$two_elements::V");
        REQUIRE(
          java_generics_class_type_var(1, java_generics_class_type)==
          "java::generics$two_elements::V");
      }
    }
  }
}
