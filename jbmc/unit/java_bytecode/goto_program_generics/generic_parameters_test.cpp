/*******************************************************************\

Module: Unit tests for instantiating generic classes.

Author: Diffblue Ltd.

\*******************************************************************/
#include <java-testing-utils/load_java_class.h>
#include <java-testing-utils/require_goto_statements.h>
#include <java-testing-utils/require_type.h>
#include <testing-utils/require_symbol.h>
#include <testing-utils/use_catch.h>
#include <util/config.h>

// NOTE: To inspect these tests at any point, use expr2java.
// A good way to verify the validity of a test is to iterate
// through all the entry point instructions and print them
// with expr2java.

SCENARIO(
  "Instantiate generic parameters to methods or fields used within",
  "[core][goto_program_generics][generic_parameters_test]")
{
  config.ansi_c.set_LP64();

  GIVEN("A class with a generic field")
  {
    const symbol_tablet &symbol_table = load_java_class(
      "GenericFields$SimpleGenericField",
      "./java_bytecode/goto_program_generics",
      "GenericFields$SimpleGenericField.foo");

    WHEN("The method input argument is created in the entry point function")
    {
      const std::vector<codet> &entry_point_code =
        require_goto_statements::require_entry_point_statements(symbol_table);

      // We trace the creation of the object that is being supplied as
      // the input to the method under test. There must be one non-null
      // assignment only, and usually looks like this:
      //   this = &tmp_object_factory$1;
      const irep_idt &tmp_object_name =
        require_goto_statements::require_entry_point_argument_assignment(
          ID_this, entry_point_code);

      THEN("Object 'this' has field 'field_input' of type Wrapper")
      {
        const auto &field_input_name =
          require_goto_statements::require_struct_component_assignment(
            tmp_object_name,
            {},
            "field_input",
            "java::Wrapper",
            {},
            entry_point_code,
            symbol_table);

        THEN("Object 'field_input' has field 'field' of type IWrapper")
        {
          require_goto_statements::require_struct_component_assignment(
            field_input_name,
            {},
            "field",
            "java::IWrapper",
            {},
            entry_point_code,
            symbol_table);
        }
        THEN("Object 'field_input' has field 'array_field' of type IWrapper[]")
        {
          require_goto_statements::require_struct_array_component_assignment(
            field_input_name,
            {},
            "array_field",
            JAVA_REFERENCE_ARRAY_CLASSID,
            entry_point_code,
            symbol_table);
        }
      }
    }
  }

  GIVEN("A class with multiple generic fields")
  {
    const symbol_tablet &symbol_table = load_java_class(
      "GenericFields$MultipleGenericFields",
      "./java_bytecode/goto_program_generics",
      "GenericFields$MultipleGenericFields.foo");

    WHEN("The method input argument is created in the entry point function")
    {
      // Again, the logic here is the same as the first test:
      // We trace the this pointer, which is the input to the
      // function we have provided as the entry point, and we
      // try to trace it down to its components, to make sure that
      // the specific fields we are interested in belong to a class with the
      // expected type, and that they behave to the expected type protocol
      // themselves.
      const std::vector<codet> &entry_point_code =
        require_goto_statements::require_entry_point_statements(symbol_table);

      // The this pointer will be assigned to the object whose class is the
      // type we are looking for, and that contains the fields we are looking
      // for, so we need to extract its identifier, and start looking for that.
      const auto &tmp_object_name =
        require_goto_statements::require_entry_point_argument_assignment(
          ID_this, entry_point_code);

      THEN("Type of multiple generic fields should be right")
      {
        const typet &class_type =
          symbol_table.lookup_ref("java::GenericFields$MultipleGenericFields")
            .type;

        const auto &component = require_type::require_component(
          to_java_class_type(class_type), "field_input2");

        const java_generic_typet &type =
          require_type::require_java_generic_type(component.type());
        require_type::require_pointer(
          type.generic_type_arguments()[0], struct_tag_typet{"java::BWrapper"});
      }

      THEN("Object 'this' has field 'field_input1' of type Wrapper")
      {
        const auto &field_input1_name =
          require_goto_statements::require_struct_component_assignment(
            tmp_object_name,
            {},
            "field_input1",
            "java::Wrapper",
            {},
            entry_point_code,
            symbol_table);

        THEN("Object 'field_input1' has field 'field' of type IWrapper")
        {
          require_goto_statements::require_struct_component_assignment(
            field_input1_name,
            {},
            "field",
            "java::IWrapper",
            {},
            entry_point_code,
            symbol_table);
        }
      }

      THEN("Object 'this' has field 'field_input2' of type Wrapper")
      {
        const auto &field_input2_name =
          require_goto_statements::require_struct_component_assignment(
            tmp_object_name,
            {},
            "field_input2",
            "java::Wrapper",
            {},
            entry_point_code,
            symbol_table);

        THEN("Object 'field_input2' has field 'field' of type BWrapper")
        {
          require_goto_statements::require_struct_component_assignment(
            field_input2_name,
            {},
            "field",
            "java::BWrapper",
            {},
            entry_point_code,
            symbol_table);
        }
      }
    }
  }

  GIVEN("A class with a nested generic field")
  {
    const symbol_tablet &symbol_table = load_java_class(
      "GenericFields$NestedGenericFields",
      "./java_bytecode/goto_program_generics",
      "GenericFields$NestedGenericFields.foo");

    WHEN("The method input argument is created in the entry point function")
    {
      // Same idea as in the other tests: Start tracing the expected types,
      // starting from the this pointer, which symbolises the input object for
      // the function we have denoted as our entry point above.
      const std::vector<codet> &entry_point_code =
        require_goto_statements::require_entry_point_statements(symbol_table);

      const auto &tmp_object_name =
        require_goto_statements::require_entry_point_argument_assignment(
          ID_this, entry_point_code);

      THEN("Object 'this' has field 'field_input1' of type Wrapper")
      {
        const auto &field_input1_name =
          require_goto_statements::require_struct_component_assignment(
            tmp_object_name,
            {},
            "field_input1",
            "java::Wrapper",
            {},
            entry_point_code,
            symbol_table);

        THEN("Object 'field_input1' has field 'field' of type Wrapper")
        {
          const auto &field_name =
            require_goto_statements::require_struct_component_assignment(
              field_input1_name,
              {},
              "field",
              "java::Wrapper",
              {},
              entry_point_code,
              symbol_table);

          THEN("Object 'field' has field 'field' of type IWrapper")
          {
            require_goto_statements::require_struct_component_assignment(
              field_name,
              {},
              "field",
              "java::IWrapper",
              {},
              entry_point_code,
              symbol_table);
          }
        }
      }
    }
  }

  GIVEN("A class with a pair generic field")
  {
    const symbol_tablet &symbol_table = load_java_class(
      "GenericFields$PairGenericField",
      "./java_bytecode/goto_program_generics",
      "GenericFields$PairGenericField.foo");

    WHEN("The method input argument is created in the entry point function")
    {
      // For an explanation of this part, look at the comments for the similar
      // parts of the previous tests.
      const std::vector<codet> &entry_point_code =
        require_goto_statements::require_entry_point_statements(symbol_table);

      const auto &tmp_object_name =
        require_goto_statements::require_entry_point_argument_assignment(
          ID_this, entry_point_code);

      THEN("Object 'this' has field 'field_input' of type PairWrapper")
      {
        const auto &field_input_name =
          require_goto_statements::require_struct_component_assignment(
            tmp_object_name,
            {},
            "field_input",
            "java::PairWrapper",
            {},
            entry_point_code,
            symbol_table);

        THEN("Object 'field_input' has field 'key' of type IWrapper")
        {
          require_goto_statements::require_struct_component_assignment(
            field_input_name,
            {},
            "first",
            "java::IWrapper",
            {},
            entry_point_code,
            symbol_table);
        }

        THEN("Object 'field_input' has field 'value' of type IWrapper")
        {
          require_goto_statements::require_struct_component_assignment(
            field_input_name,
            {},
            "second",
            "java::IWrapper",
            {},
            entry_point_code,
            symbol_table);
        }
      }
    }
  }

  GIVEN("A class with a method that accepts a generic type parameter")
  {
    const symbol_tablet &symbol_table = load_java_class(
      "GenericFields$GenericMethodParameter",
      "./java_bytecode/goto_program_generics",
      "GenericFields$GenericMethodParameter.foo");

    WHEN("The method input argument is created in the entry point function")
    {
      // For an explanation of this part, look at the comments for the similar
      // parts of the previous tests.
      const std::vector<codet> &entry_point_code =
        require_goto_statements::require_entry_point_statements(symbol_table);

      // Instead of the this pointer, we need to trace the "v" pointer, which
      // is the name of the pointer of the object that gets passed as a
      // parameter to the function.
      const auto &tmp_object_name =
        require_goto_statements::require_entry_point_argument_assignment(
          "v", entry_point_code);

      THEN("Object 'v' is of type Wrapper")
      {
        const auto &tmp_object_declaration =
          require_goto_statements::require_declaration_of_name(
            tmp_object_name, entry_point_code);

        // Trace the assignments back to the declaration of the generic type
        // and verify that it is what we expect.
        const auto &tmp_object_struct_tag = to_struct_tag_type(
          to_pointer_type(tmp_object_declaration.symbol().type()).base_type());
        REQUIRE(tmp_object_struct_tag.get_identifier() == "java::Wrapper");

        THEN("Object 'v' has field 'field' of type IWrapper")
        {
          require_goto_statements::require_struct_component_assignment(
            tmp_object_name,
            {},
            "field",
            "java::IWrapper",
            {},
            entry_point_code,
            symbol_table);
        }
      }
    }
  }

  GIVEN(
    "A class with a method that accepts a generic uninstantiated type "
    "parameter")
  {
    const symbol_tablet &symbol_table = load_java_class(
      "GenericFields$GenericMethodUninstantiatedParameter",
      "./java_bytecode/goto_program_generics",
      "GenericFields$GenericMethodUninstantiatedParameter.foo_unspec");

    WHEN("The method input argument is created in the entry point function")
    {
      // For an explanation of this part, look at the comments for the similar
      // parts of the previous tests.
      const std::vector<codet> &entry_point_code =
        require_goto_statements::require_entry_point_statements(symbol_table);

      // Instead of the this pointer, we need to trace the "v" pointer, which
      // is the name of the pointer of the object that gets passed as a
      // parameter to the function.
      const auto &tmp_object_name =
        require_goto_statements::require_entry_point_argument_assignment(
          "v", entry_point_code);

      THEN("Object 'v' is of type Wrapper")
      {
        const auto &tmp_object_declaration =
          require_goto_statements::require_declaration_of_name(
            tmp_object_name, entry_point_code);

        // Trace the assignments back to the declaration of the generic type
        // and verify that it is what we expect.
        const auto &tmp_object_struct_tag = to_struct_tag_type(
          to_pointer_type(tmp_object_declaration.symbol().type()).base_type());
        REQUIRE(tmp_object_struct_tag.get_identifier() == "java::Wrapper");

        THEN(
          "Object 'v' has field 'field' of type Object (upper bound of the "
          "uninstantiated parameter T)")
        {
          require_goto_statements::require_struct_component_assignment(
            tmp_object_name,
            {},
            "field",
            "java::java.lang.Object",
            {},
            entry_point_code,
            symbol_table);
        }
      }
    }
  }

  GIVEN("A generic class with an inner class (implicitly generic)")
  {
    const symbol_tablet &symbol_table = load_java_class(
      "GenericFields$GenericInnerOuter",
      "./java_bytecode/goto_program_generics",
      "GenericFields$GenericInnerOuter.foo");

    WHEN("The method input argument is created in the entry point function")
    {
      // For an explanation of this part, look at the comments for the similar
      // parts of the previous tests.
      const std::vector<codet> &entry_point_code =
        require_goto_statements::require_entry_point_statements(symbol_table);

      // Instead of the this pointer, we need to trace the "v" pointer, which
      // is the name of the pointer of the object that gets passed as a
      // parameter to the function.
      const auto &tmp_object_name =
        require_goto_statements::require_entry_point_argument_assignment(
          "v", entry_point_code);

      THEN("Object 'v' is of type Outer")
      {
        const auto &tmp_object_declaration =
          require_goto_statements::require_declaration_of_name(
            tmp_object_name, entry_point_code);

        // Trace the assignments back to the declaration of the generic type
        // and verify that it is what we expect.
        const auto &tmp_object_struct_tag = to_struct_tag_type(
          to_pointer_type(tmp_object_declaration.symbol().type()).base_type());
        REQUIRE(
          tmp_object_struct_tag.get_identifier() ==
          "java::GenericFields$GenericInnerOuter$Outer");

        THEN("Object 'v' has field 'field' of type InnerClass")
        {
          const auto &field_tmp_name =
            require_goto_statements::require_struct_component_assignment(
              tmp_object_name,
              {},
              "field",
              "java::GenericFields$GenericInnerOuter$Outer$InnerClass",
              {},
              entry_point_code,
              symbol_table);

          THEN("Object 'field' has field 't' of type Integer")
          {
            require_goto_statements::require_struct_component_assignment(
              field_tmp_name,
              {},
              "t",
              "java::java.lang.Integer",
              {},
              entry_point_code,
              symbol_table);
          }
        }
      }
    }
  }

  GIVEN(
    "A generic class that instantiates its parameter with different type "
    "in different scope depth")
  {
    const symbol_tablet &symbol_table = load_java_class(
      "GenericFields$GenericRewriteParameter",
      "./java_bytecode/goto_program_generics",
      "GenericFields$GenericRewriteParameter.foo");

    WHEN("The method input argument is created in the entry point function")
    {
      // For an explanation of this part, look at the comments for the similar
      // parts of the previous tests.
      const std::vector<codet> &entry_point_code =
        require_goto_statements::require_entry_point_statements(symbol_table);

      // Instead of the this pointer, we need to trace the "v" pointer, which
      // is the name of the pointer of the object that gets passed as a
      // parameter to the function.
      const auto &tmp_object_name =
        require_goto_statements::require_entry_point_argument_assignment(
          "v", entry_point_code);

      THEN("Object 'v' is of type A")
      {
        const auto &tmp_object_declaration =
          require_goto_statements::require_declaration_of_name(
            tmp_object_name, entry_point_code);

        // Trace the assignments back to the declaration of the generic type
        // and verify that it is what we expect.
        const auto &tmp_object_struct_tag = to_struct_tag_type(
          to_pointer_type(tmp_object_declaration.symbol().type()).base_type());
        REQUIRE(
          tmp_object_struct_tag.get_identifier() ==
          "java::GenericFields$GenericRewriteParameter$A");

        THEN("Object 'v' has field 'value' of type Integer")
        {
          require_goto_statements::require_struct_component_assignment(
            tmp_object_name,
            {},
            "value",
            "java::java.lang.Integer",
            {},
            entry_point_code,
            symbol_table);
        }

        THEN("Object 'v' has field 'field' of type A")
        {
          const auto &field_tmp_name =
            require_goto_statements::require_struct_component_assignment(
              tmp_object_name,
              {},
              "field",
              "java::GenericFields$GenericRewriteParameter$A",
              {},
              entry_point_code,
              symbol_table);

          THEN("Object 'field' has field 'value' of type Boolean")
          {
            require_goto_statements::require_struct_component_assignment(
              field_tmp_name,
              {},
              "value",
              "java::java.lang.Boolean",
              {},
              entry_point_code,
              symbol_table);
          }
        }
      }
    }
  }
}

SCENARIO(
  "Ignore generic parameters in fields and methods with incomplete and "
  "non-generic types",
  "[core][goto_program_generics][generic_parameters_test]")
{
  GIVEN(
    "A class with a generic field pointing to a class with unsupported "
    "signature (thus not marked as generic)")
  {
    const symbol_tablet &symbol_table = load_java_class(
      "GenericFieldUnsupported",
      "./java_bytecode/goto_program_generics",
      "GenericFieldUnsupported.foo");

    THEN("The struct for UnsupportedWrapper2 is complete and non-generic")
    {
      const std::string field_class_name = "java::UnsupportedWrapper2";
      const symbolt &superclass_symbol =
        require_symbol::require_symbol_exists(symbol_table, field_class_name);

      require_type::require_complete_java_non_generic_class(
        superclass_symbol.type);
    }

    WHEN("The method input argument is created in the entry point function")
    {
      // We trace the creation of the object that is being supplied as
      // the input to the method under test. There must be one non-null
      // assignment only, and usually looks like this:
      //   this = &tmp_object_factory$1;
      const std::vector<codet> &entry_point_code =
        require_goto_statements::require_entry_point_statements(symbol_table);

      const irep_idt &tmp_object_name =
        require_goto_statements::require_entry_point_argument_assignment(
          ID_this, entry_point_code);

      THEN("Object 'this' has field 'f' of type UnsupportedWrapper2")
      {
        // tmp_object_factory$1.f = &tmp_object_factory$2;
        // struct UnsupportedWrapper2 { struct java.lang.Object
        //   @java.lang.Object; struct java.lang.Object *field; }
        //   tmp_object_factory$2;
        const auto &field_input_name =
          require_goto_statements::require_struct_component_assignment(
            tmp_object_name,
            {},
            "f",
            "java::UnsupportedWrapper2",
            {},
            entry_point_code,
            symbol_table);

        THEN("Object 'f' has unspecialized field 'field'")
        {
          // tmp_object_factory$2.field = &tmp_object_factory$3;
          // struct java.lang.Object { __CPROVER_string @class_identifier; }
          // tmp_object_factory$3;
          require_goto_statements::require_struct_component_assignment(
            field_input_name,
            {},
            "field",
            "java::java.lang.Object",
            {},
            entry_point_code,
            symbol_table);
        }
      }
    }
  }

  GIVEN(
    "A class with a generic field pointing to a mocked class (thus "
    "incomplete and not marked as generic)")
  {
    const symbol_tablet &symbol_table = load_java_class(
      "GenericFieldOpaque",
      "./java_bytecode/goto_program_generics",
      "GenericFieldOpaque.foo");

    THEN("The struct for OpaqueWrapper is incomplete and not-generic")
    {
      const std::string field_class_name = "java::OpaqueWrapper";
      const symbolt &field_class_symbol =
        require_symbol::require_symbol_exists(symbol_table, field_class_name);

      require_type::require_incomplete_class(field_class_symbol.type);
      require_type::require_java_non_generic_class(field_class_symbol.type);
    }

    WHEN("The method input argument is created in the entry point function")
    {
      // For an explanation of this part, look at the comments for the similar
      // parts of the previous tests.
      const std::vector<codet> &entry_point_code =
        require_goto_statements::require_entry_point_statements(symbol_table);

      const irep_idt &tmp_object_name =
        require_goto_statements::require_entry_point_argument_assignment(
          ID_this, entry_point_code);

      THEN("Object 'this' has field 'f' of type OpaqueWrapper")
      {
        const auto &field_input_name =
          require_goto_statements::require_struct_component_assignment(
            tmp_object_name,
            {},
            "f",
            "java::OpaqueWrapper",
            {},
            entry_point_code,
            symbol_table);

        THEN("Object 'f' has unspecialized field 'field'")
        {
          require_goto_statements::require_struct_component_assignment(
            field_input_name,
            {},
            "field",
            "java::java.lang.Object",
            {},
            entry_point_code,
            symbol_table);
        }
      }
    }
  }
}
