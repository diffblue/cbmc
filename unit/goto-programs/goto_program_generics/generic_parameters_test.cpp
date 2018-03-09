/*******************************************************************\

 Module: Unit tests for instantiating generic classes.

 Author: Diffblue Ltd.

\*******************************************************************/
#include <testing-utils/catch.hpp>
#include <testing-utils/load_java_class.h>
#include <testing-utils/require_goto_statements.h>
#include <util/config.h>

// NOTE: To inspect these tests at any point, use expr2java.
// A good way to verify the validity of a test is to iterate
// through all the entry point instructions and print them
// with expr2java.

SCENARIO(
  "Instantiate generic parameters to methods or fields used within",
  "[core][goto_program_generics][generic_parameters_test]")
{
  GIVEN("A class with a generic field")
  {
    const symbol_tablet &symbol_table = load_java_class(
      "GenericFields$SimpleGenericField",
      "./goto-programs/goto_program_generics",
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
          "this", entry_point_code);

      THEN("Object 'this' has field 'field_input' of type SimpleWrapper")
      {
        const auto &field_input_name =
          require_goto_statements::require_struct_component_assignment(
            tmp_object_name,
            {},
            "field_input",
            "java::SimpleWrapper",
            {},
            entry_point_code);

        THEN("Object 'field_input' has field 'field' of type IWrapper")
        {
          require_goto_statements::require_struct_component_assignment(
            field_input_name,
            {},
            "field",
            "java::IWrapper",
            {},
            entry_point_code);
        }
        THEN("Object 'field_input' has field 'array_field' of type IWrapper[]")
        {
          require_goto_statements::require_struct_array_component_assignment(
            field_input_name,
            {},
            "array_field",
            "java::array[reference]",
            "java::IWrapper",
            entry_point_code);
        }
      }
    }
  }

  GIVEN("A class with multiple generic fields")
  {
    const symbol_tablet &symbol_table = load_java_class(
      "GenericFields$MultipleGenericFields",
      "./goto-programs/goto_program_generics",
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
          "this", entry_point_code);

      THEN("Object 'this' has field 'field_input1' of type SimpleWrapper")
      {
        const auto &field_input1_name =
          require_goto_statements::require_struct_component_assignment(
            tmp_object_name,
            {},
            "field_input1",
            "java::SimpleWrapper",
            {},
            entry_point_code);

        THEN("Object 'field_input1' has field 'field' of type IWrapper")
        {
          require_goto_statements::require_struct_component_assignment(
            field_input1_name,
            {},
            "field",
            "java::IWrapper",
            {},
            entry_point_code);
        }
      }

      THEN("Object 'this' has field 'field_input2' of type SimpleWrapper")
      {
        const auto &field_input2_name =
          require_goto_statements::require_struct_component_assignment(
            tmp_object_name,
            {},
            "field_input2",
            "java::SimpleWrapper",
            {},
            entry_point_code);

        THEN("Object 'field_input1' has field 'field' of type IWrapper")
        {
          require_goto_statements::require_struct_component_assignment(
            field_input2_name,
            {},
            "field",
            "java::IWrapper",
            {},
            entry_point_code);
        }
      }
    }
  }

  GIVEN("A class with a nested generic field")
  {
    const symbol_tablet &symbol_table = load_java_class(
      "GenericFields$NestedGenericFields",
      "./goto-programs/goto_program_generics",
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
          "this", entry_point_code);

      THEN("Object 'this' has field 'field_input1' of type SimpleWrapper")
      {
        const auto &field_input1_name =
          require_goto_statements::require_struct_component_assignment(
            tmp_object_name,
            {},
            "field_input1",
            "java::SimpleWrapper",
            {},
            entry_point_code);

        THEN("Object 'field_input1' has field 'field' of type SimpleWrapper")
        {
          const auto &field_name =
            require_goto_statements::require_struct_component_assignment(
              field_input1_name,
              {},
              "field",
              "java::SimpleWrapper",
              {},
              entry_point_code);

          THEN("Object 'field' has field 'field' of type IWrapper")
          {
            require_goto_statements::require_struct_component_assignment(
              field_name, {}, "field", "java::IWrapper", {}, entry_point_code);
          }
        }
      }
    }
  }

  GIVEN("A class with a pair generic field")
  {
    const symbol_tablet &symbol_table = load_java_class(
      "GenericFields$PairGenericField",
      "./goto-programs/goto_program_generics",
      "GenericFields$PairGenericField.foo");

    WHEN("The method input argument is created in the entry point function")
    {
      // For an explanation of this part, look at the comments for the similar
      // parts of the previous tests.
      const std::vector<codet> &entry_point_code =
        require_goto_statements::require_entry_point_statements(symbol_table);

      const auto &tmp_object_name =
        require_goto_statements::require_entry_point_argument_assignment(
          "this", entry_point_code);

      THEN("Object 'this' has field 'field_input' of type PairWrapper")
      {
        const auto &field_input_name =
          require_goto_statements::require_struct_component_assignment(
            tmp_object_name,
            {},
            "field_input",
            "java::PairWrapper",
            {},
            entry_point_code);

        THEN("Object 'field_input' has field 'key' of type IWrapper")
        {
          require_goto_statements::require_struct_component_assignment(
            field_input_name,
            {},
            "key",
            "java::IWrapper",
            {},
            entry_point_code);
        }

        THEN("Object 'field_input' has field 'value' of type IWrapper")
        {
          require_goto_statements::require_struct_component_assignment(
            field_input_name,
            {},
            "value",
            "java::IWrapper",
            {},
            entry_point_code);
        }
      }
    }
  }

  GIVEN("A class with a method that accepts a generic type parameter")
  {
    const symbol_tablet &symbol_table = load_java_class(
      "GenericFields$GenericMethodParameter",
      "./goto-programs/goto_program_generics",
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

      THEN("Object 'v' is of type SimpleWrapper")
      {
        const auto &tmp_object_declaration =
          require_goto_statements::require_declaration_of_name(
            tmp_object_name, entry_point_code);

        // Trace the assignments back to the declaration of the generic type
        // and verify that it is what we expect.
        const auto &tmp_object_struct =
          to_struct_type(tmp_object_declaration.symbol().type());
        REQUIRE(tmp_object_struct.get_tag() == "SimpleWrapper");

        THEN("Object 'v' has field 'field' of type IWrapper")
        {
          require_goto_statements::require_struct_component_assignment(
            tmp_object_name,
            {},
            "field",
            "java::IWrapper",
            {},
            entry_point_code);
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
      "./goto-programs/goto_program_generics",
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

      THEN("Object 'v' is of type SimpleWrapper")
      {
        const auto &tmp_object_declaration =
          require_goto_statements::require_declaration_of_name(
            tmp_object_name, entry_point_code);

        // Trace the assignments back to the declaration of the generic type
        // and verify that it is what we expect.
        const auto &tmp_object_struct =
          to_struct_type(tmp_object_declaration.symbol().type());
        REQUIRE(tmp_object_struct.get_tag() == "SimpleWrapper");

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
            entry_point_code);
        }
      }
    }
  }

  GIVEN("A generic class with an inner class (implicitly generic)")
  {
    const symbol_tablet &symbol_table = load_java_class(
      "GenericFields$GenericInnerOuter",
      "./goto-programs/goto_program_generics",
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
        const auto &tmp_object_struct =
          to_struct_type(tmp_object_declaration.symbol().type());
        REQUIRE(
          tmp_object_struct.get_tag() ==
          "GenericFields$GenericInnerOuter$Outer");

        THEN("Object 'v' has field 'field' of type InnerClass")
        {
          const auto &field_tmp_name =
            require_goto_statements::require_struct_component_assignment(
              tmp_object_name,
              {},
              "field",
              "java::GenericFields$GenericInnerOuter$Outer$InnerClass",
              {},
              entry_point_code);

          THEN("Object 'field' has field 't' of type Integer")
          {
            require_goto_statements::require_struct_component_assignment(
              field_tmp_name,
              {},
              "t",
              "java::java.lang.Integer",
              {},
              entry_point_code);
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
      "./goto-programs/goto_program_generics",
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
        const auto &tmp_object_struct =
          to_struct_type(tmp_object_declaration.symbol().type());
        REQUIRE(
          tmp_object_struct.get_tag() ==
          "GenericFields$GenericRewriteParameter$A");

        THEN("Object 'v' has field 'value' of type Integer")
        {
          require_goto_statements::require_struct_component_assignment(
            tmp_object_name,
            {},
            "value",
            "java::java.lang.Integer",
            {},
            entry_point_code);
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
              entry_point_code);

          THEN("Object 'field' has field 'value' of type Boolean")
          {
            require_goto_statements::require_struct_component_assignment(
              field_tmp_name,
              {},
              "value",
              "java::java.lang.Boolean",
              {},
              entry_point_code);
          }
        }
      }
    }
  }
}
