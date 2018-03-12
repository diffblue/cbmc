/*******************************************************************\

 Module: Unit tests for instantiating generic superclasses and interfaces.

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
  "Instantiate generic parameters of superclasses",
  "[core][goto_program_generics][generic_bases_test]")
{
  GIVEN(
    "A class extending a generic class instantiated with a standard library "
    "class")
  {
    const symbol_tablet &symbol_table = load_java_class(
      "SuperclassInst",
      "./goto-programs/goto_program_generics",
      "SuperclassInst.foo");

    WHEN("The method input argument is created in the entry point function")
    {
      const std::vector<codet> &entry_point_code =
        require_goto_statements::require_entry_point_statements(symbol_table);

      // We trace the creation of the object that is being supplied as
      // the input to the method under test. There must be one non-null
      // assignment only, and usually looks like this:
      //   this = &tmp_object_factory$1;
      const irep_idt &this_tmp_name =
        require_goto_statements::require_entry_point_argument_assignment(
          "this", entry_point_code);

      THEN("Object 'this' created has correctly specialized inherited field")
      {
        // The following checks that the superclass field gets assigned an
        // object of a correct type, e.g.:
        //  tmp_object_factory$1.@Wrapper.field =
        //     (struct java.lang.Object *) tmp_object_factory$2;
        //  tmp_object_factory$2 = &tmp_object_factory$3;
        //  struct java.lang.Integer { __CPROVER_string @class_identifier;
        //     boolean @lock; } tmp_object_factory$3;
        require_goto_statements::require_struct_component_assignment(
          this_tmp_name,
          {"Wrapper"},
          "field",
          "java::java.lang.Integer",
          {"java::java.lang.Object"},
          entry_point_code);
      }
    }
  }

  GIVEN(
    "A class extending a generic class instantiated with a user-defined class")
  {
    const symbol_tablet &symbol_table = load_java_class(
      "SuperclassInst2",
      "./goto-programs/goto_program_generics",
      "SuperclassInst2.foo");

    WHEN("The method input argument is created in the entry point function")
    {
      const std::vector<codet> &entry_point_code =
        require_goto_statements::require_entry_point_statements(symbol_table);

      // For an explanation of this part, look at the comments for the similar
      // parts of the previous tests.
      const auto &this_tmp_name =
        require_goto_statements::require_entry_point_argument_assignment(
          "this", entry_point_code);

      THEN("Object 'this' has correctly specialized inherited field")
      {
        require_goto_statements::require_struct_component_assignment(
          this_tmp_name,
          {"Wrapper"},
          "field",
          "java::IntWrapper",
          {"java::java.lang.Object"},
          entry_point_code);
      }
    }
  }

  GIVEN("A class extending an instantiated nested generic class")
  {
    const symbol_tablet &symbol_table = load_java_class(
      "SuperclassInst3",
      "./goto-programs/goto_program_generics",
      "SuperclassInst3.foo");

    WHEN("The method input argument is created in the entry point function")
    {
      const std::vector<codet> &entry_point_code =
        require_goto_statements::require_entry_point_statements(symbol_table);

      // For an explanation of this part, look at the comments for the similar
      // parts of the previous tests.
      const auto &this_tmp_name =
        require_goto_statements::require_entry_point_argument_assignment(
          "this", entry_point_code);

      THEN("Object 'this' has correctly specialized inherited field")
      {
        const irep_idt &wrapper_tmp_name =
          require_goto_statements::require_struct_component_assignment(
            this_tmp_name,
            {"Wrapper"},
            "field",
            "java::Wrapper",
            {"java::java.lang.Object"},
            entry_point_code);

        THEN("Object 'this.field' has correctly specialized field")
        {
          require_goto_statements::require_struct_component_assignment(
            wrapper_tmp_name,
            {},
            "field",
            "java::IntWrapper",
            {},
            entry_point_code);
        }
      }
    }
  }

  GIVEN("A generic class extending an uninstantiated generic class")
  {
    const symbol_tablet &symbol_table = load_java_class(
      "SuperclassUninstTest",
      "./goto-programs/goto_program_generics",
      "SuperclassUninstTest.foo");

    WHEN("The method input argument is created in the entry point function")
    {
      const std::vector<codet> &entry_point_code =
        require_goto_statements::require_entry_point_statements(symbol_table);

      // For an explanation of this part, look at the comments for the similar
      // parts of the previous tests.
      const auto &this_tmp_name =
        require_goto_statements::require_entry_point_argument_assignment(
          "this", entry_point_code);

      THEN(
        "The object 'this' has field 'f' of type "
        "java::SuperclassUninst")
      {
        const irep_idt &f_tmp_name =
          require_goto_statements::require_struct_component_assignment(
            this_tmp_name,
            {},
            "f",
            "java::SuperclassUninst",
            {},
            entry_point_code);

        THEN("The object for 'f' has correctly specialized inherited field")
        {
          require_goto_statements::require_struct_component_assignment(
            f_tmp_name,
            {"Wrapper"},
            "field",
            "java::java.lang.Integer",
            {"java::java.lang.Object"},
            entry_point_code);
        }
      }
    }
  }

  GIVEN("A generic class extending a partially instantiated generic class")
  {
    const symbol_tablet &symbol_table = load_java_class(
      "SuperclassMixedTest",
      "./goto-programs/goto_program_generics",
      "SuperclassMixedTest.foo");

    WHEN("The method input argument is created in the entry point function")
    {
      const std::vector<codet> &entry_point_code =
        require_goto_statements::require_entry_point_statements(symbol_table);

      // For an explanation of this part, look at the comments for the similar
      // parts of the previous tests.
      const auto &this_tmp_name =
        require_goto_statements::require_entry_point_argument_assignment(
          "this", entry_point_code);

      THEN("The object 'this' has field 'f' of type java::SuperclassMixed")
      {
        const irep_idt &f_tmp_name =
          require_goto_statements::require_struct_component_assignment(
            this_tmp_name,
            {},
            "f",
            "java::SuperclassMixed",
            {},
            entry_point_code);

        THEN("The object for 'f' has correctly specialized inherited fields")
        {
          require_goto_statements::require_struct_component_assignment(
            f_tmp_name,
            {"TwoWrapper"},
            "first",
            "java::java.lang.Boolean",
            {"java::java.lang.Object"},
            entry_point_code);

          require_goto_statements::require_struct_component_assignment(
            f_tmp_name,
            {"TwoWrapper"},
            "second",
            "java::IntWrapper",
            {"java::java.lang.Object"},
            entry_point_code);
        }
      }
    }
  }

  GIVEN(
    "A class with an inner classes that extend instantiated or "
    "uninstantiated generic classes")
  {
    const symbol_tablet &symbol_table = load_java_class(
      "SuperclassInnerInst",
      "./goto-programs/goto_program_generics",
      "SuperclassInnerInst.foo");

    WHEN("The method input argument is created in the entry point function")
    {
      const std::vector<codet> &entry_point_code =
        require_goto_statements::require_entry_point_statements(symbol_table);

      // For an explanation of this part, look at the comments for the similar
      // parts of the previous tests.
      const auto &this_tmp_name =
        require_goto_statements::require_entry_point_argument_assignment(
          "this", entry_point_code);

      THEN(
        "The object 'this' has fields 'inner' and 'inner_gen' "
        "of correct types")
      {
        const irep_idt &inner_tmp_name =
          require_goto_statements::require_struct_component_assignment(
            this_tmp_name,
            {},
            "inner",
            "java::SuperclassInnerInst$Inner",
            {},
            entry_point_code);
        THEN(
          "The object of 'inner' has correctly specialized inherited "
          "field")
        {
          require_goto_statements::require_struct_component_assignment(
            inner_tmp_name,
            {"Wrapper"},
            "field",
            "java::java.lang.Integer",
            {},
            entry_point_code);
        }

        const irep_idt &inner_gen_tmp_name =
          require_goto_statements::require_struct_component_assignment(
            this_tmp_name,
            {},
            "inner_gen",
            "java::SuperclassInnerInst$InnerGen",
            {},
            entry_point_code);
        THEN(
          "The object of 'inner_gen' has correctly specialized inherited "
          "field")
        {
          require_goto_statements::require_struct_component_assignment(
            inner_gen_tmp_name,
            {"Wrapper"},
            "field",
            "java::java.lang.Boolean",
            {"java::java.lang.Object"},
            entry_point_code);
        }
      }
    }
  }

  GIVEN(
    "A generic class with inner classes that extend generic classes with "
    "the use of the implicit generic parameter")
  {
    const symbol_tablet &symbol_table = load_java_class(
      "SuperclassInnerUninstTest",
      "./goto-programs/goto_program_generics",
      "SuperclassInnerUninstTest.foo");

    WHEN("The method input argument is created in the entry point function")
    {
      const std::vector<codet> &entry_point_code =
        require_goto_statements::require_entry_point_statements(symbol_table);

      // For an explanation of this part, look at the comments for the similar
      // parts of the previous tests.
      const auto &this_tmp_name =
        require_goto_statements::require_entry_point_argument_assignment(
          "this", entry_point_code);

      THEN(
        "The object 'this' has field 'f' of type "
        "java::SuperclassInnerUninst")
      {
        const irep_idt &f_tmp_name =
          require_goto_statements::require_struct_component_assignment(
            this_tmp_name,
            {},
            "f",
            "java::SuperclassInnerUninst",
            {},
            entry_point_code);

        THEN(
          "The object for 'f' has fields 'inner' and 'inner_gen' "
          "of correct types")
        {
          const irep_idt &inner_tmp_name =
            require_goto_statements::require_struct_component_assignment(
              f_tmp_name,
              {},
              "inner",
              "java::SuperclassInnerUninst$Inner",
              {},
              entry_point_code);
          THEN(
            "The object of 'inner' has correctly specialized inherited "
            "field")
          {
            require_goto_statements::require_struct_component_assignment(
              inner_tmp_name,
              {"Wrapper"},
              "field",
              "java::IntWrapper",
              {"java::java.lang.Object"},
              entry_point_code);
          }

          const irep_idt &inner_gen_tmp_name =
            require_goto_statements::require_struct_component_assignment(
              f_tmp_name,
              {},
              "inner_gen",
              "java::SuperclassInnerUninst$InnerGen",
              {},
              entry_point_code);
          THEN(
            "The object of 'inner_gen' has correctly specialized inherited "
            "fields")
          {
            require_goto_statements::require_struct_component_assignment(
              inner_gen_tmp_name,
              {"TwoWrapper"},
              "first",
              "java::IntWrapper",
              {"java::java.lang.Object"},
              entry_point_code);
            require_goto_statements::require_struct_component_assignment(
              inner_gen_tmp_name,
              {"TwoWrapper"},
              "second",
              "java::java.lang.Boolean",
              {"java::java.lang.Object"},
              entry_point_code);
          }

          const irep_idt &inner_three_tmp_name =
            require_goto_statements::require_struct_component_assignment(
              f_tmp_name,
              {},
              "inner_three",
              "java::SuperclassInnerUninst$InnerThree",
              {},
              entry_point_code);
          THEN(
            "The object of 'inner_three' has correctly specialized "
            "inherited fields")
          {
            require_goto_statements::require_struct_component_assignment(
              inner_three_tmp_name,
              {"Wrapper"},
              "field",
              "java::IntWrapper",
              {"java::java.lang.Object"},
              entry_point_code);
          }
        }
      }
    }
  }
}
