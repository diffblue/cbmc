/*******************************************************************\

 Module: Unit tests for generating new type with generic parameters
         substitued for concrete types

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

#include <testing-utils/catch.hpp>
#include <testing-utils/load_java_class.h>
#include <testing-utils/require_type.h>
#include <testing-utils/generic_utils.h>

SCENARIO("generate_outer_inner", "[core][java_bytecode][generate_outer_inner]")
{
  WHEN("Loading a class with generic and non-generic inner classes")
  {
    symbol_tablet new_symbol_table = load_java_class(
      "generic_outer_inner", "./java_bytecode/generate_concrete_generic_type");
    const std::string &class_prefix = "java::generic_outer_inner";

    WHEN("Its field t1 is specialised")
    {
      generic_utils::specialise_generic_from_component(
        class_prefix, "t1", new_symbol_table);
      const std::string &expected_prefix =
        class_prefix + "$GenericOuter<java::java.lang.Integer>";
      THEN("The corresponding specialised class symbol is created")
      {
        REQUIRE(new_symbol_table.has_symbol(expected_prefix));
        const symbolt &expected_symbol =
          new_symbol_table.lookup_ref(expected_prefix);

        const struct_typet class_struct = to_struct_type(expected_symbol.type);
        REQUIRE(is_java_specialized_generic_class_type(class_struct));

        THEN("It has field f1 of correct type")
        {
          const struct_union_typet::componentt &field =
            require_type::require_component(class_struct, "f1");
          require_type::require_pointer(
            field.type(), symbol_typet("java::java.lang.Integer"));
        }

        THEN("It has field f2 of correct type")
        {
          const struct_union_typet::componentt &field =
            require_type::require_component(class_struct, "f2");
          require_type::require_pointer(
            field.type(),
            symbol_typet("java::generic_outer_inner$GenericOuter$Inner"));
          require_type::require_java_generic_type(
            field.type(),
            {{require_type::type_argument_kindt::Inst,
              "java::java.lang.Integer"}});
        }

        THEN("It has field f3 of correct type")
        {
          const struct_union_typet::componentt &field =
            require_type::require_component(class_struct, "f3");
          require_type::require_pointer(
            field.type(),
            symbol_typet(
              "java::generic_outer_inner$GenericOuter$GenericInner"));
          require_type::require_java_generic_type(
            field.type(),
            {{require_type::type_argument_kindt::Inst,
              "java::java.lang.Integer"},
             {require_type::type_argument_kindt::Inst,
              "java::java.lang.String"}});
        }

        THEN("It has field this$0 of correct type")
        {
          const struct_union_typet::componentt &field =
            require_type::require_component(class_struct, "this$0");
          require_type::require_pointer(
            field.type(), symbol_typet("java::generic_outer_inner"));
        }
      }
    }

    WHEN("Its field t2 is specialised")
    {
      generic_utils::specialise_generic_from_component(
        class_prefix, "t2", new_symbol_table);
      const std::string &expected_prefix =
        class_prefix + "$GenericOuter<java::java.lang.Integer>$Inner";
      THEN("The corresponding specialised class symbol is created")
      {
        REQUIRE(new_symbol_table.has_symbol(expected_prefix));
        const symbolt &expected_symbol =
          new_symbol_table.lookup_ref(expected_prefix);

        const struct_typet class_struct = to_struct_type(expected_symbol.type);
        REQUIRE(is_java_specialized_generic_class_type(class_struct));

        THEN("It has field f1 of correct type")
        {
          const struct_union_typet::componentt &field =
            require_type::require_component(class_struct, "f1");
          require_type::require_pointer(
            field.type(), symbol_typet("java::java.lang.Integer"));
        }

        THEN("It has field f2 of correct type")
        {
          const struct_union_typet::componentt &field =
            require_type::require_component(class_struct, "f2");
          require_type::require_pointer(
            field.type(), symbol_typet("java::java.lang.Integer"));
        }

        THEN("It has field this$1 of correct type")
        {
          const struct_union_typet::componentt &field =
            require_type::require_component(class_struct, "this$1");
          // TODO should be java generic type - TG-1826
        }
      }
    }

    WHEN("Its field t2a is specialised")
    {
      generic_utils::specialise_generic_from_component(
        class_prefix, "t2a", new_symbol_table);
      const std::string &expected_prefix =
        class_prefix +
        "$GenericOuter<array[reference]of_java::java.lang.Integer>$Inner";
      THEN("The corresponding specialised class symbol is created")
      {
        REQUIRE(new_symbol_table.has_symbol(expected_prefix));
        const symbolt &expected_symbol =
          new_symbol_table.lookup_ref(expected_prefix);

        const struct_typet class_struct = to_struct_type(expected_symbol.type);
        REQUIRE(is_java_specialized_generic_class_type(class_struct));

        THEN("It has field f1 of correct type")
        {
          const struct_union_typet::componentt &field =
            require_type::require_component(class_struct, "f1");
          const symbol_typet &field_array =
            to_symbol_type(field.type().subtype());
          REQUIRE(field_array.get_identifier() == "java::array[reference]");
          require_type::require_pointer(
            java_array_element_type(field_array),
            symbol_typet("java::java.lang.Integer"));
        }

        THEN("It has field f2 of correct type")
        {
          const struct_union_typet::componentt &field =
            require_type::require_component(class_struct, "f2");
          require_type::require_pointer(
            field.type(), symbol_typet("java::java.lang.Integer"));
        }

        THEN("It has field this$1 of correct type")
        {
          const struct_union_typet::componentt &field =
            require_type::require_component(class_struct, "this$1");
          // TODO should be java generic type - TG-1826
        }
      }
    }

    WHEN("Its field t3 is specialised")
    {
      generic_utils::specialise_generic_from_component(
        class_prefix, "t3", new_symbol_table);
      const std::string &expected_prefix =
        class_prefix + "$GenericOuter<java::java.lang.String>$Inner$InnerInner";

      THEN("The corresponding specialised class symbol is created")
      {
        REQUIRE(new_symbol_table.has_symbol(expected_prefix));
        const symbolt &expected_symbol =
          new_symbol_table.lookup_ref(expected_prefix);

        const struct_typet class_struct = to_struct_type(expected_symbol.type);
        REQUIRE(is_java_specialized_generic_class_type(class_struct));

        THEN("It has field f1 of correct type")
        {
          const struct_union_typet::componentt &field =
            require_type::require_component(class_struct, "f1");
          require_type::require_pointer(
            field.type(), symbol_typet("java::java.lang.String"));
        }

        THEN("It has field this$2 of correct type")
        {
          const struct_union_typet::componentt &field =
            require_type::require_component(class_struct, "this$2");
          // TODO should be java generic type - TG-1826
        }
      }
    }

    WHEN("Its field t3a is specialised")
    {
      generic_utils::specialise_generic_from_component(
        class_prefix, "t3a", new_symbol_table);
      const std::string &expected_prefix = class_prefix +
                                           "$GenericOuter<array[reference]of_"
                                           "java::java.lang.String>$Inner$"
                                           "InnerInner";

      THEN("The corresponding specialised class symbol is created")
      {
        REQUIRE(new_symbol_table.has_symbol(expected_prefix));
        const symbolt &expected_symbol =
          new_symbol_table.lookup_ref(expected_prefix);

        const struct_typet class_struct = to_struct_type(expected_symbol.type);
        REQUIRE(is_java_specialized_generic_class_type(class_struct));

        THEN("It has field f1 of correct type")
        {
          const struct_union_typet::componentt &field =
            require_type::require_component(class_struct, "f1");
          const symbol_typet &field_array =
            to_symbol_type(field.type().subtype());
          REQUIRE(field_array.get_identifier() == "java::array[reference]");
          require_type::require_pointer(
            java_array_element_type(field_array),
            symbol_typet("java::java.lang.String"));
        }

        THEN("It has field this$2 of correct type")
        {
          const struct_union_typet::componentt &field =
            require_type::require_component(class_struct, "this$2");
          // TODO should be java generic type - TG-1826
        }
      }
    }

    // TODO add test for field t4 once TG-1633 is done

    WHEN("Its field t5 is specialised")
    {
      generic_utils::specialise_generic_from_component(
        class_prefix, "t5", new_symbol_table);
      const std::string &expected_prefix =
        class_prefix +
        "$Outer$Inner$GenericInnerInner<java::java.lang.Integer>";

      THEN("The corresponding specialised class symbol is created")
      {
        REQUIRE(new_symbol_table.has_symbol(expected_prefix));
        const symbolt &expected_symbol =
          new_symbol_table.lookup_ref(expected_prefix);

        const struct_typet class_struct = to_struct_type(expected_symbol.type);
        REQUIRE(is_java_specialized_generic_class_type(class_struct));

        THEN("It has field f1 of correct type")
        {
          const struct_union_typet::componentt &field =
            require_type::require_component(class_struct, "f1");
          require_type::require_pointer(
            field.type(), symbol_typet("java::java.lang.Integer"));
        }

        THEN("It has field this$2 of correct type")
        {
          const struct_union_typet::componentt &field =
            require_type::require_component(class_struct, "this$2");
          require_type::require_pointer(
            field.type(), symbol_typet(class_prefix + "$Outer$Inner"));
        }
      }
    }

    WHEN("Its field t6 is specialised")
    {
      generic_utils::specialise_generic_from_component(
        class_prefix, "t6", new_symbol_table);
      const std::string &expected_prefix =
        class_prefix + "$Outer$GenericInner<java::java.lang.Integer>";

      THEN("The corresponding specialised class symbol is created")
      {
        REQUIRE(new_symbol_table.has_symbol(expected_prefix));
        const symbolt &expected_symbol =
          new_symbol_table.lookup_ref(expected_prefix);

        const struct_typet class_struct = to_struct_type(expected_symbol.type);
        REQUIRE(is_java_specialized_generic_class_type(class_struct));

        THEN("It has field f1 of correct type")
        {
          const struct_union_typet::componentt &field =
            require_type::require_component(class_struct, "f1");
          require_type::require_pointer(
            field.type(),
            symbol_typet(
              "java::generic_outer_inner$Outer$"
              "GenericInner$GenericInnerInner"));
          require_type::require_java_generic_type(
            field.type(),
            {{require_type::type_argument_kindt::Inst,
              "java::java.lang.Integer"},
             {require_type::type_argument_kindt::Inst,
              "java::java.lang.String"}});
        }

        THEN("It has field this$1 of correct type")
        {
          const struct_union_typet::componentt &field =
            require_type::require_component(class_struct, "this$1");
          require_type::require_pointer(
            field.type(), symbol_typet(class_prefix + "$Outer"));
        }
      }
    }

    WHEN("Its field t7 is specialised")
    {
      generic_utils::specialise_generic_from_component(
        class_prefix, "t7", new_symbol_table);
      const std::string &expected_prefix =
        class_prefix +
        "$Outer$GenericInner<java::java.lang.Integer>$InnerInner";

      THEN("The corresponding specialised class symbol is created")
      {
        REQUIRE(new_symbol_table.has_symbol(expected_prefix));
        const symbolt &expected_symbol =
          new_symbol_table.lookup_ref(expected_prefix);

        const struct_typet class_struct = to_struct_type(expected_symbol.type);
        REQUIRE(is_java_specialized_generic_class_type(class_struct));

        THEN("It has field f1 of correct type")
        {
          const struct_union_typet::componentt &field =
            require_type::require_component(class_struct, "f1");
          require_type::require_pointer(
            field.type(), symbol_typet("java::java.lang.Integer"));
        }

        THEN("It has field this$2 of correct type")
        {
          const struct_union_typet::componentt &field =
            require_type::require_component(class_struct, "this$2");
          // TODO should be java generic type - TG-1826
        }
      }
    }

    WHEN("Its field t7a is specialised")
    {
      generic_utils::specialise_generic_from_component(
        class_prefix, "t7a", new_symbol_table);
      const std::string &expected_prefix =
        class_prefix +
        "$Outer$GenericInner<array[reference]"
        "of_java::java.lang.Integer>$InnerInner";

      THEN("The corresponding specialised class symbol is created")
      {
        REQUIRE(new_symbol_table.has_symbol(expected_prefix));
        const symbolt &expected_symbol =
          new_symbol_table.lookup_ref(expected_prefix);

        const struct_typet class_struct = to_struct_type(expected_symbol.type);
        REQUIRE(is_java_specialized_generic_class_type(class_struct));

        THEN("It has field f1 of correct type")
        {
          const struct_union_typet::componentt &field =
            require_type::require_component(class_struct, "f1");
          const symbol_typet &field_array =
            to_symbol_type(field.type().subtype());
          REQUIRE(field_array.get_identifier() == "java::array[reference]");
          require_type::require_pointer(
            java_array_element_type(field_array),
            symbol_typet("java::java.lang.Integer"));
        }

        THEN("It has field this$2 of correct type")
        {
          const struct_union_typet::componentt &field =
            require_type::require_component(class_struct, "this$2");
          // TODO should be java generic type - TG-1826
        }
      }
    }

    // TODO add test for field t8 once TG-1633 is done

    WHEN("Its field t9 is specialised")
    {
      generic_utils::specialise_generic_from_component(
        class_prefix, "t9", new_symbol_table);
      const std::string &expected_prefix = class_prefix +
                                           "$Outer$TwoParamGenericInner<java::"
                                           "java.lang.Integer, "
                                           "java::java.lang.String>";

      THEN("The corresponding specialised class symbol is created")
      {
        REQUIRE(new_symbol_table.has_symbol(expected_prefix));
        const symbolt &expected_symbol =
          new_symbol_table.lookup_ref(expected_prefix);

        const struct_typet class_struct = to_struct_type(expected_symbol.type);
        REQUIRE(is_java_specialized_generic_class_type(class_struct));

        THEN("It has field f1 of correct type")
        {
          const struct_union_typet::componentt &field =
            require_type::require_component(class_struct, "f1");
          require_type::require_pointer(
            field.type(), symbol_typet("java::java.lang.Integer"));
        }

        THEN("It has field f2 of correct type")
        {
          const struct_union_typet::componentt &field =
            require_type::require_component(class_struct, "f2");
          require_type::require_pointer(
            field.type(), symbol_typet("java::java.lang.String"));
        }

        THEN("It has field this$1 of correct type")
        {
          const struct_union_typet::componentt &field =
            require_type::require_component(class_struct, "this$1");
          require_type::require_pointer(
            field.type(), symbol_typet(class_prefix + "$Outer"));
        }
      }
    }

    WHEN("Its field t10 is specialised")
    {
      generic_utils::specialise_generic_from_component(
        class_prefix, "t10", new_symbol_table);
      const std::string &expected_prefix = class_prefix +
                                           "$Outer$TwoParamGenericInner<java::"
                                           "java.lang.Integer, "
                                           "java::java.lang.String>$InnerInner";

      THEN("The corresponding specialised class symbol is created")
      {
        REQUIRE(new_symbol_table.has_symbol(expected_prefix));
        const symbolt &expected_symbol =
          new_symbol_table.lookup_ref(expected_prefix);

        const struct_typet class_struct = to_struct_type(expected_symbol.type);
        REQUIRE(is_java_specialized_generic_class_type(class_struct));

        THEN("It has field f1 of correct type")
        {
          const struct_union_typet::componentt &field =
            require_type::require_component(class_struct, "f1");
          require_type::require_pointer(
            field.type(), symbol_typet("java::java.lang.Integer"));
        }

        THEN("It has field f2 of correct type")
        {
          const struct_union_typet::componentt &field =
            require_type::require_component(class_struct, "f2");
          require_type::require_pointer(
            field.type(), symbol_typet("java::java.lang.String"));
        }

        THEN("It has field this$2 of correct type")
        {
          const struct_union_typet::componentt &field =
            require_type::require_component(class_struct, "this$2");
          // TODO should be java generic type - TG-1826
        }
      }
    }

    WHEN("Its field t10a is specialised")
    {
      generic_utils::specialise_generic_from_component(
        class_prefix, "t10a", new_symbol_table);
      const std::string &expected_prefix =
        class_prefix +
        "$Outer$TwoParamGenericInner<array[reference]of_java::java.lang."
        "Integer, array[reference]of_java::java.lang.String>$InnerInner";

      THEN("The corresponding specialised class symbol is created")
      {
        REQUIRE(new_symbol_table.has_symbol(expected_prefix));
        const symbolt &expected_symbol =
          new_symbol_table.lookup_ref(expected_prefix);

        const struct_typet class_struct = to_struct_type(expected_symbol.type);
        REQUIRE(is_java_specialized_generic_class_type(class_struct));

        THEN("It has field f1 of correct type")
        {
          const struct_union_typet::componentt &field =
            require_type::require_component(class_struct, "f1");
          const symbol_typet &field_array =
            to_symbol_type(field.type().subtype());
          REQUIRE(field_array.get_identifier() == "java::array[reference]");
          require_type::require_pointer(
            java_array_element_type(field_array),
            symbol_typet("java::java.lang.Integer"));
        }

        THEN("It has field f2 of correct type")
        {
          const struct_union_typet::componentt &field =
            require_type::require_component(class_struct, "f2");
          const symbol_typet &field_array =
            to_symbol_type(field.type().subtype());
          REQUIRE(field_array.get_identifier() == "java::array[reference]");
          require_type::require_pointer(
            java_array_element_type(field_array),
            symbol_typet("java::java.lang.String"));
        }

        THEN("It has field this$2 of correct type")
        {
          const struct_union_typet::componentt &field =
            require_type::require_component(class_struct, "this$2");
          // TODO should be java generic type - TG-1826
        }
      }
    }

    WHEN("Its field t11 is specialised")
    {
      generic_utils::specialise_generic_from_component(
        class_prefix, "t11", new_symbol_table);
      const std::string &expected_prefix =
        class_prefix + "$GenericOuter<java::generic_outer_inner$Outer>";

      THEN("The corresponding specialised class symbol is created")
      {
        REQUIRE(new_symbol_table.has_symbol(expected_prefix));
        const symbolt &expected_symbol =
          new_symbol_table.lookup_ref(expected_prefix);

        const struct_typet class_struct = to_struct_type(expected_symbol.type);
        REQUIRE(is_java_specialized_generic_class_type(class_struct));

        THEN("It has field f1 of correct type")
        {
          const struct_union_typet::componentt &field =
            require_type::require_component(class_struct, "f1");
          require_type::require_pointer(
            field.type(), symbol_typet("java::generic_outer_inner$Outer"));
        }

        THEN("It has field f2 of correct type")
        {
          const struct_union_typet::componentt &field =
            require_type::require_component(class_struct, "f2");
          require_type::require_pointer(
            field.type(),
            symbol_typet("java::generic_outer_inner$GenericOuter$Inner"));
          require_type::require_java_generic_type(
            field.type(),
            {{require_type::type_argument_kindt::Inst,
              "java::generic_outer_inner$Outer"}});
        }

        THEN("It has field f3 of correct type")
        {
          const struct_union_typet::componentt &field =
            require_type::require_component(class_struct, "f3");
          require_type::require_pointer(
            field.type(),
            symbol_typet(
              "java::generic_outer_inner$GenericOuter$GenericInner"));
          require_type::require_java_generic_type(
            field.type(),
            {{require_type::type_argument_kindt::Inst,
              "java::generic_outer_inner$Outer"},
             {require_type::type_argument_kindt::Inst,
              "java::java.lang.String"}});
        }

        THEN("It has field this$0 of correct type")
        {
          const struct_union_typet::componentt &field =
            require_type::require_component(class_struct, "this$0");
          require_type::require_pointer(
            field.type(), symbol_typet(class_prefix));
        }
      }
    }
  }
}
