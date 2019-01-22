/*******************************************************************\

Module: Unit tests for parsing generic classes

Author: Diffblue Ltd.

\*******************************************************************/

#include <java-testing-utils/load_java_class.h>
#include <java-testing-utils/require_type.h>
#include <testing-utils/use_catch.h>

SCENARIO(
  "parse_derived_generic_class",
  "[core][java_bytecode][java_bytecode_parse_generics]")
{
  const symbol_tablet &new_symbol_table = load_java_class(
    "DerivedGenerics", "./java_bytecode/java_bytecode_parse_generics");

  THEN("There should be a symbol for the DerivedGenericInst class")
  {
    std::string class_prefix = "java::DerivedGenericInst";
    REQUIRE(new_symbol_table.has_symbol(class_prefix));

    const symbolt &derived_symbol = new_symbol_table.lookup_ref(class_prefix);
    const class_typet &derived_class_type =
      require_type::require_complete_java_non_generic_class(
        derived_symbol.type);

    THEN("The base for superclass has the correct generic type information")
    {
      REQUIRE(derived_class_type.bases().size() == 1);
      const typet &base_type = derived_class_type.bases().at(0).type();
      require_type::require_java_generic_struct_tag_type(
        base_type,
        "java::Generic",
        {{require_type::type_argument_kindt::Inst,
          "java::Interface_Implementation"}});
    }
  }

  THEN("There should be a symbol for the DerivedGenericInst2 class")
  {
    std::string class_prefix = "java::DerivedGenericInst2";
    REQUIRE(new_symbol_table.has_symbol(class_prefix));

    const symbolt &derived_symbol = new_symbol_table.lookup_ref(class_prefix);

    const class_typet &derived_class_type =
      require_type::require_complete_java_non_generic_class(
        derived_symbol.type);

    THEN("The base for superclass has the correct generic type information")
    {
      REQUIRE(derived_class_type.bases().size() == 1);
      const typet &base_type = derived_class_type.bases().at(0).type();
      require_type::require_java_generic_struct_tag_type(
        base_type,
        "java::GenericTwoParam",
        {{require_type::type_argument_kindt::Inst,
          "java::Interface_Implementation"},
         {require_type::type_argument_kindt::Inst, "java::java.lang.Integer"}});
    }
  }

  THEN("There should be a symbol for the DerivedGenericUninst class")
  {
    std::string class_prefix = "java::DerivedGenericUninst";
    REQUIRE(new_symbol_table.has_symbol(class_prefix));

    const symbolt &derived_symbol = new_symbol_table.lookup_ref(class_prefix);

    const class_typet &derived_class_type =
      require_type::require_complete_java_generic_class(derived_symbol.type);

    THEN("The base for superclasss has the correct generic type information")
    {
      REQUIRE(derived_class_type.bases().size() == 1);
      const typet &base_type = derived_class_type.bases().at(0).type();
      require_type::require_java_generic_struct_tag_type(
        base_type,
        "java::Generic",
        {{require_type::type_argument_kindt::Var,
          "java::DerivedGenericUninst::T"}});
    }
  }

  THEN("There should be a symbol for the DerivedGenericMixed1 class")
  {
    std::string class_prefix = "java::DerivedGenericMixed1";
    REQUIRE(new_symbol_table.has_symbol(class_prefix));

    const symbolt &derived_symbol = new_symbol_table.lookup_ref(class_prefix);

    const class_typet &derived_class_type =
      require_type::require_complete_java_generic_class(derived_symbol.type);

    THEN("The base for superclass has the correct generic type information")
    {
      REQUIRE(derived_class_type.bases().size() == 1);
      const typet &base_type = derived_class_type.bases().at(0).type();
      require_type::require_java_generic_struct_tag_type(
        base_type,
        "java::Generic",
        {{require_type::type_argument_kindt::Inst,
          "java::Interface_Implementation"}});
    }
  }

  THEN("There should be a symbol for the DerivedGenericMixed2 class")
  {
    std::string class_prefix = "java::DerivedGenericMixed2";
    REQUIRE(new_symbol_table.has_symbol(class_prefix));

    const symbolt &derived_symbol = new_symbol_table.lookup_ref(class_prefix);

    const class_typet &derived_class_type =
      require_type::require_complete_java_generic_class(derived_symbol.type);

    THEN("The base for superclass has the correct generic type information")
    {
      REQUIRE(derived_class_type.bases().size() == 1);
      const typet &base_type = derived_class_type.bases().at(0).type();
      require_type::require_java_generic_struct_tag_type(
        base_type,
        "java::GenericTwoParam",
        {{require_type::type_argument_kindt::Var,
          "java::DerivedGenericMixed2::T"},
         {require_type::type_argument_kindt::Inst, "java::java.lang.Integer"}});
    }
  }

  THEN("There should be a symbol for the ContainsInnerClass$InnerClass class")
  {
    std::string class_prefix = "java::ContainsInnerClass$InnerClass";
    REQUIRE(new_symbol_table.has_symbol(class_prefix));

    const symbolt &derived_symbol = new_symbol_table.lookup_ref(class_prefix);

    const class_typet &derived_class_type =
      require_type::require_complete_java_non_generic_class(
        derived_symbol.type);

    THEN("The base for superclass has the correct generic type information")
    {
      REQUIRE(derived_class_type.bases().size() == 1);
      const typet &base_type = derived_class_type.bases().at(0).type();
      require_type::require_java_generic_struct_tag_type(
        base_type,
        "java::Generic",
        {{require_type::type_argument_kindt::Inst, "java::java.lang.Integer"}});
    }
  }

  THEN(
    "There should be a symbol for the ContainsInnerClass$InnerClassGeneric "
    "class")
  {
    std::string class_prefix = "java::ContainsInnerClass$InnerClassGeneric";
    REQUIRE(new_symbol_table.has_symbol(class_prefix));

    const symbolt &derived_symbol = new_symbol_table.lookup_ref(class_prefix);

    const class_typet &derived_class_type =
      require_type::require_complete_java_generic_class(derived_symbol.type);

    THEN("The base for superclass has the correct generic type information")
    {
      REQUIRE(derived_class_type.bases().size() == 1);
      const typet &base_type = derived_class_type.bases().at(0).type();
      require_type::require_java_generic_struct_tag_type(
        base_type,
        "java::Generic",
        {{require_type::type_argument_kindt::Var,
          "java::ContainsInnerClass$InnerClassGeneric::T"}});
    }
  }

  THEN(
    "There should be a symbol for the ContainsInnerClassGeneric$InnerClass"
    "class")
  {
    std::string class_prefix = "java::ContainsInnerClassGeneric$InnerClass";
    REQUIRE(new_symbol_table.has_symbol(class_prefix));

    const symbolt &derived_symbol = new_symbol_table.lookup_ref(class_prefix);

    const class_typet &derived_class_type =
      require_type::require_complete_java_implicitly_generic_class(
        derived_symbol.type, {"java::ContainsInnerClassGeneric::T"});

    THEN("The base for superclass has the correct generic type information")
    {
      REQUIRE(derived_class_type.bases().size() == 1);
      const typet &base_type = derived_class_type.bases().at(0).type();
      require_type::require_java_generic_struct_tag_type(
        base_type,
        "java::Generic",
        {{require_type::type_argument_kindt::Var,
          "java::ContainsInnerClassGeneric::T"}});
    }
  }

  THEN("There should be a symbol for the ThreeHierarchy class")
  {
    std::string class_prefix = "java::ThreeHierarchy";
    REQUIRE(new_symbol_table.has_symbol(class_prefix));

    const symbolt &derived_symbol = new_symbol_table.lookup_ref(class_prefix);

    const class_typet &derived_class_type =
      require_type::require_complete_java_non_generic_class(
        derived_symbol.type);

    THEN("The base for superclass has the correct generic type information")
    {
      REQUIRE(derived_class_type.bases().size() == 1);
      const typet &base_type = derived_class_type.bases().at(0).type();
      require_type::require_java_generic_struct_tag_type(
        base_type,
        "java::DerivedGenericMixed2",
        {{require_type::type_argument_kindt::Inst, "java::java.lang.String"}});
    }
  }

  THEN(
    "There should be a symbol for the ImplementsInterfaceGenericSpecialised "
    "class")
  {
    std::string class_prefix = "java::ImplementsInterfaceGenericSpecialised";
    REQUIRE(new_symbol_table.has_symbol(class_prefix));

    const symbolt &derived_symbol = new_symbol_table.lookup_ref(class_prefix);

    const class_typet &derived_class_type =
      require_type::require_complete_java_non_generic_class(
        derived_symbol.type);

    THEN("The bases have the correct generic type information")
    {
      REQUIRE(derived_class_type.bases().size() == 2);

      THEN("The superclass is correct")
      {
        const typet &base_type = derived_class_type.bases().at(0).type();
        require_type::require_struct_tag(base_type, "java::java.lang.Object");
      }
      THEN("The second interface is correct")
      {
        const typet &base_type = derived_class_type.bases().at(1).type();
        require_type::require_java_generic_struct_tag_type(
          base_type,
          "java::InterfaceGeneric",
          {{require_type::type_argument_kindt::Inst,
            "java::java.lang.Integer"}});
      }
    }
  }

  THEN(
    "There should be a symbol for the ImplementsInterfaceGenericUnspec class")
  {
    std::string class_prefix = "java::ImplementsInterfaceGenericUnspec";
    REQUIRE(new_symbol_table.has_symbol(class_prefix));

    const symbolt &derived_symbol = new_symbol_table.lookup_ref(class_prefix);

    const class_typet &derived_class_type =
      require_type::require_complete_java_generic_class(derived_symbol.type);

    THEN("The bases have the correct generic type information")
    {
      REQUIRE(derived_class_type.bases().size() == 2);

      THEN("The superclass is correct")
      {
        const typet &base_type = derived_class_type.bases().at(0).type();
        require_type::require_struct_tag(base_type, "java::java.lang.Object");
      }
      THEN("The second interface is correct")
      {
        const typet &base_type = derived_class_type.bases().at(1).type();
        require_type::require_java_generic_struct_tag_type(
          base_type,
          "java::InterfaceGeneric",
          {{require_type::type_argument_kindt::Var,
            "java::ImplementsInterfaceGenericUnspec::E"}});
      }
    }
  }

  THEN(
    "There should be a symbol for the "
    "ImplementsMultipleInterfaces class")
  {
    std::string class_prefix = "java::ImplementsMultipleInterfaces";
    REQUIRE(new_symbol_table.has_symbol(class_prefix));

    const symbolt &derived_symbol = new_symbol_table.lookup_ref(class_prefix);

    const class_typet &derived_class_type =
      require_type::require_complete_java_non_generic_class(
        derived_symbol.type);

    THEN("The bases have the correct generic type information")
    {
      REQUIRE(derived_class_type.bases().size() == 3);

      THEN("The superclass is correct")
      {
        const typet &base_type = derived_class_type.bases().at(0).type();
        require_type::require_struct_tag(base_type, "java::java.lang.Object");
      }
      THEN("The second interface is correct")
      {
        const typet &base_type = derived_class_type.bases().at(1).type();
        require_type::require_java_generic_struct_tag_type(
          base_type,
          "java::InterfaceGeneric",
          {{require_type::type_argument_kindt::Inst,
            "java::java.lang.Integer"}});
      }
      THEN("The first interface is correct")
      {
        const typet &base_type = derived_class_type.bases().at(2).type();
        require_type::require_struct_tag(base_type, "java::Interface");
      }
    }
  }

  THEN(
    "There should be a symbol for the "
    "ExtendsAndImplements class")
  {
    std::string class_prefix = "java::ExtendsAndImplements";
    REQUIRE(new_symbol_table.has_symbol(class_prefix));

    const symbolt &derived_symbol = new_symbol_table.lookup_ref(class_prefix);

    const class_typet &derived_class_type =
      require_type::require_complete_java_non_generic_class(
        derived_symbol.type);

    THEN("The bases have the correct generic type information")
    {
      REQUIRE(derived_class_type.bases().size() == 3);

      THEN("The superclass is correct")
      {
        const typet &base_type = derived_class_type.bases().at(0).type();
        require_type::require_java_generic_struct_tag_type(
          base_type,
          "java::Generic",
          {{require_type::type_argument_kindt::Inst,
            "java::java.lang.Integer"}});
      }
      THEN("The first interface is correct")
      {
        const typet &base_type = derived_class_type.bases().at(1).type();
        require_type::require_struct_tag(base_type, "java::Interface");
      }
      THEN("The second interface is correct")
      {
        const typet &base_type = derived_class_type.bases().at(2).type();
        require_type::require_java_generic_struct_tag_type(
          base_type,
          "java::InterfaceGeneric",
          {{require_type::type_argument_kindt::Inst,
            "java::java.lang.Integer"}});
      }
    }
  }

  THEN(
    "There should be a symbol for the "
    "ExtendsAndImplementsGeneric class")
  {
    std::string class_prefix = "java::ExtendsAndImplementsGeneric";
    REQUIRE(new_symbol_table.has_symbol(class_prefix));

    const symbolt &derived_symbol = new_symbol_table.lookup_ref(class_prefix);

    const class_typet &derived_class_type =
      require_type::require_complete_java_generic_class(derived_symbol.type);

    THEN("The bases have the correct generic type information")
    {
      REQUIRE(derived_class_type.bases().size() == 3);

      THEN("The superclass is correct")
      {
        const typet &base_type = derived_class_type.bases().at(0).type();
        require_type::require_java_generic_struct_tag_type(
          base_type,
          "java::GenericTwoParam",
          {{require_type::type_argument_kindt::Var,
            "java::ExtendsAndImplementsGeneric::T"},
           {require_type::type_argument_kindt::Inst,
            "java::java.lang.Integer"}});
      }
      THEN("The first interface is correct")
      {
        const typet &base_type = derived_class_type.bases().at(1).type();
        require_type::require_struct_tag(base_type, "java::Interface");
      }
      THEN("The second interface is correct")
      {
        const typet &base_type = derived_class_type.bases().at(2).type();
        require_type::require_java_generic_struct_tag_type(
          base_type,
          "java::InterfaceGeneric",
          {{require_type::type_argument_kindt::Var,
            "java::ExtendsAndImplementsGeneric::T"}});
      }
    }
  }

  THEN(
    "There should be a symbol for the "
      "ExtendsAndImplementsSameInterface class")
  {
    std::string class_prefix = "java::ExtendsAndImplementsSameInterface";
    REQUIRE(new_symbol_table.has_symbol(class_prefix));

    const symbolt &derived_symbol = new_symbol_table.lookup_ref(class_prefix);

    const class_typet &derived_class_type =
      require_type::require_complete_java_non_generic_class(
        derived_symbol.type);

    THEN("The bases have the correct generic type information")
    {
      REQUIRE(derived_class_type.bases().size() == 2);

      THEN("The superclass is correct")
      {
        const typet &base_type = derived_class_type.bases().at(0).type();
        require_type::require_java_generic_struct_tag_type(
          base_type,
          "java::Generic",
          {{require_type::type_argument_kindt::Inst,
            "java::InterfaceGeneric"}});
      }
      THEN("The interface is correct")
      {
        const typet &base_type = derived_class_type.bases().at(1).type();
        require_type::require_java_generic_struct_tag_type(
          base_type,
          "java::InterfaceGeneric",
          {{require_type::type_argument_kindt::Inst,
            "java::java.lang.Integer"}});
      }
    }
  }

  THEN(
    "There should be a symbol for the "
      "ExtendsAndImplementsSameInterface2 class")
  {
    std::string class_prefix = "java::ExtendsAndImplementsSameInterface2";
    REQUIRE(new_symbol_table.has_symbol(class_prefix));

    const symbolt &derived_symbol = new_symbol_table.lookup_ref(class_prefix);

    const class_typet &derived_class_type =
      require_type::require_complete_java_non_generic_class(
        derived_symbol.type);

    THEN("The bases have the correct generic type information")
    {
      REQUIRE(derived_class_type.bases().size() == 2);

      THEN("The superclass is correct")
      {
        const typet &base_type = derived_class_type.bases().at(0).type();
        const java_generic_struct_tag_typet &superclass_type =
          require_type::require_java_generic_struct_tag_type(
            base_type,
            "java::Generic",
            {{require_type::type_argument_kindt::Inst,
              "java::InterfaceGeneric"}});

        const typet &type_argument = superclass_type.generic_types().at(0);
        require_type::require_java_generic_type(
          type_argument,
          {{require_type::type_argument_kindt::Inst,
             "java::java.lang.String"}});
      }
      THEN("The interface is correct")
      {
        const typet &base_type = derived_class_type.bases().at(1).type();
        require_type::require_java_generic_struct_tag_type(
          base_type,
          "java::InterfaceGeneric",
          {{require_type::type_argument_kindt::Inst,
            "java::java.lang.Integer"}});
      }
    }
  }

  THEN(
    "There should be a symbol for the "
      "ExtendsAndImplementsSameInterfaceGeneric class")
  {
    std::string class_prefix = "java::ExtendsAndImplementsSameInterfaceGeneric";
    REQUIRE(new_symbol_table.has_symbol(class_prefix));

    const symbolt &derived_symbol = new_symbol_table.lookup_ref(class_prefix);

    const class_typet &derived_class_type =
      require_type::require_complete_java_generic_class(derived_symbol.type);

    THEN("The bases have the correct generic type information")
    {
      REQUIRE(derived_class_type.bases().size() == 2);

      THEN("The superclass is correct")
      {
        const typet &base_type = derived_class_type.bases().at(0).type();
        require_type::require_java_generic_struct_tag_type(
          base_type,
          "java::Generic",
          {{require_type::type_argument_kindt::Inst,
            "java::InterfaceGeneric"}});
      }
      THEN("The interface is correct")
      {
        const typet &base_type = derived_class_type.bases().at(1).type();
        require_type::require_java_generic_struct_tag_type(
          base_type,
          "java::InterfaceGeneric",
          {{require_type::type_argument_kindt::Var,
            "java::ExtendsAndImplementsSameInterfaceGeneric::T"}});
      }
    }
  }

  THEN("There should be a symbol for the `ExtendImplicit` class")
  {
    std::string class_prefix = "java::GenericBase$ExtendImplicit";
    REQUIRE(new_symbol_table.has_symbol(class_prefix));

    const symbolt &derived_symbol = new_symbol_table.lookup_ref(class_prefix);
    const class_typet &derived_class_type =
      require_type::require_complete_java_implicitly_generic_class(
        derived_symbol.type);

    THEN("The base for superclass is implicitly generic")
    {
      REQUIRE(derived_class_type.bases().size() == 1);
      const typet &base_type = derived_class_type.bases().at(0).type();
      require_type::require_java_generic_struct_tag_type(
        base_type,
        "java::GenericBase$ImplicitGeneric",
        {{require_type::type_argument_kindt::Var, "java::GenericBase::T"}});
    }
  }

  THEN("There should be a symbol for the `ExtendImplicitAndExplicit` class")
  {
    std::string class_prefix = "java::GenericBase$ExtendImplicitAndExplicit";
    REQUIRE(new_symbol_table.has_symbol(class_prefix));

    const symbolt &derived_symbol = new_symbol_table.lookup_ref(class_prefix);
    const class_typet &derived_class_type =
      require_type::require_complete_java_implicitly_generic_class(
        derived_symbol.type);

    THEN("The base for superclass is generic *and* implicitly generic")
    {
      REQUIRE(derived_class_type.bases().size() == 1);
      const typet &base_type = derived_class_type.bases().at(0).type();
      require_type::require_java_generic_struct_tag_type(
        base_type,
        "java::GenericBase$ImplicitAndExplicitGeneric",
        {{require_type::type_argument_kindt::Var, "java::GenericBase::T"},
         {require_type::type_argument_kindt::Var,
          "java::GenericBase$ExtendImplicitAndExplicit::S"}});
    }
  }

  THEN("There should be a symbol for the `ExtendImplicitAndExplicit` class")
  {
    std::string class_prefix = "java::GenericBase2$ExtendImplicitAndExplicit";
    REQUIRE(new_symbol_table.has_symbol(class_prefix));

    const symbolt &derived_symbol = new_symbol_table.lookup_ref(class_prefix);
    const class_typet &derived_class_type =
      require_type::require_complete_java_implicitly_generic_class(
        derived_symbol.type);

    THEN("The base for superclass is generic *and* implicitly generic")
    {
      REQUIRE(derived_class_type.bases().size() == 1);
      const typet &base_type = derived_class_type.bases().at(0).type();
      require_type::require_java_generic_struct_tag_type(
        base_type,
        "java::GenericBase2$ImplicitAndExplicitGeneric",
        {{require_type::type_argument_kindt::Var, "java::GenericBase2::T"},
         {require_type::type_argument_kindt::Var, "java::GenericBase2::S"},
         {require_type::type_argument_kindt::Var, "java::GenericBase2::S"}});
    }
  }
}
