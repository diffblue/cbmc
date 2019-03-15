/*******************************************************************\

Module: Unit tests for Java-object-factory's treatment of tag types

Author: Diffblue Ltd.

\*******************************************************************/

#include <java-testing-utils/load_java_class.h>
#include <java-testing-utils/require_goto_statements.h>
#include <java_bytecode/java_bytecode_language.h>
#include <java_bytecode/java_object_factory.h>
#include <langapi/mode.h>
#include <testing-utils/message.h>
#include <testing-utils/use_catch.h>
#include <util/expr_iterator.h>

#include <algorithm>

static bool is_decl_with_struct_tag(const codet &code, const irep_idt &id)
{
  if(code.get_statement() != ID_decl)
    return false;

  const typet &decl_type = to_code_decl(code).symbol().type();
  return decl_type.id() == ID_struct_tag &&
         to_struct_tag_type(decl_type).get_identifier() == id;
}

static bool is_decl_of_type(const codet &code, const typet &type)
{
  return code.get_statement() == ID_decl &&
         to_code_decl(code).symbol().type() == type;
}

static bool
contains(const exprt &expr, std::function<bool(const exprt &)> predicate)
{
  return std::any_of(expr.depth_begin(), expr.depth_end(), predicate);
}

static bool
contains(const codet &code, std::function<bool(const codet &)> predicate)
{
  std::vector<codet> statements =
    require_goto_statements::get_all_statements(code);
  return std::any_of(statements.begin(), statements.end(), predicate);
}

static bool
contains(const typet &type, std::function<bool(const typet &)> predicate)
{
  if(predicate(type))
    return true;

  if(type.has_subtypes())
  {
    for(const auto &subtype : to_type_with_subtypes(type).subtypes())
    {
      if(contains(subtype, predicate))
        return true;
    }
  }

  return false;
}

static bool contains_decl_of_type(const codet &code, const typet &type)
{
  return contains(code, [&type](const codet &subcode) {
    return is_decl_of_type(subcode, type);
  });
}

static bool contains_decl_with_struct_tag(const codet &code, const irep_idt &id)
{
  return contains(code, [&id](const codet &subcode) {
    return is_decl_with_struct_tag(subcode, id);
  });
}

static bool uses_raw_struct_types(const typet &type)
{
  return contains(
    type, [](const typet &subtype) { return subtype.id() == ID_struct; });
}

static bool uses_raw_struct_types(const exprt &expr)
{
  return contains(expr, [](const exprt &subexpr) {
    return uses_raw_struct_types(subexpr.type());
  });
}

code_blockt
initialise_nondet_object_of_type(const typet &type, symbol_tablet &symbol_table)
{
  code_blockt created_code;
  java_object_factory_parameterst parameters;
  select_pointer_typet pointer_selector;

  object_factory(
    type,
    "root",
    created_code,
    symbol_table,
    parameters,
    lifetimet::AUTOMATIC_LOCAL,
    source_locationt(),
    pointer_selector,
    null_message_handler);

  return created_code;
}

SCENARIO(
  "java_object_factory_tag_types",
  "[core][java_bytecode][java_object_factory]")
{
  GIVEN("Some classes with fields")
  {
    register_language(new_java_bytecode_language);
    symbol_tablet symbol_table =
      load_java_class("Root", "./java_bytecode/java_object_factory");

    WHEN("Creating a nondet 'A' object")
    {
      struct_tag_typet A_type("java::A");
      struct_tag_typet B_type("java::B");
      struct_tag_typet C_type("java::C");

      const auto a_pointer = java_reference_type(A_type);
      code_blockt created_code =
        initialise_nondet_object_of_type(a_pointer, symbol_table);

      THEN("An A, a B and a C object should be allocated")
      {
        REQUIRE(contains_decl_of_type(created_code, A_type));
        REQUIRE(contains_decl_of_type(created_code, B_type));
        REQUIRE(contains_decl_of_type(created_code, C_type));
      }

      THEN("No raw struct expressions should appear")
      {
        REQUIRE_FALSE(uses_raw_struct_types(created_code));
      }
    }

    WHEN("Creating a nondet 'HasArray' object")
    {
      struct_tag_typet HasArray_type("java::HasArray");
      struct_tag_typet D_type("java::D");

      const auto HasArray_pointer = java_reference_type(HasArray_type);
      code_blockt created_code =
        initialise_nondet_object_of_type(HasArray_pointer, symbol_table);

      THEN("A HasArray object should be created")
      {
        REQUIRE(contains_decl_of_type(created_code, HasArray_type));
      }

      THEN("No raw struct expressions should appear")
      {
        REQUIRE_FALSE(uses_raw_struct_types(created_code));
      }
    }

    WHEN("Creating a nondet 'HasEnum' object")
    {
      struct_tag_typet HasEnum_type("java::HasEnum");
      struct_tag_typet E_type("java::E");

      const auto HasEnum_pointer = java_reference_type(HasEnum_type);
      code_blockt created_code =
        initialise_nondet_object_of_type(HasEnum_pointer, symbol_table);

      THEN("A HasEnum object should be allocated")
      {
        REQUIRE(contains_decl_of_type(created_code, HasEnum_type));
      }

      THEN("No raw struct expressions should appear")
      {
        REQUIRE_FALSE(uses_raw_struct_types(created_code));
      }
    }

    WHEN("Creating a nondet 'HasGeneric' object")
    {
      struct_tag_typet HasGeneric_type("java::HasGeneric");
      irep_idt generic_id = "java::Generic";
      irep_idt other_generic_id = "java::OtherGeneric";

      const auto HasGeneric_pointer = java_reference_type(HasGeneric_type);
      code_blockt created_code =
        initialise_nondet_object_of_type(HasGeneric_pointer, symbol_table);

      THEN("An HasGeneric, Generic and OtherGeneric object should be allocated")
      {
        REQUIRE(contains_decl_of_type(created_code, HasGeneric_type));
        // These ones are just checked for a tag rather than a full type because
        // the tags are decorated with generic information, and I just want to
        // check they (a) are created and (b) don't use expanded types, rather
        // than verifying their full structure.
        REQUIRE(contains_decl_with_struct_tag(created_code, generic_id));
        REQUIRE(contains_decl_with_struct_tag(created_code, other_generic_id));
      }

      THEN("No raw struct expressions should appear")
      {
        REQUIRE_FALSE(uses_raw_struct_types(created_code));
      }
    }
  }
}
