/*******************************************************************\

Module: Unit tests for assign_from_json

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

#include <java_bytecode/assignments_from_json.h>
#include <java_bytecode/ci_lazy_methods_needed.h>
#include <java_bytecode/java_bytecode_convert_class.h>
#include <java_bytecode/java_types.h>
#include <java_bytecode/java_utils.h>

#include <testing-utils/expr_query.h>
#include <testing-utils/use_catch.h>

#include <goto-programs/goto_instruction_code.h>

#include <util/arith_tools.h>
#include <util/json.h>
#include <util/symbol_table.h>

/// Add `clinit` function symbol to the table
/// \return its identifier in the symbol table
static irep_idt
add_clinit(symbol_tablet &symbol_table, const std::string &class_name)
{
  symbolt clinit_symbol;
  clinit_symbol.name = "java::" + class_name + ".<clinit>:()V";
  set_declaring_class(clinit_symbol, "java::" + class_name);
  symbol_table.insert(clinit_symbol);
  return clinit_symbol.name;
}

static void add_class_with_components(
  symbol_tablet &symbol_table,
  const std::string &class_name,
  const std::vector<std::pair<std::string, typet>> &components)
{
  symbolt test_class_symbol;
  test_class_symbol.name = "java::" + class_name;
  test_class_symbol.is_type = true;
  test_class_symbol.type = [&] {
    java_class_typet type;
    // TODO java_class_typet constructors should ensure there is always a
    // @class_identifier field, and that name is always set
    type.set_name(test_class_symbol.name);
    for(const auto &pair : components)
      type.components().emplace_back(pair.first, pair.second);
    return type;
  }();
  symbol_table.insert(test_class_symbol);
}

SCENARIO(
  "assign_from_json",
  "[core][java_static_initializers][assign_from_json]")
{
  symbol_tablet symbol_table;
  const std::size_t max_user_array_length = 100;
  std::unordered_map<std::string, object_creation_referencet> references;
  std::unordered_multimap<irep_idt, symbolt> class_to_declared_symbols;

  GIVEN("A class which has a static number in the provided JSON")
  {
    const json_objectt json = [] {
      json_objectt entry{};
      entry["field_name"] = [] {
        json_objectt int_json;
        int_json["value"] = json_numbert{"42"};
        int_json["@type"] = json_stringt{"java.lang.Integer"};
        return int_json;
      }();
      entry["@type"] = json_stringt{"TestClass"};
      return entry;
    }();
    class_to_declared_symbols.emplace("java::TestClass", [] {
      symbolt field_symbol;
      field_symbol.base_name = "field_name";
      field_symbol.name = "field_name_for_codet";
      field_symbol.type = java_int_type();
      field_symbol.is_static_lifetime = true;
      return field_symbol;
    }());
    const irep_idt clinit_name = add_clinit(symbol_table, "TestClass");
    add_class_with_components(
      symbol_table,
      "TestClass",
      {std::pair<std::string, typet>("@class_identifier", string_typet{}),
       std::pair<std::string, typet>("field_name", java_int_type())});

    const reference_typet test_class_type =
      reference_type(struct_tag_typet{"java::TestClass"});
    optionalt<ci_lazy_methods_neededt> option{};
    const code_with_references_listt code = assign_from_json(
      symbol_exprt{"symbol_to_assign", test_class_type},
      json,
      clinit_name,
      symbol_table,
      option,
      max_user_array_length,
      references);

    code_with_referencest::reference_substitutiont reference_substitution =
      [&](const std::string &reference_id) -> object_creation_referencet & {
      UNREACHABLE;
    };
    code_blockt block;
    for(auto code_with_references : code.list)
      block.append(code_with_references->to_code(reference_substitution));
    THEN(
      "The instruction is the declaration of a symbol of TestClass* type,"
      "followed by its allocation")
    {
      const symbol_exprt declared_symbol =
        make_query(block)[0].as<code_declt>()[0].as<symbol_exprt>().get();
      REQUIRE(declared_symbol.type() == test_class_type);
      REQUIRE(
        make_query(block)[1].as<code_assignt>()[0].as<symbol_exprt>().get() ==
        declared_symbol);
    }
    THEN("The instruction assigns the symbol to `symbol_to_assign`")
    {
      REQUIRE(
        make_query(block)[2]
          .as<code_assignt>()[0]
          .as<symbol_exprt>()
          .get()
          .get_identifier() == "symbol_to_assign");
    }
    THEN("The instruction zero-initializes the struct")
    {
      REQUIRE(
        make_query(block)[3].as<code_assignt>()[1].get().type() ==
        test_class_type.subtype());
    }
    THEN("The instruction assigns the field to 42")
    {
      REQUIRE(
        make_query(block)[4]
          .as<code_assignt>()[0]
          .as<member_exprt>()
          .get()
          .get_component_name() == "field_name");
      REQUIRE(
        numeric_cast_v<mp_integer>(make_query(block)[4]
                                     .as<code_assignt>()[1]
                                     .as<constant_exprt>()
                                     .get()) == 42);
    }
  }

  GIVEN("A class with an array field")
  {
    const json_objectt json = [] {
      json_objectt entry{};
      entry["array_field"] = [] {
        json_objectt array_json;
        array_json["@items"] = json_arrayt{json_numbert{"42"}};
        array_json["@type"] = json_stringt{"[I"};
        return array_json;
      }();
      entry["@type"] = json_stringt{"TestClass"};
      return entry;
    }();
    class_to_declared_symbols.emplace("java::TestClass", [] {
      symbolt field_symbol;
      field_symbol.base_name = "array_field";
      field_symbol.name = "field_name_for_codet";
      field_symbol.type = java_int_type();
      field_symbol.is_static_lifetime = true;
      return field_symbol;
    }());
    const irep_idt clinit_name = add_clinit(symbol_table, "TestClass");
    add_class_with_components(
      symbol_table,
      "TestClass",
      {std::pair<std::string, typet>("@class_identifier", string_typet{}),
       std::pair<std::string, typet>("array_field", java_array_type('i'))});
    // For array[int]
    add_java_array_types(symbol_table);

    const reference_typet test_class_type =
      reference_type(struct_tag_typet{"java::TestClass"});
    optionalt<ci_lazy_methods_neededt> option{};
    const code_with_references_listt code = assign_from_json(
      symbol_exprt{"symbol_to_assign", test_class_type},
      json,
      clinit_name,
      symbol_table,
      option,
      max_user_array_length,
      references);

    code_with_referencest::reference_substitutiont reference_substitution =
      [&](const std::string &reference_id) -> object_creation_referencet & {
      UNREACHABLE;
    };
    code_blockt block;
    for(auto code_with_references : code.list)
      block.append(code_with_references->to_code(reference_substitution));

    THEN("The instruction is the declaration of a symbol of TestClass* type")
    {
      const symbol_exprt allocation_symbol =
        make_query(block)[0].as<code_declt>()[0].as<symbol_exprt>().get();
      REQUIRE(allocation_symbol.type() == test_class_type);
      THEN("The instruction declares the array data")
      {
        REQUIRE(
          make_query(block)[1]
            .as<code_declt>()[0]
            .as<symbol_exprt>()
            .get()
            .type() == java_reference_type(java_int_type()));
      }
      THEN("The instruction allocates the TestClass object")
      {
        REQUIRE(
          make_query(block)[2].as<code_assignt>()[0].as<symbol_exprt>().get() ==
          allocation_symbol);
      }
    }
    THEN("The instruction assigns the symbol to \"symbol_to_assign\"")
    {
      REQUIRE(
        make_query(block)[3]
          .as<code_assignt>()[0]
          .as<symbol_exprt>()
          .get()
          .get_identifier() == "symbol_to_assign");
    }

    THEN("The instruction zero-initializes the struct")
    {
      REQUIRE(
        make_query(block)[4].as<code_assignt>()[0].get().type() ==
        test_class_type.subtype());
    }
    THEN("The instruction allocates the array field, with a size of exactly 1")
    {
      REQUIRE(
        make_query(block)[5]
          .as<code_assignt>()[0]
          .as<member_exprt>()
          .get()
          .get_component_name() == "array_field");
      auto side_effect = make_query(block)[5]
                           .as<code_assignt>()[1]
                           .as<side_effect_exprt>()
                           .get();
      REQUIRE(side_effect.get_statement() == ID_java_new_array);
      REQUIRE(
        numeric_cast_v<mp_integer>(
          make_query(side_effect)[0].as<constant_exprt>().get()) == 1);
    }
    THEN("The instruction copies the data to user_specified_array_data_init")
    {
      REQUIRE(
        make_query(block)[6]
          .as<code_assignt>()[0]
          .as<symbol_exprt>()
          .get()
          .get_identifier() ==
        "java::TestClass.<clinit>:()V::user_specified_array_data_init");
    }
    THEN("The instruction assigns the array cell to 42")
    {
      REQUIRE(
        numeric_cast_v<mp_integer>(make_query(block)[7]
                                     .as<code_assignt>()[1]
                                     .as<constant_exprt>()
                                     .get()) == 42);
    }
  }

  GIVEN("A class with a nondet array field")
  {
    const json_objectt json = [] {
      json_objectt entry{};
      entry["array_field"] = [] {
        json_objectt int_json;
        int_json["@items"] = json_arrayt{json_numbert{"42"}};
        int_json["@type"] = json_stringt{"[I"};
        int_json["@nondetLength"] = json_truet{};
        return int_json;
      }();
      entry["@type"] = json_stringt{"TestClass"};
      return entry;
    }();
    class_to_declared_symbols.emplace("java::TestClass", [] {
      symbolt field_symbol;
      field_symbol.base_name = "array_field";
      field_symbol.name = "field_name_for_codet";
      field_symbol.type = java_int_type();
      field_symbol.is_static_lifetime = true;
      return field_symbol;
    }());
    const irep_idt clinit_name = add_clinit(symbol_table, "TestClass");
    add_class_with_components(
      symbol_table,
      "TestClass",
      {std::pair<std::string, typet>("@class_identifier", string_typet{}),
       std::pair<std::string, typet>("array_field", java_array_type('i'))});
    // For array[int]
    add_java_array_types(symbol_table);

    const reference_typet test_class_type =
      reference_type(struct_tag_typet{"java::TestClass"});
    optionalt<ci_lazy_methods_neededt> option{};
    const code_with_references_listt code = assign_from_json(
      symbol_exprt{"symbol_to_assign", test_class_type},
      json,
      clinit_name,
      symbol_table,
      option,
      max_user_array_length,
      references);

    code_with_referencest::reference_substitutiont reference_substitution =
      [&](const std::string &reference_id) -> object_creation_referencet & {
      UNREACHABLE;
    };
    code_blockt block;
    for(auto code_with_references : code.list)
      block.append(code_with_references->to_code(reference_substitution));

    THEN("The instruction is the declaration of a symbol of TestClass* type")
    {
      const symbol_exprt allocation_symbol =
        make_query(block)[0].as<code_declt>()[0].as<symbol_exprt>().get();
      REQUIRE(allocation_symbol.type() == test_class_type);
      THEN("The instruction declares a symbol for the length")
      {
        REQUIRE(
          make_query(block)[1]
            .as<code_declt>()[0]
            .as<symbol_exprt>()
            .get()
            .type() == java_int_type());
      }
      THEN("The instruction declares the array data")
      {
        REQUIRE(
          make_query(block)[2]
            .as<code_declt>()[0]
            .as<symbol_exprt>()
            .get()
            .type() == java_reference_type(java_int_type()));
      }
      THEN("The instruction allocates the struct")
      {
        REQUIRE(
          make_query(block)[3].as<code_assignt>()[0].as<symbol_exprt>().get() ==
          allocation_symbol);
      }
    }
    THEN("The instruction assigns the symbol to \"symbol_to_assign\"")
    {
      REQUIRE(
        make_query(block)[4]
          .as<code_assignt>()[0]
          .as<symbol_exprt>()
          .get()
          .get_identifier() == "symbol_to_assign");
    }

    THEN("The instruction zero-initializes the struct")
    {
      REQUIRE(
        make_query(block)[5].as<code_assignt>()[0].get().type() ==
        test_class_type.subtype());
    }
    THEN("The instruction makes the length nondet")
    {
      REQUIRE(
        make_query(block)[6].as<code_assignt>()[0].get().type() ==
        java_int_type());
      auto side_effect = make_query(block)[6]
                           .as<code_assignt>()[1]
                           .as<side_effect_exprt>()
                           .get();
      REQUIRE(side_effect.get_statement() == ID_nondet);
    }
    THEN("The instruction adds assumption on the length")
    {
      REQUIRE(
        make_query(block)[7].as<code_assumet>()[0].get().type() ==
        bool_typet{});
    }
    THEN("The instruction allocates the array field, with the symbolic length")
    {
      REQUIRE(
        make_query(block)[8]
          .as<code_assignt>()[0]
          .as<member_exprt>()
          .get()
          .get_component_name() == "array_field");
      auto side_effect = make_query(block)[8]
                           .as<code_assignt>()[1]
                           .as<side_effect_exprt>()
                           .get();
      REQUIRE(side_effect.get_statement() == ID_java_new_array);
      make_query(side_effect)[0].as<symbol_exprt>().get();
    }
    THEN("The instruction adds additional assumptions on the length")
    {
      REQUIRE(
        make_query(block)[9].as<code_assumet>()[0].get().type() ==
        bool_typet{});
    }
    THEN("The instruction copies the data to user_specified_array_data_init")
    {
      REQUIRE(
        make_query(block)[10]
          .as<code_assignt>()[0]
          .as<symbol_exprt>()
          .get()
          .get_identifier() ==
        "java::TestClass.<clinit>:()V::user_specified_array_data_init");
    }
    THEN("The instruction assigns the array cell to 42")
    {
      REQUIRE(
        numeric_cast_v<mp_integer>(make_query(block)[11]
                                     .as<code_assignt>()[1]
                                     .as<constant_exprt>()
                                     .get()) == 42);
    }
  }
  GIVEN("An object with two fields referencing the same array")
  {
    const json_objectt json = [] {
      json_objectt entry{};
      entry["array_field_1"] = [] {
        json_objectt json;
        json["@ref"] = json_stringt{"id_of_array_2"};
        return json;
      }();
      entry["array_field_2"] = [] {
        json_objectt int_json;
        int_json["@items"] = json_arrayt{json_numbert{"42"}};
        int_json["@type"] = json_stringt{"[I"};
        int_json["@id"] = json_stringt{"id_of_array_2"};
        return int_json;
      }();
      entry["@type"] = json_stringt{"TestClass"};
      return entry;
    }();
    class_to_declared_symbols.emplace("java::TestClass", [] {
      symbolt field_symbol;
      field_symbol.base_name = "array_field_1";
      field_symbol.name = "field_name_1_for_codet";
      field_symbol.type = java_int_type();
      field_symbol.is_static_lifetime = true;
      return field_symbol;
    }());
    class_to_declared_symbols.emplace("java::TestClass", [] {
      symbolt field_symbol;
      field_symbol.base_name = "array_field_2";
      field_symbol.name = "field_name_2_for_codet";
      field_symbol.type = java_int_type();
      field_symbol.is_static_lifetime = true;
      return field_symbol;
    }());
    const irep_idt clinit_name = add_clinit(symbol_table, "TestClass");
    add_class_with_components(
      symbol_table,
      "TestClass",
      {std::pair<std::string, typet>("@class_identifier", string_typet{}),
       std::pair<std::string, typet>("array_field_1", java_array_type('i')),
       std::pair<std::string, typet>("array_field_2", java_array_type('i'))});
    // For array[int]
    add_java_array_types(symbol_table);

    const reference_typet test_class_type =
      reference_type(struct_tag_typet{"java::TestClass"});
    optionalt<ci_lazy_methods_neededt> option{};
    const code_with_references_listt code = assign_from_json(
      symbol_exprt{"symbol_to_assign", test_class_type},
      json,
      clinit_name,
      symbol_table,
      option,
      max_user_array_length,
      references);

    code_with_referencest::reference_substitutiont reference_substitution =
      [&](const std::string &reference_id) -> object_creation_referencet & {
      REQUIRE(reference_id == "id_of_array_2");
      auto it = references.find(reference_id);
      REQUIRE(it != references.end());
      return it->second;
    };
    code_blockt block;
    for(auto code_with_references : code.list)
      block.append(code_with_references->to_code(reference_substitution));

    THEN(
      "The instruction declares a symbol of TestClass* type: "
      "TestClass* malloc_site;")
    {
      const symbol_exprt allocation_symbol =
        make_query(block)[0].as<code_declt>()[0].as<symbol_exprt>().get();
      REQUIRE(allocation_symbol.type() == test_class_type);
    }
    THEN(
      "declares the array data: "
      "int[] user_specified_array_ref;")
    {
      REQUIRE(
        make_query(block)[1]
          .as<code_declt>()[0]
          .as<symbol_exprt>()
          .get()
          .type() == java_array_type('i'));
    }
    THEN(
      "declares the length: "
      "int user_specified_array_length;")
    {
      REQUIRE(
        make_query(block)[2]
          .as<code_declt>()[0]
          .as<symbol_exprt>()
          .get()
          .type() == java_int_type());
    }
    THEN(
      "declares the data:"
      "int* user_specified_array_data_init;")
    {
      REQUIRE(
        make_query(block)[3]
          .as<code_declt>()[0]
          .as<symbol_exprt>()
          .get()
          .type() == java_reference_type(java_int_type()));
    }
    THEN(
      "allocates the object:"
      "malloc_site = new TestClass();")
    {
      REQUIRE(
        make_query(block)[4]
          .as<code_assignt>()[0]
          .as<symbol_exprt>()
          .get()
          .type() == test_class_type);
      REQUIRE(
        make_query(block)[4]
          .as<code_assignt>()[1]
          .as<side_effect_exprt>()
          .get()
          .get_statement() == ID_allocate);
    }

    THEN(
      "assigns the allocated object:"
      "symbol_to_assign = malloc_site;")
    {
      REQUIRE(
        make_query(block)[5]
          .as<code_assignt>()[0]
          .as<symbol_exprt>()
          .get()
          .get_identifier() == "symbol_to_assign");
    }
    THEN(
      "zero-initialize the object:"
      "*malloc_site = {\"java::\", NULL, NULL};")
    {
      REQUIRE(
        make_query(block)[6]
          .as<code_assignt>()[0]
          .as<dereference_exprt>()[0]
          .get()
          .type() == test_class_type);
    }
    THEN(
      "allocate the array :"
      "user_specified_array_ref = new int[1];")
    {
      REQUIRE(
        make_query(block)[7].as<code_assignt>()[0].get().type() ==
        java_array_type('i'));
      const auto side_effect_expr = make_query(block)[7]
                                      .as<code_assignt>()[1]
                                      .as<side_effect_exprt>()
                                      .get();
      REQUIRE(side_effect_expr.get_statement() == ID_java_new_array);
      REQUIRE(
        numeric_cast_v<mp_integer>(
          make_query(side_effect_expr)[0].as<constant_exprt>().get()) == 1);
    }
    THEN(
      "assign array_field_1 :"
      "malloc_site->array_field_1 = user_specified_array_ref;")
    {
      REQUIRE(
        make_query(block)[8]
          .as<code_assignt>()[0]
          .as<member_exprt>()
          .get()
          .get_component_name() == "array_field_1");
    }
    THEN(
      "assign pointer to the data for initializing it:"
      "user_specified_array_data_init = user_specified_array_ref->data;")
    {
      REQUIRE(
        make_query(block)[9].as<code_assignt>()[0].get().type() ==
        java_reference_type(java_int_type()));
    }
    THEN(
      "assign the array cell value :"
      "user_specified_array_data_init[0] = 42;")
    {
      REQUIRE(
        numeric_cast_v<mp_integer>(make_query(block)[10]
                                     .as<code_assignt>()[1]
                                     .as<constant_exprt>()
                                     .get()) == 42);
    }
    THEN(
      "assign array_field_2 :"
      "malloc_site->array_field_2 = user_specified_array_ref;")
    {
      REQUIRE(
        make_query(block)[11]
          .as<code_assignt>()[0]
          .as<member_exprt>()
          .get()
          .get_component_name() == "array_field_2");
    }
  }
}
