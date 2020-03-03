/*******************************************************************\

Module: Unit tests for the structed_datat related classes

Author: Thomas Kiley

\*******************************************************************/

#include <testing-utils/use_catch.h>
#include <util/structured_data.h>

TEST_CASE("label", "[core][util][structured_data][label]")
{
  SECTION("Empty label")
  {
    labelt empty_label({});
    REQUIRE(empty_label.camel_case() == "");
    REQUIRE(empty_label.kebab_case() == "");
    REQUIRE(empty_label.snake_case() == "");
    REQUIRE(empty_label.pretty() == "");
  }
  SECTION("Single element")
  {
    labelt empty_label({"hello"});
    REQUIRE(empty_label.camel_case() == "hello");
    REQUIRE(empty_label.kebab_case() == "hello");
    REQUIRE(empty_label.snake_case() == "hello");
    REQUIRE(empty_label.pretty() == "Hello");
  }
  SECTION("Two elements")
  {
    labelt empty_label({"hello", "goodbye"});
    REQUIRE(empty_label.camel_case() == "helloGoodbye");
    REQUIRE(empty_label.kebab_case() == "hello-goodbye");
    REQUIRE(empty_label.snake_case() == "hello_goodbye");
    REQUIRE(empty_label.pretty() == "Hello goodbye");
  }
  SECTION("Odd casing elements")
  {
    labelt empty_label({"HelLo", "Goodbye"});
    REQUIRE(empty_label.camel_case() == "helloGoodbye");
    REQUIRE(empty_label.kebab_case() == "hello-goodbye");
    REQUIRE(empty_label.snake_case() == "hello_goodbye");
    REQUIRE(empty_label.pretty() == "Hello goodbye");
  }
}

TEST_CASE("Label equality", "[core][util][structured_data][label]")
{
  labelt empty_label({});
  labelt single_label({"a"});
  labelt capital_label({"A"});
  labelt b_label({"b"});
  labelt multi_label({"b", "c", "d"});
  labelt multi_label2({"b", "d", "d"});

  REQUIRE(empty_label < single_label);
  REQUIRE(empty_label < capital_label);
  REQUIRE(empty_label < b_label);
  REQUIRE(empty_label < multi_label);
  REQUIRE(empty_label < multi_label2);

  REQUIRE_FALSE(single_label < capital_label);
  REQUIRE_FALSE(capital_label < single_label);

  REQUIRE(single_label < b_label);
  REQUIRE(single_label < multi_label);
  REQUIRE(single_label < multi_label2);

  REQUIRE(capital_label < b_label);
  REQUIRE(capital_label < multi_label);
  REQUIRE(capital_label < multi_label2);

  REQUIRE(b_label < multi_label);
  REQUIRE(b_label < multi_label2);

  REQUIRE(multi_label < multi_label2);
}

TEST_CASE("Convert structured_datat", "[core][util][structured_data]")
{
  GIVEN("Empty structured data")
  {
    structured_datat empty_data{{}};

    THEN("Empty json object")
    {
      REQUIRE(to_json(empty_data) == json_nullt());
    }

    THEN("Empty xml object")
    {
      REQUIRE(to_xml(empty_data).elements.empty());
      REQUIRE(to_xml(empty_data).data.empty());
    }

    THEN("Empty pretty object")
    {
      REQUIRE(to_pretty(empty_data) == "");
    }
  }
  GIVEN("Single node XML")
  {
    const labelt label = labelt{{"node", "name"}};
    const structured_data_entryt entry =
      structured_data_entryt::data_node(json_stringt{"nodeValue"});
    structured_datat single_node{{{label, entry}}};

    THEN("Appropriate json object")
    {
      json_objectt expected;
      expected["nodeName"] = json_stringt{"nodeValue"};
      REQUIRE(to_json(single_node) == expected);
    }

    THEN("Appropriate xml object")
    {
      xmlt expected_xml{"node-name"};
      expected_xml.data = "nodeValue";
      auto result = to_xml(single_node);
      REQUIRE(result == expected_xml);
    }

    THEN("Appropriate pretty object")
    {
      REQUIRE(to_pretty(single_node) == "Node name: nodeValue");
    }
  }
  GIVEN("Nested nodes")
  {
    const labelt child1_label = labelt{{"child", "1"}};
    const structured_data_entryt child1_value =
      structured_data_entryt::data_node(json_stringt{"c1v"});
    const labelt child2_label = labelt{{"child", "2"}};
    const structured_data_entryt child2_value =
      structured_data_entryt::data_node(json_stringt{"c2v"});
    structured_datat single_node{
      {{child1_label, child1_value}, {child2_label, child2_value}}};

    THEN("Appropriate json object")
    {
      json_objectt expected;
      expected["child1"] = json_stringt{"c1v"};
      expected["child2"] = json_stringt{"c2v"};
      REQUIRE(to_json(single_node) == expected);
    }

    THEN("Empty xml object")
    {
      xmlt expected_xml{"root"};
      xmlt expected_child1 = xmlt{"child-1"};
      expected_child1.data = "c1v";
      xmlt expected_child2 = xmlt{"child-2"};
      expected_child2.data = "c2v";
      expected_xml.elements = {{expected_child1, expected_child2}};
      auto result = to_xml(single_node);
      REQUIRE(result == expected_xml);
    }

    THEN("Empty pretty object")
    {
      std::string expected =
        "Child 1: c1v\n"
        "Child 2: c2v";
      REQUIRE(to_pretty(single_node) == expected);
    }
  }
  SECTION("Non-string data")
  {
    const labelt child1_label = labelt{{"child", "1"}};
    const structured_data_entryt child1_value =
      structured_data_entryt::data_node(json_numbert{"10"});

    structured_datat single_node{{{child1_label, child1_value}}};

    THEN("Appropriate json object")
    {
      json_objectt expected;
      expected["child1"] = json_numbert{"10"};
      REQUIRE(to_json(single_node) == expected);
    }

    THEN("Empty xml object")
    {
      xmlt expected_xml = xmlt{"child-1"};
      expected_xml.data = "10";
      auto result = to_xml(single_node);
      REQUIRE(result == expected_xml);
    }

    THEN("Empty pretty object")
    {
      std::string expected = "Child 1: 10";
      REQUIRE(to_pretty(single_node) == expected);
    }
  }
}
