/*******************************************************************\

Module: Unit tests for class_hierarchyt output functions

Author: Diffblue Ltd.

\*******************************************************************/

#include <testing-utils/catch.hpp>
#include <java-testing-utils/load_java_class.h>

#include <goto-programs/class_hierarchy.h>

#include <iostream>
#include <sstream>

void require_parent_child_relationship(
  const std::string &parent_raw,
  const std::string &child_raw,
  const std::string &output_dot)
{
  std::string parent = "java::" + parent_raw;
  std::string child = "java::" + child_raw;

  std::stringstream dot_expectation;

  dot_expectation << "\"" << child << "\" -> \"" << parent << "\"";

  REQUIRE(output_dot.find(dot_expectation.str()) != std::string::npos);
}

SCENARIO(
  "Output a simple class hierarchy",
  "[core][goto-programs][class_hierarchy]")
{
  symbol_tablet symbol_table =
    load_java_class("HierarchyTest", "./java_bytecode/goto-programs/");
  class_hierarchyt hierarchy;

  std::stringstream output_stream;
  std::stringstream output_dot_stream;

  hierarchy(symbol_table);
  hierarchy.output_dot(output_dot_stream);

  std::string output_dot = output_dot_stream.str();

  require_parent_child_relationship(
    "HierarchyTest", "HierarchyTestChild1", output_dot);
  require_parent_child_relationship(
    "HierarchyTest", "HierarchyTestChild2", output_dot);
  require_parent_child_relationship(
    "HierarchyTestChild1", "HierarchyTestGrandchild", output_dot);
  require_parent_child_relationship(
    "HierarchyTestInterface1", "HierarchyTestGrandchild", output_dot);
  require_parent_child_relationship(
    "HierarchyTestInterface2", "HierarchyTestGrandchild", output_dot);
}
