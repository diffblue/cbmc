/*******************************************************************\

 Module: Unit tests for class_hierarchy_grapht

 Author: Diffblue Limited. All rights reserved.

\*******************************************************************/

#include <testing-utils/catch.hpp>
#include <testing-utils/load_java_class.h>

#include <goto-programs/class_hierarchy.h>

void require_parent_child_relationship(
  const std::string &parent_raw,
  const std::string &child_raw,
  const class_hierarchy_grapht &hierarchy)
{
  irep_idt parent = "java::" + parent_raw;
  irep_idt child = "java::" + child_raw;

  const class_hierarchy_grapht::nodes_by_namet &nodes_map =
    hierarchy.get_nodes_by_class_identifier();
  REQUIRE(nodes_map.count(parent) != 0);
  REQUIRE(nodes_map.count(child) != 0);
  REQUIRE(hierarchy.has_edge(nodes_map.at(parent), nodes_map.at(child)));
}

SCENARIO(
  "Output a simple class hierarchy"
  "[core][goto-programs][class_hierarchy_graph]")
{
  symbol_tablet symbol_table =
    load_java_class("HierarchyTest", "goto-programs/");
  class_hierarchy_grapht hierarchy;
  hierarchy.populate(symbol_table);

  require_parent_child_relationship(
    "HierarchyTest", "HierarchyTestChild1", hierarchy);
  require_parent_child_relationship(
    "HierarchyTest", "HierarchyTestChild2", hierarchy);
  require_parent_child_relationship(
    "HierarchyTestChild1", "HierarchyTestGrandchild", hierarchy);
  require_parent_child_relationship(
    "HierarchyTestInterface1", "HierarchyTestGrandchild", hierarchy);
  require_parent_child_relationship(
    "HierarchyTestInterface2", "HierarchyTestGrandchild", hierarchy);
}
