/*******************************************************************\

Module: Unit tests for class_hierarchy_grapht

Author: Diffblue Ltd.

\*******************************************************************/

#include <testing-utils/catch.hpp>
#include <java-testing-utils/load_java_class.h>

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
  "Output a simple class hierarchy graph",
  "[core][goto-programs][class_hierarchy_graph]")
{
  symbol_tablet symbol_table =
    load_java_class("HierarchyTest", "./java_bytecode/goto-programs/");
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

SCENARIO(
  "class_hierarchy_graph",
  "[core][goto-programs][class_hierarchy_graph]")
{
  symbol_tablet symbol_table =
    load_java_class("HierarchyTest", "./java_bytecode/goto-programs/");
  class_hierarchy_grapht hierarchy;
  hierarchy.populate(symbol_table);

  WHEN("Retrieving direct children of a given class")
  {
    const class_hierarchy_grapht::idst ht_direct_children =
      hierarchy.get_direct_children("java::HierarchyTest");
    THEN("The correct list of direct children should be returned")
    {
      REQUIRE(ht_direct_children.size() == 2);
      REQUIRE(
        find(
          ht_direct_children.begin(),
          ht_direct_children.end(),
          "java::HierarchyTestChild1") != ht_direct_children.end());
      REQUIRE(
        find(
          ht_direct_children.begin(),
          ht_direct_children.end(),
          "java::HierarchyTestChild2") != ht_direct_children.end());
    }
  }
  WHEN("Retrieving all children of a given class")
  {
    const class_hierarchy_grapht::idst ht_all_children =
      hierarchy.get_children_trans("java::HierarchyTest");
    THEN("The correct list of children should be returned")
    {
      REQUIRE(ht_all_children.size() == 3);
      REQUIRE(
        find(
          ht_all_children.begin(),
          ht_all_children.end(),
          "java::HierarchyTestChild1") != ht_all_children.end());
      REQUIRE(
        find(
          ht_all_children.begin(),
          ht_all_children.end(),
          "java::HierarchyTestChild2") != ht_all_children.end());
      REQUIRE(
        find(
          ht_all_children.begin(),
          ht_all_children.end(),
          "java::HierarchyTestGrandchild") != ht_all_children.end());
    }
  }
  WHEN("Retrieving all parents of a given class")
  {
    const class_hierarchy_grapht::idst htg_all_parents =
      hierarchy.get_parents_trans("java::HierarchyTestGrandchild");
    THEN("The correct list of parents should be returned")
    {
      REQUIRE(htg_all_parents.size() == 5);
      REQUIRE(
        find(
          htg_all_parents.begin(),
          htg_all_parents.end(),
          "java::HierarchyTestChild1") != htg_all_parents.end());
      REQUIRE(
        find(
          htg_all_parents.begin(),
          htg_all_parents.end(),
          "java::HierarchyTest") != htg_all_parents.end());
      REQUIRE(
        find(
          htg_all_parents.begin(),
          htg_all_parents.end(),
          "java::HierarchyTestInterface1") != htg_all_parents.end());
      REQUIRE(
        find(
          htg_all_parents.begin(),
          htg_all_parents.end(),
          "java::HierarchyTestInterface2") != htg_all_parents.end());
      REQUIRE(
        find(
          htg_all_parents.begin(),
          htg_all_parents.end(),
          "java::java.lang.Object") != htg_all_parents.end());
    }
  }
}
