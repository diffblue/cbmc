/// Author: Diffblue Ltd.

/// \file Tests for sharing-node utility

#define SN_INTERNAL_CHECKS

#include <testing-utils/use_catch.h>
#include <util/sharing_node.h>

void sharing_node_test()
{
  SECTION("Leaf test")
  {
    typedef sharing_node_leaft<int, int> leaft;

    // Basic leaf
    {
      const leaft leaf(1, 2);

      REQUIRE(!leaf.empty());
      REQUIRE(leaf.shares_with(leaf));
      REQUIRE(leaf.get_key() == 1);
      REQUIRE(leaf.get_value() == 2);
    }

    // Shared leaf
    {
      const leaft leaf1(1, 2);
      const leaft leaf2(leaf1);

      REQUIRE(leaf1.shares_with(leaf2));
      REQUIRE(leaf2.get_key() == 1);
      REQUIRE(leaf2.get_value() == 2);
    }

    // Modify shared leaf
    {
      const leaft leaf1(1, 2);
      leaft leaf2(leaf1);

      REQUIRE(leaf2.shares_with(leaf1));

      auto &v = leaf2.get_value();
      v = 3;
      REQUIRE(leaf2.get_value() == 3);
      REQUIRE(!leaf2.shares_with(leaf1));
    }

    // Detaching
    {
      leaft leaf(1, 2);

      auto p = leaf.data.get();
      leaf.write();

      REQUIRE(leaf.data.get() == p);
    }
  }

  SECTION("Inner node test")
  {
    typedef sharing_node_innert<int, int> innert;

    // Empty container
    {
      const innert c;

      REQUIRE(c.empty());
    }

    // Single container
    {
      innert c;
      const innert &cc = c;

      c.place_leaf(1, 2);
      c.place_leaf(3, 4);

      REQUIRE(!cc.get_container().empty());
      REQUIRE(cc.find_leaf(1) != nullptr);
      REQUIRE(cc.find_leaf(3) != nullptr);

      auto leaf = c.find_leaf(1);
      REQUIRE(leaf->get_key() == 1);
      REQUIRE(leaf->get_value() == 2);

      c.remove_leaf(1);
      c.remove_leaf(3);

      REQUIRE(cc.get_container().empty());
    }

    // Shared container
    {
      innert c1;
      c1.place_leaf(1, 2);
      c1.place_leaf(3, 4);

      innert c2(c1);
      auto leaf = c2.find_leaf(1);
      auto &v = leaf->get_value();
      v = 7;

      REQUIRE(!c1.shares_with(c2));

      {
        auto leaf1 = c1.find_leaf(1);
        auto leaf2 = c2.find_leaf(1);

        REQUIRE(!leaf1->shares_with(*leaf2));
      }

      {
        auto leaf1 = c1.find_leaf(3);
        auto leaf2 = c2.find_leaf(3);

        REQUIRE(leaf1->shares_with(*leaf2));
      }
    }

    // Internal node mapping to other internal nodes
    {
      innert i;
      const innert &ci = i;

      i.add_child(0);

      REQUIRE(!i.empty());
      REQUIRE(!i.get_to_map().empty());
      REQUIRE(ci.find_child(0) != nullptr);

      i.remove_child(0);

      REQUIRE(i.get_to_map().empty());
      REQUIRE(ci.find_child(0) == nullptr);

      innert *p;

      p = i.add_child(1);

      REQUIRE(p != nullptr);
    }
  }

  SECTION("Combined")
  {
    typedef sharing_node_leaft<int, int> leaft;
    typedef sharing_node_innert<int, int> innert;

    innert map;

    REQUIRE(map.empty());

    innert *ip;
    innert *cp;
    leaft *lp;

    // Add 0 -> 0 -> (0, 1)

    ip = &map;

    ip = ip->add_child(0);
    REQUIRE(ip != nullptr);

    cp = ip->add_child(0);
    REQUIRE(cp != nullptr);

    lp = cp->place_leaf(0, 1);
    REQUIRE(lp != nullptr);

    // Add 1 -> 2 -> (3, 4)

    ip = &map;

    ip = ip->add_child(1);
    REQUIRE(ip != nullptr);

    cp = ip->add_child(2);
    REQUIRE(cp != nullptr);

    lp = cp->place_leaf(3, 4);
    REQUIRE(lp != nullptr);

    // Add 1 -> 3 -> (4, 5)

    ip = &map;

    ip = ip->add_child(1);
    REQUIRE(ip != nullptr);

    cp = ip->add_child(3);
    REQUIRE(cp != nullptr);

    lp = cp->place_leaf(4, 5);
    REQUIRE(lp != nullptr);

    // Copy

    innert map2(map);

    REQUIRE(map2.shares_with(map));
  }
}

TEST_CASE("Sharing node")
{
  sharing_node_test();
}
