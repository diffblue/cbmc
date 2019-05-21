/// Author: Diffblue Ltd.

/// \file Tests for sharing-node utility

#define SN_INTERNAL_CHECKS

#include <testing-utils/use_catch.h>
#include <util/sharing_node.h>

// could be an internal node or a container node
class innert : public sharing_nodet<int, int>
{
public:
  friend void sharing_node_internals_test();
};

void sharing_node_internals_test()
{
  SECTION("Internal node test")
  {
    innert internal;
    REQUIRE(!internal.data);

    internal.write_internal();
    REQUIRE(internal.data);
    REQUIRE(internal.data.use_count() == 1);

    innert internal2(internal);
    REQUIRE(internal.use_count() == 2);
    REQUIRE(internal2.use_count() == 2);

    internal2.write_internal();
    REQUIRE(internal.use_count() == 1);
    REQUIRE(internal2.use_count() == 1);
  }

  SECTION("Container node test")
  {
    innert container;
    REQUIRE(!container.data);

    container.write_container();
    REQUIRE(container.data);
    REQUIRE(container.data.use_count() == 1);

    innert container2(container);
    REQUIRE(container.use_count() == 2);
    REQUIRE(container2.use_count() == 2);

    container2.write_container();
    REQUIRE(container.use_count() == 1);
    REQUIRE(container2.use_count() == 1);
  }
}

TEST_CASE("Sharing node internals", "[core][util]")
{
  sharing_node_internals_test();
}

TEST_CASE("Sharing node", "[core][util]")
{
  SECTION("Leaf test")
  {
    typedef sharing_nodet<int, int> leaft;

    // Basic leaf
    {
      const leaft leaf(1, 2);

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

      leaf2.set_value(3);

      REQUIRE(leaf2.get_value() == 3);
      REQUIRE(!leaf2.shares_with(leaf1));
    }
  }

  SECTION("Inner node test")
  {
    typedef sharing_nodet<int, int> innert;

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

      leaf->set_value(7);

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
    }
  }
}
