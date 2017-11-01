// Copyright 2016-2017 DiffBlue Limited. All Rights Reserved.

/// \file Tests for sharing-node utility

#include <iostream>
#include <cassert>

#include <util/sharing_node.h>
#include <testing-utils/catch.hpp>

void sharing_node_test()
{
  typedef sharing_nodet<std::string, std::string> snt;

  // internal node test
  {
    snt sn1;
    const snt &sn2=sn1;

    const snt *p2;

    REQUIRE(sn1.is_empty());

    sn1.add_child(0);
    sn1.add_child(1);
    sn1.add_child(2);

    REQUIRE(!sn2.is_empty());
    REQUIRE(sn2.is_internal());
    REQUIRE(!sn2.is_container());
    REQUIRE(!sn2.is_leaf());

    REQUIRE(sn2.get_sub().size()==3);

    p2=sn2.find_child(0);
    REQUIRE(p2!=nullptr);

    p2=sn1.find_child(0);
    REQUIRE(p2!=nullptr);

    p2=sn2.find_child(3);
    REQUIRE(p2==nullptr);

    p2=sn1.find_child(3);
    REQUIRE(p2==nullptr);

    sn1.remove_child(0);
    REQUIRE(sn2.get_sub().size()==2);

    sn1.clear();
    REQUIRE(sn2.is_empty());
  }

  // container node test
  {
    snt sn1;

    snt *p1;
    const snt *p2;

    sn1.add_child(0);
    sn1.add_child(1);

    p1=sn1.add_child(2);
    p2=p1;

    REQUIRE(p1->find_leaf("a")==nullptr);
    REQUIRE(p2->find_leaf("a")==nullptr);

    p1->place_leaf("a", "b");
    REQUIRE(p2->get_container().size()==1);
    p1->place_leaf("c", "d");
    REQUIRE(p2->get_container().size()==2);

    REQUIRE(p2->is_container());

    p1->remove_leaf("a");
    REQUIRE(p2->get_container().size()==1);
  }

  // copy test 1
  {
    snt sn1;
    snt sn2;

    sn2=sn1;
    REQUIRE(sn1.data.use_count()==3);
    REQUIRE(sn2.data.use_count()==3);

    sn1.add_child(0);
    REQUIRE(sn1.data.use_count()==1);
    // the newly created node is empty as well
    REQUIRE(sn2.data.use_count()==3);

    sn2=sn1;
    REQUIRE(sn2.data.use_count()==2);
  }

  // copy test 2
  {
    snt sn1;
    const snt &sn1c=sn1;
    snt *p;

    p=sn1.add_child(0);
    p->place_leaf("x", "y");

    p=sn1.add_child(1);
    p->place_leaf("a", "b");
    p->place_leaf("c", "d");

    snt sn2;
    const snt &sn2c=sn2;
    sn2=sn1;

    REQUIRE(sn1.is_internal());
    REQUIRE(sn2.is_internal());

    sn1.remove_child(0);
    REQUIRE(sn1c.get_sub().size()==1);

    REQUIRE(sn2c.get_sub().size()==2);
  }
}

TEST_CASE("Sharing node")
{
  sharing_node_test();
}
