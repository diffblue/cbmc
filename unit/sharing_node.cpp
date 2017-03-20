#include <iostream>
#include <cassert>

#include <util/sharing_node.h>

void sharing_node_test()
{
  std::cout << "Running sharing node test" << std::endl;

  typedef sharing_nodet<std::string, std::string> snt;

  // internal node test
  {
    snt sn1;
    const snt &sn2=sn1;

    const snt *p2;

    assert(sn1.is_empty());

    sn1.add_child(0);
    sn1.add_child(1);
    sn1.add_child(2);

    assert(!sn2.is_empty());
    assert(sn2.is_internal());
    assert(!sn2.is_container());
    assert(!sn2.is_leaf());

    assert(sn2.get_sub().size()==3);

    p2=sn2.find_child(0);
    assert(p2!=nullptr);

    p2=sn1.find_child(0);
    assert(p2!=nullptr);

    p2=sn2.find_child(3);
    assert(p2==nullptr);

    p2=sn1.find_child(3);
    assert(p2==nullptr);

    sn1.remove_child(0);
    assert(sn2.get_sub().size()==2);

    sn1.clear();
    assert(sn2.is_empty());
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

    assert(p1->find_leaf("a")==nullptr);
    assert(p2->find_leaf("a")==nullptr);

    p1->place_leaf("a", "b");
    assert(p2->get_container().size()==1);
    p1->place_leaf("c", "d");
    assert(p2->get_container().size()==2);

    assert(p2->is_container());

    p1->remove_leaf("a");
    assert(p2->get_container().size()==1);
  }

  // copy test 1
  {
    snt sn1;
    snt sn2;

    sn2=sn1;
    assert(sn1.data.use_count()==3);
    assert(sn2.data.use_count()==3);

    sn1.add_child(0);
    assert(sn1.data.use_count()==1);
    // the newly created node is empty as well
    assert(sn2.data.use_count()==3);

    sn2=sn1;
    assert(sn2.data.use_count()==2);
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

    assert(sn1.is_internal());
    assert(sn2.is_internal());

    sn1.remove_child(0);
    assert(sn1c.get_sub().size()==1);

    assert(sn2c.get_sub().size()==2);
  }
}

int main()
{
  sharing_node_test();  

  return 0;
}

