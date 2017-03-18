#include <iostream>
#include <cassert>

#include <util/sharing_map.h>

typedef sharing_mapt<irep_idt, std::string, irep_id_hash> smt;

// helpers
void fill(smt &sm)
{
  sm.insert("i", "0");
  sm.insert("j", "1");
  sm.insert("k", "2");
}

void fill2(smt &sm)
{
  sm.insert("l", "3");
  sm.insert("m", "4");
  sm.insert("n", "5");
}

// tests

void sharing_map_interface_test()
{
  std::cout << "Running interface test" << std::endl;

  // empty map
  {
    smt sm;

    assert(sm.empty());
    assert(sm.size()==0);
    assert(!sm.has_key("i"));
  }

  // insert elements
  {
    smt sm;

    smt::const_find_type r1=sm.insert(std::make_pair("i", "0"));
    assert(r1.second);

    smt::const_find_type r2=sm.insert("j", "1");
    assert(r2.second);

    smt::const_find_type r3=sm.insert(std::make_pair("i", "0"));
    assert(!r3.second);

    assert(sm.size()==2);
    assert(!sm.empty());
  }

  // place elements
  {
    smt sm1;
    smt sm2(sm1);

    smt::find_type r1=sm1.place("i", "0");
    assert(r1.second);
    assert(!sm2.has_key("i"));    

    std::string &s1=r1.first;
    s1="1";

    assert(sm1.at("i")=="1");
  }

  // retrieve elements
  {
    smt sm;
    sm.insert("i", "0");
    sm.insert("j", "1");

    const smt &sm2=sm;

    std::string s;
    s=sm2.at("i");
    assert(s=="0");

    try {
      sm2.at("k");
      assert(false);
    } catch (...) {}

    s=sm2.at("j");
    assert(s=="1");

    assert(sm.has_key("i"));
    assert(sm.has_key("j"));
    assert(!sm.has_key("k"));

    std::string &s2=sm.at("i");
    s2="3";
    assert(sm2.at("i")=="3");

    assert(sm.size()==2);

    smt::find_type r=sm.find("i");
    assert(r.second);
    r.first="4";
    assert(sm2.at("i")=="4");

    smt::const_find_type rc=sm2.find("k");
    assert(!rc.second);
  }

  // remove elements
  {
    smt sm;
    sm.insert("i", "0");
    sm.insert("j", "1");

    assert(sm.erase("k")==0);
    assert(sm.size()==2);

    assert(sm.erase("i")==1);
    assert(!sm.has_key("i"));

    assert(sm.erase("j")==1);
    assert(!sm.has_key("j"));

    sm.insert("i", "0");
    sm.insert("j", "1");

    smt sm3(sm);
  
    assert(sm.has_key("i"));
    assert(sm.has_key("j"));
    assert(sm3.has_key("i"));
    assert(sm3.has_key("j"));

    sm.erase("i");

    assert(!sm.has_key("i"));
    assert(sm.has_key("j"));

    assert(sm3.has_key("i"));
    assert(sm3.has_key("j"));

    sm3.erase("i");
    assert(!sm3.has_key("i"));
  }

  // operator[]
  {
    smt sm;

    sm["i"];
    assert(sm.has_key("i"));

    sm["i"]="0";
    assert(sm.at("i")=="0");

    sm["j"]="1";
    assert(sm.at("j")=="1");
  }
}

void sharing_map_copy_test()
{
  std::cout << "Running copy test" << std::endl;

  smt sm1;
  const smt &sm2=sm1;

  fill(sm1);

  assert(sm2.find("i").first=="0");
  assert(sm2.find("j").first=="1");
  assert(sm2.find("k").first=="2");

  smt sm3=sm1;
  const smt &sm4=sm3;

  assert(sm3.erase("l")==0);
  assert(sm3.erase("i")==1);

  assert(!sm4.has_key("i"));
  sm3.place("i", "3");
  assert(sm4.find("i").first=="3");
}

class some_keyt
{
public:
  some_keyt(size_t s) : s(s)
  {
  }

  size_t s;

  bool operator==(const some_keyt &other) const
  {
    return s==other.s;
  }
};

class some_key_hash
{
public:
  size_t operator()(const some_keyt &k) const
  {
    return k.s & 0x3;
  }
};

void sharing_map_collision_test()
{
  std::cout << "Running collision test" << std::endl;

  typedef sharing_mapt<some_keyt, std::string, some_key_hash> smt;

  smt sm;

  sm.insert(0, "a");
  sm.insert(8, "b");
  sm.insert(16, "c");

  sm.insert(1, "d");
  sm.insert(2, "e");

  sm.erase(8);

  assert(sm.has_key(0));
  assert(sm.has_key(16));

  assert(sm.has_key(1));
  assert(sm.has_key(2));

  assert(!sm.has_key(8));
}

void sharing_map_view_test()
{
  std::cout << "Running view test" << std::endl;

  // view test
  {
    smt sm;
  
    fill(sm);
  
    smt::viewt view;
    sm.get_view(view);

    assert(view.size()==3);
  }

  // delta view test (no sharing, same keys)
  {
    smt sm1;
    fill(sm1);

    smt sm2;
    fill(sm2);

    smt::delta_viewt delta_view;

    sm1.get_delta_view(sm2, delta_view);
    assert(delta_view.size()==3);

    delta_view.clear();
    sm1.get_delta_view(sm2, delta_view, false);
    assert(delta_view.size()==3);
  }

  // delta view test (all shared, same keys)
  {
    smt sm1;
    fill(sm1);

    smt sm2(sm1);
    
    smt::delta_viewt delta_view;

    sm1.get_delta_view(sm2, delta_view);
    assert(delta_view.size()==0);

    delta_view.clear();
    sm1.get_delta_view(sm2, delta_view, false);
    assert(delta_view.size()==0);
  }

  // delta view test (some sharing, same keys)
  {
    smt sm1;
    fill(sm1);

    smt sm2(sm1);
    auto r=sm2.find("i");
    assert(r.second);
    r.first="3";
    
    smt::delta_viewt delta_view;

    sm1.get_delta_view(sm2, delta_view);
    assert(delta_view.size()>0); // not everything is shared
    assert(delta_view.size()<3); // there is some sharing

    delta_view.clear();
    sm1.get_delta_view(sm2, delta_view, false);
    assert(delta_view.size()>0); // not everything is shared
    assert(delta_view.size()<3); // there is some sharing
  }

  // delta view test (no sharing, different keys)
  {
    smt sm1;
    fill(sm1);

    smt sm2;
    fill2(sm2);

    smt::delta_viewt delta_view;

    sm1.get_delta_view(sm2, delta_view);
    assert(delta_view.size()==0);

    delta_view.clear();
    sm1.get_delta_view(sm2, delta_view, false);
    assert(delta_view.size()==3);
  }
}

int main()
{
  sharing_map_interface_test();
  sharing_map_copy_test();
  sharing_map_collision_test();
  sharing_map_view_test();

  return 0;
}

