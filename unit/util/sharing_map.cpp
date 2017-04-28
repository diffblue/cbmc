/*******************************************************************\

 Module: Unit tests for the util/sharing_map

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

#include <iostream>

#include <catch.hpp>
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

typedef size_t some_keyt;

class some_key_hasht
{
public:
  size_t operator()(const some_keyt &k) const
  {
    return k & 0x3;
  }
};



TEST_CASE("sharing map", "[core][util][sharing_map]")
{
  SECTION("interface")
  {
    SECTION("empty map")
    {
      smt sm;
      REQUIRE(sm.empty());
      REQUIRE(sm.size()==0);
      REQUIRE(!sm.has_key("i"));
    }

    SECTION("insert elements")
    {
      smt sm;

      smt::const_find_type r1=sm.insert(std::make_pair("i", "0"));
      REQUIRE(r1.second);

      smt::const_find_type r2=sm.insert("j", "1");
      REQUIRE(r2.second);

      smt::const_find_type r3=sm.insert(std::make_pair("i", "0"));
      REQUIRE(!r3.second);

      REQUIRE(sm.size()==2);
      REQUIRE_FALSE(sm.empty());
    }

    SECTION("place elements")
    {
      smt sm1;
      smt sm2(sm1);

      smt::find_type r1=sm1.place("i", "0");
      REQUIRE(r1.second);
      REQUIRE_FALSE(sm2.has_key("i"));

      std::string &s1=r1.first;
      s1="1";

      REQUIRE(sm1.at("i")=="1");
    }
    SECTION("retrieve elements")
    {
      smt sm;
      sm.insert("i", "0");
      sm.insert("j", "1");

      const smt &sm2=sm;

      std::string s;
      s=sm2.at("i");
      REQUIRE(s=="0");

      try
      {
        sm2.at("k");
        REQUIRE(false);
      } catch (...) {}

      s=sm2.at("j");
      REQUIRE(s=="1");

      REQUIRE(sm.has_key("i"));
      REQUIRE(sm.has_key("j"));
      REQUIRE_FALSE(sm.has_key("k"));

      std::string &s2=sm.at("i");
      s2="3";
      REQUIRE(sm2.at("i")=="3");

      REQUIRE(sm.size()==2);

      smt::find_type r=sm.find("i");
      REQUIRE(r.second);
      r.first="4";
      REQUIRE(sm2.at("i")=="4");

      smt::const_find_type rc=sm2.find("k");
      REQUIRE_FALSE(rc.second);
    }


    SECTION("remove elements")
    {
      smt sm;
      sm.insert("i", "0");
      sm.insert("j", "1");

      REQUIRE(sm.erase("k")==0);
      REQUIRE(sm.size()==2);

      REQUIRE(sm.erase("i")==1);
      REQUIRE(!sm.has_key("i"));

      REQUIRE(sm.erase("j")==1);
      REQUIRE(!sm.has_key("j"));

      sm.insert("i", "0");
      sm.insert("j", "1");

      smt sm3(sm);

      REQUIRE(sm.has_key("i"));
      REQUIRE(sm.has_key("j"));
      REQUIRE(sm3.has_key("i"));
      REQUIRE(sm3.has_key("j"));

      sm.erase("i");

      REQUIRE(!sm.has_key("i"));
      REQUIRE(sm.has_key("j"));

      REQUIRE(sm3.has_key("i"));
      REQUIRE(sm3.has_key("j"));

      sm3.erase("i");
      REQUIRE(!sm3.has_key("i"));
    }

    SECTION("operator[]")
    {
      smt sm;

      sm["i"];
      REQUIRE(sm.has_key("i"));

      sm["i"]="0";
      REQUIRE(sm.at("i")=="0");

      sm["j"]="1";
      REQUIRE(sm.at("j")=="1");
    }
  }

  SECTION("copy")
  {
    smt sm1;
    const smt &sm2=sm1;

    fill(sm1);

    REQUIRE(sm2.find("i").first=="0");
    REQUIRE(sm2.find("j").first=="1");
    REQUIRE(sm2.find("k").first=="2");

    smt sm3=sm1;
    const smt &sm4=sm3;

    REQUIRE(sm3.erase("l")==0);
    REQUIRE(sm3.erase("i")==1);

    REQUIRE(!sm4.has_key("i"));
    sm3.place("i", "3");
    REQUIRE(sm4.find("i").first=="3");
  }

  SECTION("collision_test")
  {
    typedef sharing_mapt<some_keyt, std::string, some_key_hasht> sm2t;

    sm2t sm;

    sm.insert(0, "a");
    sm.insert(8, "b");
    sm.insert(16, "c");

    sm.insert(1, "d");
    sm.insert(2, "e");

    sm.erase(8);

    REQUIRE(sm.has_key(0));
    REQUIRE(sm.has_key(16));

    REQUIRE(sm.has_key(1));
    REQUIRE(sm.has_key(2));

    REQUIRE(!sm.has_key(8));
  }

  SECTION("view_test")
  {
    SECTION("view test")
    {
      smt sm;

      fill(sm);

      smt::viewt view;
      sm.get_view(view);

      REQUIRE(view.size()==3);
    }

    SECTION("delta view test (no sharing, same keys)")
    {
      smt sm1;
      fill(sm1);

      smt sm2;
      fill(sm2);

      smt::delta_viewt delta_view;

      sm1.get_delta_view(sm2, delta_view);
      REQUIRE(delta_view.size()==3);

      delta_view.clear();
      sm1.get_delta_view(sm2, delta_view, false);
      REQUIRE(delta_view.size()==3);
    }

    SECTION("delta view test (all shared, same keys)")
    {
      smt sm1;
      fill(sm1);

      smt sm2(sm1);

      smt::delta_viewt delta_view;

      sm1.get_delta_view(sm2, delta_view);
      REQUIRE(delta_view.size()==0);

      delta_view.clear();
      sm1.get_delta_view(sm2, delta_view, false);
      REQUIRE(delta_view.size()==0);
    }

    SECTION("delta view test (some sharing, same keys)")
    {
      smt sm1;
      fill(sm1);

      smt sm2(sm1);
      auto r=sm2.find("i");
      REQUIRE(r.second);
      r.first="3";

      smt::delta_viewt delta_view;

      sm1.get_delta_view(sm2, delta_view);
      REQUIRE(delta_view.size()>0); // not everything is shared
      REQUIRE(delta_view.size()<3); // there is some sharing

      delta_view.clear();
      sm1.get_delta_view(sm2, delta_view, false);
      REQUIRE(delta_view.size()>0); // not everything is shared
      REQUIRE(delta_view.size()<3); // there is some sharing
    }

    SECTION("delta view test (no sharing, different keys)")
    {
      smt sm1;
      fill(sm1);

      smt sm2;
      fill2(sm2);

      smt::delta_viewt delta_view;

      sm1.get_delta_view(sm2, delta_view);
      REQUIRE(delta_view.size()==0);

      delta_view.clear();
      sm1.get_delta_view(sm2, delta_view, false);
      REQUIRE(delta_view.size()==3);
    }
  }
}


