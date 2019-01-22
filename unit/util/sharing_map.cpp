/*******************************************************************\

Module: Unit tests for sharing map

Author: Daniel Poetzl

\*******************************************************************/

#define SM_INTERNAL_CHECKS
#define SN_INTERNAL_CHECKS

#include <climits>
#include <random>
#include <set>

#include <testing-utils/use_catch.h>
#include <util/sharing_map.h>

class smt : public sharing_mapt<irep_idt, std::string, irep_id_hash>
{
  friend void sharing_map_interface_test();
  friend void sharing_map_copy_test();
  friend void sharing_map_collision_test();
  friend void sharing_map_view_test();
  friend void sharing_map_sharing_stats_test();
};

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
  SECTION("Empty map")
  {
    smt sm;

    REQUIRE(sm.empty());
    REQUIRE(sm.size() == 0);
    REQUIRE(!sm.has_key("i"));
  }

  SECTION("Insert elements")
  {
    smt sm;

    smt::const_find_type r1 = sm.insert(std::make_pair("i", "0"));
    REQUIRE(r1.second);

    smt::const_find_type r2 = sm.insert("j", "1");
    REQUIRE(r2.second);

    smt::const_find_type r3 = sm.insert(std::make_pair("i", "0"));
    REQUIRE(!r3.second);

    REQUIRE(sm.size() == 2);
    REQUIRE(!sm.empty());
  }

  SECTION("Place elements")
  {
    smt sm1;
    smt sm2(sm1);

    smt::find_type r1 = sm1.place("i", "0");
    REQUIRE(r1.second);
    REQUIRE(!sm2.has_key("i"));

    std::string &s1 = r1.first;
    s1 = "1";

    REQUIRE(sm1.at("i") == "1");
  }

  SECTION("Retrieve elements")
  {
    smt sm;
    sm.insert("i", "0");
    sm.insert("j", "1");

    const smt &sm2 = sm;

    std::string s;
    s = sm2.at("i");
    REQUIRE(s == "0");

    try
    {
      sm2.at("k");
      REQUIRE(false);
    }
    catch(...)
    {
    }

    s = sm2.at("j");
    REQUIRE(s == "1");

    REQUIRE(sm.has_key("i"));
    REQUIRE(sm.has_key("j"));
    REQUIRE(!sm.has_key("k"));

    std::string &s2 = sm.at("i");
    s2 = "3";
    REQUIRE(sm2.at("i") == "3");

    REQUIRE(sm.size() == 2);

    smt::find_type r = sm.find("i");
    REQUIRE(r.second);
    r.first = "4";
    REQUIRE(sm2.at("i") == "4");

    smt::const_find_type rc = sm2.find("k");
    REQUIRE(!rc.second);
  }

  SECTION("Remove elements")
  {
    smt sm;
    sm.insert("i", "0");
    sm.insert("j", "1");

    REQUIRE(sm.erase("k") == 0);
    REQUIRE(sm.size() == 2);

    REQUIRE(sm.erase("i") == 1);
    REQUIRE(!sm.has_key("i"));

    REQUIRE(sm.erase("j") == 1);
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

  SECTION("Subscript operator")
  {
    smt sm;

    sm["i"];
    REQUIRE(sm.has_key("i"));

    sm["i"] = "0";
    REQUIRE(sm.at("i") == "0");

    sm["j"] = "1";
    REQUIRE(sm.at("j") == "1");
  }
}

void sharing_map_copy_test()
{
  smt sm1;
  const smt &sm2 = sm1;

  fill(sm1);

  REQUIRE(sm2.find("i").first == "0");
  REQUIRE(sm2.find("j").first == "1");
  REQUIRE(sm2.find("k").first == "2");

  smt sm3 = sm1;
  const smt &sm4 = sm3;

  REQUIRE(sm3.erase("l") == 0);
  REQUIRE(sm3.erase("i") == 1);

  REQUIRE(!sm4.has_key("i"));
  sm3.place("i", "3");
  REQUIRE(sm4.find("i").first == "3");
}

class some_keyt
{
public:
  some_keyt() : s(0)
  {
  }

  some_keyt(size_t s) : s(s)
  {
  }

  size_t s;

  bool operator==(const some_keyt &other) const
  {
    return s == other.s;
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
  typedef sharing_mapt<some_keyt, std::string, some_key_hash> smt;

  smt sm;

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

void sharing_map_view_test()
{
  SECTION("View of empty map")
  {
    smt sm;
    smt::viewt view;

    sm.get_view(view);
  }

  SECTION("View")
  {
    typedef std::pair<dstringt, std::string> pt;

    smt sm;
    smt::viewt view;
    std::vector<pt> pairs;

    auto sort_view = [&pairs, &view]() {
      pairs.clear();
      for(auto &p : view)
      {
        pairs.push_back({p.first, p.second});
      }
      std::sort(pairs.begin(), pairs.end());
    };

    fill(sm);

    sm.get_view(view);

    REQUIRE(view.size() == 3);

    sort_view();

    REQUIRE((pairs[0] == pt("i", "0")));
    REQUIRE((pairs[1] == pt("j", "1")));
    REQUIRE((pairs[2] == pt("k", "2")));

    sm.insert("l", "3");

    view.clear();
    sm.get_view(view);

    REQUIRE(view.size() == 4);

    sort_view();

    REQUIRE((pairs[3] == pt("l", "3")));
  }

  SECTION("Delta view (no sharing, same keys)")
  {
    smt sm1;
    fill(sm1);

    smt sm2;
    fill(sm2);

    smt::delta_viewt delta_view;

    sm1.get_delta_view(sm2, delta_view);
    REQUIRE(delta_view.size() == 3);

    delta_view.clear();
    sm1.get_delta_view(sm2, delta_view, false);
    REQUIRE(delta_view.size() == 3);
  }

  SECTION("delta view (all shared, same keys)")
  {
    smt sm1;
    fill(sm1);

    smt sm2(sm1);

    smt::delta_viewt delta_view;

    sm1.get_delta_view(sm2, delta_view);
    REQUIRE(delta_view.size() == 0);

    delta_view.clear();
    sm1.get_delta_view(sm2, delta_view, false);
    REQUIRE(delta_view.size() == 0);
  }

  SECTION("delta view (some sharing, same keys)")
  {
    smt sm1;
    fill(sm1);

    smt sm2(sm1);
    auto r = sm2.find("i");
    REQUIRE(r.second);
    r.first = "3";

    smt::delta_viewt delta_view;

    sm1.get_delta_view(sm2, delta_view);
    REQUIRE(delta_view.size() > 0); // not everything is shared
    REQUIRE(delta_view.size() < 3); // there is some sharing

    delta_view.clear();
    sm1.get_delta_view(sm2, delta_view, false);
    REQUIRE(delta_view.size() > 0); // not everything is shared
    REQUIRE(delta_view.size() < 3); // there is some sharing
  }

  SECTION("delta view (no sharing, different keys)")
  {
    smt sm1;
    fill(sm1);

    smt sm2;
    fill2(sm2);

    smt::delta_viewt delta_view;

    sm1.get_delta_view(sm2, delta_view);
    REQUIRE(delta_view.size() == 0);

    delta_view.clear();
    sm1.get_delta_view(sm2, delta_view, false);
    REQUIRE(delta_view.size() == 3);
  }
}

void sharing_map_sharing_stats_test()
{
  SECTION("count nodes")
  {
    std::set<void *> marked;
    smt sm;
    int count = 0;

    count = sm.count_unmarked_nodes(false, marked, false);
    REQUIRE(count == 0);

    count = sm.count_unmarked_nodes(true, marked, false);
    REQUIRE(count == 0);

    sm.insert("i", "1");
    count = sm.count_unmarked_nodes(false, marked, false);
    REQUIRE(count == 8);

    count = sm.count_unmarked_nodes(true, marked, false);
    REQUIRE(count == 1);

    sm.clear();
    fill(sm);
    count = sm.count_unmarked_nodes(true, marked, false);
    REQUIRE(count == 3);
  }

  SECTION("marking")
  {
    std::set<void *> marked;
    smt sm;

    fill(sm);

    sm.count_unmarked_nodes(false, marked, true);
    REQUIRE(marked.empty());

    smt sm2(sm);
    sm.count_unmarked_nodes(false, marked, true);
    REQUIRE(marked.size() == 1);

    marked.clear();
    smt sm3(sm);
    sm3["x"];
    sm.count_unmarked_nodes(false, marked, true);
    REQUIRE(marked.size() >= 2);
  }

  SECTION("sharing stats")
  {
    std::vector<smt> v;
    smt::sharing_map_statst sms;

    SECTION("sharing stats no sharing")
    {
      v.emplace_back();
      v.emplace_back();

      REQUIRE(v.size() == 2);

      // Empty maps
      sms = smt::get_sharing_stats(v.begin(), v.end());
      REQUIRE(sms.num_nodes == 0);
      REQUIRE(sms.num_unique_nodes == 0);
      REQUIRE(sms.num_leafs == 0);
      REQUIRE(sms.num_unique_leafs == 0);

      smt &sm1 = v.at(0);
      smt &sm2 = v.at(1);

      fill(sm1);
      fill(sm2);

      // Non-empty maps
      sms = smt::get_sharing_stats(v.begin(), v.end());
      REQUIRE(sms.num_leafs == 6);
      REQUIRE(sms.num_unique_leafs == 6);
    }

    SECTION("sharing stats sharing 1")
    {
      smt sm1;
      fill(sm1);
      v.push_back(sm1);

      smt sm2(sm1);
      v.push_back(sm2);

      sms = smt::get_sharing_stats(v.begin(), v.end());
      REQUIRE(sms.num_leafs == 6);
      REQUIRE(sms.num_unique_leafs == 3);
    }

    SECTION("sharing stats sharing 2")
    {
      smt sm1;
      fill(sm1);
      v.push_back(sm1);

      smt sm2(sm1);
      v.push_back(sm2);

      smt sm3(sm1);
      // new
      sm3["x"];
      v.push_back(sm3);

      smt sm4(sm1);
      // existing
      sm4["i"];
      v.push_back(sm4);

      sms = smt::get_sharing_stats(v.begin(), v.end());
      REQUIRE(sms.num_leafs == 13);
      REQUIRE(sms.num_unique_leafs == 5);
    }
  }

  SECTION("sharing stats map")
  {
    std::map<irep_idt, smt> m;

    smt sm1;
    fill(sm1);

    smt sm2(sm1);

    m["a"] = sm1;
    m["b"] = sm2;

    smt::sharing_map_statst sms;
    sms = smt::get_sharing_stats_map(m.begin(), m.end());
    REQUIRE(sms.num_leafs == 6);
    REQUIRE(sms.num_unique_leafs == 3);
  }
}

TEST_CASE("Sharing map interface")
{
  sharing_map_interface_test();
}

TEST_CASE("Sharing map copying")
{
  sharing_map_copy_test();
}

TEST_CASE("Sharing map collisions")
{
  sharing_map_collision_test();
}

TEST_CASE("Sharing map views")
{
  sharing_map_view_test();
}

TEST_CASE("Sharing map sharing stats")
{
  sharing_map_sharing_stats_test();
}
