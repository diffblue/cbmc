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

typedef sharing_mapt<irep_idt, std::string, false, irep_id_hash>
  sharing_map_standardt;

class sharing_map_internalt : public sharing_map_standardt
{
  friend void sharing_map_internals_test();
};

typedef sharing_mapt<irep_idt, std::string, true, irep_id_hash>
  sharing_map_error_checkt;

// helpers
void fill(sharing_map_standardt &sm)
{
  sm.insert("i", "0");
  sm.insert("j", "1");
  sm.insert("k", "2");
}

void fill2(sharing_map_standardt &sm)
{
  sm.insert("l", "3");
  sm.insert("m", "4");
  sm.insert("n", "5");
}

// tests

class some_keyt
{
public:
  some_keyt() : s(0)
  {
  }

  explicit some_keyt(size_t s) : s(s)
  {
  }

  size_t s;

  bool operator==(const some_keyt &other) const
  {
    return s == other.s;
  }
};

class some_key_hasht
{
public:
  size_t operator()(const some_keyt &k) const
  {
    return k.s & 0x3;
  }
};

void sharing_map_internals_test()
{
  SECTION("count nodes")
  {
    std::set<const void *> marked;
    sharing_map_internalt sm;
    std::size_t count = 0;

    count = sm.count_unmarked_nodes(false, marked, false);
    REQUIRE(count == 0);
    REQUIRE(marked.empty());

    count = sm.count_unmarked_nodes(true, marked, false);
    REQUIRE(count == 0);
    REQUIRE(marked.empty());

    sm.insert("i", "1");
    count = sm.count_unmarked_nodes(false, marked, false);
    REQUIRE(count == 8);
    REQUIRE(marked.empty());

    count = sm.count_unmarked_nodes(true, marked, false);
    REQUIRE(count == 1);
    REQUIRE(marked.empty());

    sm.clear();
    fill(sm);
    count = sm.count_unmarked_nodes(true, marked, false);
    REQUIRE(count == 3);
    REQUIRE(marked.empty());
  }

  SECTION("marking")
  {
    std::set<const void *> marked;
    sharing_map_internalt sm;

    fill(sm);

    sm.count_unmarked_nodes(false, marked, true);
    REQUIRE(marked.empty());

    sharing_map_internalt sm2(sm);
    sm.count_unmarked_nodes(false, marked, true);
    REQUIRE(marked.size() == 1);

    marked.clear();
    sharing_map_internalt sm3(sm);
    sm3.insert("x", "0");
    sm.count_unmarked_nodes(false, marked, true);
    REQUIRE(marked.size() >= 2);
  }
}

TEST_CASE("Sharing map internals test", "[core][util]")
{
  sharing_map_internals_test();
}

TEST_CASE("Sharing map interface", "[core][util]")
{
  SECTION("Empty map")
  {
    sharing_map_standardt sm;

    REQUIRE(sm.empty());
    REQUIRE(sm.size() == 0);
    REQUIRE(!sm.has_key("i"));
  }

  SECTION("Insert elements")
  {
    sharing_map_standardt sm;

    sm.insert("i", "0");
    sm.insert("j", "1");

    REQUIRE(sm.size() == 2);
    REQUIRE(!sm.empty());
    REQUIRE(sm.has_key("i"));
    REQUIRE(sm.has_key("j"));
    REQUIRE(!sm.has_key("k"));
  }

  SECTION("Replace elements")
  {
    sharing_map_standardt sm;
    fill(sm);

    sm.replace("i", "9");
    auto r = sm.find("i");
    REQUIRE(r);
    REQUIRE(r->get() == "9");
  }

  SECTION("Retrieve elements")
  {
    sharing_map_standardt sm;
    sm.insert("i", "0");
    sm.insert("j", "1");

    REQUIRE(sm.has_key("i"));
    REQUIRE(sm.has_key("j"));
    REQUIRE(!sm.has_key("k"));

    REQUIRE(sm.size() == 2);

    auto r1 = sm.find("i");
    REQUIRE(r1);
    REQUIRE(r1->get() == "0");

    auto r2 = sm.find("k");
    REQUIRE(!r2);
  }

  SECTION("Remove elements")
  {
    sharing_map_standardt sm;
    sm.insert("i", "0");
    sm.insert("j", "1");

    REQUIRE(sm.size() == 2);

    sm.erase("i");
    REQUIRE(!sm.has_key("i"));

    sm.erase("j");
    REQUIRE(!sm.has_key("j"));

    sm.erase_if_exists("j");
    REQUIRE(!sm.has_key("j"));
    sm.insert("j", "1");
    sm.erase_if_exists("j");
    REQUIRE(!sm.has_key("j"));

    sm.insert("i", "0");
    sm.insert("j", "1");

    sharing_map_standardt sm3(sm);

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
}

TEST_CASE("Sharing map copying", "[core][util]")
{
  sharing_map_standardt sm1;
  fill(sm1);

  sharing_map_standardt sm2(sm1);

  sm2.erase("i");
  REQUIRE(!sm2.has_key("i"));
  REQUIRE(sm1.has_key("i"));

  sharing_map_standardt sm3(sm2);
  REQUIRE(!sm3.has_key("i"));
  sm3.insert("i", "0");

  REQUIRE(sm1.has_key("i"));
  REQUIRE(!sm2.has_key("i"));
  REQUIRE(sm3.has_key("i"));
}

TEST_CASE("Sharing map collisions", "[core][util]")
{
  typedef sharing_mapt<some_keyt, std::string, false, some_key_hasht>
    sharing_map_collisionst;

  sharing_map_collisionst sm;

  sm.insert(some_keyt(0), "a");
  sm.insert(some_keyt(8), "b");
  sm.insert(some_keyt(16), "c");

  sm.insert(some_keyt(1), "d");
  sm.insert(some_keyt(2), "e");

  sm.erase(some_keyt(8));

  REQUIRE(sm.has_key(some_keyt(0)));
  REQUIRE(sm.has_key(some_keyt(16)));

  REQUIRE(sm.has_key(some_keyt(1)));
  REQUIRE(sm.has_key(some_keyt(2)));

  REQUIRE(!sm.has_key(some_keyt(8)));
}

TEST_CASE("Sharing map views", "[core][util]")
{
  SECTION("View of empty map")
  {
    sharing_map_standardt sm;
    sharing_map_standardt::viewt view;

    sm.get_view(view);
  }

  SECTION("View")
  {
    typedef std::pair<dstringt, std::string> pt;

    sharing_map_standardt sm;
    sharing_map_standardt::viewt view;
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

    REQUIRE(!sm.has_key("l"));
    sm.insert("l", "3");

    view.clear();
    sm.get_view(view);

    REQUIRE(view.size() == 4);

    sort_view();

    REQUIRE((pairs[3] == pt("l", "3")));
  }

  SECTION("Delta view (no sharing, same keys)")
  {
    sharing_map_standardt sm1;
    fill(sm1);

    sharing_map_standardt sm2;
    fill(sm2);

    sharing_map_standardt::delta_viewt delta_view;

    sm1.get_delta_view(sm2, delta_view);
    REQUIRE(delta_view.size() == 3);

    delta_view.clear();
    sm1.get_delta_view(sm2, delta_view, false);
    REQUIRE(delta_view.size() == 3);
  }

  SECTION("delta view (all shared, same keys)")
  {
    sharing_map_standardt sm1;
    fill(sm1);

    sharing_map_standardt sm2(sm1);

    sharing_map_standardt::delta_viewt delta_view;

    sm1.get_delta_view(sm2, delta_view);
    REQUIRE(delta_view.size() == 0);

    delta_view.clear();
    sm1.get_delta_view(sm2, delta_view, false);
    REQUIRE(delta_view.size() == 0);
  }

  SECTION("delta view (some sharing, same keys)")
  {
    sharing_map_standardt sm1;
    fill(sm1);

    sharing_map_standardt sm2(sm1);
    sm2.replace("i", "3");

    sharing_map_standardt::delta_viewt delta_view;

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
    sharing_map_standardt sm1;
    fill(sm1);

    sharing_map_standardt sm2;
    fill2(sm2);

    sharing_map_standardt::delta_viewt delta_view;

    sm1.get_delta_view(sm2, delta_view);
    REQUIRE(delta_view.size() == 0);

    delta_view.clear();
    sm1.get_delta_view(sm2, delta_view, false);
    REQUIRE(delta_view.size() == 3);
  }
}

TEST_CASE("Sharing map sharing stats", "[core][util]")
{
#if !defined(_MSC_VER)
  SECTION("sharing stats")
  {
    std::vector<sharing_map_standardt> v;
    sharing_map_standardt::sharing_map_statst sms;

    SECTION("sharing stats no sharing")
    {
      v.emplace_back();
      v.emplace_back();

      REQUIRE(v.size() == 2);

      // Empty maps
      sms = sharing_map_standardt::get_sharing_stats(v.begin(), v.end());
      REQUIRE(sms.num_nodes == 0);
      REQUIRE(sms.num_unique_nodes == 0);
      REQUIRE(sms.num_leafs == 0);
      REQUIRE(sms.num_unique_leafs == 0);

      sharing_map_standardt &sm1 = v.at(0);
      sharing_map_standardt &sm2 = v.at(1);

      fill(sm1);
      fill(sm2);

      // Non-empty maps
      sms = sharing_map_standardt::get_sharing_stats(v.begin(), v.end());
      REQUIRE(sms.num_leafs == 6);
      REQUIRE(sms.num_unique_leafs == 6);
    }

    SECTION("sharing stats sharing 1")
    {
      sharing_map_standardt sm1;
      fill(sm1);
      v.push_back(sm1);

      sharing_map_standardt sm2(sm1);
      v.push_back(sm2);

      sms = sharing_map_standardt::get_sharing_stats(v.begin(), v.end());
      REQUIRE(sms.num_leafs == 6);
      REQUIRE(sms.num_unique_leafs == 3);
    }

    SECTION("sharing stats sharing 2")
    {
      sharing_map_standardt sm1;
      fill(sm1);
      v.push_back(sm1);

      sharing_map_standardt sm2(sm1);
      v.push_back(sm2);

      sharing_map_standardt sm3(sm1);
      sm3.insert("x", "0");
      v.push_back(sm3);

      sharing_map_standardt sm4(sm1);
      sm4.replace("i", "4");
      v.push_back(sm4);

      sms = sharing_map_standardt::get_sharing_stats(v.begin(), v.end());
      REQUIRE(sms.num_leafs == 13);
      REQUIRE(sms.num_unique_leafs == 5);
    }
  }

  SECTION("sharing stats map")
  {
    std::map<irep_idt, sharing_map_standardt> m;

    sharing_map_standardt sm1;
    fill(sm1);

    sharing_map_standardt sm2(sm1);

    m["a"] = sm1;
    m["b"] = sm2;

    sharing_map_standardt::sharing_map_statst sms;
    sms = sharing_map_standardt::get_sharing_stats_map(m.begin(), m.end());
    REQUIRE(sms.num_leafs == 6);
    REQUIRE(sms.num_unique_leafs == 3);
  }
#endif
}

TEST_CASE("Sharing map replace non-existing", "[.]")
{
  sharing_map_standardt sm;
  fill(sm);

  sm.replace("x", "0");
}

TEST_CASE("Sharing map replace with equal value", "[.]")
{
  sharing_map_error_checkt sm;

  sm.insert("i", "0");
  sm.replace("i", "0");
}

TEST_CASE("Sharing map insert existing", "[.]")
{
  sharing_map_standardt sm;
  fill(sm);

  sm.insert("i", "4");
}

TEST_CASE("Sharing map erase non-existing", "[.]")
{
  sharing_map_standardt sm;
  fill(sm);

  sm.erase("x");
}
