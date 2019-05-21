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

struct unsigned_hasht
{
  std::size_t operator()(const unsigned v) const
  {
    return static_cast<std::size_t>(v);
  }
};

class sharing_map_unsignedt
  : public sharing_mapt<unsigned, std::string, false, unsigned_hasht>
{
  friend void sharing_map_internals_test();
};

// helpers
template <class some_sharing_mapt>
void fill(some_sharing_mapt &sm)
{
  sm.insert("i", "0");
  sm.insert("j", "1");
  sm.insert("k", "2");
}

template <class some_sharing_mapt>
void fill2(some_sharing_mapt &sm)
{
  sm.insert("l", "3");
  sm.insert("m", "4");
  sm.insert("n", "5");
}

class key_hasht
{
public:
  std::size_t operator()(const std::size_t &k) const
  {
    return k & 0x3;
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
    REQUIRE(count == 2);
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

  // These tests check whether the internal representation of the map has the
  // expected shape after a series of operations. This is done by checking
  // whether the map has a number of nodes (inner nodes, container nodes, and
  // leaf nodes) that is consistent with the expected shape.
  SECTION("single map shape")
  {
    std::set<const void *> marked;
    std::size_t count = 0;
    const std::size_t chunk = sharing_map_unsignedt::chunk;
    const std::size_t levels = sharing_map_unsignedt::levels;

    sharing_map_unsignedt sm;

    count = sm.count_unmarked_nodes(false, marked, false);
    REQUIRE(count == 0);

    sm.insert(0, "a");
    count = sm.count_unmarked_nodes(false, marked, false);
    REQUIRE(count == 2);

    SECTION("first node decisive")
    {
      sm.insert(1, "b");
      count = sm.count_unmarked_nodes(false, marked, false);
      REQUIRE(count == 3);

      sm.replace(1, "c");
      count = sm.count_unmarked_nodes(false, marked, false);
      REQUIRE(count == 3);

      sm.erase(1);
      count = sm.count_unmarked_nodes(false, marked, false);
      REQUIRE(count == 2);
    }

    SECTION("second node decisive")
    {
      sm.insert(1 << chunk, "b");
      count = sm.count_unmarked_nodes(false, marked, false);
      REQUIRE(count == 4);

      sm.replace(1 << chunk, "c");
      count = sm.count_unmarked_nodes(false, marked, false);
      REQUIRE(count == 4);

      sm.erase(1 << chunk);
      count = sm.count_unmarked_nodes(false, marked, false);
      REQUIRE(count == 3);
    }

    SECTION("third node decisive")
    {
      sm.insert(1 << (2 * chunk), "b");
      count = sm.count_unmarked_nodes(false, marked, false);
      REQUIRE(count == 5);

      sm.replace(1 << (2 * chunk), "c");
      count = sm.count_unmarked_nodes(false, marked, false);
      REQUIRE(count == 5);

      sm.erase(1 << (2 * chunk));
      count = sm.count_unmarked_nodes(false, marked, false);
      REQUIRE(count == 4);
    }

    SECTION("last non-container node is decisive")
    {
      sm.insert(1 << (chunk * (levels - 1)), "b");
      count = sm.count_unmarked_nodes(false, marked, false);
      REQUIRE(count == levels + 2); // inner nodes + leafs

      sm.replace(1 << (chunk * (levels - 1)), "c");
      count = sm.count_unmarked_nodes(false, marked, false);
      REQUIRE(count == levels + 2); // inner nodes + leafs

      sm.erase(1 << (chunk * (levels - 1)));
      count = sm.count_unmarked_nodes(false, marked, false);
      REQUIRE(count == levels + 1); // inner nodes + leafs
    }

    SECTION("stored in container node")
    {
      // existing leaf will be migrated to the bottom
      sm.insert(1 << (chunk * levels), "b");
      count = sm.count_unmarked_nodes(false, marked, false);
      REQUIRE(count == levels + 1 + 2); // inner nodes + container + leafs

      sm.replace(1 << (chunk * levels), "c");
      count = sm.count_unmarked_nodes(false, marked, false);
      REQUIRE(count == levels + 1 + 2); // inner nodes + container + leafs

      sm.erase(1 << (chunk * levels));
      count = sm.count_unmarked_nodes(false, marked, false);
      REQUIRE(count == levels + 1 + 1); // inner nodes + container + leafs

      // existing leaf still in container, not migrating necessary
      sm.insert(1 << (chunk * levels), "d");
      count = sm.count_unmarked_nodes(false, marked, false);
      REQUIRE(count == levels + 1 + 2); // inner nodes + container + leafs
    }
  }

  SECTION("delta view (sharing, one of the maps is deeper)")
  {
    std::set<const void *> marked;
    std::size_t chunk = sharing_map_unsignedt::chunk;

    std::vector<sharing_map_unsignedt> v;
    v.reserve(2);

    v.push_back(sharing_map_unsignedt());
    sharing_map_unsignedt &sm1 = v.front();

    SECTION("additional element in second map")
    {
      sm1.insert(0, "a");

      v.emplace_back(sm1);
      sharing_map_unsignedt &sm2 = v.back();

      sm2.insert(1 << (2 * chunk), "b");

#if !defined(_MSC_VER)
      sharing_map_unsignedt::sharing_map_statst sms;

      sms = sharing_map_unsignedt::get_sharing_stats(v.begin(), v.end());
      REQUIRE(sms.num_leafs == 1 + 2);
      REQUIRE(sms.num_unique_leafs == 1 + 1);
      REQUIRE(sms.num_nodes == 2 + 5);
      REQUIRE(sms.num_unique_nodes == 2 + 4);
#endif

      sharing_map_unsignedt::delta_viewt delta_view;
      sm1.get_delta_view(sm2, delta_view, false);
      REQUIRE(delta_view.size() == 0);

      delta_view.clear();
      sm2.get_delta_view(sm1, delta_view, false);
      REQUIRE(delta_view.size() == 1);
      REQUIRE(delta_view[0].k == (1 << (2 * chunk)));
    }
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

    cbmc_invariants_should_throwt invariants_throw;

    REQUIRE_THROWS_AS(sm.insert("i", "4"), invariant_failedt);
  }

  SECTION("Replace and update elements")
  {
    sharing_map_standardt sm;
    fill(sm);

    sm.replace("i", "9");
    auto r = sm.find("i");
    REQUIRE(r);
    REQUIRE(r->get() == "9");

    sm.update("i", [](std::string &str) { str += "0"; });
    auto r2 = sm.find("i");
    REQUIRE(r2);
    REQUIRE(r2->get() == "90");
  }

  SECTION("Replace and update elements errors")
  {
    sharing_map_standardt sm;
    fill(sm);

    sharing_map_error_checkt debug_sm;
    fill(debug_sm);

    cbmc_invariants_should_throwt invariants_throw;

    SECTION("Replace non-existing")
    {
      REQUIRE_THROWS_AS(sm.replace("x", "0"), invariant_failedt);
    }

    SECTION("Update non-existing")
    {
      REQUIRE_THROWS_AS(
        sm.update("x", [](std::string &str) {}), invariant_failedt);
    }

    SECTION("Replace with equal")
    {
      REQUIRE_THROWS_AS(debug_sm.replace("i", "0"), invariant_failedt);
    }

    SECTION("Update with equal")
    {
      REQUIRE_THROWS_AS(
        debug_sm.update("i", [](std::string &str) {}), invariant_failedt);
    }
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

    cbmc_invariants_should_throwt invariants_throw;

    REQUIRE_THROWS_AS(sm3.erase("x"), invariant_failedt);
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
  typedef sharing_mapt<std::size_t, std::string, false, key_hasht>
    sharing_map_collisionst;

  sharing_map_collisionst sm;

  SECTION("Basic")
  {
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

  SECTION("Delta view")
  {
    sm.insert(0, "a");

    sharing_map_collisionst sm2;

    sm2.insert(8, "b");
    sm2.insert(16, "c");

    sharing_map_collisionst::delta_viewt delta_view;

    sm.get_delta_view(sm2, delta_view, false);

    REQUIRE(delta_view.size() == 1);
    REQUIRE(delta_view[0].k == 0);
    REQUIRE(!delta_view[0].is_in_both_maps());
  }
}

TEST_CASE("Sharing map views and iteration", "[core][util]")
{
  SECTION("View of empty map")
  {
    sharing_map_standardt sm;
    sharing_map_standardt::viewt view;

    sm.get_view(view);
  }

  SECTION("View")
  {
    typedef std::pair<std::string, std::string> pt;

    sharing_map_standardt sm;
    sharing_map_standardt::viewt view;
    std::vector<pt> pairs;

    auto sort_view = [&pairs, &view]() {
      pairs.clear();
      for(auto &p : view)
      {
        pairs.push_back({id2string(p.first), p.second});
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

  SECTION("Iterate")
  {
    sharing_map_standardt sm;

    sm.iterate([](const irep_idt &key, const std::string &value) {});

    fill(sm);

    typedef std::pair<std::string, std::string> pt;
    std::vector<pt> pairs;

    sm.iterate([&pairs](const irep_idt &key, const std::string &value) {
      pairs.push_back({id2string(key), value});
    });

    std::sort(pairs.begin(), pairs.end());
    REQUIRE(pairs.size() == 3);
    REQUIRE((pairs[0] == pt("i", "0")));
    REQUIRE((pairs[1] == pt("j", "1")));
    REQUIRE((pairs[2] == pt("k", "2")));
  }

  SECTION("Delta view (one empty)")
  {
    sharing_map_standardt sm1;
    fill(sm1);

    sharing_map_standardt sm2;

    sharing_map_standardt::delta_viewt delta_view;

    sm1.get_delta_view(sm2, delta_view, false);
    REQUIRE(delta_view.size() == 3);

    delta_view.clear();
    sm2.get_delta_view(sm1, delta_view, false);
    REQUIRE(delta_view.empty());
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

  SECTION("delta view (no sharing, one of the maps is deeper)")
  {
    std::set<const void *> marked;
    std::size_t chunk = 3;

    sharing_map_unsignedt sm1;
    sharing_map_unsignedt sm2;

    SECTION("left map deeper")
    {
      sm1.insert(0, "a");
      sm1.insert(1 << (2 * chunk), "b");

      sm2.insert(0, "c");
      sm2.insert(1, "d");

      sharing_map_unsignedt::delta_viewt delta_view;
      sm1.get_delta_view(sm2, delta_view, false);

      REQUIRE(delta_view.size() == 2);

      const bool b0 = delta_view[0].is_in_both_maps();
      const bool b1 = delta_view[1].is_in_both_maps();

      REQUIRE((b0 || b1));
      REQUIRE(!(b0 && b1));

      if(b0)
      {
        REQUIRE(delta_view[0].k == 0);
        REQUIRE(delta_view[0].m == "a");
        REQUIRE(delta_view[0].get_other_map_value() == "c");

        REQUIRE(delta_view[1].k == 1 << (2 * chunk));
        REQUIRE(delta_view[1].m == "b");
      }
      else
      {
        REQUIRE(delta_view[0].k == 1 << (2 * chunk));
        REQUIRE(delta_view[0].m == "b");

        REQUIRE(delta_view[1].k == 0);
        REQUIRE(delta_view[1].m == "a");
        REQUIRE(delta_view[1].get_other_map_value() == "c");
      }
    }

    SECTION("right map deeper")
    {
      sm1.insert(0, "c");
      sm1.insert(1, "d");

      sm2.insert(0, "a");
      sm2.insert(1 << (2 * chunk), "b");

      sharing_map_unsignedt::delta_viewt delta_view;
      sm1.get_delta_view(sm2, delta_view, false);

      REQUIRE(delta_view.size() == 2);

      const bool b0 = delta_view[0].is_in_both_maps();
      const bool b1 = delta_view[1].is_in_both_maps();

      REQUIRE((b0 || b1));
      REQUIRE(!(b0 && b1));

      if(b0)
      {
        REQUIRE(delta_view[0].k == 0);
        REQUIRE(delta_view[0].m == "c");
        REQUIRE(delta_view[0].get_other_map_value() == "a");

        REQUIRE(delta_view[1].k == 1);
        REQUIRE(delta_view[1].m == "d");
      }
      else
      {
        REQUIRE(delta_view[0].k == 1);
        REQUIRE(delta_view[0].m == "d");

        REQUIRE(delta_view[1].k == 0);
        REQUIRE(delta_view[1].m == "c");
        REQUIRE(delta_view[1].get_other_map_value() == "a");
      }
    }
  }
}

TEST_CASE("Sharing map view validity", "[core][util]")
{
  SECTION("View validity")
  {
    sharing_map_standardt sm;
    sharing_map_standardt::viewt view;

    fill(sm);
    fill2(sm);

    sharing_map_standardt sm2(sm);
    sm2.replace("l", "8");

    sm.get_view(view);

    std::size_t i_idx = 0;
    std::size_t k_idx = 0;

    for(std::size_t i = 0; i < view.size(); i++)
    {
      if(view[i].first == "i")
        i_idx = i;

      if(view[i].first == "k")
        k_idx = i;
    }

    sm.erase("i");
    sm.replace("k", "7");
    sm.insert("o", "6");

    for(std::size_t i = 0; i < view.size(); i++)
    {
      if(i == i_idx || i == k_idx)
        continue;

      auto &p = view[i];

      REQUIRE(&p.second == &sm.find(p.first)->get());
    }
  }

  SECTION("Delta view validity")
  {
    sharing_map_standardt sm;

    sharing_map_standardt::delta_viewt delta_view;

    fill(sm);
    fill2(sm);

    sharing_map_standardt sm2(sm);

    sm2.erase("i");
    sm2.erase("j");
    sm2.erase("k");

    sm2.erase("m");
    sm2.erase("n");

    sm.get_delta_view(sm2, delta_view, false);

    REQUIRE(delta_view.size() == 5);

    std::size_t i_idx = 0;
    std::size_t k_idx = 0;

    for(std::size_t i = 0; i < delta_view.size(); i++)
    {
      if(delta_view[i].k == "i")
        i_idx = i;

      if(delta_view[i].k == "k")
        k_idx = i;
    }

    sm.erase("i");
    sm.replace("k", "7");
    sm.insert("o", "6");

    for(std::size_t i = 0; i < delta_view.size(); i++)
    {
      if(i == i_idx || i == k_idx)
        continue;

      auto &delta_item = delta_view[i];

      REQUIRE(&delta_item.m == &sm.find(delta_item.k)->get());
    }
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

struct no_default_constructort
{
  no_default_constructort() = delete;
  explicit no_default_constructort(int val) : val(val)
  {
  }
  no_default_constructort(const no_default_constructort &) = default;

  int val;
};

TEST_CASE("Sharing map with a non-default-constructable value", "[core][util]")
{
  typedef sharing_mapt<int, no_default_constructort>
    sharing_map_no_default_constructort;

  sharing_map_no_default_constructort map1;

  map1.insert(0, no_default_constructort{0});
  map1.insert(1, no_default_constructort{1});

  sharing_map_no_default_constructort map2 = map1;
  map2.replace(1, no_default_constructort{3});
  map2.insert(2, no_default_constructort{2});

  sharing_map_no_default_constructort::delta_viewt delta_view;
  map2.get_delta_view(map1, delta_view, false);

  REQUIRE(delta_view.size() == 2);
  const auto &entry_1 = delta_view[delta_view[0].k == 1 ? 0 : 1];
  const auto &entry_2 = delta_view[delta_view[0].k == 1 ? 1 : 0];

  REQUIRE(entry_1.k == 1);
  REQUIRE(entry_1.is_in_both_maps());
  REQUIRE(entry_1.m.val == 3);
  REQUIRE(entry_1.get_other_map_value().val == 1);

  REQUIRE(entry_2.k == 2);
  REQUIRE(!entry_2.is_in_both_maps());
  REQUIRE(entry_2.m.val == 2);
}
