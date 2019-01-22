/// Author: Daniel Poetzl

/// \file Tests for small map

#include <testing-utils/use_catch.h>
#include <util/small_map.h>

// This method is a friend of small_map
void small_map_test()
{
  SECTION("Basic")
  {
    small_mapt<int> m;

    REQUIRE(m.empty());
    REQUIRE(m.size() == 0);

    int &i = m[0];
    i = 7;

    REQUIRE(!m.empty());
    REQUIRE(m.size() == 1);

    int &j = m[5];
    j = 3;

    REQUIRE(m.size() == 2);

    int &k = m[6];
    k = 9;

    REQUIRE(m.size() == 3);

    auto it1 = m.find(2);
    REQUIRE(it1 == m.end());

    auto it2 = m.find(5);
    REQUIRE(it2 != m.end());

    std::size_t n1 = m.erase(2);
    REQUIRE(!n1);

    std::size_t n2 = m.erase(5);
    REQUIRE(n2 == 1);
  }

  SECTION("Iterator")
  {
    small_mapt<int> m;

    m[0] = 0;
    m[3] = 3;
    m[7] = 7;

    REQUIRE(m.size() == 3);

    REQUIRE(m.begin() != m.end());

    auto it1 = m.begin()++;
    it1++;
    auto it2 = ++m.begin();
    REQUIRE(it1 == it2);

    int cnt = 0;
    for(auto it = m.begin(); it != m.end(); it++)
    {
      REQUIRE(it->first == it->second);
      REQUIRE((*it).first == (*it).second);
      cnt++;
    }

    REQUIRE(cnt == 3);

    m.erase(0);
    m.erase(3);
    m.erase(7);

    REQUIRE(m.begin() == m.end());
  }

  SECTION("Copy")
  {
    small_mapt<int> m1;

    m1[3] = 3;
    m1[5] = 5;

    small_mapt<int> m2(m1);

    REQUIRE(m1.size() == m2.size());

    REQUIRE(m1[3] == m2[3]);
    REQUIRE(m1[5] == m2[5]);

    m2[3] = 4;

    REQUIRE(m1[3] != m2[3]);

    REQUIRE(m1.size() == m2.size());

    m2[4] = 4;

    REQUIRE(m1.size() != m2.size());
  }

  SECTION("Copy and modify")
  {
    small_mapt<int> m;

    m[0] = 1;
    m[1] = 2;
    m[3] = 3;
    m[7] = 4;

    REQUIRE(m.size() == 4);

    small_mapt<int> *p = m.copy_and_erase(3);

    REQUIRE(p->size() == 3);

    REQUIRE((*p)[0] == 1);
    REQUIRE((*p)[1] == 2);
    REQUIRE((*p)[7] == 4);

    delete p;

    p = m.copy_and_insert(6, 4);

    REQUIRE(p->size() == 5);

    REQUIRE((*p)[0] == 1);
    REQUIRE((*p)[1] == 2);
    REQUIRE((*p)[3] == 3);
    REQUIRE((*p)[6] == 4);
    REQUIRE((*p)[7] == 4);

    delete p;
  }

  SECTION("Boundary")
  {
    small_mapt<int> m;

    for(std::size_t i = 0; i < small_mapt<int>::NUM; i++)
    {
      m[i] = i;
    }

    for(std::size_t i = 0; i < small_mapt<int>::NUM; i++)
    {
      m.erase(i);
    }

    REQUIRE(m.empty());
  }

  SECTION("Value iterator")
  {
    small_mapt<int> m;

    m[0] = 0;
    m[1] = 1;
    m[4] = 4;

    auto v_it = m.value_begin();
    REQUIRE(v_it != m.value_end());
    REQUIRE(*v_it == 4);

    v_it++;
    REQUIRE(*v_it == 1);

    v_it++;
    REQUIRE(*v_it == 0);

    v_it++;
    REQUIRE(v_it == m.value_end());
  }

  SECTION("Non-default arguments")
  {
    small_mapt<int, uint32_t, 4> m;

    m[0] = 1;
    m[1] = 2;
    m[2] = 3;
    m[3] = 4;

    REQUIRE(m.size() == 4);

    REQUIRE(m[0] == 1);
    REQUIRE(m[1] == 2);
    REQUIRE(m[2] == 3);
    REQUIRE(m[3] == 4);

    std::size_t n;

    n = m.erase(1);
    REQUIRE(n == 1);
    REQUIRE(m.size() == 3);

    n = m.erase(3);
    REQUIRE(n == 1);
    REQUIRE(m.size() == 2);

    n = m.erase(3);
    REQUIRE(n == 0);
    REQUIRE(m.size() == 2);

    auto it = m.find(2);
    REQUIRE(it != m.end());
  }
}

TEST_CASE("Small map")
{
  small_map_test();
}
