/// Author: Daniel Poetzl

/// \file Tests for small shared n-way pointer

#include <testing-utils/use_catch.h>
#include <util/small_shared_n_way_ptr.h>

bool data1_destructed = false;
bool data2_destructed = false;
bool data3_destructed = false;

class data1t : public small_shared_n_way_pointee_baset<2, unsigned>
{
public:
  data1t() = default;

  explicit data1t(int i) : d1(i)
  {
  }

  ~data1t()
  {
    data1_destructed = true;
  }

  int d1;
};

class data2t : public small_shared_n_way_pointee_baset<2, unsigned>
{
public:
  data2t() = default;

  explicit data2t(int i) : d2(i)
  {
  }

  ~data2t()
  {
    data2_destructed = true;
  }

  int d2;
};

class data3t : public small_shared_n_way_pointee_baset<3, unsigned>
{
public:
  ~data3t()
  {
    data3_destructed = true;
  }
};

TEST_CASE("Small shared n-way pointer", "[core][util]")
{
  typedef small_shared_n_way_ptrt<data1t, data2t> spt;

  SECTION("Types")
  {
    spt sp1;
    spt sp2 = spt::create_small_shared_n_way_ptr<0>(new data1t());
    spt sp3 = spt::create_small_shared_n_way_ptr<1>(new data2t());

    REQUIRE(sp1.is_same_type(sp1));
    REQUIRE(sp2.is_same_type(sp2));
    REQUIRE(sp3.is_same_type(sp3));

    REQUIRE(sp1.is_same_type(sp2));
    REQUIRE(sp1.is_same_type(sp3));

    REQUIRE(!sp2.is_same_type(sp3));

    REQUIRE(sp1.is_derived<0>());
    REQUIRE(sp1.is_derived<1>());

    REQUIRE(sp2.is_derived<0>());
    REQUIRE(!sp2.is_derived<1>());

    REQUIRE(sp3.is_derived<1>());
    REQUIRE(!sp3.is_derived<0>());
  }

  SECTION("Basic")
  {
    spt sp1;
    REQUIRE(!sp1);
    REQUIRE(sp1.get() == nullptr);
    REQUIRE(sp1.use_count() == 0);

    const data1t *p;

    p = sp1.get_derived<0>();
    REQUIRE(p == nullptr);

    spt sp2 = spt::create_small_shared_n_way_ptr<0>(new data1t());
    REQUIRE(sp2.use_count() == 1);

    p = sp2.get_derived<0>();
    REQUIRE(p != nullptr);

    spt sp3(sp2);
    REQUIRE(sp3.is_derived<0>());
    REQUIRE(sp2.get_derived<0>() == sp3.get_derived<0>());
    REQUIRE(sp2.use_count() == 2);
    REQUIRE(sp3.use_count() == 2);

    sp1 = sp2;
    REQUIRE(sp1.is_derived<0>());
    REQUIRE(sp1.get_derived<0>() == sp2.get_derived<0>());
    REQUIRE(sp1.use_count() == 3);
    REQUIRE(sp2.use_count() == 3);
    REQUIRE(sp3.use_count() == 3);

    sp1.reset();
    REQUIRE(!sp1);
    REQUIRE(sp1.use_count() == 0);
    REQUIRE(sp2.use_count() == 2);
    REQUIRE(sp2.use_count() == 2);

    {
      spt sp4(sp2);
      REQUIRE(sp4.use_count() == 3);
    }

    REQUIRE(sp2.use_count() == 2);
  }

  SECTION("Creation")
  {
    spt sp1 = make_shared_2<0, data1t, data2t>();
    spt sp2 = make_shared_2<1, data1t, data2t>();

    REQUIRE(!sp1.is_same_type(sp2));

    sp1 = make_shared_2<0, data1t, data2t>(0);
    sp2 = make_shared_2<1, data1t, data2t>(0);

    REQUIRE(!sp1.is_same_type(sp2));
  }

  SECTION("Destruction")
  {
    data1_destructed = false;
    data2_destructed = false;

    {
      spt sp = make_shared_2<0, data1t, data2t>();
      REQUIRE(sp);
    }

    REQUIRE(data1_destructed);
    REQUIRE(!data2_destructed);

    data1_destructed = false;

    {
      spt sp1 = make_shared_2<0, data1t, data2t>();

      {
        spt sp2(sp1);
        REQUIRE(sp2.use_count() == 2);
      }

      REQUIRE(!data1_destructed);
      REQUIRE(!data2_destructed);

      REQUIRE(sp1.use_count() == 1);
    }

    REQUIRE(data1_destructed);
    REQUIRE(!data2_destructed);
  }

  SECTION("Three target types")
  {
    typedef small_shared_n_way_ptrt<data3t, data3t, data3t> sp3t;

    sp3t sp1 = make_shared_3<0, data3t, data3t, data3t>();
    REQUIRE(sp1.is_derived<0>());
    REQUIRE(!sp1.is_derived<1>());
    REQUIRE(!sp1.is_derived<2>());

    sp3t sp2 = make_shared_3<1, data3t, data3t, data3t>();
    REQUIRE(!sp2.is_derived<0>());
    REQUIRE(sp2.is_derived<1>());
    REQUIRE(!sp2.is_derived<2>());

    sp3t sp3 = make_shared_3<2, data3t, data3t, data3t>();
    REQUIRE(!sp3.is_derived<0>());
    REQUIRE(!sp3.is_derived<1>());
    REQUIRE(sp3.is_derived<2>());
  }
}
