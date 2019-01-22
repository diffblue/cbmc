/// Author: Daniel Poetzl

/// \file Tests for small shared two-way pointer

#include <testing-utils/use_catch.h>
#include <util/small_shared_two_way_ptr.h>

class d1t : public small_shared_two_way_pointeet<unsigned>
{
public:
  d1t() = default;

  explicit d1t(int i) : d1(i)
  {
  }

  int d1;
};

class d2t : public small_shared_two_way_pointeet<unsigned>
{
public:
  d2t() = default;

  explicit d2t(int i) : d2(i)
  {
  }

  int d2;
};

TEST_CASE("Small shared two-way pointer")
{
  typedef small_shared_two_way_ptrt<d1t, d2t> spt;

  SECTION("Types")
  {
    spt sp1;
    spt sp2(new d1t());
    spt sp3(new d2t());

    REQUIRE(sp1.is_same_type(sp1));
    REQUIRE(sp2.is_same_type(sp2));
    REQUIRE(sp3.is_same_type(sp3));

    REQUIRE(sp1.is_same_type(sp2));
    REQUIRE(sp1.is_same_type(sp3));

    REQUIRE(!sp2.is_same_type(sp3));

    REQUIRE(sp1.is_derived_u());
    REQUIRE(sp1.is_derived_v());

    REQUIRE(sp2.is_derived_u());
    REQUIRE(!sp2.is_derived_v());

    REQUIRE(sp3.is_derived_v());
    REQUIRE(!sp3.is_derived_u());
  }

  SECTION("Basic")
  {
    spt sp1;
    REQUIRE(sp1.use_count() == 0);

    const d1t *p;

    p = sp1.get_derived_u();
    REQUIRE(p == nullptr);

    spt sp2(new d1t());
    REQUIRE(sp2.use_count() == 1);

    p = sp2.get_derived_u();
    REQUIRE(p != nullptr);

    spt sp3(sp2);
    REQUIRE(sp3.is_derived_u());
    REQUIRE(sp2.get_derived_u() == sp3.get_derived_u());
    REQUIRE(sp2.use_count() == 2);
    REQUIRE(sp3.use_count() == 2);

    sp1 = sp2;
    REQUIRE(sp1.is_derived_u());
    REQUIRE(sp1.get_derived_u() == sp2.get_derived_u());
    REQUIRE(sp1.use_count() == 3);
    REQUIRE(sp2.use_count() == 3);
    REQUIRE(sp3.use_count() == 3);
  }

  SECTION("Creation")
  {
    spt sp1 = make_shared_derived_u<d1t, d2t>();
    spt sp2 = make_shared_derived_v<d1t, d2t>();

    REQUIRE(!sp1.is_same_type(sp2));

    sp1 = make_shared_derived_u<d1t, d2t>(0);
    sp2 = make_shared_derived_v<d1t, d2t>(0);

    REQUIRE(!sp1.is_same_type(sp2));
  }
}
