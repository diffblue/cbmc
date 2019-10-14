// Author: Diffblue Limited

#include <testing-utils/use_catch.h>

#include <util/interval_union.h>

TEST_CASE("interval_union", "[core][test-gen-util][interval_union]")
{
  // Define interval union [:-10][-5:0][5:10]
  interval_uniont first =
    interval_uniont::smaller_or_equal(-10)
      .make_union(interval_uniont::greater_or_equal(-5).make_intersection(
        interval_uniont::smaller_or_equal(0)))
      .make_union(interval_uniont::greater_or_equal(5))
      .make_intersection(interval_uniont::smaller_or_equal(10));

  REQUIRE(first.to_string() == "[:-10][-5:0][5:10]");

  // Define interval union [:-15][-8:-6][1:2][4:5][8:]
  interval_uniont second =
    interval_uniont::smaller_or_equal(-15)
      .make_union(interval_uniont::greater_or_equal(-8).make_intersection(
        interval_uniont::smaller_or_equal(-6)))
      .make_union(interval_uniont::greater_or_equal(1).make_intersection(
        interval_uniont::smaller_or_equal(2)))
      .make_union(interval_uniont::greater_or_equal(4).make_intersection(
        interval_uniont::smaller_or_equal(5)))
      .make_union(interval_uniont::greater_or_equal(8));

  REQUIRE(second.to_string() == "[:-15][-8:-6][1:2][4:5][8:]");

  // Define interval union [12:]
  interval_uniont third = interval_uniont::greater_or_equal(12);
  REQUIRE(third.to_string() == "[12:]");

  REQUIRE_FALSE(first.is_empty());
  REQUIRE(first.maximum().has_value());
  REQUIRE(first.maximum().value() == 10);
  REQUIRE_FALSE(first.minimum().has_value());

  REQUIRE_FALSE(second.is_empty());
  REQUIRE_FALSE(second.maximum().has_value());
  REQUIRE_FALSE(second.minimum().has_value());

  REQUIRE_FALSE(third.is_empty());
  REQUIRE_FALSE(third.maximum().has_value());
  REQUIRE(third.minimum().has_value());
  REQUIRE(third.minimum().value() == 12);

  REQUIRE(first.make_union(second).to_string() == "[:-10][-8:2][4:]");
  REQUIRE(first.make_intersection(second).to_string() == "[:-15][5:5][8:10]");

  REQUIRE(first.make_intersection(third).is_empty());
  REQUIRE(first.make_intersection(third).to_string() == "[]");
}
