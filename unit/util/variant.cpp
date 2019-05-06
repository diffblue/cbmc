// Copyright 2016-2019 Diffblue Limited. All Rights Reserved.

#include <testing-utils/use_catch.h>
#include <util/variant.h>

TEST_CASE("Ensure variant has been included", "[core][util][variant]")
{
  variantt<int, float> some_type = 1;
  REQUIRE(some_type.index() == 0);
  some_type = 1.0f;
  REQUIRE(some_type.index() == 1);
}
