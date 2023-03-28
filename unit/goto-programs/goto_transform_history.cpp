// Author: Diffblue Ltd.

#include <goto-programs/goto_transform_history.h>

#include <testing-utils/use_catch.h>

TEST_CASE("Goto transform history data structure", "[core][goto-programs]")
{
  goto_transform_historyt history;
  REQUIRE(history.transforms().empty());
  history.add(goto_transform_kindt::mm_io);
  REQUIRE_THAT(
    history.transforms(),
    Catch::Matchers::Equals(
      goto_transform_historyt::transformst{goto_transform_kindt::mm_io}));
  history.add(goto_transform_kindt::adjust_float_expressions);
  REQUIRE_THAT(
    history.transforms(),
    Catch::Matchers::Equals(goto_transform_historyt::transformst{
      goto_transform_kindt::mm_io,
      goto_transform_kindt::adjust_float_expressions}));
}
