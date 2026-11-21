/*******************************************************************\

Module: Unit tests for optionst

Author: Diffblue Ltd

\*******************************************************************/

/// \file
/// Unit tests for optionst

#include <util/json.h>
#include <util/options.h>

#include <testing-utils/use_catch.h>

TEST_CASE("optionst::to_json", "[core][util][options]")
{
  optionst options;
  options.set_option("flag", true);
  options.set_option("list", optionst::value_listt{"foo", "bar"});
  options.set_option("empty", optionst::value_listt{});

  const json_objectt expected{
    {"empty", json_arrayt{}},
    {"flag", json_arrayt{json_stringt{"1"}}},
    {"list", json_arrayt{json_stringt{"foo"}, json_stringt{"bar"}}}};

  REQUIRE(options.to_json() == expected);
}
