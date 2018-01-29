/*******************************************************************\

Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

#include <string>
#include <cstddef>

#include <testing-utils/catch.hpp>
#include <analyses/cfg_dominators.h>
#include <memory>

// Graph:

SCENARIO("Looking up dominators")
{
  // Graph:
  //  int x = rand();
  //  if (x<0) {
  //    x = -x;
  //  } else {
  //    x = x - 1;
  //    log(x);
  //  }
  //  return x;
  using domt = dominatorst<std::string, std::size_t>;
  auto dominators_data =
    std::make_shared<dominators_datat<std::string, std::size_t>>(
      std::vector<std::string>{"int x = rand();",
                               "if (x < 0)",
                               "x = -x;",
                               "x = x - 1;",
                               "log(x);",
                               "return x;"},
      std::vector<std::size_t>{domt::npos, 0, 1, 1, 3, 1});

  WHEN("Looking at the dominators of the root")
  {
    THEN("They should only exactly the root")
    {
      domt root_doms(dominators_data, 0);
      REQUIRE(root_doms.size() == 1);
      REQUIRE(*root_doms.begin() == dominators_data->data[0]);
    }
  }

  WHEN(
    "Looking at the dominators of a node that should have multiple dominators")
  {
    THEN("They should actually have multiple dominators")
    {
      domt log_doms(dominators_data, 4);
      REQUIRE(log_doms.size() == 4);
      REQUIRE(log_doms.find(dominators_data->data[0]) != log_doms.end());
      REQUIRE(log_doms.find(dominators_data->data[1]) != log_doms.end());
      REQUIRE(log_doms.find(dominators_data->data[3]) != log_doms.end());
      REQUIRE(log_doms.find(dominators_data->data[4]) != log_doms.end());
    }
  }
}
