/*******************************************************************\

Module: Unit tests for expr_iterator

Author: Diffblue Ltd

\*******************************************************************/

/// \file
/// expr_iterator unit tests

#include <testing-utils/use_catch.h>

#include <util/expr_iterator.h>
#include <util/std_expr.h>

SCENARIO("expr_iterator", "[core][utils][expr_iterator]")
{
  GIVEN("An expression of depth 3")
  {
    symbol_exprt symbol("whatever", bool_typet());
    notequal_exprt middle1(symbol, symbol);
    equal_exprt middle2(symbol, symbol);
    implies_exprt top(middle1, middle2);

    WHEN("Visiting the expressions with a depth iterator")
    {
      std::vector<irep_idt> ids;
      for(auto it = top.depth_begin(), itend = top.depth_end(); it != itend;
          ++it)
      {
        ids.push_back(it->id());
      }

      THEN("We expect to see parents before children")
      {
        REQUIRE(
          ids == std::vector<irep_idt>{ID_implies,
                                       ID_notequal,
                                       ID_symbol,
                                       ID_symbol,
                                       ID_equal,
                                       ID_symbol,
                                       ID_symbol});
      }
    }

    WHEN("Replacing one of the middle nodes mid-walk")
    {
      std::vector<irep_idt> ids;
      for(auto it = top.depth_begin(), itend = top.depth_end(); it != itend;
          ++it)
      {
        if(it->id() == ID_notequal)
          it.mutate() = not_exprt(equal_exprt(symbol, symbol));

        ids.push_back(it->id());
      }

      THEN("We expect to see the newly added child nodes")
      {
        REQUIRE(
          ids == std::vector<irep_idt>{ID_implies,
                                       ID_not,
                                       ID_equal,
                                       ID_symbol,
                                       ID_symbol,
                                       ID_equal,
                                       ID_symbol,
                                       ID_symbol});
      }
    }

    WHEN(
      "Replacing one of the middle nodes mid-walk and skipping the new "
      "children")
    {
      std::vector<irep_idt> ids;
      for(auto it = top.depth_begin(), itend = top.depth_end(); it != itend;
          /* no ++it */)
      {
        bool replace_here = it->id() == ID_notequal;

        if(replace_here)
          it.mutate() = not_exprt(equal_exprt(symbol, symbol));

        ids.push_back(it->id());

        if(replace_here)
          it.next_sibling_or_parent();
        else
          ++it;
      }

      THEN("We expect to skip the newly added child nodes")
      {
        REQUIRE(
          ids == std::vector<irep_idt>{
                   ID_implies, ID_not, ID_equal, ID_symbol, ID_symbol});
      }
    }
  }
}
