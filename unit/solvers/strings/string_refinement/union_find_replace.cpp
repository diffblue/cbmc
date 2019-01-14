/*******************************************************************\

Module: Unit tests for union_find_replacet in
        solvers/refinement/string_refinement.cpp

Author: Diffblue Ltd.

\*******************************************************************/

#include <testing-utils/catch.hpp>

#include <solvers/strings/string_refinement.h>

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/std_expr.h>
#include <util/std_types.h>

SCENARIO("union_find_replace", "[core][solvers][strings][string_refinement]")
{
  GIVEN("An empty dictionary")
  {
    union_find_replacet dict;
    pointer_typet char_pointer_type = pointer_type(unsignedbv_typet(16));
    const symbol_exprt a("a", char_pointer_type);
    const symbol_exprt b("b", char_pointer_type);
    const symbol_exprt c("c", char_pointer_type);
    const symbol_exprt d("d", char_pointer_type);
    const symbol_exprt e("e", char_pointer_type);
    const symbol_exprt f("f", char_pointer_type);

    WHEN("Relations a=b, a=c, d=b, e=f are added")
    {
      dict.make_union(a, b);
      dict.make_union(a, c);
      dict.make_union(d, b);
      dict.make_union(e, f);
      THEN("find(d)=find(c), but find(e)!=find(a)")
      {
        REQUIRE(dict.find(d) == dict.find(c)); // transitive equality
        REQUIRE(dict.find(a) == dict.find(a)); // trivial equality
        REQUIRE(dict.find(b) == dict.find(d)); // rhs only symbol
        REQUIRE(dict.find(b) == dict.find(c)); // rhs only transitive
        REQUIRE(dict.find(e) != dict.find(a)); // transitive not equal
        REQUIRE(dict.find(f) != dict.find(a)); // transitive not equal
      }

      GIVEN("Expressions a+e, a+d, c+f, c+d")
      {
        plus_exprt a_plus_e(a, e);
        plus_exprt a_plus_d(a, d);
        plus_exprt c_plus_f(c, f);
        plus_exprt c_plus_d(c, d);
        WHEN("We use the dictionary for replacement")
        {
          dict.replace_expr(a_plus_e);
          dict.replace_expr(a_plus_d);
          dict.replace_expr(c_plus_f);
          dict.replace_expr(c_plus_d);
          THEN("a+e=c+f but a+e!=c+d")
          {
            REQUIRE(a_plus_e == c_plus_f);
            REQUIRE(a_plus_e != c_plus_d);
            REQUIRE(a_plus_d == c_plus_d);
          }
        }
      }

      THEN("Introducing cycles does not cause infinite loops or exceptions")
      {
        dict.make_union(c, d);
        REQUIRE(dict.find(d) == dict.find(c));
        REQUIRE(dict.find(e) != dict.find(a));
      }
    }
  }
}
