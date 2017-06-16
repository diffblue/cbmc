/*******************************************************************\
 Module: Unit tests for variable/sensitivity/abstract_object::merge
 Author: DiffBlue Limited. All rights reserved.
\*******************************************************************/

#include <catch.hpp>

#include <analyses/interval.h>
#include <util/std_types.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>
#include <util/arith_tools.h>

#define V(X)   (binary2integer(X.get(ID_value).c_str(), 2))
#define V_(X)  (binary2integer(X.c_str(), 2))


SCENARIO("modulo interval domain",
  "[core][analyses][interval][modulo]")
{
  GIVEN("Two simple signed intervals")
  {
    const typet type=signedbv_typet(32);
    symbol_tablet symbol_table;
    namespacet ns(symbol_table);

    source_locationt source_location;

    std::map<int, constant_exprt> v;

    for(int i = -100; i <= 100; i++)
    {
      v[i] = from_integer(mp_integer(i), type);
    }

    WHEN("Positive RHS")
    {

      THEN("Ensure result is consistent.")
      {
        REQUIRE(intervalt(v[10], v[20]).modulo(intervalt(v[5], v[5])) == intervalt(v[0], v[4]));
        REQUIRE(intervalt(v[10], v[20]).modulo(intervalt(v[4], v[5])) == intervalt(v[0], v[4]));
        REQUIRE(intervalt(v[10], v[20]).modulo(intervalt(v[0], v[5])) == intervalt::top(type));
        REQUIRE(intervalt(v[10], v[20]).modulo(intervalt(v[-5], v[5])) == intervalt::top(type));

        REQUIRE(intervalt(v[-10], v[20]).modulo(intervalt(v[0], v[5])) == intervalt::top(type));
        REQUIRE(intervalt(v[-20], v[-10]).modulo(intervalt(v[0], v[5])) == intervalt::top(type));

        REQUIRE(intervalt(v[-20], v[-10]).modulo(intervalt(v[1], v[1])) == intervalt(v[0]));

        REQUIRE(intervalt(v[30], v[50]).modulo(intervalt(v[2], v[2])) == intervalt(v[0], v[1]));

        // Problems
        REQUIRE(intervalt(v[30], max_exprt(type)).modulo(intervalt(v[2], v[2])) == intervalt(v[0], v[1]));

      }
    }
  }
}
