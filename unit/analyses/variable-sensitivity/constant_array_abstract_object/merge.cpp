/*******************************************************************\

 Module: Unit tests for constant_array_abstract_object::merge

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

#include <typeinfo>
#include <catch.hpp>
#include <util/namespace.h>
#include <util/options.h>
#include <util/symbol_table.h>
#include <util/std_expr.h>

#include <analyses/ai.h>
#include <analyses/variable-sensitivity/variable_sensitivity_domain.h>

#include <analyses/variable-sensitivity/abstract_enviroment.h>
#include <analyses/variable-sensitivity/abstract_object.h>
#include <analyses/variable-sensitivity/constant_array_abstract_object.h>
#include <analyses/variable-sensitivity/variable_sensitivity_object_factory.h>

typedef constant_array_abstract_objectt::constant_array_abstract_object_pointert
  constant_array_abstract_object_pointert;

// Util


class array_utilt
{
public:
  array_utilt(const abstract_environmentt &enviroment, const namespacet &ns):
    enviroment(enviroment), ns(ns)
  {}

  exprt read_index(
     constant_array_abstract_object_pointert array_object,
    const index_exprt &index) const
  {
    return array_object->read_index(enviroment, index, ns)->to_constant();
  }

private:
  const abstract_environmentt &enviroment;
  const namespacet ns;
};

SCENARIO("merge_constant_array_abstract_object",
  "[core]"
  "[analyses][variable-sensitivity][constant_array_abstract_object][merge]")
{
  GIVEN("Two arrays of size 3, whose first elements are the same")
  {
  // int val1[3] = {1, 2, 3}
  exprt val1=
    array_exprt(
      array_typet(integer_typet(), constant_exprt::integer_constant(3)));
  val1.operands().push_back(constant_exprt::integer_constant(1));
  val1.operands().push_back(constant_exprt::integer_constant(2));
  val1.operands().push_back(constant_exprt::integer_constant(3));

  // int val2[3] = {1, 4, 5}
  exprt val2=
    array_exprt(
      array_typet(integer_typet(), constant_exprt::integer_constant(3)));
  val2.operands().push_back(constant_exprt::integer_constant(1));
  val2.operands().push_back(constant_exprt::integer_constant(4));
  val2.operands().push_back(constant_exprt::integer_constant(5));

  // index_exprt for reading from an array
  const index_exprt i0=
    index_exprt(nil_exprt(), constant_exprt::integer_constant(0));
  const index_exprt i1=
    index_exprt(nil_exprt(), constant_exprt::integer_constant(1));
  const index_exprt i2=
    index_exprt(nil_exprt(), constant_exprt::integer_constant(2));

  abstract_environmentt enviroment;
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  optionst options;
  options.set_option("pointers", true);
  options.set_option("arrays", true);
  options.set_option("structs", true);
  variable_sensitivity_object_factoryt::instance().set_options(options);

  array_utilt util(enviroment, ns);

  abstract_object_pointert result;
  bool modified=false;
  WHEN("Merging two constant array AOs with the same array")
  {
    auto op1=
      std::make_shared<constant_array_abstract_objectt>(val1, enviroment, ns);
    auto op2=
      std::make_shared<constant_array_abstract_objectt>(val1, enviroment, ns);

    result=abstract_objectt::merge(op1, op2, modified);

    const auto &cast_result=
      std::dynamic_pointer_cast<const constant_array_abstract_objectt>(
        result);
    THEN("The original constant array AO should be returned")
    {
      // Though we may become top or bottom, the type should be unchanged
      REQUIRE(cast_result);

      // Correctness of merge
      REQUIRE_FALSE(modified);
      REQUIRE_FALSE(cast_result->is_top());
      REQUIRE_FALSE(cast_result->is_bottom());
      REQUIRE(util.read_index(cast_result, i0)==val1.op0());
      REQUIRE(util.read_index(cast_result, i1)==val1.op1());
      REQUIRE(util.read_index(cast_result, i2)==val1.op2());

      // Is optimal
      REQUIRE(result==op1);
    }
  }
  WHEN("Merging two constant array AOs with different value arrays")
  {
    auto op1=
      std::make_shared<constant_array_abstract_objectt>(val1, enviroment, ns);
    auto op2=
      std::make_shared<constant_array_abstract_objectt>(val2, enviroment, ns);

    result=abstract_objectt::merge(op1, op2, modified);

    const auto &cast_result=
      std::dynamic_pointer_cast<const constant_array_abstract_objectt>(result);

    THEN("A new constant array AO whose first value is the same and "
      "the other two are top")
    {
      // Though we may become top or bottom, the type should be unchanged
      REQUIRE(cast_result);

      // Correctness of merge
      REQUIRE(modified);
      REQUIRE_FALSE(cast_result->is_top());
      REQUIRE_FALSE(cast_result->is_bottom());
      REQUIRE(util.read_index(cast_result, i0)==val1.op0());
      REQUIRE(util.read_index(cast_result, i1)==nil_exprt());
      REQUIRE(util.read_index(cast_result, i2)==nil_exprt());

      // Since it has modified, we definitely shouldn't be reusing the pointer
      REQUIRE_FALSE(result==op1);
      }
    }
  }
}
