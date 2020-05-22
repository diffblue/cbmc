/*******************************************************************\

Module: Unit tests for value set abstract values

Author: Diffblue Ltd.

\*******************************************************************/

#include "value_set_test_common.h"
#include <analyses/variable-sensitivity/value_set_abstract_value.h>

TEST_CASE(
  "A value set abstract object created from type is top",
  VALUE_SET_TEST_TAGS)
{
  value_set_abstract_valuet abstract_value(signedbv_typet{32});
  REQUIRE(abstract_value.is_top());
  REQUIRE(!abstract_value.is_bottom());
}
