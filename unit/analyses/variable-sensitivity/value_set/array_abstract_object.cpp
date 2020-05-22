/*******************************************************************\

Module: Unit tests for value set array abstract values

Author: Diffblue Ltd.

\*******************************************************************/

#include "value_set_test_common.h"
#include <analyses/variable-sensitivity/value_set_array_abstract_object.h>
#include <util/arith_tools.h>

TEST_CASE(
  "A value set array abstract object created from type is top",
  VALUE_SET_TEST_TAGS)
{
  value_set_array_abstract_objectt abstract_object{
    array_typet{signedbv_typet{32}, from_integer(1, unsignedbv_typet{32})}};
  REQUIRE(abstract_object.is_top());
  REQUIRE(!abstract_object.is_bottom());
}
