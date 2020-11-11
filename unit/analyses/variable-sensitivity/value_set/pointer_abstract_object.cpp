/*******************************************************************\

Module: Unit tests for value set pointer abstract objects

Author: Diffblue Ltd.

\*******************************************************************/

#include "value_set_test_common.h"
#include <analyses/variable-sensitivity/value_set_pointer_abstract_object.h>

TEST_CASE(
  "A value set pointer abstract object created from type is top",
  VALUE_SET_TEST_TAGS)
{
  value_set_pointer_abstract_objectt abstract_object(
    pointer_typet(signedbv_typet{32}, 32));
  REQUIRE(abstract_object.is_top());
  REQUIRE(!abstract_object.is_bottom());
}
