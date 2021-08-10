/*******************************************************************\

 Module: Unit tests helpers for arrays

 Author: Jez Higgins, jez@jezuk.co.uk

\*******************************************************************/
#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_FULL_ARRAY_ABSTRACT_OBJECT_ARRAY_BUILDER_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_FULL_ARRAY_ABSTRACT_OBJECT_ARRAY_BUILDER_H

#include <analyses/variable-sensitivity/full_array_abstract_object.h>

full_array_abstract_objectt::full_array_pointert build_array(
  const exprt &array_expr,
  abstract_environmentt &environment,
  const namespacet &ns);

const int TOP_MEMBER = std::numeric_limits<int>::max();
full_array_abstract_objectt::full_array_pointert build_array(
  const std::vector<int> &array,
  abstract_environmentt &environment,
  const namespacet &ns);

full_array_abstract_objectt::full_array_pointert build_top_array();

full_array_abstract_objectt::full_array_pointert build_bottom_array();

#endif
