/*******************************************************************\

 Module: Unit tests helpers for structs

 Author: Jez Higgins, jez@jezuk.co.uk

\*******************************************************************/
#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_FULL_STRUCT_ABSTRACT_OBJECT_STRUCT_BUILDER_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_FULL_STRUCT_ABSTRACT_OBJECT_STRUCT_BUILDER_H

#include <analyses/variable-sensitivity/full_struct_abstract_object.h>

#include <map>

class abstract_environmentt;
class namespacet;

full_struct_abstract_objectt::constant_struct_pointert build_struct(
  const struct_exprt &starting_value,
  abstract_environmentt &environment,
  const namespacet &ns);

const int TOP_MEMBER = std::numeric_limits<int>::max();
full_struct_abstract_objectt::constant_struct_pointert build_struct(
  const std::map<std::string, int> &members,
  abstract_environmentt &environment,
  const namespacet &ns);

exprt read_component(
  full_struct_abstract_objectt::constant_struct_pointert struct_object,
  const member_exprt &component,
  const abstract_environmentt &environment,
  const namespacet &ns);

full_struct_abstract_objectt::constant_struct_pointert build_top_struct();

full_struct_abstract_objectt::constant_struct_pointert build_bottom_struct();

#endif
