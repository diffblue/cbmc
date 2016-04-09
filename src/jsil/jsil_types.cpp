/*******************************************************************\

Module: Jsil Language

Author: Daiva Naudziuniene, daivan@amazon.com

\*******************************************************************/

#include "jsil_types.h"

typet jsil_any_typet()
{
  return jsil_union_typet({
                          empty_typet(),
                          jsil_referencet(),
                          jsil_valuet()
                          });
}

typet jsil_value_or_emptyt()
{
  return jsil_union_typet({
                          jsil_valuet(),
                          empty_typet()
                          });
}

typet jsil_value_or_referencet()
{
  return jsil_union_typet({
                          jsil_valuet(),
                          jsil_referencet()
                          });
}

typet jsil_valuet()
{
  return jsil_union_typet({
                          jsil_undefinedt(),
                          jsil_nullt(),
                          jsil_prim_typet(),
                          jsil_objectt()
                          });
}

typet jsil_prim_typet()
{
  return jsil_union_typet({
                          floatbv_typet(),
                          string_typet(),
                          bool_typet()
                          });
}

typet jsil_referencet() {
  return jsil_union_typet({
                          jsil_member_referencet(),
                          jsil_variable_referencet()
                          });
}

typet jsil_member_referencet()
{
  return typet("jsil_member_referencet");
}

typet jsil_variable_referencet()
{
  return typet("jsil_variable_referencet");
}

typet jsil_objectt() {
  return jsil_union_typet({
                          jsil_user_objectt(),
                          jsil_builtin_objectt()
                          });
}

typet jsil_user_objectt()
{
  return typet("jsil_user_objectt");
}

typet jsil_builtin_objectt()
{
  return typet("jsil_builtin_objectt");
}

typet jsil_nullt()
{
  return typet("jsil_nullt");
}

typet jsil_undefinedt()
{
  return typet("jsil_undefinedt");
}

typet jsil_kindt()
{
  return typet("jsil_kindt");
}

/*******************************************************************\

Function: jsil_upper_bound_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool jsil_is_subtype(const typet &type1, const typet &type2)
{
  if(type2.id()==ID_union)
  {
    const jsil_union_typet &type2_union=to_jsil_union_type(type2);
    if(type1.id()==ID_union)
    {
      return to_jsil_union_type(type1).is_subtype(type2_union);
    }
    else
    {
      return (jsil_union_typet(type1).is_subtype(type2_union));
    }
  }
  else
    return type1.id()==type2.id();
}

typet jsil_union(const typet &type1, const typet &type2)
{
  return jsil_union_typet(type1).union_with(
    jsil_union_typet(type2)).to_type();
}

bool compare_components(
  const union_typet::componentt &comp1,
  const union_typet::componentt &comp2)
{
  return comp1.type().id().get_no() < comp2.type().id().get_no();
}

jsil_union_typet::jsil_union_typet(
  const std::vector<typet> &types):union_typet()
{
  auto &elements=components();
  for(const auto &type : types)
  {
    if(type.id()==ID_union)
    {
      for(const auto &component : to_union_type(type).components())
      {
        elements.push_back(component);
      }
    }
    else
      elements.push_back(componentt(ID_anonymous, type));
  }

  std::sort(elements.begin(), elements.end(), compare_components);
}

/*******************************************************************\

Function: jsil_union_typet::union_with

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

jsil_union_typet jsil_union_typet::union_with(
  const jsil_union_typet &other) const
{
  auto &elements1 = components();
  auto &elements2 = other.components();
  jsil_union_typet result;
  auto &elements = result.components();
  elements.resize(elements1.size()+elements2.size());
  std::vector<union_typet::componentt>::iterator it=std::set_union(
    elements1.begin(), elements1.end(), elements2.begin(), elements2.end(),
	elements.begin(), compare_components);
  elements.resize(it-elements.begin());
  return result;
}

/*******************************************************************\

Function: jsil_union_typet::intersect_with

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

jsil_union_typet jsil_union_typet::intersect_with(
  const jsil_union_typet &other) const
{
  auto &elements1=components();
  auto &elements2=other.components();
  jsil_union_typet result;
  auto &elements=result.components();
  elements.resize(std::min(elements1.size(),elements2.size()));
  std::vector<union_typet::componentt>::iterator it=std::set_intersection(
    elements1.begin(), elements1.end(), elements2.begin(), elements2.end(),
    elements.begin(), compare_components);
  elements.resize(it-elements.begin());

  return result;
}

/*******************************************************************\

Function: jsil_union_typet::is_subtype

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool jsil_union_typet::is_subtype(const jsil_union_typet &other) const
{
  auto &elements1=components();
  auto &elements2=other.components();
  std::vector<union_typet::componentt> diff(elements1.size());
  std::vector<union_typet::componentt>::iterator it=std::set_difference(
    elements1.begin(), elements1.end(), elements2.begin(), elements2.end(),
    diff.begin(), compare_components);
  diff.resize(it-diff.begin());

  return diff.empty();
}

/*******************************************************************\

Function: jsil_union_typet::to_type()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const typet& jsil_union_typet::to_type() const
{
  auto &elements=components();
  if (elements.size()==1)
    return elements[0].type();

  return *this;
}
