/*******************************************************************\

Module: Jsil Language

Author: Daiva Naudziuniene, daivan@amazon.com

\*******************************************************************/

#include <algorithm>

#include "jsil_types.h"

/*******************************************************************\

Function: jsil_any_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet jsil_any_type()
{
  return jsil_union_typet({ // NOLINT(whitespace/braces)
                          jsil_empty_type(),
                          jsil_reference_type(),
                          jsil_value_type()
                          });
}

/*******************************************************************\

Function: jsil_value_or_empty_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet jsil_value_or_empty_type()
{
  return jsil_union_typet({ // NOLINT(whitespace/braces)
                          jsil_value_type(),
                          jsil_empty_type()
                          });
}

/*******************************************************************\

Function: jsil_value_or_reference_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet jsil_value_or_reference_type()
{
  return jsil_union_typet({ // NOLINT(whitespace/braces)
                          jsil_value_type(),
                          jsil_reference_type()
                          });
}

/*******************************************************************\

Function: jsil_value_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet jsil_value_type()
{
  return jsil_union_typet({ // NOLINT(whitespace/braces)
                          jsil_undefined_type(),
                          jsil_null_type(),
                          jsil_prim_type(),
                          jsil_object_type()
                          });
}

/*******************************************************************\

Function: jsil_prim_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet jsil_prim_type()
{
  return jsil_union_typet({ // NOLINT(whitespace/braces)
                          floatbv_typet(),
                          string_typet(),
                          bool_typet()
                          });
}

/*******************************************************************\

Function: jsil_reference_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet jsil_reference_type()
{
  return jsil_union_typet({ // NOLINT(whitespace/braces)
                          jsil_member_reference_type(),
                          jsil_variable_reference_type()
                          });
}

/*******************************************************************\

Function: jsil_member_reference_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet jsil_member_reference_type()
{
  return typet("jsil_member_reference_type");
}

/*******************************************************************\

Function: jsil_variable_reference_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet jsil_variable_reference_type()
{
  return typet("jsil_variable_reference_type");
}

/*******************************************************************\

Function: jsil_object_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet jsil_object_type()
{
  return jsil_union_typet({ // NOLINT(whitespace/braces)
                          jsil_user_object_type(),
                          jsil_builtin_object_type()
                          });
}

/*******************************************************************\

Function: jsil_user_object_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet jsil_user_object_type()
{
  return typet("jsil_user_object_type");
}

/*******************************************************************\

Function: jsil_builtin_object_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet jsil_builtin_object_type()
{
  return typet("jsil_builtin_object_type");
}

/*******************************************************************\

Function: jsil_null_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet jsil_null_type()
{
  return typet("jsil_null_type");
}

/*******************************************************************\

Function: jsil_undefined_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet jsil_undefined_type()
{
  return typet("jsil_undefined_type");
}

/*******************************************************************\

Function: jsil_kind

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet jsil_kind()
{
  return typet("jsil_kind");
}

/*******************************************************************\

Function: jsil_empty_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet jsil_empty_type()
{
  return typet("jsil_empty_type");
}

/*******************************************************************\

Function: jsil_is_subtype

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
      return to_jsil_union_type(type1).is_subtype(type2_union);
    else
      return jsil_union_typet(type1).is_subtype(type2_union);
  }
  else
    return type1.id()==type2.id();
}

/*******************************************************************\

Function: jsil_incompatible_types

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool jsil_incompatible_types(const typet &type1, const typet &type2)
{
  return jsil_union_typet(type1).intersect_with(
    jsil_union_typet(type2)).components().empty();
}

/*******************************************************************\

Function: jsil_union

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet jsil_union(const typet &type1, const typet &type2)
{
  return jsil_union_typet(type1)
    .union_with(jsil_union_typet(type2)).to_type();
}

/*******************************************************************\

Function: compare_components

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool compare_components(
  const union_typet::componentt &comp1,
  const union_typet::componentt &comp2)
{
  return comp1.type().id()<comp2.type().id();
}

/*******************************************************************\

Function: jsil_union_typet::jsil_union_typet

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

jsil_union_typet::jsil_union_typet(const std::vector<typet> &types):
    union_typet()
{
  auto &elements=components();
  for(const auto &type : types)
  {
    if(type.id()==ID_union)
    {
      for(const auto &component : to_union_type(type).components())
        elements.push_back(component);
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
  auto &elements1=components();
  auto &elements2=other.components();
  jsil_union_typet result;
  auto &elements=result.components();
  elements.resize(elements1.size()+elements2.size());
  std::vector<union_typet::componentt>::iterator it=std::set_union(
    elements1.begin(), elements1.end(),
    elements2.begin(), elements2.end(),
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
  elements.resize(std::min(elements1.size(), elements2.size()));
  std::vector<union_typet::componentt>::iterator it=std::set_intersection(
    elements1.begin(), elements1.end(),
    elements2.begin(), elements2.end(),
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
  auto it=components().begin();
  auto it2=other.components().begin();
  while(it<components().end())
  {
    if(it2>=other.components().end())
    {
      // We haven't found all types, but the second array finishes
      return false;
    }

    if(it->type().id()==it2->type().id())
    {
      // Found the type
      it++;
      it2++;
    }
    else if(it->type().id()<it2->type().id())
    {
      // Missing type
      return false;
    }
    else // it->type().id()>it2->type().id()
    {
      // Skip one element in the second array
      it2++;
    }
  }

  return true;
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
  if(elements.size()==1)
    return elements[0].type();

  return *this;
}
