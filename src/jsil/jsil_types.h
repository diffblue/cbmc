/*******************************************************************\

Module: Jsil Language

Author: Daiva Naudziuniene, daivan@amazon.com

\*******************************************************************/

/// \file
/// Jsil Language

#ifndef CPROVER_JSIL_JSIL_TYPES_H
#define CPROVER_JSIL_JSIL_TYPES_H

#include <util/c_types.h>

typet jsil_kind();
typet jsil_any_type();
typet jsil_value_or_empty_type();
typet jsil_value_or_reference_type();
typet jsil_value_type();
typet jsil_prim_type();
typet jsil_reference_type();
typet jsil_member_reference_type();
typet jsil_variable_reference_type();
typet jsil_object_type();
typet jsil_user_object_type();
typet jsil_builtin_object_type();
typet jsil_null_type();
typet jsil_undefined_type();
typet jsil_empty_type();

bool jsil_is_subtype(const typet &type1, const typet &type2);
bool jsil_incompatible_types(const typet &type1, const typet &type2);
typet jsil_union(const typet &type1, const typet &type2);

class jsil_builtin_code_typet:public code_typet
{
public:
  explicit jsil_builtin_code_typet(code_typet &code):
    code_typet(code)
  {
    set("jsil_builtin_proceduret", true);
  }
};

inline jsil_builtin_code_typet &to_jsil_builtin_code_type(
  code_typet &code)
{
  assert(code.get_bool("jsil_builtin_proceduret"));
  return static_cast<jsil_builtin_code_typet &>(code);
}

inline bool is_jsil_builtin_code_type(const typet &type)
{
  return type.id()==ID_code &&
         type.get_bool("jsil_builtin_proceduret");
}

class jsil_spec_code_typet:public code_typet
{
public:
  explicit jsil_spec_code_typet(code_typet &code):
    code_typet(code)
  {
    set("jsil_spec_proceduret", true);
  }
};

inline jsil_spec_code_typet &to_jsil_spec_code_type(
  code_typet &code)
{
  assert(code.get_bool("jsil_spec_proceduret"));
  return static_cast<jsil_spec_code_typet &>(code);
}

inline bool is_jsil_spec_code_type(const typet &type)
{
  return type.id()==ID_code &&
         type.get_bool("jsil_spec_proceduret");
}

class jsil_union_typet:public union_typet
{
public:
  jsil_union_typet():union_typet() { }

  explicit jsil_union_typet(const typet &type)
    :jsil_union_typet(std::vector<typet>({type})) { }

  explicit jsil_union_typet(const std::vector<typet> &types);

  jsil_union_typet union_with(const jsil_union_typet &other) const;

  jsil_union_typet intersect_with(const jsil_union_typet &other) const;

  bool is_subtype(const jsil_union_typet &other) const;

  const typet &to_type() const;
};

inline jsil_union_typet &to_jsil_union_type(typet &type)
{
  assert(type.id()==ID_union);
  return static_cast<jsil_union_typet &>(type);
}

inline const jsil_union_typet &to_jsil_union_type(const typet &type)
{
  assert(type.id()==ID_union);
  return static_cast<const jsil_union_typet &>(type);
}

#endif // CPROVER_JSIL_JSIL_TYPES_H
