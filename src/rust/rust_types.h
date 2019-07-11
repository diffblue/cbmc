/*******************************************************************\

Module: Rust Language

Author: Brett Schiff, bschiff@amazon.com

\*******************************************************************/
// Adapted from the similarly named file in the jsil directory

/// \file
/// Rust Language

#ifndef CPROVER_RUST_RUST_TYPES_H
#define CPROVER_RUST_RUST_TYPES_H

#include <util/std_types.h>
#include <util/type.h>

typet rusttype_to_ctype(irep_idt name);
typet rust_resolve_differing_types(exprt &a, exprt &b);

typet rust_kind();
typet rust_any_type();
typet rust_value_or_empty_type();
typet rust_value_or_reference_type();
typet rust_value_type();
typet rust_prim_type();
typet rust_reference_type();
typet rust_member_reference_type();
typet rust_variable_reference_type();
typet rust_object_type();
typet rust_user_object_type();
typet rust_builtin_object_type();
typet rust_null_type();
typet rust_undefined_type();
typet rust_empty_type();

bool rust_is_subtype(const typet &type1, const typet &type2);
bool rust_incompatible_types(const typet &type1, const typet &type2);
typet rust_union(const typet &type1, const typet &type2);

bool is_empty_type(typet const &type);

class rust_builtin_code_typet : public code_typet
{
public:
  explicit rust_builtin_code_typet(code_typet &code) : code_typet(code)
  {
    set("rust_builtin_proceduret", true);
  }
};

inline rust_builtin_code_typet &to_rust_builtin_code_type(code_typet &code)
{
  // assert(code.get_bool("rust_builtin_proceduret"));
  if(!(code.get_bool("rust_builtin_proceduret")))
    throw 0;
  return static_cast<rust_builtin_code_typet &>(code);
}

inline bool is_rust_builtin_code_type(const typet &type)
{
  return type.id() == ID_code && type.get_bool("rust_builtin_proceduret");
}

class rust_spec_code_typet : public code_typet
{
public:
  explicit rust_spec_code_typet(code_typet &code) : code_typet(code)
  {
    set("rust_spec_proceduret", true);
  }
};

inline rust_spec_code_typet &to_rust_spec_code_type(code_typet &code)
{
  // assert(code.get_bool("rust_spec_proceduret"));
  if(!(code.get_bool("rust_spec_proceduret")))
    throw 0;
  return static_cast<rust_spec_code_typet &>(code);
}

inline bool is_rust_spec_code_type(const typet &type)
{
  return type.id() == ID_code && type.get_bool("rust_spec_proceduret");
}

class rust_union_typet : public union_typet
{
public:
  rust_union_typet() : union_typet()
  {
  }

  explicit rust_union_typet(const typet &type)
    : rust_union_typet(std::vector<typet>({type}))
  {
  }

  explicit rust_union_typet(const std::vector<typet> &types);

  rust_union_typet union_with(const rust_union_typet &other) const;

  rust_union_typet intersect_with(const rust_union_typet &other) const;

  bool is_subtype(const rust_union_typet &other) const;

  const typet &to_type() const;
};

inline rust_union_typet &to_rust_union_type(typet &type)
{
  // assert(type.id() == ID_union);
  if(!(type.id() == ID_union))
    throw 0;
  return static_cast<rust_union_typet &>(type);
}

inline const rust_union_typet &to_rust_union_type(const typet &type)
{
  // assert(type.id() == ID_union);
  if(!(type.id() == ID_union))
    throw 0;
  return static_cast<const rust_union_typet &>(type);
}

#endif // CPROVER_RUST_RUST_TYPES_H
