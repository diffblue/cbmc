// Author: Diffblue Ltd.

#ifndef CPROVER_SOLVERS_SMT2_INCREMENTAL_STRUCT_ENCODING_H
#define CPROVER_SOLVERS_SMT2_INCREMENTAL_STRUCT_ENCODING_H

#include <util/expr.h> // For passing exprt by value. // IWYU pragma: keep
#include <util/namespace.h> // std::reference_wrapper<const namespacet> below
#include <util/type.h> // For passing `typet` by value. // IWYU pragma: keep

#include <memory>

class boolbv_widtht;
class member_exprt;
class struct_tag_typet;
class union_tag_typet;

/// Encodes struct types/values into non-struct expressions/types.
class struct_encodingt final
{
public:
  explicit struct_encodingt(const namespacet &ns);
  struct_encodingt(const struct_encodingt &other);
  ~struct_encodingt();

  typet encode(typet type) const;
  exprt encode(exprt expr) const;
  /// Reconstructs a struct expression of the \p original_type using the data
  /// from the bit vector \p encoded expression.
  exprt
  decode(const exprt &encoded, const struct_tag_typet &original_type) const;
  exprt
  decode(const exprt &encoded, const union_tag_typet &original_type) const;

private:
  std::unique_ptr<boolbv_widtht> boolbv_width;
  // The referenced type must be complete here: reference_wrapper's
  // constraints inspect it, and instantiating them for a forward-declared
  // namespacet had gcc 16 report -Wsfinae-incomplete when the class was
  // defined afterwards.
  std::reference_wrapper<const namespacet> ns;

  exprt encode_member(const member_exprt &member_expr) const;
};

#endif // CPROVER_SOLVERS_SMT2_INCREMENTAL_STRUCT_ENCODING_H
