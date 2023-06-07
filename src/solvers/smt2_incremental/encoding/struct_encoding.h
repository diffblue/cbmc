// Author: Diffblue Ltd.

#ifndef CPROVER_SOLVERS_SMT2_INCREMENTAL_STRUCT_ENCODING_H
#define CPROVER_SOLVERS_SMT2_INCREMENTAL_STRUCT_ENCODING_H

#include <util/expr.h> // For passing exprt by value. // IWYU pragma: keep
#include <util/type.h> // For passing `typet` by value. // IWYU pragma: keep

#include <memory>

class namespacet;
class boolbv_widtht;
class member_exprt;

/// Encodes struct types/values into non-struct expressions/types.
class struct_encodingt final
{
public:
  explicit struct_encodingt(const namespacet &ns);
  struct_encodingt(const struct_encodingt &other);
  ~struct_encodingt();

  typet encode(typet type) const;
  exprt encode(exprt expr) const;

private:
  std::unique_ptr<boolbv_widtht> boolbv_width;
  std::reference_wrapper<const namespacet> ns;

  exprt encode_member(const member_exprt &member_expr) const;
};

#endif // CPROVER_SOLVERS_SMT2_INCREMENTAL_STRUCT_ENCODING_H
