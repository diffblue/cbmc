// Author: Diffblue Ltd.

#ifndef CPROVER_SOLVERS_SMT2_INCREMENTAL_STRUCT_ENCODING_H
#define CPROVER_SOLVERS_SMT2_INCREMENTAL_STRUCT_ENCODING_H

#include <util/type.h> // For passing `typet` by value. // IWYU pragma: keep

#include <memory>

class namespacet;
class boolbv_widtht;

/// Encodes struct types/values into non-struct expressions/types.
class struct_encodingt final
{
public:
  explicit struct_encodingt(const namespacet &ns);
  struct_encodingt(const struct_encodingt &other);
  ~struct_encodingt();

  typet encode(typet type) const;

private:
  std::unique_ptr<boolbv_widtht> boolbv_width;
};

#endif // CPROVER_SOLVERS_SMT2_INCREMENTAL_STRUCT_ENCODING_H
