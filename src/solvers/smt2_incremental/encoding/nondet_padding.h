// Author: Diffblue Ltd.

/// \file
/// Expressions for use in incremental SMT2 decision procedure

#ifndef CPROVER_SOLVERS_SMT2_INCREMENTAL_ENCODING_NONDET_PADDING_H
#define CPROVER_SOLVERS_SMT2_INCREMENTAL_ENCODING_NONDET_PADDING_H

#include <util/bitvector_types.h>
#include <util/expr.h>
#include <util/invariant.h>

class nondet_padding_exprt;
void validate_expr(const nondet_padding_exprt &padding);

/// This expression serves as a placeholder for the bits which have non
/// deterministic value in a larger bit vector. It is inserted in contexts where
/// a subset of the bits are assigned to an expression and the remainder are
/// left unspecified.
class nondet_padding_exprt : public expr_protectedt
{
public:
  static const irep_idt ID_nondet_padding;

  explicit nondet_padding_exprt(typet type)
    : expr_protectedt{ID_nondet_padding, std::move(type)}
  {
    validate_expr(*this);
  }
};

template <>
inline bool can_cast_expr<nondet_padding_exprt>(const exprt &base)
{
  return base.id() == nondet_padding_exprt::ID_nondet_padding;
}

inline void validate_expr(const nondet_padding_exprt &padding)
{
  INVARIANT(
    can_cast_type<bv_typet>(padding.type()),
    "Nondet padding is expected to pad a bit vector type.");
}

#endif // CPROVER_SOLVERS_SMT2_INCREMENTAL_ENCODING_NONDET_PADDING_H
