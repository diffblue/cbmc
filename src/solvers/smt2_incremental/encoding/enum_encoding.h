// Author: Diffblue Ltd.

#ifndef CPROVER_SOLVERS_SMT2_INCREMENTAL_ENCODING_ENUM_ENCODING_H
#define CPROVER_SOLVERS_SMT2_INCREMENTAL_ENCODING_ENUM_ENCODING_H

#include <util/expr.h>

/// Function to lower `expr` and its sub-expressions containing enum types.
/// Specifically it replaces the node `c_enum_tag_typet` type with the
/// underlying type of the enum the tag points to.
/// @param expr the expression to lower.
/// @param ns the namespace where to lookup `c_enum_tag_type`s.
/// @return the lowered expression.
exprt lower_enum(exprt expr, const namespacet &ns);

#endif // CPROVER_SOLVERS_SMT2_INCREMENTAL_ENCODING_ENUM_ENCODING_H
