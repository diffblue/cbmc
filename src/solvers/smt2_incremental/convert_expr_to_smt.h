// Author: Diffblue Ltd.

#ifndef CPROVER_SOLVERS_SMT2_INCREMENTAL_CONVERT_EXPR_TO_SMT_H
#define CPROVER_SOLVERS_SMT2_INCREMENTAL_CONVERT_EXPR_TO_SMT_H

#include <solvers/smt2_incremental/smt_terms.h>

class exprt;

/// \brief Converts the \p expression to an smt encoding of the same expression
///   stored as term ast (abstract syntax tree).
smt_termt convert_expr_to_smt(const exprt &expression);

#endif // CPROVER_SOLVERS_SMT2_INCREMENTAL_CONVERT_EXPR_TO_SMT_H
