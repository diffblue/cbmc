// Author: Diffblue Ltd.

#ifndef CPROVER_SOLVERS_SMT2_INCREMENTAL_CONVERT_EXPR_TO_SMT_H
#define CPROVER_SOLVERS_SMT2_INCREMENTAL_CONVERT_EXPR_TO_SMT_H

#include <solvers/smt2_incremental/object_tracking.h>
#include <solvers/smt2_incremental/smt_sorts.h>
#include <solvers/smt2_incremental/smt_terms.h>

class exprt;
class typet;

/// \brief Converts the \p type to an smt encoding of the same expression
///   stored as sort ast (abstract syntax tree).
smt_sortt convert_type_to_smt_sort(const typet &type);

/// \brief Converts the \p expression to an smt encoding of the same expression
///   stored as term ast (abstract syntax tree).
smt_termt
convert_expr_to_smt(const exprt &expression, const smt_object_mapt &object_map);

#endif // CPROVER_SOLVERS_SMT2_INCREMENTAL_CONVERT_EXPR_TO_SMT_H
