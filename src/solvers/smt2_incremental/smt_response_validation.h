// Author: Diffblue Ltd.

#ifndef CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT_RESPONSE_VALIDATION_H
#define CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT_RESPONSE_VALIDATION_H

#include <util/nodiscard.h>

#include <solvers/smt2_incremental/response_or_error.h>
#include <solvers/smt2_incremental/smt_responses.h>

NODISCARD response_or_errort<smt_responset> validate_smt_response(
  const irept &parse_tree,
  const std::unordered_map<irep_idt, smt_identifier_termt> &identifier_table);

#endif // CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT_RESPONSE_VALIDATION_H
