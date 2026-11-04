/*******************************************************************\

Module: State-encoding solver backend selection

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// Construction of the decision procedure used for cprover's state-encoding
/// queries: either the built-in SAT backend (bit-vector flattening) or an
/// external SMT2 solver.

#ifndef CPROVER_CPROVER_STATE_ENCODING_SOLVER_FACTORY_H
#define CPROVER_CPROVER_STATE_ENCODING_SOLVER_FACTORY_H

#include <util/invariant.h>
#include <util/message.h>
#include <util/namespace.h>

#include <solvers/decision_procedure.h>
#include <solvers/sat/satcheck.h>

#include "bv_pointers_wide.h"
#include "cprover_smt2_dec.h"

#include <memory>
#include <string>

/// Owns the solver objects backing a state-encoding query and hands out the
/// \ref decision_proceduret to use.  Exactly one backend is populated: the
/// external SMT2 decision procedure when a solver binary is configured, or the
/// SAT backend (satcheck + bit-vector flattening) otherwise.
struct state_encoding_solvert
{
  // SAT backend (used when no SMT2 solver binary is configured)
  std::unique_ptr<satcheckt> satcheck;
  std::unique_ptr<bv_pointers_widet> bv;
  // external SMT2 backend
  std::unique_ptr<cprover_smt2_dect> smt2;

  /// The decision procedure to drive the query with.
  decision_proceduret &solver()
  {
    if(smt2 != nullptr)
      return *smt2;
    INVARIANT(
      bv != nullptr, "state-encoding solver bundle must have a backend");
    return *bv;
  }
};

/// Construct the state-encoding solver backend.  When \p smt2_solver_binary is
/// non-empty the external SMT2 solver is used; otherwise the built-in SAT
/// backend is used.  Centralises the selection so the call sites stay
/// consistent.
inline state_encoding_solvert make_state_encoding_solver(
  const namespacet &ns,
  const std::string &smt2_solver_binary,
  message_handlert &message_handler)
{
  state_encoding_solvert result;

  if(smt2_solver_binary.empty())
  {
    result.satcheck = std::make_unique<satcheckt>(message_handler);
    result.bv = std::make_unique<bv_pointers_widet>(
      ns, *result.satcheck, message_handler);
  }
  else
  {
    result.smt2 = std::make_unique<cprover_smt2_dect>(
      ns, smt2_solver_binary, message_handler);
  }

  return result;
}

#endif // CPROVER_CPROVER_STATE_ENCODING_SOLVER_FACTORY_H
