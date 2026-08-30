/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_SOLVERS_PROP_PROP_H
#define CPROVER_SOLVERS_PROP_PROP_H

// decision procedure wrapper for boolean propositional logics

#include <util/message.h>
#include <util/threeval.h>

#include "literal.h"

#include <cstdint>

/// \brief Abstract interface for propositional logic solvers.
///
/// Provides the common API for constructing propositional formulas and solving
/// them. Formulas are built from \ref literalt variables obtained via
/// \ref new_variable, combined using Boolean operators (\ref land, \ref lor,
/// etc.), and constrained via clauses (\ref lcnf) or unit constraints
/// (\ref l_set_to). Calling \ref prop_solve checks satisfiability; the
/// satisfying assignment can then be read via \ref l_get, or, in the
/// unsatisfiable case, the conflict queried via \ref is_in_conflict.
///
/// Concrete implementations include SAT solvers (MiniSat, CaDiCaL, etc.)
/// and structural representations (DIMACS file output, AIG).
///
/// The solver supports incremental use: after solving, new constraints or
/// variables may be added and the solver invoked again. The state machine
/// below describes which operations are valid in each state.
///
/// A propositional solver follows a state machine:
///
///   UNKNOWN ──prop_solve()──► SAT ──lcnf()/new_variable()──► UNKNOWN
///      ▲                      │
///      │                      └──l_get() valid
///      │
///   UNKNOWN ──prop_solve()──► UNSAT ──lcnf()/new_variable()──► UNKNOWN
///      │                       │
///      │                       └──is_in_conflict() valid
///      │
///   UNKNOWN ──prop_solve()──► ERROR (sticky)
///
/// After construction, the solver is in the UNKNOWN state. Calling
/// \ref prop_solve transitions to SAT, UNSAT, or ERROR. Reading the
/// satisfying assignment via \ref l_get is only valid in the SAT state.
/// Querying \ref is_in_conflict is only valid in the UNSAT state.
/// Adding new constraints (\ref lcnf, \ref l_set_to) or variables
/// (\ref new_variable) transitions SAT/UNSAT back to UNKNOWN. The ERROR state
/// is sticky: once \ref prop_solve has reported an error (or thrown), adding
/// constraints or variables does not clear it (see \ref clear_status()).
class propt
{
public:
  explicit propt(message_handlert &message_handler) : log(message_handler)
  {
  }

  virtual ~propt() { }

  // boolean operators
  virtual literalt land(literalt a, literalt b)=0;
  virtual literalt lor(literalt a, literalt b)=0;
  virtual literalt land(const bvt &bv)=0;
  virtual literalt lor(const bvt &bv)=0;
  virtual literalt lxor(literalt a, literalt b)=0;
  virtual literalt lxor(const bvt &bv)=0;
  virtual literalt lnand(literalt a, literalt b)=0;
  virtual literalt lnor(literalt a, literalt b)=0;
  virtual literalt lequal(literalt a, literalt b)=0;
  virtual literalt limplies(literalt a, literalt b)=0;
  virtual literalt lselect(literalt a, literalt b, literalt c)=0; // a?b:c
  virtual void set_equal(literalt a, literalt b);

  virtual void l_set_to(literalt a, bool value)
  {
    clear_status();
    set_equal(a, const_literal(value));
  }

  void l_set_to_true(literalt a)
  { l_set_to(a, true); }
  void l_set_to_false(literalt a)
  { l_set_to(a, false); }

  // constraints
  void lcnf(literalt l0, literalt l1)
  {
    lcnf_bv.resize(2);
    lcnf_bv[0] = l0;
    lcnf_bv[1] = l1;
    lcnf(lcnf_bv);
  }

  void lcnf(literalt l0, literalt l1, literalt l2)
  {
    lcnf_bv.resize(3);
    lcnf_bv[0]=l0;
    lcnf_bv[1]=l1;
    lcnf_bv[2]=l2;
    lcnf(lcnf_bv);
  }

  void lcnf(literalt l0, literalt l1, literalt l2, literalt l3)
  {
    lcnf_bv.resize(4);
    lcnf_bv[0]=l0;
    lcnf_bv[1]=l1;
    lcnf_bv[2]=l2;
    lcnf_bv[3]=l3;
    lcnf(lcnf_bv);
  }

  /// Add the clause \p bv to the formula.
  /// This is a non-virtual entry point that calls \ref clear_status() once
  /// and dispatches to the backend-specific \ref do_lcnf, ensuring the
  /// state-machine invariant is enforced for every backend without per-backend
  /// boilerplate.
  void lcnf(const bvt &bv)
  {
    clear_status();
    do_lcnf(bv);
  }
  virtual bool has_set_to() const { return true; }

  // Some solvers (notably aig) prefer encodings that avoid raw CNF
  // They overload this to return false and thus avoid some optimisations
  virtual bool cnf_handled_well() const { return true; }

  // solving with assumptions
  virtual bool has_assumptions() const
  {
    return false;
  }

  // variables
  virtual literalt new_variable()=0;
  virtual void set_variable_name(literalt, const irep_idt &) { }
  virtual size_t no_variables() const=0;
  virtual bvt new_variables(std::size_t width);

  // solving
  virtual std::string solver_text() const = 0;
  enum class resultt { P_SATISFIABLE, P_UNSATISFIABLE, P_ERROR };
  resultt prop_solve();
  resultt prop_solve(const bvt &assumptions);

  /// Solver state: tracks whether the model or conflict can be queried.
  // TODO: resultt (P_SATISFIABLE/P_UNSATISFIABLE/P_ERROR) and statust
  // (UNKNOWN/SAT/UNSAT/ERROR) overlap heavily; statust additionally
  // distinguishes the "not yet solved" UNKNOWN state. These should be unified
  // as a follow-up (e.g. by using statust everywhere, or std::optional<resultt>
  // for the state), which would also remove the status_from_result() helper in
  // prop.cpp.
  enum class statust
  {
    UNKNOWN,
    SAT,
    UNSAT,
    ERROR
  };

  /// Return the current solver state.
  statust get_status() const
  {
    return solver_state;
  }

  // satisfying assignment
  virtual tvt l_get(literalt a) const=0;
  virtual void set_assignment(literalt a, bool value) = 0;

  /// Returns true if an assumption is in the final conflict.
  /// Note that only literals that are assumptions (see set_assumptions)
  /// may be queried.
  /// \return true iff the given literal is part of the final conflict
  virtual bool is_in_conflict(literalt l) const = 0;
  virtual bool has_is_in_conflict() const { return false; }

  // an incremental solver may remove any variables that aren't frozen
  virtual void set_frozen(literalt) { }

  // Resource limits:
  virtual void set_time_limit_seconds(uint32_t)
  {
    log.warning() << "CPU limit ignored (not implemented)" << messaget::eom;
  }

  std::size_t get_number_of_solver_calls() const;

protected:
  // solve under the given assumption
  virtual resultt do_prop_solve(const bvt &assumptions) = 0;

  /// Backend-specific clause addition. Called by the non-virtual \ref lcnf
  /// entry point, which has already invalidated any cached solver state via
  /// \ref clear_status().
  virtual void do_lcnf(const bvt &bv) = 0;

  /// Transition to UNKNOWN state when the solver is mutated.
  /// The ERROR state is intentionally sticky: once the solver has encountered
  /// an error, adding new constraints does not clear it.
  void clear_status()
  {
    if(solver_state == statust::SAT || solver_state == statust::UNSAT)
      solver_state = statust::UNKNOWN;
  }

  // to avoid a temporary for lcnf(...)
  bvt lcnf_bv;

  messaget log;
  std::size_t number_of_solver_calls = 0;
  statust solver_state = statust::UNKNOWN;
};

#endif // CPROVER_SOLVERS_PROP_PROP_H
