/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "satcheck_minisat2.h"

#ifndef _WIN32
#  include <signal.h>
#  include <unistd.h>
#endif

#include <limits>

#include <util/invariant.h>
#include <util/make_unique.h>
#include <util/threeval.h>

#include <minisat/core/Solver.h>
#include <minisat/simp/SimpSolver.h>

#ifndef HAVE_MINISAT2
#error "Expected HAVE_MINISAT2"
#endif

void convert(const bvt &bv, Minisat::vec<Minisat::Lit> &dest)
{
  PRECONDITION(
    bv.size() <= static_cast<std::size_t>(std::numeric_limits<int>::max()));
  dest.capacity(static_cast<int>(bv.size()));

  for(const auto &literal : bv)
  {
    if(!literal.is_false())
      dest.push(Minisat::mkLit(literal.var_no(), literal.sign()));
  }
}

template<typename T>
tvt satcheck_minisat2_baset<T>::l_get(literalt a) const
{
  if(a.is_true())
    return tvt(true);
  else if(a.is_false())
    return tvt(false);

  tvt result;

  if(a.var_no()>=(unsigned)solver->model.size())
    return tvt::unknown();

  using Minisat::lbool;

  if(solver->model[a.var_no()]==l_True)
    result=tvt(true);
  else if(solver->model[a.var_no()]==l_False)
    result=tvt(false);
  else
    return tvt::unknown();

  if(a.sign())
    result=!result;

  return result;
}

template<typename T>
void satcheck_minisat2_baset<T>::set_polarity(literalt a, bool value)
{
  PRECONDITION(!a.is_constant());

  using Minisat::lbool;

  try
  {
    add_variables();
    solver->setPolarity(a.var_no(), value ? l_True : l_False);
  }
  catch(Minisat::OutOfMemoryException)
  {
    log.error() << "SAT checker ran out of memory" << messaget::eom;
    status = statust::ERROR;
    throw std::bad_alloc();
  }
}

template<typename T>
void satcheck_minisat2_baset<T>::interrupt()
{
  solver->interrupt();
}

template<typename T>
void satcheck_minisat2_baset<T>::clear_interrupt()
{
  solver->clearInterrupt();
}

const std::string satcheck_minisat_no_simplifiert::solver_text()
{
  return "MiniSAT 2.2.1 without simplifier";
}

const std::string satcheck_minisat_simplifiert::solver_text()
{
  return "MiniSAT 2.2.1 with simplifier";
}

template<typename T>
void satcheck_minisat2_baset<T>::add_variables()
{
  while((unsigned)solver->nVars()<no_variables())
    solver->newVar();
}

template<typename T>
void satcheck_minisat2_baset<T>::lcnf(const bvt &bv)
{
  try
  {
    add_variables();

    for(const auto &literal : bv)
    {
      if(literal.is_true())
        return;
      else if(!literal.is_false())
      {
        INVARIANT(
          literal.var_no() < (unsigned)solver->nVars(),
          "variable not added yet");
      }
    }

    Minisat::vec<Minisat::Lit> c;

    convert(bv, c);

    // Note the underscore.
    // Add a clause to the solver without making superflous internal copy.

    solver->addClause_(c);

    if(solver_hardness)
    {
      // To map clauses to lines of program code, track clause indices in the
      // dimacs cnf output. Dimacs output is generated after processing
      // clauses to remove duplicates and clauses that are trivially true.
      // Here, a clause is checked to see if it can be thus eliminated. If
      // not, add the clause index to list of clauses in
      // solver_hardnesst::register_clause().
      static size_t cnf_clause_index = 0;
      bvt cnf;
      bool clause_removed = process_clause(bv, cnf);

      if(!clause_removed)
        cnf_clause_index++;

      solver_hardness->register_clause(
        bv, cnf, cnf_clause_index, !clause_removed);
    }

    clause_counter++;
  }
  catch(const Minisat::OutOfMemoryException &)
  {
    log.error() << "SAT checker ran out of memory" << messaget::eom;
    status = statust::ERROR;
    throw std::bad_alloc();
  }
}

#ifndef _WIN32

/*
static Minisat::Solver *solver_to_interrupt=nullptr;

static void interrupt_solver(int signum)
{
  (void)signum; // unused parameter -- just removing the name trips up cpplint
  solver_to_interrupt->interrupt();
}
*/

#endif

template <typename T>
propt::resultt satcheck_minisat2_baset<T>::do_prop_solve()
{
  PRECONDITION(status != statust::ERROR);

  log.statistics() << (no_variables() - 1) << " variables, "
                   << solver->nClauses() << " clauses" << messaget::eom;

  status = statust::ERROR;
  return resultt::P_ERROR;

  /*
  try
  {
    add_variables();

    if(!solver->okay())
    {
      log.status() << "SAT checker inconsistent: instance is UNSATISFIABLE"
                   << messaget::eom;
      status = statust::UNSAT;
      return resultt::P_UNSATISFIABLE;
    }

    // if assumptions contains false, we need this to be UNSAT
    for(const auto &assumption : assumptions)
    {
      if(assumption.is_false())
      {
        log.status() << "got FALSE as assumption: instance is UNSATISFIABLE"
                     << messaget::eom;
        status = statust::UNSAT;
        return resultt::P_UNSATISFIABLE;
      }
    }

    Minisat::vec<Minisat::Lit> solver_assumptions;
    convert(assumptions, solver_assumptions);

    using Minisat::lbool;

#ifndef _WIN32

    void (*old_handler)(int) = SIG_ERR;

    if(time_limit_seconds != 0)
    {
      solver_to_interrupt = solver.get();
      old_handler = signal(SIGALRM, interrupt_solver);
      if(old_handler == SIG_ERR)
        log.warning() << "Failed to set solver time limit" << messaget::eom;
      else
        alarm(time_limit_seconds);
    }

    lbool solver_result = solver->solveLimited(solver_assumptions);

    if(old_handler != SIG_ERR)
    {
      alarm(0);
      signal(SIGALRM, old_handler);
      solver_to_interrupt = solver.get();
    }

#else // _WIN32

    if(time_limit_seconds != 0)
    {
      log.warning() << "Time limit ignored (not supported on Win32 yet)"
                    << messaget::eom;
    }

    lbool solver_result = solver->solve(solver_assumptions) ? l_True : l_False;

#endif

    if(solver_result == l_True)
    {
      log.status() << "SAT checker: instance is SATISFIABLE" << messaget::eom;
      CHECK_RETURN(solver->model.size() > 0);
      status = statust::SAT;
      return resultt::P_SATISFIABLE;
    }

    if(solver_result == l_False)
    {
      log.status() << "SAT checker: instance is UNSATISFIABLE" << messaget::eom;
      status = statust::UNSAT;
      return resultt::P_UNSATISFIABLE;
    }

    log.status() << "SAT checker: timed out or other error" << messaget::eom;
    status = statust::ERROR;
    return resultt::P_ERROR;
  }
  catch(const Minisat::OutOfMemoryException &)
  {
    log.error() << "SAT checker ran out of memory" << messaget::eom;
    status=statust::ERROR;
    return resultt::P_ERROR;
  }
  */
}

template<typename T>
void satcheck_minisat2_baset<T>::set_assignment(literalt a, bool value)
{
  PRECONDITION(!a.is_constant());

  try
  {
    unsigned v = a.var_no();
    bool sign = a.sign();

    // MiniSat2 kills the model in case of UNSAT
    solver->model.growTo(v + 1);
    value ^= sign;
    solver->model[v] = Minisat::lbool(value);
  }
  catch(const Minisat::OutOfMemoryException &)
  {
    log.error() << "SAT checker ran out of memory" << messaget::eom;
    status = statust::ERROR;
    throw std::bad_alloc();
  }
}

template <typename T>
satcheck_minisat2_baset<T>::satcheck_minisat2_baset(
  message_handlert &message_handler)
  : cnf_solvert(message_handler),
    solver(util_make_unique<T>()),
    time_limit_seconds(0)
{
}

template <typename T>
satcheck_minisat2_baset<T>::~satcheck_minisat2_baset() = default;

template<typename T>
bool satcheck_minisat2_baset<T>::is_in_conflict(literalt a) const
{
  int v=a.var_no();

  for(int i=0; i<solver->conflict.size(); i++)
    if(var(solver->conflict[i])==v)
      return true;

  return false;
}

template<typename T>
void satcheck_minisat2_baset<T>::set_assumptions(const bvt &bv)
{
  // We filter out 'true' assumptions which cause an assertion violation
  // in Minisat2.
  assumptions.clear();
  for(const auto &assumption : bv)
  {
    if(!assumption.is_true())
    {
      assumptions.push_back(assumption);
    }
  }
}

template class satcheck_minisat2_baset<Minisat::Solver>;
template class satcheck_minisat2_baset<Minisat::SimpSolver>;

void satcheck_minisat_simplifiert::set_frozen(literalt a)
{
  try
  {
    if(!a.is_constant())
    {
      add_variables();
      solver->setFrozen(a.var_no(), true);
    }
  }
  catch(const Minisat::OutOfMemoryException &)
  {
    log.error() << "SAT checker ran out of memory" << messaget::eom;
    status = statust::ERROR;
    throw std::bad_alloc();
  }
}

bool satcheck_minisat_simplifiert::is_eliminated(literalt a) const
{
  PRECONDITION(!a.is_constant());

  return solver->isEliminated(a.var_no());
}
