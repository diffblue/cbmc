/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "satcheck_minisat2.h"

#ifndef _MSC_VER
#include <inttypes.h>
#include <signal.h>
#include <unistd.h>
#endif

#include <limits>
#include <stack>

#include <util/invariant.h>
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

  forall_literals(it, bv)
    if(!it->is_false())
      dest.push(Minisat::mkLit(it->var_no(), it->sign()));
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

  try
  {
    add_variables();
    solver->setPolarity(a.var_no(), value);
  }
  catch(Minisat::OutOfMemoryException)
  {
    messaget::error() << "SAT checker ran out of memory" << eom;
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

    forall_literals(it, bv)
    {
      if(it->is_true())
        return;
      else if(!it->is_false())
      {
        INVARIANT(
          it->var_no() < (unsigned)solver->nVars(), "variable not added yet");
      }
    }

    Minisat::vec<Minisat::Lit> c;

    convert(bv, c);

    // Note the underscore.
    // Add a clause to the solver without making superflous internal copy.

    solver->addClause_(c);

    clause_counter++;
  }
  catch(const Minisat::OutOfMemoryException &)
  {
    messaget::error() << "SAT checker ran out of memory" << eom;
    status = statust::ERROR;
    throw std::bad_alloc();
  }
}

#ifndef _WIN32

static Minisat::Solver *solver_to_interrupt=nullptr;

static void interrupt_solver(int signum)
{
  solver_to_interrupt->interrupt();
}

#endif

template<typename T>
propt::resultt satcheck_minisat2_baset<T>::prop_solve()
{
  PRECONDITION(status != statust::ERROR);

  {
    messaget::status() <<
      (no_variables()-1) << " variables, " <<
      solver->nClauses() << " clauses" << eom;
  }

  try
  {
    add_variables();

    if(!solver->okay())
    {
      messaget::status() <<
        "SAT checker inconsistent: instance is UNSATISFIABLE" << eom;
    }
    else
    {
      // if assumptions contains false, we need this to be UNSAT
      bool has_false=false;

      forall_literals(it, assumptions)
        if(it->is_false())
          has_false=true;

      if(has_false)
      {
        messaget::status() <<
          "got FALSE as assumption: instance is UNSATISFIABLE" << eom;
      }
      else
      {
        Minisat::vec<Minisat::Lit> solver_assumptions;
        convert(assumptions, solver_assumptions);

        using Minisat::lbool;

#ifndef _WIN32

        void (*old_handler)(int)=SIG_ERR;

        if(time_limit_seconds!=0)
        {
          solver_to_interrupt=solver;
          old_handler=signal(SIGALRM, interrupt_solver);
          if(old_handler==SIG_ERR)
            warning() << "Failed to set solver time limit" << eom;
          else
            alarm(time_limit_seconds);
        }

        lbool solver_result=solver->solveLimited(solver_assumptions);

        if(old_handler!=SIG_ERR)
        {
          alarm(0);
          signal(SIGALRM, old_handler);
          solver_to_interrupt=solver;
        }

#else // _WIN32

        if(time_limit_seconds!=0)
        {
          messaget::warning() <<
            "Time limit ignored (not supported on Win32 yet)" << messaget::eom;
        }

        lbool solver_result=
          solver->solve(solver_assumptions) ? l_True : l_False;

#endif

        if(solver_result==l_True)
        {
          messaget::status() <<
            "SAT checker: instance is SATISFIABLE" << eom;
          CHECK_RETURN(solver->model.size()>0);
          status=statust::SAT;
          return resultt::P_SATISFIABLE;
        }
        else if(solver_result==l_False)
        {
          messaget::status() <<
            "SAT checker: instance is UNSATISFIABLE" << eom;
        }
        else
        {
          messaget::status() <<
            "SAT checker: timed out or other error" << eom;
          status=statust::ERROR;
          return resultt::P_ERROR;
        }
      }
    }

    status=statust::UNSAT;
    return resultt::P_UNSATISFIABLE;
  }
  catch(const Minisat::OutOfMemoryException &)
  {
    messaget::error() <<
      "SAT checker ran out of memory" << eom;
    status=statust::ERROR;
    return resultt::P_ERROR;
  }
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
    messaget::error() << "SAT checker ran out of memory" << eom;
    status = statust::ERROR;
    throw std::bad_alloc();
  }
}

template<typename T>
satcheck_minisat2_baset<T>::satcheck_minisat2_baset(T *_solver):
  solver(_solver), time_limit_seconds(0)
{
}

template<>
satcheck_minisat2_baset<Minisat::Solver>::~satcheck_minisat2_baset()
{
  delete solver;
}

template<>
satcheck_minisat2_baset<Minisat::SimpSolver>::~satcheck_minisat2_baset()
{
  delete solver;
}

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
  assumptions=bv;

  forall_literals(it, assumptions)
    if(it->is_true())
    {
      assumptions.clear();
      break;
    }
}

satcheck_minisat_no_simplifiert::satcheck_minisat_no_simplifiert():
  satcheck_minisat2_baset<Minisat::Solver>(new Minisat::Solver)
{
}

satcheck_minisat_simplifiert::satcheck_minisat_simplifiert():
  satcheck_minisat2_baset<Minisat::SimpSolver>(new Minisat::SimpSolver)
{
}

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
    messaget::error() << "SAT checker ran out of memory" << eom;
    status = statust::ERROR;
    throw std::bad_alloc();
  }
}

bool satcheck_minisat_simplifiert::is_eliminated(literalt a) const
{
  PRECONDITION(!a.is_constant());

  return solver->isEliminated(a.var_no());
}
