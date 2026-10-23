/*******************************************************************\

Module: Unit tests for the propt and decision_proceduret state machines

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// Backend-independent unit tests for the solver state machine formalised in
/// propt and decision_proceduret. These use small mock back ends so that the
/// safety guarantees (status invalidation, exception handling, sticky ERROR
/// state) can be exercised in isolation, independently of which SAT solver is
/// configured.

#include <util/message.h>
#include <util/std_expr.h>

#include <solvers/decision_procedure.h>
#include <solvers/sat/cnf.h>
#include <testing-utils/use_catch.h>

#include <stdexcept>

/// Minimal concrete decision_proceduret that records how often the mutation
/// hooks are called and lets the test drive the result of dec_solve().
class mock_decision_proceduret : public decision_proceduret
{
public:
  bool throw_on_solve = false;
  resultt next_result = resultt::D_SATISFIABLE;
  std::size_t do_set_to_calls = 0;
  std::size_t do_handle_calls = 0;

  exprt get(const exprt &) const override
  {
    return nil_exprt{};
  }
  void print_assignment(std::ostream &) const override
  {
  }
  std::string decision_procedure_text() const override
  {
    return "mock decision procedure";
  }
  std::size_t get_number_of_solver_calls() const override
  {
    return 0;
  }

protected:
  void do_set_to(const exprt &, bool) override
  {
    ++do_set_to_calls;
  }
  exprt do_handle(const exprt &expr) override
  {
    ++do_handle_calls;
    return expr;
  }
  resultt dec_solve(const exprt &) override
  {
    if(throw_on_solve)
      throw std::runtime_error("mock decision procedure failure");
    return next_result;
  }
};

SCENARIO(
  "decision_proceduret state machine",
  "[core][solvers][decision_procedure][dp_state]")
{
  mock_decision_proceduret dp;
  const true_exprt constraint;

  GIVEN("a freshly constructed decision procedure")
  {
    THEN("the initial status is D_ERROR (not yet solved)")
    {
      REQUIRE(dp.get_status() == decision_proceduret::resultt::D_ERROR);
    }
  }

  GIVEN("a decision procedure that reports D_SATISFIABLE")
  {
    dp.next_result = decision_proceduret::resultt::D_SATISFIABLE;

    WHEN("operator() is invoked")
    {
      const auto result = dp();
      THEN("it returns and records the satisfiable result")
      {
        REQUIRE(result == decision_proceduret::resultt::D_SATISFIABLE);
        REQUIRE(dp.get_status() == decision_proceduret::resultt::D_SATISFIABLE);
      }
      THEN("a direct call to set_to() resets the status to D_ERROR")
      {
        dp.set_to(constraint, true);
        REQUIRE(dp.get_status() == decision_proceduret::resultt::D_ERROR);
        REQUIRE(dp.do_set_to_calls == 1);
      }
      THEN("set_to_true()/set_to_false() also reset the status")
      {
        dp.set_to_true(constraint);
        REQUIRE(dp.get_status() == decision_proceduret::resultt::D_ERROR);
        dp.next_result = decision_proceduret::resultt::D_SATISFIABLE;
        REQUIRE(dp() == decision_proceduret::resultt::D_SATISFIABLE);
        dp.set_to_false(constraint);
        REQUIRE(dp.get_status() == decision_proceduret::resultt::D_ERROR);
        REQUIRE(dp.do_set_to_calls == 2);
      }
      THEN("a direct call to handle() resets the status to D_ERROR")
      {
        dp.handle(constraint);
        REQUIRE(dp.get_status() == decision_proceduret::resultt::D_ERROR);
        REQUIRE(dp.do_handle_calls == 1);
      }
    }
  }

  GIVEN("a decision procedure that has reported D_SATISFIABLE")
  {
    dp.next_result = decision_proceduret::resultt::D_SATISFIABLE;
    REQUIRE(dp() == decision_proceduret::resultt::D_SATISFIABLE);

    WHEN("a subsequent solve throws")
    {
      dp.throw_on_solve = true;
      THEN("the exception propagates and the status is reset to D_ERROR")
      {
        REQUIRE_THROWS_AS(dp(), std::runtime_error);
        REQUIRE(dp.get_status() == decision_proceduret::resultt::D_ERROR);
      }
      THEN("the assumption-taking overload behaves the same way")
      {
        REQUIRE_THROWS_AS(dp(constraint), std::runtime_error);
        REQUIRE(dp.get_status() == decision_proceduret::resultt::D_ERROR);
      }
    }
  }
}

/// Minimal concrete propt (via cnft, which provides the Boolean operators)
/// that lets the test drive the result of do_prop_solve() and count clauses.
class mock_propt : public cnft
{
public:
  explicit mock_propt(message_handlert &message_handler) : cnft(message_handler)
  {
  }

  bool throw_on_solve = false;
  resultt next_result = resultt::P_SATISFIABLE;
  std::size_t clauses = 0;

  std::string solver_text() const override
  {
    return "mock propositional solver";
  }
  size_t no_clauses() const override
  {
    return clauses;
  }
  tvt l_get(literalt) const override
  {
    return tvt{true};
  }
  void set_assignment(literalt, bool) override
  {
  }
  bool is_in_conflict(literalt) const override
  {
    return false;
  }

protected:
  void do_lcnf(const bvt &) override
  {
    ++clauses;
  }
  resultt do_prop_solve(const bvt &) override
  {
    if(throw_on_solve)
      throw std::runtime_error("mock solver failure");
    return next_result;
  }
};

SCENARIO(
  "propt state machine (mock backend)",
  "[core][solvers][prop][prop_state]")
{
  null_message_handlert message_handler;
  mock_propt solver{message_handler};

  GIVEN("a freshly constructed solver")
  {
    THEN("the initial state is UNKNOWN")
    {
      REQUIRE(solver.get_status() == propt::statust::UNKNOWN);
    }
  }

  GIVEN("a solver that reports SAT")
  {
    solver.next_result = propt::resultt::P_SATISFIABLE;
    const literalt l = solver.new_variable();
    REQUIRE(solver.prop_solve() == propt::resultt::P_SATISFIABLE);
    REQUIRE(solver.get_status() == propt::statust::SAT);

    WHEN("a clause is added via lcnf()")
    {
      solver.lcnf(bvt{l});
      THEN("the state is invalidated to UNKNOWN")
      {
        REQUIRE(solver.get_status() == propt::statust::UNKNOWN);
      }
    }
    WHEN("a unit constraint is added via l_set_to()")
    {
      solver.l_set_to(l, true);
      THEN("the state is invalidated to UNKNOWN")
      {
        REQUIRE(solver.get_status() == propt::statust::UNKNOWN);
      }
    }
    WHEN("a new variable is allocated")
    {
      solver.new_variable();
      THEN("the state is invalidated to UNKNOWN")
      {
        REQUIRE(solver.get_status() == propt::statust::UNKNOWN);
      }
    }
  }

  GIVEN("a solver whose do_prop_solve() throws")
  {
    solver.throw_on_solve = true;

    WHEN("prop_solve() is called")
    {
      THEN("the exception propagates and the state becomes ERROR")
      {
        REQUIRE_THROWS_AS(solver.prop_solve(), std::runtime_error);
        REQUIRE(solver.get_status() == propt::statust::ERROR);
      }
    }
  }

  GIVEN("a solver in the ERROR state")
  {
    solver.throw_on_solve = true;
    REQUIRE_THROWS_AS(solver.prop_solve(), std::runtime_error);
    REQUIRE(solver.get_status() == propt::statust::ERROR);
    const literalt l = solver.new_variable();

    WHEN("constraints or variables are added")
    {
      THEN("the ERROR state is sticky: it is not cleared by lcnf()")
      {
        solver.lcnf(bvt{l});
        REQUIRE(solver.get_status() == propt::statust::ERROR);
      }
      THEN("the ERROR state is not cleared by l_set_to()")
      {
        solver.l_set_to(l, true);
        REQUIRE(solver.get_status() == propt::statust::ERROR);
      }
      THEN("the ERROR state is not cleared by new_variable()")
      {
        solver.new_variable();
        REQUIRE(solver.get_status() == propt::statust::ERROR);
      }
    }
  }
}
