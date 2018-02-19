/*******************************************************************\

 Module: Unit tests for bv refinement

 Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

#include <testing-utils/use_catch.h>

#include <iostream>
#include <solvers/refinement/bv_refinement.h>
#include <solvers/sat/satcheck.h>
#include <util/arith_tools.h>
#include <util/config.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>
#include <util/std_types.h>
#include <util/symbol_table.h>

static void test_solver(decision_proceduret &solver, const namespacet &ns)
{
  WHEN("We give two contradictory inputs")
  {
    const symbol_exprt s1{"symbol_var1", signedbv_typet(32)};
    const exprt constant_int = from_integer(99, signedbv_typet(32));
    const binary_relation_exprt lemma1{s1, ID_ge, constant_int};
    const not_exprt lemma2{lemma1};

    WHEN("The inputs are not simplified")
    {
      solver << lemma1;
      solver << lemma2;

      THEN("it should be unsatisfiable")
      {
        const auto result = solver();
        REQUIRE(result == decision_proceduret::resultt::D_UNSATISFIABLE);
      }
    }

    WHEN("The inputs are simplified")
    {
      simplify_expr(lemma1, ns);
      simplify_expr(lemma2, ns);
      solver << lemma1;
      solver << lemma2;

      THEN("it should be unsatisfiable")
      {
        const auto result = solver();
        REQUIRE(result == decision_proceduret::resultt::D_UNSATISFIABLE);
      }
    }
  }

  WHEN("We give an array access")
  {
    const symbol_exprt s1{"symbol_var1", signedbv_typet(32)};
    const symbol_exprt s2{"symbol_var2", array_typet(unsignedbv_typet(16), s1)};
    const exprt constant_int = from_integer(99, signedbv_typet(32));
    const exprt constant_char = from_integer('A', unsignedbv_typet(16));
    const index_exprt index_expr{
      s2, plus_exprt(s1, from_integer(3, signedbv_typet(32)))};
    const equal_exprt lemma1{index_expr, constant_char};

    WHEN("The input is not simplified")
    {
      solver << lemma1;

      THEN("it should be satisfiable")
      {
        const auto result = solver();
        REQUIRE(result == decision_proceduret::resultt::D_SATISFIABLE);
      }
    }

    WHEN("The input is simplified")
    {
      simplify_expr(lemma1, ns);
      solver << lemma1;

      THEN("it should be satisfiable")
      {
        const auto result = solver();
        REQUIRE(result == decision_proceduret::resultt::D_SATISFIABLE);
      }
    }
  }

  WHEN("We give a conjunction of constraints on arrays")
  {
    const symbol_exprt length{"symbol_length_1", signedbv_typet(32)};
    const symbol_exprt array{
      "symbol_array1", array_typet(unsignedbv_typet(16), length)};
    const symbol_exprt var{"symbol_univ_var10", signedbv_typet(32)};

    exprt::operandst ops;

    // array[1+var] == 'Z'
    ops.push_back(
      equal_exprt(
        index_exprt(
          array, plus_exprt(from_integer(1, signedbv_typet(32)), var)),
        from_integer('Z', unsignedbv_typet(16))));

    // array[2+var] == 'A'
    ops.push_back(
      equal_exprt(
        index_exprt(
          array, plus_exprt(from_integer(2, signedbv_typet(32)), var)),
        from_integer('A', unsignedbv_typet(16))));

    // array[3+var] == 'A'
    ops.push_back(
      equal_exprt(
        index_exprt(
          array, plus_exprt(from_integer(3, signedbv_typet(32)), var)),
        from_integer('A', unsignedbv_typet(16))));

    // array[4+var] == 'C'
    ops.push_back(
      equal_exprt(
        index_exprt(
          array, plus_exprt(from_integer(4, signedbv_typet(32)), var)),
        from_integer('C', unsignedbv_typet(16))));

    // array[var] = 'C'
    ops.push_back(
      equal_exprt(
        index_exprt(array, var), from_integer('C', unsignedbv_typet(16))));

    // var <= 83
    ops.push_back(
      binary_relation_exprt(var, ID_ge, from_integer(83, signedbv_typet(32))));

    // var >= 87
    ops.push_back(
      not_exprt(
        binary_relation_exprt(
          var, ID_ge, from_integer(87, signedbv_typet(32)))));

    exprt lemma1 = conjunction(ops);
    solver << lemma1;

    WHEN("The input is simplified")
    {
      exprt copy{lemma1};
      simplify_expr(copy, ns);
      solver << copy;

      THEN("it should be satisfiable")
      {
        const auto result = solver();
        REQUIRE(result == decision_proceduret::resultt::D_SATISFIABLE);
      }
    }

    WHEN("The input is not simplified")
    {
      solver << lemma1;

      THEN("it should be satisfiable")
      {
        const auto result = solver();
        REQUIRE(result == decision_proceduret::resultt::D_SATISFIABLE);
      }
    }
  }
}

SCENARIO("add lemma", "[core][solvers][refinement][bv_refinement]")
{
  // Without this line, the program aborts with:
  // `Reason: pointer must have non-zero width`
  config.set_arch("none");

  stream_message_handlert log{std::cout};

  GIVEN("Boolbv solver with no simplifier")
  {
    satcheck_no_simplifiert sat_check{log};
    symbol_tablet symbol_table;
    namespacet ns(symbol_table);
    boolbvt solver(ns, sat_check);
    solver.set_message_handler(log);

    test_solver(solver, ns);
  }

  GIVEN("Boolbv solver with simplifier")
  {
    satcheck_minisat_simplifiert sat_check_simplifier{log};
    symbol_tablet symbol_table;
    namespacet ns{symbol_table};
    boolbvt solver{ns, sat_check_simplifier};
    solver.set_message_handler(log);

    test_solver(solver, ns);
  }

  GIVEN("BV pointers solver with no simplifier")
  {
    satcheck_minisat_no_simplifiert sat_check_no_simplifier{log};
    symbol_tablet symbol_table;
    namespacet ns{symbol_table};
    bv_pointerst solver{ns, sat_check_no_simplifier};
    solver.set_message_handler(log);

    test_solver(solver, ns);
  }

  GIVEN("BV pointers solver with simplifier")
  {
    satcheck_minisat_simplifiert sat_check_simplifier{log};
    symbol_tablet symbol_table;
    namespacet ns{symbol_table};
    bv_pointerst solver(ns, sat_check_simplifier);
    solver.set_message_handler(log);

    test_solver(solver, ns);
  }

  GIVEN("BV refinement solver with no simplifier")
  {
    satcheck_minisat_no_simplifiert sat_check_no_simplifier{log};
    symbol_tablet symbol_table;
    namespacet ns{symbol_table};
    bv_refinementt::infot info;
    info.ns = &ns;
    info.prop = &sat_check_no_simplifier;
    info.refine_arithmetic = true;
    info.refine_arrays = true;
    info.max_node_refinement = 5;
    bv_refinementt solver{info};
    solver.set_message_handler(log);

    test_solver(solver, ns);
  }

  GIVEN("BV refinement solver with simplifier")
  {
    satcheck_minisat_simplifiert sat_check_simplifier{log};
    symbol_tablet symbol_table;
    namespacet ns{symbol_table};
    bv_refinementt::infot info;
    info.ns = &ns;
    info.prop = &sat_check_simplifier;
    info.refine_arithmetic = true;
    info.refine_arrays = true;
    info.max_node_refinement = 5;
    bv_refinementt solver{info};
    solver.set_message_handler(log);

    test_solver(solver, ns);
  }
}
