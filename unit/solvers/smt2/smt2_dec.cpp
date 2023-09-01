//
// Author: Julian Parsert
//

#include <testing-utils/use_catch.h>
#include <namespace.h>
#include <symbol_table.h>
#include <message.h>
#include <solvers/smt2/smt2_dec.h>
#include <util/tempfile.h>

TEST_CASE(
  "smt2_dect::smt2_dect decision_procedure_text.",
  "[core][solvers][smt2]")
{
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  null_message_handlert message_h;

  smt2_dect solver(
    ns, "test_solver", "generated to test the solver.", "BV", smt2_dect::solvert::Z3, message_h, {"-T:5"});

  CHECK(solver.decision_procedure_text() == "SMT2 BV using Z3");

}

TEST_CASE(
  "smt2_dect::smt2_dect sygus commandline argument for cvc5.",
  "[core][solvers][smt2]")
{
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  std::stringstream ss;
  stream_message_handlert message_h(ss);
  message_h.set_verbosity(10);

  smt2_dect solver(
    ns, "solver_version", "generated to test the solver version output.", "BV", smt2_dect::solvert::Z3, message_h, {"--version"});

  decision_proceduret::resultt res = solver();

  // CHECK(get message == "VERSION")
  // output should start with "This is cvc5 version"

  CHECK(res == decision_proceduret::resultt::D_ERROR);
}